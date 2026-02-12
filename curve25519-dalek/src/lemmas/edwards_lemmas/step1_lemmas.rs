//! Lemmas for step_1 of Edwards point decompression
//!
//! ## step_1 Function
//!
//! ```text
//! fn step_1(repr: &CompressedEdwardsY) -> (Choice, FieldElement, FieldElement, FieldElement)
//!                                          // (is_valid, X, Y, Z)
//! ```
//!
//! Decodes the Y coordinate from compressed bytes and computes a candidate X coordinate.
//! - Extracts Y from `repr`, sets Z = 1
//! - Computes u = Y² - 1 and v = d·Y² + 1
//! - Calls sqrt_ratio_i(u, v) to find X such that X² = u/v (if it exists)
//! - Returns `is_valid = Choice(1)` if Y is valid (u/v is a square), else `Choice(0)`
//!
//! ## Key Properties Proven
//!
//! 1. **Curve equation correctness**: If x² = (y² - 1)/(d·y² + 1), then (x, y) is on the curve
//! 2. **Validity correspondence**: sqrt_ratio_i success ↔ math_is_valid_y_coordinate
//! 3. **Edge cases**: u = 0 implies identity point, failure implies invalid Y
#![allow(unused_imports)]
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// sqrt_ratio to Curve Equation Connection
// =============================================================================
/// Lemma: If x² = u/v where u = y² - 1 and v = d·y² + 1,
/// then (x, y) satisfies the Edwards curve equation -x² + y² = 1 + d·x²·y²
///
/// This is the fundamental property that connects the square root computation
/// in decompress to the curve equation.
pub proof fn lemma_sqrt_ratio_implies_on_curve(x: nat, y: nat)
    requires
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let y2 = field_square(y);
            let u = field_sub(y2, 1);
            let v = field_add(field_mul(d, y2), 1);
            v != 0 && field_mul(field_square(x), v) == u
        }),
    ensures
        math_on_edwards_curve(x, y),
{
    // =======================================================================
    // Goal: math_on_edwards_curve(x, y), i.e., y² - x² = 1 + d·x²·y²
    //
    // Mathematical Proof:
    //   Given: x² · v = u, where u = y² - 1, v = d·y² + 1
    //   1. x²·(d·y² + 1) = y² - 1              [precondition]
    //   2. x²·d·y² + x² = y² - 1               [distributivity]
    //   3. d·x²·y² + x² = y² - 1               [commutativity]
    //   4. d·x²·y² + 1 = y² - x²               [rearrange: add 1, subtract x²]
    //   5. 1 + d·x²·y² = y² - x²               [commutativity of addition]
    //   This is the curve equation: -x² + y² = 1 + d·x²·y²  ✓
    // =======================================================================
    let p = p();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let dy2 = field_mul(d, y2);
    let u = field_sub(y2, 1);
    let v = field_add(dy2, 1);
    let x2y2 = field_mul(x2, y2);
    let d_x2y2 = field_mul(d, x2y2);
    let x2_dy2 = field_mul(x2, dy2);

    p_gt_2();

    assert(math_on_edwards_curve(x, y)) by {
        // Step 1: From precondition x² · v = u
        assert(field_mul(x2, v) == u);

        // Step 2: Distributivity - x² · (d·y² + 1) = x²·d·y² + x²
        assert(field_add(x2_dy2, x2) == u) by {
            lemma_field_mul_distributes_over_add(x2, dy2, 1);
            lemma_small_mod(x2, p);
        };

        // Step 3: Commutativity - x²·(d·y²) = d·(x²·y²)
        assert(x2_dy2 == d_x2y2) by {
            lemma_mul_mod_noop_right(x2 as int, (d * y2) as int, p as int);
            lemma_mul_mod_noop_right(d as int, (x2 * y2) as int, p as int);
            assert(x2 as int * (d as int * y2 as int) == d as int * (x2 as int * y2 as int)) by {
                lemma_mul_is_associative(x2 as int, d as int, y2 as int);
                lemma_mul_is_commutative(x2 as int, d as int);
                lemma_mul_is_associative(d as int, x2 as int, y2 as int);
            };
        };

        // Step 4: Rearrange d·x²·y² + x² = y² - 1 to d·x²·y² + 1 = y² - x²
        assert(field_add(d_x2y2, 1) == field_sub(y2, x2)) by {
            assert(field_add(d_x2y2, x2) == u);
            assert(d_x2y2 < p && x2 < p && y2 < p) by {
                lemma_mod_bound((d * x2y2) as int, p as int);
                lemma_mod_bound((x * x) as int, p as int);
                lemma_mod_bound((y * y) as int, p as int);
            };
            lemma_field_add_sub_rearrange(d_x2y2, x2, y2);
        };

        // Step 5: Commutativity of addition - 1 + d·x²·y² = d·x²·y² + 1
        assert(field_add(1, d_x2y2) == field_sub(y2, x2)) by {
            lemma_add_mod_noop(1, d_x2y2 as int, p as int);
            lemma_add_mod_noop(d_x2y2 as int, 1, p as int);
        };
    };
}

// =============================================================================
// Y-Coordinate Validity Lemmas
// =============================================================================
/// Lemma: Connects sqrt_ratio_i success to math_is_valid_y_coordinate
///
/// When sqrt_ratio_i returns (true, r), it means u/v is a square,
/// which is exactly what math_is_valid_y_coordinate checks.
pub proof fn lemma_sqrt_ratio_success_means_valid_y(y: nat, r: nat)
    requires
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let y2 = field_square(y);
            let v = field_add(field_mul(d, y2), 1);
            let u = field_sub(y2, 1);
            v != 0 && field_mul(field_square(r), v) == u % p()
        }),
    ensures
        math_is_valid_y_coordinate(y),
{
    // Goal: math_is_valid_y_coordinate(y)
    //
    // The spec has three cases:
    //   1. u % p == 0 → true
    //   2. v % p == 0 → false (but we have v ≠ 0)
    //   3. ∃ r < p: r² · v = u → true (we have witness r)
    p_gt_2();
    let p = p();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let y2 = field_square(y);
    let u = field_sub(y2, 1);
    let v = field_add(field_mul(d, y2), 1);

    // Show u < p and v < p (field operations return reduced values)
    assert(u < p) by {
        lemma_mod_bound((((y2 % p) + p) - (1nat % p)) as int, p as int);
    };
    assert(v < p) by {
        lemma_mod_bound(((d * y2) % p + 1) as int, p as int);
    };

    // Since u < p: u % p = u
    lemma_small_mod(u, p);

    // Since v < p and v ≠ 0: v % p ≠ 0
    lemma_small_mod(v, p);
    assert(v % p != 0);

    // Construct witness r' = r % p
    let r_prime = r % p;

    // r' < p
    lemma_mod_bound(r as int, p as int);
    assert(r_prime < p);

    // r'² = r² (squaring absorbs mod p)
    lemma_square_mod_noop(r);
    assert(field_square(r_prime) == field_square(r));

    // r'² · v = u (connecting to the existential)
    assert(field_mul(field_square(r_prime), v) == u % p);

    // Now trigger the spec's existential
    assert(math_is_valid_y_coordinate(y)) by {
        if u % p != 0 {
            // In the else branch - need existential witness
            assert(r_prime < p);
            assert(field_mul(field_square(r_prime), v) == u % p);
        }
    };
}

/// Connect sqrt_ratio_i result to curve semantics
///
/// When sqrt_ratio_i succeeds with v ≠ 0, we can prove:
/// - math_is_valid_y_coordinate(y)
/// - math_on_edwards_curve(x, y)
pub proof fn lemma_step1_curve_semantics(
    y: nat,  // fe51_as_canonical_nat(&Y)
    x: nat,  // fe51_as_canonical_nat(&X) from sqrt_ratio_i
)
    requires
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let y2 = field_square(y);
            let u = field_sub(y2, 1);
            let v = field_add(field_mul(d, y2), 1);
            // sqrt_ratio_i succeeded: x² · v = u (mod p)
            v != 0 && field_mul(field_square(x), v) == u % p()
        }),
    ensures
        math_is_valid_y_coordinate(y),
        math_on_edwards_curve(x, y),
{
    p_gt_2();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let y2 = field_square(y);
    let u_math = field_sub(y2, 1);
    let v_math = field_add(field_mul(d, y2), 1);

    // Goal 1: math_is_valid_y_coordinate(y)
    // From precondition: x²·v = u (mod p), so x is witness for valid Y
    assert(math_is_valid_y_coordinate(y)) by {
        lemma_sqrt_ratio_success_means_valid_y(y, x);
    };

    // Goal 2: math_on_edwards_curve(x, y)
    //
    // Mathematical reasoning:
    //   Precondition gives: x²·v == u % p
    //   lemma_sqrt_ratio_implies_on_curve requires: x²·v == u (not u % p)
    //   Bridge: Since u_math = field_sub(...) < p, we have u % p = u

    assert(math_on_edwards_curve(x, y)) by {
        // Step 1: u_math < p (field_sub returns reduced result)
        assert(u_math < p()) by {
            lemma_mod_bound((((y2 % p()) + p()) - (1nat % p())) as int, p() as int);
        };

        // Step 2: u_math % p == u_math (from Step 1)
        assert(u_math % p() == u_math) by {
            lemma_small_mod(u_math, p());
        };

        // Step 3: Transform precondition x²·v == u % p to x²·v == u
        assert(field_mul(field_square(x), v_math) == u_math);

        // Step 4: Apply curve equation derivation
        lemma_sqrt_ratio_implies_on_curve(x, y);
    };
}

// =============================================================================
// Edge Case Lemmas for step_1
// =============================================================================
// Note: lemma_square_matches_field_square is in field_lemmas/field_algebra_lemmas.rs.
/// When y² = 1 in decompress, (0, y) is on the Edwards curve.
/// This is the edge case where y = ±1 (identity-related points).
pub proof fn lemma_u_zero_implies_identity_point(y: nat)
    requires
        field_sub(field_square(y), 1) == 0,
    ensures
        field_square(y) == 1,
        math_on_edwards_curve(0, y),
        math_is_valid_y_coordinate(y),
{
    let p = p();
    p_gt_2();

    let y2 = field_square(y);

    // Step 1: Prove y² = 1
    //
    // Given: field_sub(y², 1) = 0
    // Expanding: field_sub(y2, 1) = (y2 + p - 1) % p  [since y2, 1 < p]
    //
    // Since field_sub(y2, 1) = 0, we have (y2 + p - 1) % p = 0, so y2 + p - 1 is a multiple of p.
    // Range: y2 ∈ [0, p) implies y2 + p - 1 ∈ [p-1, 2p-1)
    // The only multiple of p in [p-1, 2p-1) is p itself.
    // Therefore y2 + p - 1 = p, giving y2 = 1.
    //
    // Case analysis below rules out y2 = 0 and y2 >= 2 by showing they give field_sub(y2, 1) ≠ 0.
    assert(y2 == 1) by {
        // Establish bounds
        assert(y2 < p) by {
            lemma_mod_bound((y * y) as int, p as int);
        };
        assert(y2 % p == y2) by {
            lemma_small_mod(y2, p);
        };
        assert(1nat % p == 1) by {
            lemma_small_mod(1, p);
        };

        // Range of sum: y2 + p - 1 ∈ [p-1, 2p-1)
        let sum = (y2 + p - 1) as int;
        assert(p as int - 1 <= sum);  // since y2 >= 0
        assert(sum < 2 * p as int - 1);  // since y2 < p

        // Case analysis: only y2 == 1 gives sum % p == 0
        if y2 == 0 {
            // sum = p - 1, and (p - 1) % p = p - 1 ≠ 0
            assert(sum == p as int - 1);
            assert(sum % p as int == (p - 1) as int) by {
                lemma_small_mod((p - 1) as nat, p);
            };
            // This contradicts field_sub(y2, 1) = 0
        } else if y2 >= 2 {
            // sum = y2 + p - 1 >= p + 1
            assert(sum >= p as int + 1);
            // sum % p = sum - p = y2 - 1 >= 1
            assert(sum % p as int == y2 as int - 1) by {
                lemma_small_mod((y2 - 1) as nat, p);
                lemma_mod_multiples_vanish(-1, sum, p as int);
            };
            // y2 - 1 >= 1 ≠ 0, contradicts field_sub(y2, 1) = 0
        }
        // The only remaining case is y2 == 1

    };

    // Step 2: Prove (0, y) is on the curve
    // Curve equation: -x² + y² = 1 + d·x²·y²
    // With x = 0 and y² = 1: both sides equal 1
    assert(math_on_edwards_curve(0, y)) by {
        lemma_small_mod(0, p);
        lemma_small_mod(1, p);

        let d = fe51_as_canonical_nat(&EDWARDS_D);
        let x2 = field_square(0);
        let x2y2 = field_mul(x2, y2);
        let d_x2y2 = field_mul(d, x2y2);

        // x2 = (0 * 0) % p = 0
        assert(x2 == 0) by {
            assert(0int * 0int == 0int) by {
                lemma_mul_basics(0int);
            }
            lemma_small_mod(0nat, p);
        }

        // x2y2 = (0 * y2) % p = 0
        assert(x2y2 == 0) by {
            assert(0int * (y2 as int) == 0int) by {
                lemma_mul_basics(y2 as int);
            }
            lemma_small_mod(0nat, p);
        }

        // d_x2y2 = (d * 0) % p = 0
        assert(d_x2y2 == 0) by {
            assert((d as int) * 0int == 0int) by {
                lemma_mul_basics(d as int);
            }
            lemma_small_mod(0nat, p);
        }

        // RHS: field_add(1, 0) = (1 + 0) % p = 1
        assert(field_add(1, d_x2y2) == 1) by {
            assert(d_x2y2 == 0);
            lemma_small_mod(1nat, p);
        }

        // LHS: y² - 0 = y² = 1
        // field_sub(y2, x2) = (((y2 % p) + p) - (x2 % p)) % p
        // = ((1 + p) - 0) % p = (p + 1) % p = 1
        assert(field_sub(y2, x2) == 1) by {
            assert(x2 == 0);
            assert(y2 == 1);
            // field_sub(1, 0) = (((1 % p) + p) - (0 % p)) % p
            //                      = ((1 + p) - 0) % p
            //                      = (p + 1) % p = 1
            assert(1nat % p == 1) by {
                lemma_small_mod(1nat, p);
            }
            assert(0nat % p == 0) by {
                lemma_small_mod(0nat, p);
            }
            // (p + 1) % p = 1
            assert((p + 1) % p == 1) by {
                lemma_mod_adds(p as int, 1, p as int);
                lemma_mod_self_0(p as int);
                lemma_small_mod(1nat, p);
            }
        };

        // LHS == RHS == 1, so curve equation holds
    };

    // Step 3: Prove math_is_valid_y_coordinate(y)
    // From the spec: when u % p == 0, it returns true directly
    assert(math_is_valid_y_coordinate(y)) by {
        lemma_small_mod(0, p);
        // By definition of math_is_valid_y_coordinate, when u % p == 0, it's true
    };
}

/// When sqrt_ratio_i fails with v ≠ 0 and u ≠ 0, y is not a valid y-coordinate.
///
/// This follows from lemma_no_square_root_when_times_i:
/// - sqrt_ratio_i failing means it found x with x²·v = i·u (from precondition)
/// - By lemma_no_square_root_when_times_i, no r exists with r²·v = u or -u
/// - Therefore math_is_valid_y_coordinate (which asks if such r exists) is false
///
/// ## Precondition about exists|x|
/// The caller must establish that there exists x with x²·v = i·u.
/// This comes from sqrt_ratio_i's postcondition `fe51_is_sqrt_ratio_times_i` when it fails.
pub proof fn lemma_sqrt_ratio_failure_means_invalid_y(y: nat, u: nat, v: nat)
    requires
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let y2 = field_square(y);
            u == field_sub(y2, 1) && v == field_add(field_mul(d, y2), 1)
        }),
        v % p() != 0,
        u % p() != 0,
        // There exists x such that x²·v = i·u (comes from sqrt_ratio_i failure)
        exists|x: nat| x < p() && #[trigger] field_mul(field_square(x), v) == (sqrt_m1() * u) % p(),
    ensures
        !math_is_valid_y_coordinate(y),
{
    // Goal: !math_is_valid_y_coordinate(y)
    //
    // math_is_valid_y_coordinate(y) is true iff:
    //   u % p == 0  OR  exists|r| r < p && r²·v == ±u
    //
    // We have from preconditions: u % p != 0 and v % p != 0
    // We'll show: forall r < p. r²·v ≠ ±u (negates the existential)
    // Therefore math_is_valid_y_coordinate(y) is false.
    // Step 1: Get the forall from lemma_no_square_root_when_times_i
    // The lemma now takes r as parameter
    // Note: Must use `assert forall|r|` (not `assert(forall|r|)`) to bind r in the by block
    // Explicit trigger matches math_is_valid_y_coordinate's trigger
    assert forall|r: nat| r < p() implies #[trigger] field_mul(field_square(r), v) != u % p()
        && field_mul(field_square(r), v) != field_neg(u) by {
        lemma_no_square_root_when_times_i(u, v, r);
    };

    // Step 2: Restate as negation of the existential
    // Explicit trigger matches math_is_valid_y_coordinate's trigger
    assert(forall|r: nat|
        r < p() ==> !(#[trigger] field_mul(field_square(r), v) == u % p() || field_mul(
            field_square(r),
            v,
        ) == field_neg(u)));
}

/// Main lemma for step_1: proves curve semantics from sqrt_ratio_i result.
/// It takes the mathematical values (nats) and proves the curve semantics.
///
/// ## Parameters
/// - `y`: The Y coordinate value
/// - `x`: The X coordinate value (from sqrt_ratio_i)
/// - `u_math`: Y² - 1 (mathematical value)
/// - `v_math`: d·Y² + 1 (mathematical value)
/// - `sqrt_ratio_succeeded`: The choice result from sqrt_ratio_i (as bool)
///
/// ## Proves
/// - sqrt_ratio_succeeded <==> math_is_valid_y_coordinate(y)
/// - sqrt_ratio_succeeded ==> math_on_edwards_curve(x, y)
pub proof fn lemma_step1_case_analysis(
    y: nat,
    x: nat,
    u_math: nat,
    v_math: nat,
    sqrt_ratio_succeeded: bool,
)
    requires
// u = Y² - 1, v = d·Y² + 1

        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let y2 = field_square(y);
            u_math == field_sub(y2, 1) && v_math == field_add(field_mul(d, y2), 1)
        }),
        // sqrt_ratio_i postconditions (encapsulated in spec function)
        // Includes both math correctness and boundedness (x < p, x % 2 == 0)
        sqrt_ratio_i_post(u_math, v_math, sqrt_ratio_succeeded, x),
    ensures
        sqrt_ratio_succeeded <==> math_is_valid_y_coordinate(y),
        sqrt_ratio_succeeded ==> math_on_edwards_curve(x, y),
{
    // Case analysis on sqrt_ratio_succeeded (sqrt_ratio_i success/failure)
    if sqrt_ratio_succeeded {
        // Case: sqrt_ratio_i returned true
        // Goal: math_is_valid_y_coordinate(y) && math_on_edwards_curve(x, y)
        if v_math != 0 {
            // Subcase: v ≠ 0 (main case)
            assert(math_is_valid_y_coordinate(y) && math_on_edwards_curve(x, y)) by {
                // From precondition: is_sqrt_ratio holds
                assert(is_sqrt_ratio(u_math, v_math, x));
                assert((x * x * v_math) % p() == u_math) by {
                    assert(u_math == field_canonical(u_math)) by {
                        lemma_small_mod(u_math, p());
                    }
                }

                // Convert to field_mul form for curve semantics
                lemma_is_sqrt_ratio_to_field(x, u_math, v_math);

                // Apply curve semantics lemma
                lemma_step1_curve_semantics(y, x);
            };
        } else {
            // Subcase: v = 0 (identity points y = ±1)
            assert(math_is_valid_y_coordinate(y) && math_on_edwards_curve(x, y)) by {
                // By contrapositive: sqrt_ratio_succeeded && v = 0 ==> u = 0
                assert(u_math == 0);
                // From precondition: u = 0 ==> x = 0
                assert(x == 0);
                // Identity point lemma
                lemma_u_zero_implies_identity_point(y);
            };
        }
    } else {
        // Case: sqrt_ratio_i returned false
        // Goal: !math_is_valid_y_coordinate(y)
        assert(!math_is_valid_y_coordinate(y)) by {
            // By contrapositive of (u = 0 ==> sqrt_ratio_succeeded): !sqrt_ratio_succeeded ==> u ≠ 0
            assert(u_math != 0);
            lemma_small_mod(u_math, p());
            assert(u_math % p() != 0);

            if v_math % p() == 0 {
                // Subcase: v = 0 (degenerate)
                // From math_is_valid_y_coordinate spec: v % p == 0 && u % p != 0 → false
                // (inlined from lemma_v_zero_u_nonzero_means_invalid_y)
            } else {
                // Subcase: v % p ≠ 0, sqrt_ratio_i failed means no square root exists
                // Since v_math < p(), we have v_math % p() = v_math, so v_math != 0
                assert(v_math != 0) by {
                    assert(v_math % p() != 0);
                    lemma_small_mod(v_math, p());
                };

                // Establish the antecedent: !sqrt_ratio_succeeded && u_math != 0 && v_math != 0
                assert(!sqrt_ratio_succeeded);
                assert(u_math != 0);

                // From precondition: is_sqrt_ratio_times_i(u_math, v_math, x)
                assert(is_sqrt_ratio_times_i(u_math, v_math, x));
                assert((x * x * v_math) % p() == (sqrt_m1() * u_math) % p());

                // Establish the existential for lemma_sqrt_ratio_failure_means_invalid_y
                // We need to prove: exists|r: nat| r < p() && field_mul(field_square(r), v_math) == (sqrt_m1() * u_math) % p()
                // The witness is x, and we know:
                //   - x < p() (from precondition)
                //   - (x * x * v_math) % p() == (sqrt_m1() * u_math) % p() (just established)

                // First show x satisfies the math_field form
                let x_sq = field_square(x);  // = (x * x) % p
                let lhs = field_mul(x_sq, v_math);  // = (x_sq * v_math) % p = ((x*x) % p * v_math) % p
                let rhs = (sqrt_m1() * u_math) % p();

                assert(lhs == rhs) by {
                    // lhs = ((x*x) % p * v_math) % p
                    // We know: (x * x * v_math) % p = rhs
                    // By mul_mod_noop: ((x*x) % p * v_math) % p = (x * x * v_math) % p
                    lemma_mul_mod_noop_left((x * x) as int, v_math as int, p() as int);
                };

                // Now we can assert the existential with x as witness
                assert(x < p() && field_mul(field_square(x), v_math) == (sqrt_m1() * u_math) % p());

                lemma_sqrt_ratio_failure_means_invalid_y(y, u_math, v_math);
            }
        };
    }
}

} // verus!
