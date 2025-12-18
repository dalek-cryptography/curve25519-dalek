//! Helper functions for scalar operations in MODIFIED CODE
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;

#[allow(unused_imports)]
use crate::lemmas::field_lemmas::u8_32_as_nat_injectivity_lemmas::*;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

// ============================================================================
// Core lemmas for Scalar::ZERO and Scalar::ONE
// ============================================================================
/// Lemma: bytes_to_nat of all-zero bytes equals 0
pub proof fn lemma_bytes_to_nat_zero()
    ensures
        bytes_to_nat(&Scalar::ZERO.bytes) == 0,
{
    // 0 * x == 0 for all terms
    assert forall|i: nat| i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Lemma: bytes_to_nat of ONE's bytes equals 1
pub proof fn lemma_bytes_to_nat_one()
    ensures
        bytes_to_nat(&Scalar::ONE.bytes) == 1,
{
    let bytes = Scalar::ONE.bytes;
    assert(bytes[0] == 1);
    // pow2(0) == 1
    lemma2_to64();
    // 0 * x == 0 for remaining terms
    assert forall|i: nat| 1 <= i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Combined lemma for ZERO: value is 0, less than L, and congruent to 0
pub proof fn lemma_scalar_zero_properties()
    ensures
        scalar_to_nat(&Scalar::ZERO) == 0,
        scalar_to_nat(&Scalar::ZERO) < group_order(),
        scalar_congruent_nat(&Scalar::ZERO, 0),
{
    lemma_bytes_to_nat_zero();
    lemma_small_mod(0nat, group_order());
}

/// Combined lemma for ONE: value is 1, less than L, and congruent to 1
pub proof fn lemma_scalar_one_properties()
    ensures
        scalar_to_nat(&Scalar::ONE) == 1,
        scalar_to_nat(&Scalar::ONE) < group_order(),
        scalar_congruent_nat(&Scalar::ONE, 1),
{
    lemma_bytes_to_nat_one();
    lemma_small_mod(1nat, group_order());
}

// ============================================================================
// Lemmas for From<T> implementations (scalar construction from integers)
// ============================================================================
/// Lemma: u8_32_as_nat_rec from index n is 0 when all bytes from n onwards are zero.
///
/// This is the key insight: the "suffix" part of the sum vanishes when trailing bytes are zero.
pub proof fn lemma_suffix_zero_when_bytes_zero(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat_rec(bytes, n) == 0,
    decreases 32 - n,
{
    let goal = u8_32_as_nat_rec(bytes, n) == 0;

    assert(goal) by {
        if n >= 32 {
            // Base case: u8_32_as_nat_rec(bytes, 32) == 0 by definition
        } else {
            // IH: u8_32_as_nat_rec(bytes, n+1) == 0
            assert(u8_32_as_nat_rec(bytes, (n + 1) as nat) == 0) by {
                lemma_suffix_zero_when_bytes_zero(bytes, (n + 1) as nat);
            }

            // bytes[n] == 0 and 0 * pow2(n*8) == 0
            assert(bytes[n as int] as nat * pow2((n * 8) as nat) == 0) by {
                lemma_mul_basics(pow2((n * 8) as nat) as int);
            }

        }
    }
}

/// Lemma: bytes_to_nat equals as_nat_prefix when trailing bytes are zero.
///
/// Mathematical proof:
///   bytes_to_nat = prefix(n) + suffix(n)    [by lemma_decomposition_prefix_rec]
///   suffix(n) = 0                           [by lemma_suffix_zero_when_bytes_zero]
///   Therefore: bytes_to_nat = prefix(n)
pub proof fn lemma_bytes_to_nat_with_trailing_zeros(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        bytes_to_nat(bytes) == as_nat_prefix(bytes, n),
{
    let goal = bytes_to_nat(bytes) == as_nat_prefix(bytes, n);

    assert(goal) by {
        // bytes_to_nat == u8_32_as_nat_rec(bytes, 0)
        assert(bytes_to_nat(bytes) == u8_32_as_nat_rec(bytes, 0)) by {
            lemma_u8_32_as_nat_equals_rec(bytes);
        }

        // u8_32_as_nat_rec(bytes, 0) == as_nat_prefix(bytes, n) + u8_32_as_nat_rec(bytes, n)
        assert(u8_32_as_nat_rec(bytes, 0) == as_nat_prefix(bytes, n) + u8_32_as_nat_rec(bytes, n))
            by {
            lemma_decomposition_prefix_rec(bytes, n);
        }

        // u8_32_as_nat_rec(bytes, n) == 0
        assert(u8_32_as_nat_rec(bytes, n) == 0) by {
            lemma_suffix_zero_when_bytes_zero(bytes, n);
        }
    }
}

// ============================================================================
// Bridge Lemmas: Connecting bytes_seq_to_nat to bytes_to_nat
//
// The key insight is that bytes_seq_to_nat (Horner form) and bytes_seq_to_nat_clear_aux
// (direct sum form) compute the same value.
// ============================================================================
/// Lemma: Horner form equals direct sum form for any sequence.
///
/// This is THE key lemma that connects the two recursion patterns:
/// - bytes_seq_to_nat uses Horner's method: b[0] + 256*(b[1] + 256*(...))
/// - bytes_seq_to_nat_clear_aux uses direct sums: b[0]*2^0 + b[1]*2^8 + ...
///
/// Both compute the same polynomial value.
pub proof fn lemma_bytes_seq_to_nat_equals_clear_aux(seq: Seq<u8>)
    ensures
        bytes_seq_to_nat(seq) == bytes_seq_to_nat_clear_aux(seq, seq.len() as nat),
    decreases seq.len(),
{
    let goal = bytes_seq_to_nat(seq) == bytes_seq_to_nat_clear_aux(seq, seq.len() as nat);

    assert(goal) by {
        if seq.len() == 0 {
            // Base case: both are 0
        } else {
            let tail = seq.skip(1);

            // IH: bytes_seq_to_nat(tail) == bytes_seq_to_nat_clear_aux(tail, tail.len())
            assert(bytes_seq_to_nat(tail) == bytes_seq_to_nat_clear_aux(tail, tail.len() as nat))
                by {
                lemma_bytes_seq_to_nat_equals_clear_aux(tail);
            }

            // bytes_seq_to_nat(seq) = seq[0] + 256 * bytes_seq_to_nat(tail)
            //                       = seq[0] + 256 * clear_aux(tail, n-1)
            //                       = clear_aux(seq, n)               [by lemma_horner_shift_equivalence]
            assert(seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(
                tail,
                (seq.len() - 1) as nat,
            ) == bytes_seq_to_nat_clear_aux(seq, seq.len() as nat)) by {
                lemma_horner_shift_equivalence(seq);
            }
        }
    }
}

/// Helper lemma: Shows that Horner's method equals the direct sum for a single step.
///
/// For a sequence [b₀, b₁, ..., bₙ₋₁]:
/// b₀ + 256 * Σᵢ₌₀ⁿ⁻² bᵢ₊₁ * 2^{8i} = Σᵢ₌₀ⁿ⁻¹ bᵢ * 2^{8i}
proof fn lemma_horner_shift_equivalence(seq: Seq<u8>)
    requires
        seq.len() > 0,
    ensures
        seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(seq.skip(1), (seq.len() - 1) as nat)
            == bytes_seq_to_nat_clear_aux(seq, seq.len() as nat),
    decreases seq.len(),
{
    let n = seq.len() as nat;
    let tail = seq.skip(1);

    if n == 1 {
        // Base case: seq = [b₀], tail = []
        // LHS: b₀ + 256 * 0 = b₀
        // RHS: clear_aux([b₀], 1) = 0 + b₀ * pow2(0) = b₀
        assert(seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(tail, 0)
            == bytes_seq_to_nat_clear_aux(seq, 1)) by {
            reveal_with_fuel(bytes_seq_to_nat_clear_aux, 2);
            lemma2_to64();
        }
    } else {
        // n > 1: Use lemma_shift_clear_aux
        assert(seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(tail, (n - 1) as nat)
            == bytes_seq_to_nat_clear_aux(seq, n)) by {
            lemma_shift_clear_aux(seq, tail, n);
        }
    }
}

/// Helper: Shows that 256 * clear_aux(tail, k) + seq[0] relates to clear_aux(seq, k+1)
proof fn lemma_shift_clear_aux(seq: Seq<u8>, tail: Seq<u8>, n: nat)
    requires
        n == seq.len() as nat,
        n > 1,
        tail == seq.skip(1),
        tail.len() == n - 1,
    ensures
        seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(tail, (n - 1) as nat)
            == bytes_seq_to_nat_clear_aux(seq, n),
    decreases n,
{
    let goal = seq[0] as nat + pow2(8) * bytes_seq_to_nat_clear_aux(tail, (n - 1) as nat)
        == bytes_seq_to_nat_clear_aux(seq, n);

    assert(goal) by {
        // lemma_clear_aux_shift_induction gives:
        //   seq[0] * pow2(0) + pow2(8) * clear_aux(tail, n-1) == clear_aux(seq, n)
        assert(seq[0] as nat * pow2(0) + pow2(8) * bytes_seq_to_nat_clear_aux(tail, (n - 1) as nat)
            == bytes_seq_to_nat_clear_aux(seq, n)) by {
            lemma_clear_aux_shift_induction(seq, tail, n, (n - 1) as nat);
        }

        // Since pow2(0) == 1, seq[0] * pow2(0) == seq[0]
        assert(seq[0] as nat * pow2(0) == seq[0] as nat) by {
            lemma2_to64();
        }
    }
}

/// Inductive helper for the shift proof
///
/// This lemma establishes the key relationship between Horner's method
/// and the direct sum representation:
///   seq[0] + 256 * clear_aux(tail, k) == clear_aux(seq, k+1)
proof fn lemma_clear_aux_shift_induction(seq: Seq<u8>, tail: Seq<u8>, n: nat, k: nat)
    requires
        n == seq.len() as nat,
        n > 0,
        tail == seq.skip(1),
        tail.len() == n - 1,
        k <= n - 1,
    ensures
        seq[0] as nat * pow2(0) + pow2(8) * bytes_seq_to_nat_clear_aux(tail, k)
            == bytes_seq_to_nat_clear_aux(seq, (k + 1) as nat),
    decreases k,
{
    let goal = seq[0] as nat * pow2(0) + pow2(8) * bytes_seq_to_nat_clear_aux(tail, k)
        == bytes_seq_to_nat_clear_aux(seq, (k + 1) as nat);

    assert(goal) by {
        reveal_with_fuel(bytes_seq_to_nat_clear_aux, 2);
        lemma2_to64();

        if k == 0 {
            // Base case: LHS = seq[0] * 1 + 256 * 0 = seq[0]
            //            RHS = clear_aux(seq, 1) = 0 + pow2(0) * seq[0] = seq[0]
            assert(seq[0] as nat * pow2(0) == pow2(0) * seq[0] as nat) by {
                lemma_mul_is_commutative(seq[0] as int, pow2(0) as int);
            }
        } else {
            let k1 = (k - 1) as nat;

            // Inductive hypothesis
            assert(seq[0] as nat * pow2(0) + pow2(8) * bytes_seq_to_nat_clear_aux(tail, k1)
                == bytes_seq_to_nat_clear_aux(seq, k)) by {
                lemma_clear_aux_shift_induction(seq, tail, n, k1);
            }

            // Key arithmetic: pow2(8) * pow2((k-1)*8) == pow2(k*8)
            assert(pow2(8) * pow2((k1 * 8) as nat) == pow2((k * 8) as nat)) by {
                lemma_pow2_adds(8, (k1 * 8) as nat);
                assert(8 + k1 * 8 == k * 8) by {
                    lemma_mul_is_distributive_sub(8, k as int, 1);
                }
            }

            // tail[k-1] == seq[k] since tail = seq.skip(1)
            assert(tail[k1 as int] == seq[k as int]);

            // Expand clear_aux(tail, k) using its definition
            let tail_prev = bytes_seq_to_nat_clear_aux(tail, k1);
            let tail_term = pow2((k1 * 8) as nat) * tail[k1 as int] as nat;

            // Distributive: 256 * (a + b) = 256 * a + 256 * b
            assert(pow2(8) * bytes_seq_to_nat_clear_aux(tail, k) == pow2(8) * tail_prev + pow2(8)
                * tail_term) by {
                lemma_mul_is_distributive_add(pow2(8) as int, tail_prev as int, tail_term as int);
            }

            // Associativity: 256 * (pow2((k-1)*8) * tail[k-1]) = pow2(k*8) * seq[k]
            assert(pow2(8) * tail_term == pow2((k * 8) as nat) * seq[k as int] as nat) by {
                lemma_mul_is_associative(
                    pow2(8) as int,
                    pow2((k1 * 8) as nat) as int,
                    tail[k1 as int] as int,
                );
            }

            // Chain: LHS = seq[0] + 256 * clear_aux(tail, k)
            //            = seq[0] + 256 * tail_prev + 256 * tail_term
            //            = clear_aux(seq, k) + pow2(k*8) * seq[k]   [by IH]
            //            = clear_aux(seq, k+1)                       [by definition]
        }
    }
}

/// Lemma: bytes_seq_to_nat_clear_aux equals as_nat_prefix when bytes match.
///
/// This connects sequences to arrays - trivial since both have identical structure.
pub proof fn lemma_clear_aux_equals_as_nat_prefix(seq: Seq<u8>, bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        seq.len() >= n,
        forall|i: int| #![auto] 0 <= i < n ==> seq[i] == bytes[i],
    ensures
        bytes_seq_to_nat_clear_aux(seq, n) == as_nat_prefix(bytes, n),
    decreases n,
{
    reveal(bytes_seq_to_nat_clear_aux);

    if n == 0 {
        // Both are 0: bytes_seq_to_nat_clear_aux(seq, 0) == 0 == as_nat_prefix(bytes, 0)
    } else {
        // IH: clear_aux(seq, n-1) == as_nat_prefix(bytes, n-1)
        assert(bytes_seq_to_nat_clear_aux(seq, (n - 1) as nat) == as_nat_prefix(
            bytes,
            (n - 1) as nat,
        )) by {
            lemma_clear_aux_equals_as_nat_prefix(seq, bytes, (n - 1) as nat);
        }

        // Both add the same term: element[n-1] * pow2((n-1)*8)
        assert(seq[(n - 1) as int] == bytes[(n - 1) as int]);
    }
}

/// Combined lemma: bytes_seq_to_nat equals as_nat_prefix for matching bytes.
///
/// This is the main bridge lemma used by From<T> implementations.
pub proof fn lemma_bytes_seq_to_nat_equals_as_nat_prefix(seq: Seq<u8>, bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        seq.len() == n,
        forall|i: int| #![auto] 0 <= i < n ==> seq[i] == bytes[i],
    ensures
        bytes_seq_to_nat(seq) == as_nat_prefix(bytes, n),
{
    assert(bytes_seq_to_nat(seq) == as_nat_prefix(bytes, n)) by {
        // Step 1: Horner == direct sum (on sequences)
        assert(bytes_seq_to_nat(seq) == bytes_seq_to_nat_clear_aux(seq, n)) by {
            lemma_bytes_seq_to_nat_equals_clear_aux(seq);
        }

        // Step 2: direct sum on seq == direct sum on array
        assert(bytes_seq_to_nat_clear_aux(seq, n) == as_nat_prefix(bytes, n)) by {
            lemma_clear_aux_equals_as_nat_prefix(seq, bytes, n);
        }
    }
}

/// Lemma: bytes_to_nat of a 32-byte array with only the first byte set equals that byte.
///
/// This is a special case of lemma_bytes_to_nat_with_trailing_zeros for n=1.
pub proof fn lemma_bytes_to_nat_first_byte_only(bytes: &[u8; 32])
    requires
        forall|i: int| 1 <= i < 32 ==> bytes[i] == 0,
    ensures
        bytes_to_nat(bytes) == bytes[0] as nat,
{
    // bytes_to_nat(bytes) == as_nat_prefix(bytes, 1)
    assert(bytes_to_nat(bytes) == as_nat_prefix(bytes, 1)) by {
        lemma_bytes_to_nat_with_trailing_zeros(bytes, 1);
    }

    // as_nat_prefix(bytes, 1) == bytes[0]
    // Expand definition: as_nat_prefix(bytes, 1) = as_nat_prefix(bytes, 0) + bytes[0] * pow2(0)
    assert(as_nat_prefix(bytes, 0) == 0);
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(as_nat_prefix(bytes, 1) == as_nat_prefix(bytes, 0) + bytes[0] as nat * pow2(0 as nat));
    assert(bytes[0] as nat * pow2(0) == bytes[0] as nat);
}

/// Generalized lemma for From<T> proofs.
///
/// Given a sequence of n bytes and a 32-byte array where:
/// - The first n bytes of the array match the sequence
/// - The remaining bytes (n..31) are zero
///
/// Proves that bytes_to_nat of the array equals bytes_seq_to_nat of the sequence.
///
/// This lemma captures the common proof pattern for From<u16>, From<u32>,
/// From<u64>, and From<u128>.
pub proof fn lemma_from_le_bytes(le_seq: Seq<u8>, bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        le_seq.len() == n,
        forall|i: int| #![auto] 0 <= i < n ==> le_seq[i] == bytes[i],
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        bytes_to_nat(bytes) == bytes_seq_to_nat(le_seq),
{
    assert(bytes_to_nat(bytes) == bytes_seq_to_nat(le_seq)) by {
        // Chain: bytes_seq_to_nat(le_seq) == as_nat_prefix == bytes_to_nat
        lemma_bytes_seq_to_nat_equals_as_nat_prefix(le_seq, bytes, n);
        lemma_bytes_to_nat_with_trailing_zeros(bytes, n);
    }
}

// ============================================================================
// Main helper functions
// ============================================================================
impl Scalar {
    /// Compute the product of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The product of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let product = Scalar::product_of_slice(&scalars);
    /// assert_eq!(product, Scalar::from(30u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn product_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        ensures
            scalar_to_nat(&result) < group_order(),
            scalar_congruent_nat(&result, product_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ONE;

        proof {
            lemma_scalar_one_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: product extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc * &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes_to_nat(&acc.bytes);
                let old_acc_val = bytes_to_nat(&_old_acc.bytes);
                let scalar_val = bytes_to_nat(&scalars[i as int].bytes);
                let prod_prev = product_of_scalars(scalars@.subrange(0, i as int));

                lemma_mul_mod_noop_general(old_acc_val as int, scalar_val as int, L as int);
                lemma_mul_mod_noop_general(prod_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(prod_prev as int * scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }

    /// Compute the sum of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The sum of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let sum = Scalar::sum_of_slice(&scalars);
    /// assert_eq!(sum, Scalar::from(10u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        ensures
            scalar_to_nat(&result) < group_order(),
            scalar_congruent_nat(&result, sum_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ZERO;

        proof {
            lemma_scalar_zero_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: sum extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc + &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes_to_nat(&acc.bytes);
                let old_acc_val = bytes_to_nat(&_old_acc.bytes);
                let scalar_val = bytes_to_nat(&scalars[i as int].bytes);
                let sum_prev = sum_of_scalars(scalars@.subrange(0, i as int));

                lemma_mod_bound(old_acc_val as int + scalar_val as int, L as int);
                lemma_add_mod_noop(old_acc_val as int, scalar_val as int, L as int);
                lemma_add_mod_noop(sum_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(sum_prev as int + scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }
}

} // verus!
