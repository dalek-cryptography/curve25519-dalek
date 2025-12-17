# Step 1 Proof: Mathematical ↔ Verus Correspondence

This document maps the mathematical proof for `step_1` of Edwards point decompression to its Verus implementation.

---

## What `step_1` Must Prove

`step_1` takes a compressed Edwards Y coordinate and computes `(is_valid, X, Y, Z)` where:

| Postcondition | What It Means |
|---------------|---------------|
| **A.** `spec_field_element(&Y) == spec_field_element_from_bytes(&repr)` | Y is correctly extracted from bytes |
| **B.** `spec_field_element(&Z) == 1` | Z coordinate is set to 1 |
| **C.** `choice_is_true(is_valid) <==> math_is_valid_y_coordinate(y)` | Validity matches the mathematical definition |
| **D.** `choice_is_true(is_valid) ==> math_on_edwards_curve(x, y)` | If valid, (X, Y) lies on the curve |
| **E.** `(spec_field_element(&X) % p()) % 2 == 0` | X is the non-negative square root (LSB = 0) |
| **F.** `spec_field_element(&X) < p()` | X is bounded |

---

## Proof Structure Overview

```
step_1 proves:
├── A. Y extraction         → from_bytes ensures
├── B. Z = 1                → lemma_one_field_element_value
├── C. validity ↔ valid_y   → lemma_step1_case_analysis
├── D. valid ⟹ on_curve    → lemma_step1_case_analysis
├── E. X is non-negative    → sqrt_ratio_i ensures  
├── F. X bounded            → sqrt_ratio_i ensures
└── G. Limb bounds (overflow prevention) → lemma_one_limbs_bounded, lemma_edwards_d_limbs_bounded
```

---

## Postcondition A: Y Extraction

### Mathematical Statement

$$Y = \text{bytes\_le}(\text{repr}) \mod 2^{255} \mod p$$

The Y coordinate is extracted from the compressed representation by interpreting the first 255 bits as a little-endian integer modulo p.

### Verus Proof

| Verus Lemma/Ensures | Statement |
|---------------------|-----------|
| `from_bytes` ensures | `spec_field_element(&result) == spec_field_element_from_bytes(bytes)` |

**Proof:** Direct from `from_bytes` postcondition. No additional lemmas needed.

---

## Postcondition B: Z = 1

### Mathematical Statement

$$Z = 1$$

The Z coordinate in extended projective form is initialized to 1 for an affine point.

### Verus Proof

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_one_field_element_value` | `field_lemmas/constants_lemmas.rs` | `spec_field_element(&FieldElement::ONE) == 1` |

**Proof:** Apply `lemma_one_field_element_value()` to show `Z = ONE` has value 1.

---

## Postcondition C: Validity Equivalence

### Mathematical Statement

We need to prove:
$$\text{is\_valid} = \text{true} \iff \exists x: (x, y) \text{ is on the Edwards curve}$$

This breaks down into three sub-proofs:

| Case | What to Prove |
|------|---------------|
| **C1** | When `sqrt_ratio_i` succeeds with `v ≠ 0`: `is_valid ⟺ math_is_valid_y_coordinate(y)` |
| **C2** | When `u = 0`: `is_valid = true` and `x = 0` (identity point case) |
| **C3** | When `sqrt_ratio_i` fails: `¬math_is_valid_y_coordinate(y)` |

### Mathematical Proof for C1: Success Case

```
Given: sqrt_ratio_i returns (true, x) with x² · v ≡ u (mod p)
Where: u = y² - 1, v = d·y² + 1

Claim: math_is_valid_y_coordinate(y) is true

Proof:
  1. x² · v ≡ u (mod p)                    [sqrt_ratio_i postcondition]
  2. We have a witness x < p              [sqrt_ratio_i bound]
  3. math_is_valid_y_coordinate asks:
     ∃r < p: r² · v ≡ u (mod p)
  4. x is exactly such a witness          [from (1), (2)]
  ∴ math_is_valid_y_coordinate(y) = true   ∎
```

### Verus Proof for C1

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_is_sqrt_ratio_to_math_field` | `sqrt_ratio_lemmas.rs` | `is_sqrt_ratio(u, v, x) ⟹ math_field_mul(math_field_square(x), v) == u` |
| `lemma_sqrt_ratio_success_means_valid_y` | `step1_lemmas.rs` | `is_sqrt_ratio success ⟹ math_is_valid_y_coordinate(y)` |

**Verus code:**
```rust
assert(math_is_valid_y_coordinate(y)) by {
    // From sqrt_ratio_i: is_sqrt_ratio holds
    assert((x * x * v) % p() == u);
    
    // Convert to math_field form
    lemma_is_sqrt_ratio_to_math_field(x, u_math, v_math);
    
    // Apply validity lemma with witness x
    lemma_sqrt_ratio_success_means_valid_y(y, u_math, v_math, x);
};
```

---

### Mathematical Proof for C2: Identity Point Case

```
Given: u = y² - 1 = 0 (mod p)

Claim: y² = 1, x = 0, and (0, y) is on the curve

Proof:
  1. u = y² - 1 ≡ 0 (mod p)               [given]
  2. y² ≡ 1 (mod p)                       [rearranging (1)]
  3. sqrt_ratio_i returns (true, 0)       [0² · v = 0 = u ✓]
  4. Curve equation: -x² + y² = 1 + d·x²·y²
     With x = 0: y² = 1                   [which is true by (2)]
  ∴ (0, y) is on the curve                 ∎
```

### Verus Proof for C2

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_u_zero_implies_identity_point` | `step1_lemmas.rs` | `u == 0 ⟹ y² == 1 ∧ math_on_edwards_curve(0, y) ∧ math_is_valid_y_coordinate(y)` |

**Verus code:**
```rust
assert(u_math == 0 ==> (is_valid && x == 0)) by {
    lemma_u_zero_implies_identity_point(y, u_math);
};
```

---

### Mathematical Proof for C3: Failure Case

```
Given: sqrt_ratio_i returns (false, x) with x² · v ≡ i · u (mod p)
Where: i = √(-1), u ≠ 0, v ≠ 0

Claim: ¬math_is_valid_y_coordinate(y)

Proof by contradiction:
  Assume: ∃r < p: r² · v ≡ u (mod p)
  
  1. x² · v ≡ i · u (mod p)               [sqrt_ratio_i postcondition]
  2. r² · v ≡ u (mod p)                   [assumption]
  3. Divide (1) by (2): x²/r² ≡ i (mod p)
  4. (x/r)² ≡ i (mod p)                   [quotient of squares]
  5. This says i is a quadratic residue    [x/r is a square root]
  6. But i is NOT a quadratic residue     [axiom: Euler criterion]
  
  Contradiction! ∴ No such r exists.
  ∴ ¬math_is_valid_y_coordinate(y)         ∎
```

### Verus Proof for C3

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_sqrt_ratio_failure_means_invalid_y` | `step1_lemmas.rs` | `sqrt_ratio_i failure ⟹ ¬math_is_valid_y_coordinate(y)` |
| `lemma_no_square_root_when_times_i` | `sqrt_ratio_lemmas.rs` | `x²·v ≡ i·u ⟹ ¬∃r: r²·v ≡ u` |
| `axiom_sqrt_m1_not_square` | `sqrt_ratio_lemmas.rs` | `i is not a quadratic residue` (axiom) |

**Verus code:**
```rust
assert(!math_is_valid_y_coordinate(y)) by {
    assert((x * x * v_math) % p() == (spec_sqrt_m1() * u_math) % p());
    lemma_sqrt_ratio_failure_means_invalid_y(y, u_math, v_math);
};
```

---

### Unified Verus Lemma for C: `lemma_step1_case_analysis`

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_step1_case_analysis` | `step1_lemmas.rs` | Unifies C1, C2, C3: `is_valid ⟺ math_is_valid_y_coordinate(y)` |

**This is the main lemma that proves postcondition C.** It performs case analysis on:
- `is_valid && v ≠ 0` → calls `lemma_sqrt_ratio_success_means_valid_y`
- `u == 0` → calls `lemma_u_zero_implies_identity_point`
- `!is_valid && u ≠ 0 && v ≠ 0` → calls `lemma_sqrt_ratio_failure_means_invalid_y`

---

## Postcondition D: On Curve When Valid

### Mathematical Statement

$$\text{is\_valid} = \text{true} \implies (x, y) \text{ satisfies } -x^2 + y^2 = 1 + d \cdot x^2 \cdot y^2$$

### Mathematical Proof

```
Given: sqrt_ratio_i returns (true, x) with x² · v ≡ u (mod p)
Where: u = y² - 1, v = d·y² + 1

Claim: -x² + y² = 1 + d·x²·y² (mod p)

Proof:
  1. x² · v ≡ u (mod p)                   [precondition]
  2. x² · (d·y² + 1) ≡ y² - 1             [substituting u, v]
  3. x²·d·y² + x² ≡ y² - 1                [distributivity: a(b+c) = ab+ac]
  4. d·x²·y² + x² ≡ y² - 1                [commutativity: x²·d·y² = d·x²·y²]
  5. d·x²·y² + 1 ≡ y² - x²                [add 1, subtract x² from both sides]
  6. 1 + d·x²·y² ≡ y² - x²                [commutativity of addition]
  
  This is exactly the curve equation: -x² + y² = 1 + d·x²·y²  ∎
```

### Verus Proof

| Verus Lemma | Location | Statement |
|-------------|----------|-----------|
| `lemma_sqrt_ratio_implies_on_curve` | `step1_lemmas.rs` | `x²·v == u ⟹ math_on_edwards_curve(x, y)` |
| `lemma_field_mul_distributes_over_add` | `field_algebra_lemmas.rs` | `a·(b+c) == a·b + a·c` (Step 3) |
| `lemma_field_add_sub_rearrange` | `field_algebra_lemmas.rs` | `a+b+1 == c ⟹ a+1 == c-b` (Step 5) |

**Verus code:**
```rust
assert(math_on_edwards_curve(x, y)) by {
    // Step 2: From precondition
    assert(math_field_mul(x2, v) == u);
    
    // Step 3: Distributivity
    assert(math_field_add(x2_dy2, x2) == u) by {
        lemma_field_mul_distributes_over_add(x2, dy2, 1);
    };
    
    // Step 4: Commutativity
    assert(x2_dy2 == d_x2y2) by {
        lemma_mul_is_associative(x2, d, y2);
        lemma_mul_is_commutative(x2, d);
    };
    
    // Step 5: Rearrangement
    assert(math_field_add(d_x2y2, 1) == math_field_sub(y2, x2)) by {
        lemma_field_add_sub_rearrange(d_x2y2, x2, y2);
    };
};
```

---

## Postconditions E & F: X Properties

### Mathematical Statement

$$x \mod 2 = 0 \text{ (non-negative root)}$$
$$x < p \text{ (bounded)}$$

### Verus Proof

| Source | Statement |
|--------|-----------|
| `sqrt_ratio_i` ensures | `(spec_field_element(&result) % p()) % 2 == 0` |
| `sqrt_ratio_i` ensures | `spec_field_element(&result) < p()` |

**Proof:** Direct from `sqrt_ratio_i` postconditions. No additional lemmas needed.

---

## Limb Bounds: Overflow Prevention (Implementation Detail)

### Why This Is Needed

The field element representation uses 5 limbs of 51 bits each. Field operations like `*` (multiply) and `-` (subtract) have **preconditions** requiring input limbs to be bounded to prevent overflow during computation.

### Where Limb Bounds Are Established

```rust
// edwards.rs step_1, lines 353-357
proof {
    // Setup constant bounds
    lemma_one_limbs_bounded();      // ONE.limbs[i] < 2^51
    lemma_edwards_d_limbs_bounded(); // EDWARDS_D.limbs[i] < 2^51
}
```

### What Each Lemma Proves

| Lemma | Location | Statement | Needed For |
|-------|----------|-----------|------------|
| `lemma_one_limbs_bounded` | `field_lemmas/constants_lemmas.rs` | `fe51_limbs_bounded(&ONE, 51)` | `u = &YY - &Z` |
| `lemma_edwards_d_limbs_bounded` | `edwards_lemmas/constants_lemmas.rs` | `fe51_limbs_bounded(&EDWARDS_D, 51)` | `yy_times_d = &YY * &EDWARDS_D` |

### How Bounds Flow Through Operations

```
Y                       [51-bit bounded from from_bytes]
  ↓ square()
YY                      [52-bit bounded]
  ↓ - Z (ONE)
u = YY - Z              [needs ONE 51-bit bounded ✓]
  ↓ * EDWARDS_D
yy_times_d = YY * D     [needs EDWARDS_D 51-bit bounded ✓, result 52-bit]
  ↓ + Z (ONE)
v = yy_times_d + Z      [52-bit + 1 < 54-bit, safe for sqrt_ratio_i]
```

### Mathematical Justification

This is purely an **implementation concern**, not part of the mathematical proof. The mathematical proof works over the abstract field $\mathbb{F}_p$ where overflow doesn't exist. These lemmas ensure the concrete 64-bit limb representation doesn't overflow during computation.

---

## Complete Dependency Graph for step_1

```
step_1 ensures
│
├── A: Y extraction
│   └── from_bytes ensures ✅
│
├── B: Z = 1
│   └── lemma_one_field_element_value ✅
│
├── C & D: Validity ↔ Valid Y & On Curve
│   └── lemma_step1_case_analysis ✅
│       │
│       ├── [C1: Success case]
│       │   ├── lemma_is_sqrt_ratio_to_math_field ✅
│       │   ├── lemma_sqrt_ratio_success_means_valid_y ✅
│       │   └── lemma_sqrt_ratio_implies_on_curve ✅
│       │       ├── lemma_field_mul_distributes_over_add ✅
│       │       └── lemma_field_add_sub_rearrange ✅
│       │
│       ├── [C2: Identity case]
│       │   └── lemma_u_zero_implies_identity_point ✅
│       │
│       └── [C3: Failure case]
│           └── lemma_sqrt_ratio_failure_means_invalid_y ✅
│               └── lemma_no_square_root_when_times_i ✅
│                   ├── axiom_sqrt_m1_squared 🔶
│                   ├── axiom_sqrt_m1_not_square 🔶
│                   ├── axiom_neg_sqrt_m1_not_square 🔶
│                   ├── lemma_i_inverse_is_neg_i ✅
│                   ├── lemma_algebraic_chain_base ✅
│                   ├── lemma_u_times_inv_iu_is_neg_i ✅
│                   ├── lemma_neg_u_times_inv_iu_is_i ✅
│                   └── lemma_quotient_of_squares ✅
│
├── E: X non-negative
│   └── sqrt_ratio_i ensures ✅
│
├── F: X bounded
│   └── sqrt_ratio_i ensures ✅
│
└── G: Limb bounds (field operation preconditions)
    ├── lemma_one_limbs_bounded ✅       [for: u = YY - Z]
    └── lemma_edwards_d_limbs_bounded ✅ [for: yy_times_d = YY * EDWARDS_D]
```

**Legend:** ✅ Proved | 🔶 Axiom (mathematically justified)

---

## Summary Table

| What to Prove | Math Proof Key Step | Verus Lemma(s) |
|---------------|---------------------|----------------|
| **A: Y extraction** | Bytes to field element | `from_bytes` ensures |
| **B: Z = 1** | Constant value | `lemma_one_field_element_value` |
| **C1: Valid ⟹ valid_y** | Witness r = x exists | `lemma_sqrt_ratio_success_means_valid_y` |
| **C2: u = 0 ⟹ identity** | y² = 1, x = 0 | `lemma_u_zero_implies_identity_point` |
| **C3: ¬valid ⟹ ¬valid_y** | i is not QR | `lemma_sqrt_ratio_failure_means_invalid_y`, `axiom_sqrt_m1_not_square` |
| **D: Valid ⟹ on curve** | x²·v = u ⟹ curve eq | `lemma_sqrt_ratio_implies_on_curve`, `lemma_field_mul_distributes_over_add`, `lemma_field_add_sub_rearrange` |
| **E: X non-negative** | LSB = 0 | `sqrt_ratio_i` ensures |
| **F: X bounded** | x < p | `sqrt_ratio_i` ensures |
| **G: Limb bounds** | (impl. detail: overflow prevention) | `lemma_one_limbs_bounded`, `lemma_edwards_d_limbs_bounded` |

---

## File Locations

| Lemma Category | File |
|----------------|------|
| Main step1 lemmas (case analysis, curve, validity) | `lemmas/edwards_lemmas/step1_lemmas.rs` |
| Decompress-specific lemmas (sign bit, negation) | `lemmas/edwards_lemmas/decompress_lemmas.rs` |
| sqrt_ratio spec lemmas & SQRT_M1 axioms | `lemmas/common_lemmas/sqrt_ratio_lemmas.rs` |
| Field algebra (distributivity, quotients, etc.) | `lemmas/field_lemmas/field_algebra_lemmas.rs` |
| Field constants (ONE value, limb bounds) | `lemmas/field_lemmas/constants_lemmas.rs` |
| Edwards constants (EDWARDS_D limb bounds) | `lemmas/edwards_lemmas/constants_lemmas.rs` |
| step_1 implementation | `edwards.rs` |
