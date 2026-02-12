# Proof of `CompressedEdwardsY::decompress`

This document provides a mathematical proof of correctness for the `decompress` function that recovers an Edwards curve point from its compressed representation.

**Verus Verification:** ✅ 913 verified, 0 errors

---

## Table of Contents

1. [Background](#background-ed25519-curve)
2. [Theorem Statement](#theorem-correctness-of-decompress)
3. [Math ↔ Lemma Mapping](#math--lemma-mapping)
4. [Proof Dependency Graph](#proof-dependency-graph)
5. [Detailed Proofs](#detailed-proofs)
6. [Axioms](#axioms-trust-assumptions)
7. [Lemma Reference](#lemma-reference)

---

## Background: Ed25519 Curve

The Ed25519 curve is a twisted Edwards curve. The general form is:

$$a \cdot x^2 + y^2 = 1 + d \cdot x^2 \cdot y^2 \pmod{p}$$

For Ed25519, $a = -1$, giving:

$$-x^2 + y^2 = 1 + d \cdot x^2 \cdot y^2 \pmod{p}$$

where:
- $p = 2^{255} - 19$ (a prime)
- $d = -121665/121666 \pmod{p}$
- $y < p < 2^{255}$

### Point Compression

A point $(x, y)$ on the curve can be compressed to 32 bytes (indexed 0–31):
- Store all 255 bits of $y$ in the first 255 bits 
- Store the sign bit of $x$ (i.e., $x \bmod 2$) in the high bit of the last byte (byte 31)

### Point Decompression

Given the compressed representation:
1. Extract $y$ from the first 255 bits
2. Compute $x^2$ from the curve equation
3. Compute $x = \sqrt{x^2}$ (if it exists)
4. Adjust sign of $x$ based on the stored sign bit

---

## Theorem: Correctness of `decompress`

**Statement:** If `decompress` returns `Some(point)`, then:
1. **Point on curve:** The point lies on the Edwards curve
2. **Y preserved:** The Y coordinate matches the compressed representation
3. **Sign correct:** The X coordinate has the correct sign
4. **Extended coord:** The extended coordinate T satisfies T = X·Y/Z

---

## Math ↔ Lemma Mapping

This table maps each mathematical proof step to its corresponding Verus lemma.

| Proof Step | Mathematical Statement | Verus Lemma | Lemma States |
|------------|----------------------|-------------|--------------|
| **Part 1** | Y = bytes_le(repr) mod p | `from_bytes` ensures | `fe51_as_canonical_nat(&Y) == field_element_from_bytes(bytes)` |
| **Part 2** | x² = (y² - 1)/(d·y² + 1) = u/v | Field op ensures | `fe51_is_sqrt_ratio` ⟺ `(x * x * v) % p == u % p` |
| **Part 3** | sqrt_ratio_i computes √(u/v) | `lemma_is_sqrt_ratio_to_field` | `fe51_is_sqrt_ratio(u, v, x) ==> field_mul(x², v) == u` |
| **Part 4** | x²·v = u ⟹ on_curve(x, y) | `lemma_sqrt_ratio_implies_on_curve` | `field_mul(x², v) == u ==> math_on_edwards_curve(x, y)` |
| **Part 5** | on_curve(x, y) ⟹ on_curve(-x, y) | `lemma_negation_preserves_curve` | `math_on_edwards_curve(x, y) ==> math_on_edwards_curve(-x, y)` |
| **Part 6** | Z = 1 ⟹ valid extended point | `lemma_decompress_produces_valid_point` | `z == 1 && on_curve(x, y) ==> is_valid_edwards_point(...)` |
| **Part 7** | Sign bit after conditional negate | `lemma_sign_bit_after_conditional_negate` | Correctly sets LSB(X) = sign_bit |
| **Part 8** | Valid Y ↔ sqrt_ratio succeeds | `lemma_step1_case_analysis` | `choice_is_true(is_valid) <==> math_is_valid_y_coordinate(y)` |

---

## Proof Dependency Graph

### Top Level: `decompress` → `step_1` + `step_2`

```
decompress() ✅                                          [edwards.rs]
│
├── step_1() ✅                                          [edwards.rs]
│   │
│   │   ▼ Internal lemmas for field bounds ────────────────────────────
│   ├── lemma_one_limbs_bounded ✅                      [field_lemmas/constants_lemmas.rs]
│   ├── lemma_edwards_d_limbs_bounded ✅                [edwards_lemmas/constants_lemmas.rs]
│   ├── lemma_one_field_element_value ✅                [field_lemmas/constants_lemmas.rs]
│   │   └── Statement: fe51_as_canonical_nat(ONE) == 1
│   │
│   │   ▼ Field operation correspondence ──────────────────────────────
│   ├── lemma_square_matches_field_square ✅       [step1_lemmas.rs]
│   │   └── Statement: fe51_as_canonical_nat(Y.square()) == field_square(y)
│   │
│   │   ▼ Main case analysis lemma ────────────────────────────────────
│   └── lemma_step1_case_analysis ✅                    [step1_lemmas.rs]
│       │   Statement: choice_is_true(is_valid) <==> math_is_valid_y_coordinate(y)
│       │              AND is_valid ==> math_on_edwards_curve(x, y)
│       │
│       ├── lemma_is_sqrt_ratio_to_field ✅        [sqrt_ratio_lemmas.rs]
│       │   └── Statement: fe51_is_sqrt_ratio(u, v, x) ==> field_mul(x², v) == u
│       │
│       ├── lemma_sqrt_ratio_success_means_valid_y ✅   [step1_lemmas.rs]
│       │   │   Statement: fe51_is_sqrt_ratio success ==> math_is_valid_y_coordinate(y)
│       │   │
│       │   └── lemma_sqrt_ratio_implies_on_curve ✅    [step1_lemmas.rs]
│       │       │   Statement: field_mul(x², v) == u ==> math_on_edwards_curve(x, y)
│       │       │
│       │       ├── lemma_field_mul_distributes_over_add ✅  [field_algebra_lemmas.rs]
│       │       │   └── Statement: a·(b+c) == a·b + a·c
│       │       │
│       │       └── lemma_field_add_sub_rearrange ✅         [field_algebra_lemmas.rs]
│       │           └── Statement: a+b+1 == c ==> a+1 == c-b
│       │
│       ├── lemma_u_zero_implies_identity_point ✅      [step1_lemmas.rs]
│       │   └── Statement: u == 0 ==> x == 0 && (y == 1 || y == -1)
│       │
│       └── lemma_sqrt_ratio_failure_means_invalid_y ✅  [step1_lemmas.rs]
│           │   Statement: !fe51_is_sqrt_ratio success ==> !math_is_valid_y_coordinate(y)
│           │
│           └── lemma_no_square_root_when_times_i ✅    [sqrt_ratio_lemmas.rs]
│               │   Statement: v·r² == i·u && v ≠ 0 ==> ¬∃x: v·x² == u
│               │
│               ├── axiom_sqrt_m1_squared 🔶            [sqrt_ratio_lemmas.rs]
│               │   └── Axiom: i² == -1 mod p
│               ├── axiom_sqrt_m1_not_square 🔶         [sqrt_ratio_lemmas.rs]
│               │   └── Axiom: i is not a quadratic residue
│               ├── axiom_neg_sqrt_m1_not_square 🔶     [sqrt_ratio_lemmas.rs]
│               │   └── Axiom: -i is not a quadratic residue
│               ├── lemma_i_inverse_is_neg_i ✅         [sqrt_ratio_lemmas.rs]
│               │   └── Statement: i⁻¹ == -i mod p
│               ├── lemma_algebraic_chain_base ✅       [sqrt_ratio_lemmas.rs]
│               │   └── Statement: q² = r_squared_v · inv(i·u)
│               ├── lemma_u_times_inv_iu_is_neg_i ✅    [sqrt_ratio_lemmas.rs]
│               │   └── Statement: u · inv(i·u) = -i
│               └── lemma_neg_u_times_inv_iu_is_i ✅    [sqrt_ratio_lemmas.rs]
│                   └── Statement: (-u) · inv(i·u) = i
│
├── step_2() ✅                                          [edwards.rs]
│
└── lemma_decompress_valid_branch ✅                     [decompress_lemmas.rs]
    │   Statement: Proves all 3 ensures clauses of decompress
    │
    ├── lemma_negation_preserves_curve ✅                [decompress_lemmas.rs]
    │   │   Statement: math_on_edwards_curve(x, y) ==> math_on_edwards_curve(-x, y)
    │   │
    │   ├── lemma_neg_square_eq ✅                       [field_algebra_lemmas.rs]
    │   │   └── Statement: field_square(-x) == field_square(x)
    │   │
    │   └── lemma_square_mod_noop ✅                     [field_algebra_lemmas.rs]
    │       └── Statement: (x % p)² % p == x² % p
    │
    ├── lemma_decompress_produces_valid_point ✅         [decompress_lemmas.rs]
    │   │   Statement: z == 1 && on_curve(x, y) ==> is_valid_edwards_point(X, Y, Z, T)
    │   │
    │   ├── lemma_field_inv_one ✅                       [field_algebra_lemmas.rs]
    │   │   └── Statement: inv(1) == 1
    │   │
    │   └── lemma_square_mod_noop ✅                     [field_algebra_lemmas.rs]
    │
    ├── lemma_sign_bit_one_implies_x_nonzero ✅     [decompress_lemmas.rs]
    │   │   Statement: y² ≠ 1 ==> x ≠ 0 (enables sign bit proof)
    │   │
    │   └── lemma_x_zero_implies_y_squared_one ✅    [decompress_lemmas.rs]
    │       └── Statement: x = 0 && on_curve(x, y) ==> y² = 1 (contrapositive)
    │
    └── lemma_decompress_field_element_sign_bit ✅       [decompress_lemmas.rs]
        │   Statement: fe51_as_canonical_nat_sign_bit(&X) == sign_bit
        │
        └── lemma_sign_bit_after_conditional_negate ✅   [decompress_lemmas.rs]
            └── Statement: If sign_bit == 0: LSB(X) = 0
                           If sign_bit == 1: X ← p - X, LSB(X) = 1
```

### Legend
- ✅ = Fully proved (no assume/admit)
- 🔶 = Axiom (mathematically justified, uses admit)

---

## Detailed Proofs

### Part 1: Y coordinate extraction

**Math:** $Y = \text{bytes}_\text{le}(\text{repr}) \bmod 2^{255} \bmod p$

**Verus:** `from_bytes` ensures clause

| Property | Verus Specification |
|----------|-------------------|
| **Ensures** | `fe51_as_canonical_nat(&result) == field_element_from_bytes(bytes)` |
| **Location** | `field.rs` |

---

### Part 2: Computing x² = u/v from curve equation

**Math:**
```
From: -x² + y² = 1 + d·x²·y² (mod p)
Rearrange: y² - 1 = x²(1 + d·y²)
Therefore: x² = (y² - 1)/(d·y² + 1) = u/v
where: u = y² - 1, v = d·y² + 1
```

**Verus:** Field operation postconditions

| Operation | Ensures Clause |
|-----------|---------------|
| `square()` | `fe51_as_canonical_nat(&result) == field_square(input)` |
| `Sub` | `fe51_as_canonical_nat(&result) == field_sub(a, b)` |
| `Mul` | `fe51_as_canonical_nat(&result) == field_mul(a, b)` |
| `Add` | `fe51_as_canonical_nat(&result) == field_add(a, b)` |

---

### Part 3: sqrt_ratio_i computes √(u/v)

**Math:**
```
sqrt_ratio_i(u, v) returns (is_square, r) where:
- If u/v is a quadratic residue: returns (true, r) with r²·v ≡ u (mod p)
- Otherwise: returns (false, r) with r²·v ≡ i·u (mod p)
```

**Verus:**

| Lemma | Statement |
|-------|-----------|
| `lemma_is_sqrt_ratio_to_field` | `fe51_is_sqrt_ratio(u, v, x) ==> field_mul(field_square(x), v) == u` |

**Spec definition:**
```rust
pub open spec fn fe51_is_sqrt_ratio(u: int, v: int, x: &FieldElement51) -> bool {
    (fe51_as_canonical_nat(x) * fe51_as_canonical_nat(x) * v) % p() == u % p()
}
```

---

### Part 4: x²·v = u implies on_curve(x, y) — Core Algebraic Proof

**Math:**
```
Given: x²·v ≡ u (mod p)
Where: u = y² - 1, v = d·y² + 1

Step 1: x²·v = u
        x²·(d·y² + 1) = y² - 1

Step 2: Distribute (by lemma_field_mul_distributes_over_add)
        x²·d·y² + x² = y² - 1

Step 3: Rearrange (by lemma_field_add_sub_rearrange)
        d·x²·y² + 1 = y² - x²

Step 4: This IS the curve equation:
        -x² + y² = 1 + d·x²·y² ✓
```

**Verus:**

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lemma_sqrt_ratio_implies_on_curve` | `field_mul(x², v) == u ==> math_on_edwards_curve(x, y)` | `decompress_lemmas.rs` |
| └─ `lemma_field_mul_distributes_over_add` | `a·(b+c) == a·b + a·c` | `field_algebra_lemmas.rs` |
| └─ `lemma_field_add_sub_rearrange` | `a+b+1 == c ==> a+1 == c-b` | `field_algebra_lemmas.rs` |

**Verus proof sketch:**
```rust
pub proof fn lemma_sqrt_ratio_implies_on_curve(x: int, y: int, u: int, v: int)
    requires
        field_mul(field_square(x), v) == u,
        u == field_sub(field_square(y), 1),
        v == field_add(field_mul(MATH_EDWARDS_D, field_square(y)), 1),
    ensures
        math_on_edwards_curve(x, y),
{
    let x2 = field_square(x);
    let y2 = field_square(y);
    let dy2 = field_mul(MATH_EDWARDS_D, y2);
    
    // Step 1: From precondition x²·v = u
    assert(field_mul(x2, v) == u);
    
    // Step 2: Distributivity
    lemma_field_mul_distributes_over_add(x2, dy2, 1);
    // gives: x²·(dy² + 1) = x²·dy² + x²
    
    // Step 3-4: Rearrangement to curve equation
    lemma_field_add_sub_rearrange(d_x2y2, x2, y2);
    // gives: d·x²·y² + 1 = y² - x²
    
    assert(math_on_edwards_curve(x, y));
}
```

---

### Part 5: Negation preserves curve membership

**Math:**
```
(-x)² = (p - x)² = p² - 2px + x² ≡ x² (mod p)
Since curve equation uses only x²:
on_curve(x, y) ⟺ on_curve(-x, y)
```

**Verus:**

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lemma_negation_preserves_curve` | `math_on_edwards_curve(x, y) ==> math_on_edwards_curve(-x, y)` | `decompress_lemmas.rs` |
| └─ `lemma_neg_square_eq` | `field_square(-x) == field_square(x)` | `field_algebra_lemmas.rs` |
| └─ `lemma_square_mod_noop` | `(x % p)² % p == x² % p` | `field_algebra_lemmas.rs` |

**Verus proof sketch:**
```rust
pub proof fn lemma_negation_preserves_curve(x: int, y: int)
    requires math_on_edwards_curve(x, y),
    ensures math_on_edwards_curve(field_neg(x), y),
{
    let neg_x = field_neg(x);
    
    // Key: (-x)² = x²
    lemma_neg_square_eq(x);
    lemma_square_mod_noop(x);
    
    assert(field_square(neg_x) == field_square(x));
    // Therefore curve equation holds for (-x, y)
}
```

---

### Part 6: Z = 1 implies valid extended point

**Math:**
```
For extended coordinates (X:Y:Z:T):
  Required: Z ≠ 0, (X/Z, Y/Z) on curve, T·Z = X·Y

When Z = 1:
  - Z = 1 ≠ 0 ✓
  - X/Z = X, Y/Z = Y (already on curve) ✓
  - T = X·Y, so T·1 = X·Y ✓
```

**Verus:**

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lemma_decompress_produces_valid_point` | `z == 1 && on_curve(x, y) ==> is_valid_edwards_point(...)` | `decompress_lemmas.rs` |
| └─ `lemma_field_inv_one` | `field_inv(1) == 1` | `field_algebra_lemmas.rs` |

**Verus proof sketch:**
```rust
pub proof fn lemma_decompress_produces_valid_point(x: int, y: int, t: int, z: int)
    requires
        z == 1,
        math_on_edwards_curve(x, y),
        t == field_mul(x, y),
    ensures
        is_valid_edwards_point_math(x, y, z, t),
{
    // Part 1: Z ≠ 0
    assert(z != 0);
    
    // Part 2: (X/Z, Y/Z) on curve
    lemma_field_inv_one();
    // inv(1) = 1, so X/1 = X, Y/1 = Y
    
    // Part 3: T·Z = X·Y
    // T = X·Y, Z = 1, so T·1 = X·Y ✓
}
```

---

### Part 7: Sign bit correctness after conditional negate

**Math:**
```
sqrt_ratio_i returns the "non-negative" root (LSB = 0)
Let x_before = result from sqrt_ratio_i (even, so LSB = 0)

If sign_bit = 0:
  X unchanged, LSB(X) = 0 = sign_bit ✓

If sign_bit = 1:
  X ← p - X (field negation)
  p is odd, x_before is even
  ⟹ p - x_before is odd (LSB = 1)
  ⟹ LSB(X) = 1 = sign_bit ✓
```

**Verus:**

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lemma_sign_bit_after_conditional_negate` | Sign bit is correctly set after conditional negation | `decompress_lemmas.rs` |
| `lemma_decompress_field_element_sign_bit` | `fe51_as_canonical_nat_sign_bit(&X) == sign_bit` | `decompress_lemmas.rs` |
| `lemma_sign_bit_one_implies_x_nonzero` | `y² ≠ 1 ==> x ≠ 0` (enables proof when sign_bit = 1) | `decompress_lemmas.rs` |

**Verus proof sketch:**
```rust
pub proof fn lemma_decompress_field_element_sign_bit(
    x_before: int,
    x_after: int,
    repr_byte_31: u8,
)
    requires
        x_before % 2 == 0,  // sqrt_ratio_i returns non-negative
        x_before < p(),
        x_after == if (repr_byte_31 >> 7) == 1 { p() - x_before } else { x_before },
    ensures
        (x_after % p()) % 2 == (repr_byte_31 >> 7) as int,
{
    let sign_bit = (repr_byte_31 >> 7) as int;
    if sign_bit == 0 {
        // x_after = x_before, LSB = 0 = sign_bit
    } else {
        // x_after = p - x_before
        // p is odd, x_before is even ⟹ p - x_before is odd
        lemma_p_is_odd();
        // LSB(x_after) = 1 = sign_bit
    }
}
```

---

### Part 8: Case analysis — validity ↔ sqrt_ratio success

**Math:**
```
math_is_valid_y_coordinate(y) ⟺ ∃x: (x, y) on curve
                              ⟺ u/v is a quadratic residue
                              ⟺ sqrt_ratio_i returns is_square = true
```

**Verus:**

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lemma_step1_case_analysis` | `choice_is_true(is_valid) <==> math_is_valid_y_coordinate(y)` | `step1_lemmas.rs` |
| └─ `lemma_sqrt_ratio_success_means_valid_y` | Success ⟹ valid Y | `step1_lemmas.rs` |
| └─ `lemma_sqrt_ratio_failure_means_invalid_y` | Failure ⟹ invalid Y | `step1_lemmas.rs` |
| └─ `lemma_u_zero_implies_identity_point` | u = 0 ⟹ identity point | `step1_lemmas.rs` |

---

## Main Proof Orchestration

### `decompress` function structure

```rust
pub fn decompress(&self) -> Option<EdwardsPoint>
    requires is_valid_compressed_edwards_y(&self.0),
    ensures
        result.is_some() ==> is_valid_edwards_point(result.unwrap()),
        result.is_some() ==> Y_matches_repr,
        result.is_some() ==> sign_bit_correct,
{
    // Step 1: Compute Y, u, v, and attempt sqrt_ratio
    let (is_valid, X, Y, Z) = step_1(self);
    
    proof {
        // From step_1: is_valid <==> math_is_valid_y_coordinate(y)
        // From step_1: is_valid ==> math_on_edwards_curve(x, y)
    }
    
    if choice_into(is_valid) {
        // Step 2: Apply sign bit and construct point
        let point = step_2(self, X, Y, Z);
        
        proof {
            // This single lemma proves all 3 ensures clauses
            lemma_decompress_valid_branch(&self.0, x_orig, y, &point);
        }
        Some(point)
    } else {
        None
    }
}
```

### `lemma_decompress_valid_branch` — The Master Lemma

This lemma proves all three ensures clauses of `decompress`:

```rust
pub proof fn lemma_decompress_valid_branch(
    repr_bytes: &[u8; 32],
    x_orig: int,
    y: int,
    point: &EdwardsPoint,
)
    requires
        math_on_edwards_curve(x_orig, y),
        // ... additional preconditions
    ensures
        is_valid_edwards_point(*point),                              // Goal 1
        fe51_as_canonical_nat(&point.Y) == y,                           // Goal 2
        fe51_as_canonical_nat_sign_bit(&point.X) == (repr_bytes[31] >> 7), // Goal 3
{
    let sign_bit = (repr_bytes[31] >> 7) as int;
    let x_final = if sign_bit == 1 { field_neg(x_orig) } else { x_orig };
    
    // ═══════════════════════════════════════════════════════════════
    // Goal 1: is_valid_edwards_point
    // ═══════════════════════════════════════════════════════════════
    assert(is_valid_edwards_point(*point)) by {
        // If sign_bit == 1, we negated X, but curve membership preserved
        assert(math_on_edwards_curve(x_final, y)) by {
            if sign_bit == 1 {
                lemma_negation_preserves_curve(x_orig, y);
            }
        };
        // Z = 1 ⟹ valid extended point
        lemma_decompress_produces_valid_point(x_final, y, t, z);
    };
    
    // ═══════════════════════════════════════════════════════════════
    // Goal 2: Y preserved
    // ═══════════════════════════════════════════════════════════════
    // Direct from step_2: point.Y == Y from step_1
    assert(fe51_as_canonical_nat(&point.Y) == y);
    
    // ═══════════════════════════════════════════════════════════════
    // Goal 3: Sign bit correct
    // ═══════════════════════════════════════════════════════════════
    assert(fe51_as_canonical_nat_sign_bit(&point.X) == sign_bit) by {
        lemma_sign_bit_one_implies_x_nonzero(repr_bytes, x_orig, y);
        lemma_decompress_field_element_sign_bit(x_orig, x_final, repr_bytes[31]);
    };
}
```

---

## Axioms (Trust Assumptions)

The proof relies on 4 axioms about number-theoretic properties that are expensive to verify computationally:

| Axiom | Statement | Mathematical Justification | Location |
|-------|-----------|---------------------------|----------|
| `axiom_sqrt_m1_squared` | $i^2 \equiv -1 \pmod{p}$ | Definition: SQRT_M1 is computed to satisfy this | `sqrt_ratio_lemmas.rs` |
| `axiom_sqrt_m1_not_square` | $i$ is not a quadratic residue | Euler criterion: $i^{(p-1)/2} = -1$ | `sqrt_ratio_lemmas.rs` |
| `axiom_neg_sqrt_m1_not_square` | $-i$ is not a quadratic residue | Euler criterion: $(-i)^{(p-1)/2} = -1$ | `sqrt_ratio_lemmas.rs` |
| `axiom_p_is_prime` | $p = 2^{255} - 19$ is prime | Well-known mathematical fact | `primality_specs.rs` |

**Note:** All lemmas in the decompress proof chain are **fully proved** — only axioms use `admit()`.

---

## Lemma Reference

### Core Decompress Lemmas (`decompress_lemmas.rs`)

| Lemma | Formal Statement | Status |
|-------|-----------------|--------|
| `lemma_negation_preserves_curve` | `math_on_edwards_curve(x, y) ==> math_on_edwards_curve(-x, y)` | ✅ |
| `lemma_decompress_produces_valid_point` | `z == 1 && on_curve(x, y) ==> is_valid_edwards_point(...)` | ✅ |
| `lemma_sign_bit_after_conditional_negate` | Sign bit correctly set after negate | ✅ |
| `lemma_decompress_field_element_sign_bit` | `fe51_as_canonical_nat_sign_bit(&X) == sign_bit` | ✅ |
| `lemma_sign_bit_one_implies_x_nonzero` | `y² ≠ 1 ==> x ≠ 0` | ✅ |
| `lemma_decompress_valid_branch` | Proves all 3 ensures clauses | ✅ |

### Step1 Lemmas (`step1_lemmas.rs`)

| Lemma | Formal Statement | Status |
|-------|-----------------|--------|
| `lemma_sqrt_ratio_implies_on_curve` | `field_mul(x², v) == u ==> math_on_edwards_curve(x, y)` | ✅ |
| `lemma_sqrt_ratio_success_means_valid_y` | `fe51_is_sqrt_ratio success ==> math_is_valid_y_coordinate(y)` | ✅ |
| `lemma_sqrt_ratio_failure_means_invalid_y` | `!fe51_is_sqrt_ratio success ==> !math_is_valid_y_coordinate(y)` | ✅ |
| `lemma_u_zero_implies_identity_point` | `u == 0 ==> x == 0 && (y == ±1)` | ✅ |
| `lemma_step1_case_analysis` | `choice_is_true <==> math_is_valid_y_coordinate` | ✅ |

### Field Algebra Lemmas (`field_algebra_lemmas.rs`)

| Lemma | Formal Statement | Status |
|-------|-----------------|--------|
| `lemma_field_mul_distributes_over_add` | `a·(b+c) == a·b + a·c` | ✅ |
| `lemma_field_add_sub_rearrange` | Algebraic rearrangement for curve equation | ✅ |
| `lemma_neg_square_eq` | `(-x)² == x² mod p` | ✅ |
| `lemma_square_mod_noop` | `(x % p)² % p == x² % p` | ✅ |
| `lemma_field_inv_one` | `inv(1) == 1` | ✅ |
| `lemma_inv_of_product` | `inv(a·b) == inv(a)·inv(b)` | ✅ |
| `lemma_inv_of_square` | `inv(x²) == inv(x)²` | ✅ |
| `lemma_quotient_of_squares` | `a²/b² == (a/b)²` | ✅ |

### Constants Lemmas

| Lemma | Location | Statement | Status |
|-------|----------|-----------|--------|
| `lemma_one_limbs_bounded` | `field_lemmas/constants_lemmas.rs` | ONE.limbs < 2^51 | ✅ |
| `lemma_one_field_element_value` | `field_lemmas/constants_lemmas.rs` | `fe51_as_canonical_nat(ONE) == 1` | ✅ |
| `lemma_edwards_d_limbs_bounded` | `edwards_lemmas/constants_lemmas.rs` | EDWARDS_D.limbs < 2^51 | ✅ |

### SQRT_M1 Lemmas (`sqrt_ratio_lemmas.rs`)

| Lemma | Formal Statement | Status |
|-------|-----------------|--------|
| `lemma_multiply_by_i_flips_sign` | `(r·i)² == -r²` | ✅ |
| `lemma_i_inverse_is_neg_i` | `i⁻¹ == -i mod p` | ✅ |
| `lemma_no_square_root_when_times_i` | `v·r² == i·u ==> ¬∃x: v·x² == u` | ✅ |
| `lemma_algebraic_chain_base` | `q² = r_squared_v · inv(i·u)` | ✅ |
| `lemma_u_times_inv_iu_is_neg_i` | `u · inv(i·u) = -i` | ✅ |
| `lemma_neg_u_times_inv_iu_is_i` | `(-u) · inv(i·u) = i` | ✅ |
| `lemma_flipped_sign_becomes_correct` | `v·r² = -u ==> v·(r·i)² = u` | ✅ |
| `lemma_is_sqrt_ratio_to_field` | `fe51_is_sqrt_ratio(u, v, x) ==> field_mul(x², v) == u` | ✅ |

---

## Verification Summary

| Metric | Value |
|--------|-------|
| Total verified | **913** |
| Errors | **0** |
| Axioms | 4 (all mathematically justified) |
| Lemmas with admits | **0** |
| **Success path** | ✅ **Fully proved** |
| **Failure path** | ✅ **Fully proved** |

---

## File Locations

| Component | File |
|-----------|------|
| `decompress` function | `edwards.rs` |
| `step_1`, `step_2` | `edwards.rs` |
| Main decompress lemmas | `lemmas/edwards_lemmas/decompress_lemmas.rs` |
| Step1 curve/validity lemmas | `lemmas/edwards_lemmas/step1_lemmas.rs` |
| Field algebra lemmas | `lemmas/field_lemmas/field_algebra_lemmas.rs` |
| Field constants | `lemmas/field_lemmas/constants_lemmas.rs` |
| Edwards constants | `lemmas/edwards_lemmas/constants_lemmas.rs` |
| SQRT_M1 axioms & lemmas | `lemmas/common_lemmas/sqrt_ratio_lemmas.rs` |
| Primality axiom | `specs/primality_specs.rs` |

---

## References

1. [RFC 8032](https://www.rfc-editor.org/rfc/rfc8032) - Edwards-Curve Digital Signature Algorithm (EdDSA)
2. [BBJLP2008] Bernstein et al. - "Twisted Edwards Curves"
3. [HWCD2008] Hisil et al. - "Twisted Edwards Curves Revisited"
4. [decompress_proof_status.md](decompress_proof_status.md) - Detailed verification status and complete dependency graph
