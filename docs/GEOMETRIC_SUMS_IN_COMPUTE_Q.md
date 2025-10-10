# Geometric Sums in lemma_compute_q

## Overview

This document explains how geometric series formulas are essential to proving `lemma_compute_q`, which establishes that the carry propagation algorithm correctly computes whether `as_nat(limbs) >= p()`.

## The Proof Chain

```
lemma_compute_q (line 965)
  │
  ├─ Step 1: lemma_all_carries_bounded_by_3
  │          Proves all carries < 3
  │
  ├─ Step 2: lemma_q_is_binary (line 982)
  │          Proves q can only be 0 or 1
  │          │
  │          └──> lemma_carry_propagation_is_division (line 859)
  │               Proves: q = (as_nat(limbs) + 19) / 2^255
  │               │
  │               └──> lemma_radix51_telescoping_direct (line 783)  ⭐ KEY LEMMA
  │                    Proves telescoping division in radix-51
  │                    │
  │                    ├──> lemma_radix51_telescoping_expansion (line 238)
  │                    │    Pure algebraic expansion showing cancellation
  │                    │
  │                    └──> lemma_radix51_remainder_bound (line 246) 🎯 GEOMETRIC SUMS HERE!
  │                         Proves: r0 + r1*2^51 + ... + r4*2^204 < 2^255
  │                         │
  │                         ├──> lemma_radix_51_partial_geometric_sum() (line 438)
  │                         │    Proves: 2^51 + 2^102 + 2^153 + 2^204 < 2^255
  │                         │
  │                         └──> lemma_geometric_series_radix51() (line 487)
  │                              Proves: (2^51 - 1) × (1 + 2^51 + ... + 2^204) = 2^255 - 1
  │
  └─ Step 3: lemma_q_biconditional
             Proves: as_nat(limbs) >= p() ⟺ q == 1
```

## The Mathematical Story

### 1. The Telescoping Division (lines 142-250)

The carry propagation algorithm processes 5 limbs through successive divisions by 2^51:

```
Stage 0: limbs[0] + 19 = q0 × 2^51 + r0
Stage 1: limbs[1] + q0 = q1 × 2^51 + r1
Stage 2: limbs[2] + q1 = q2 × 2^51 + r2
Stage 3: limbs[3] + q2 = q3 × 2^51 + r3
Stage 4: limbs[4] + q3 = q4 × 2^51 + r4
```

where each `0 ≤ ri < 2^51` (remainders are bounded).

### 2. The Telescoping Property

When you substitute these equations into the radix-51 representation of `as_nat(limbs) + 19`, the intermediate quotients `q0, q1, q2, q3` **telescope** (cancel out):

```
as_nat(limbs) + 19 = limbs[0] + limbs[1]×2^51 + limbs[2]×2^102 + limbs[3]×2^153 + limbs[4]×2^204 + 19

Substituting the stage equations and expanding:
  = (q0×2^51 + r0 - 19)
  + (q1×2^51 + r1 - q0)×2^51
  + (q2×2^51 + r2 - q1)×2^102
  + (q3×2^51 + r3 - q2)×2^153
  + (q4×2^51 + r4 - q3)×2^204
  + 19

After expansion and cancellation:
  = q4 × 2^51 × 2^204 + (r0 + r1×2^51 + r2×2^102 + r3×2^153 + r4×2^204)
  = q4 × 2^255 + remainder
```

Key observation: All intermediate quotients cancel!
- `+q0×2^51 - q0×2^51 = 0`
- `+q1×2^102 - q1×2^102 = 0`
- `+q2×2^153 - q2×2^153 = 0`
- `+q3×2^204 - q3×2^204 = 0`

This is proven in `lemma_radix51_telescoping_expansion` (lines 48-129).

### 3. Why We Need Division Uniqueness

To conclude that `q4 = (as_nat(limbs) + 19) / 2^255`, we invoke the **uniqueness of integer division**:

**Division Theorem:** For any integer `n` and positive divisor `d`, there exist **unique** integers `q` (quotient) and `r` (remainder) such that:
- `n = q × d + r`
- `0 ≤ r < d`

We've shown:
- ✅ `as_nat(limbs) + 19 = q4 × 2^255 + remainder` (telescoping)
- ❓ `0 ≤ remainder < 2^255` (needs proof!)

If both conditions hold, then by uniqueness, `q4` **must be** the quotient.

### 4. Bounding the Remainder - The Critical Step

This is where **geometric sums become essential**!

We need to prove:
```
remainder = r0 + r1×2^51 + r2×2^102 + r3×2^153 + r4×2^204 < 2^255
```

Since each `ri < 2^51`, the worst-case (maximum) value occurs when all `ri = 2^51 - 1`:

```
remainder_max = (2^51 - 1) + (2^51 - 1)×2^51 + (2^51 - 1)×2^102 + (2^51 - 1)×2^153 + (2^51 - 1)×2^204
              = (2^51 - 1) × (1 + 2^51 + 2^102 + 2^153 + 2^204)
              = (2^51 - 1) × sum_powers
```

So we need: `(2^51 - 1) × sum_powers < 2^255`

### 5. Enter the Geometric Series Formula!

`lemma_geometric_series_radix51` (lines 497-562) proves the **exact closed form**:

```rust
pub proof fn lemma_geometric_series_radix51(sum_powers: int)
    requires
        sum_powers == 1 + pow2(51) + pow2(102) + pow2(153) + pow2(204),
    ensures
        (pow2(51) - 1) * sum_powers == pow2(255) - 1,
```

This is the **classic geometric series formula** with first term `a = 1`, ratio `r = 2^51`, and `n = 5` terms:

```
sum = a × (1 + r + r² + r³ + r⁴)
    = 1 × (1 + 2^51 + 2^102 + 2^153 + 2^204)

Closed form: (r - 1) × sum = r^5 - 1
           : (2^51 - 1) × sum_powers = (2^51)^5 - 1 = 2^255 - 1
```

**Proof sketch:**
```
(r - 1) × (1 + r + r² + r³ + r⁴)
  = r × (1 + r + r² + r³ + r⁴) - (1 + r + r² + r³ + r⁴)
  = (r + r² + r³ + r⁴ + r⁵) - (1 + r + r² + r³ + r⁴)
  = r⁵ - 1   (telescoping!)
```

### 6. Completing the Bound

From the geometric series formula:
```
(2^51 - 1) × sum_powers = 2^255 - 1
```

Therefore:
```
remainder ≤ (2^51 - 1) × sum_powers = 2^255 - 1 < 2^255  ✓
```

This satisfies the division theorem's requirement that `remainder < divisor`!

### 7. Division Uniqueness Concludes the Proof

With both conditions satisfied:
- `as_nat(limbs) + 19 = q4 × 2^255 + remainder`
- `0 ≤ remainder < 2^255`

By uniqueness of division (invoked at line 249):
```rust
lemma_div_quotient_unique(value, pow2(255) as int, q4, remainder);
```

We conclude: **`q4 = (as_nat(limbs) + 19) / 2^255`** ✓

## Why the Geometric Formula Is Essential

### Attempt 1: Naive Bound (Too Weak)

You might think: "Each term is bounded, so just add the bounds":
```
remainder < 2^51 + 2^51×2^51 + 2^51×2^102 + 2^51×2^153 + 2^51×2^204
          = 2^51 × (1 + 2^51 + 2^102 + 2^153 + 2^204)
          = 2^51 × sum_powers
```

But this is **too weak**! We need to bound `2^51 × sum_powers`:
```
2^51 × sum_powers = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
```

This includes `2^255`, so: `2^51 × sum_powers ≥ 2^255` ✗

This doesn't prove `remainder < 2^255`!

### Attempt 2: Partial Sum (Better, but Still Not Tight)

`lemma_radix_51_partial_geometric_sum` proves:
```
2^51 + 2^102 + 2^153 + 2^204 < 2^255
```

This helps but doesn't directly bound `(2^51 - 1) × sum_powers`.

### The Correct Approach: Exact Formula

Only the **exact geometric series formula** gives the tight bound:
```
(2^51 - 1) × sum_powers = 2^255 - 1
```

This is **exactly one less than 2^255**, which is the tightest possible bound!

## Supporting Lemmas

### lemma_radix_51_partial_geometric_sum (lines 565-643)

Proves the simpler bound:
```
2^51 + 2^102 + 2^153 + 2^204 < 2^255
```

Used as an intermediate step in `lemma_radix51_remainder_bound`. While this can be derived from the full geometric series formula, the direct proof (using dominance by the largest term) is clearer for Verus's SMT solver.

### lemma_radix51_telescoping_expansion (lines 48-129)

Proves the pure algebraic expansion showing that intermediate quotients cancel in the telescoping sum. This is the algebraic heart of why carry propagation works.

## Key Insight

The geometric sum `1 + r + r² + ... + r^n` appears naturally when you:
1. Use radix-`r` representation (here `r = 2^51`)
2. Have `n+1` limbs (here 5 limbs = 4 powers + constant term)
3. Want to bound the remainder when all remainders are maximal

The closed form `(r-1) × sum = r^(n+1) - 1` is not just elegant mathematics—it's **essential** for the proof because it gives the exact bound needed for division uniqueness.

## Radix-51 and 2^255

The choice of radix-51 and 5 limbs is not arbitrary:
- 5 limbs of 51 bits each: `51 × 5 = 255 bits`
- This exactly covers the field prime: `p = 2^255 - 19`
- The geometric series with `r = 2^51` and 5 terms gives `r^5 - 1 = 2^255 - 1`
- This precise match makes the division by `2^255` clean!

## Takeaway

**Geometric sums are not optional decoration—they are the mathematical foundation that makes the telescoping division proof work!** Without the closed-form formula `(2^51 - 1) × sum_powers = 2^255 - 1`, you cannot prove the remainder is bounded by `2^255`, and therefore cannot use division uniqueness to conclude that `q4` is the correct quotient.

This is a beautiful example of how a classic result from discrete mathematics (geometric series) is essential to modern cryptographic verification.

## Related Lemmas

- **lemma_geometric_series_radix51** (line 497): Full geometric series formula
- **lemma_radix_51_partial_geometric_sum** (line 565): Partial sum bound
- **lemma_radix51_remainder_bound** (line 253): Main remainder bound using geometric sums
- **lemma_radix51_telescoping_expansion** (line 48): Algebraic cancellation
- **lemma_radix51_telescoping_direct** (line 142): Complete telescoping division theorem
- **lemma_carry_propagation_is_division** (line 734): Connects algorithm to division
- **lemma_q_is_binary** (line 849): Proves q ∈ {0, 1}
- **lemma_compute_q** (line 965): Top-level theorem

## Files

All lemmas are in: `curve25519-dalek/src/backend/serial/u64/field_lemmas/to_bytes_lemmas.rs`

