# Mathematical Proof for `part1` Function

## Overview

The `part1` function is a helper for Montgomery reduction. Given a sum, it computes `p` such that `(sum + p * L[0])` is divisible by 2^52, returning the carry.

## Function Body

```rust
fn part1(sum: u128) -> (u128, u64) {
    let mask52: u64 = 0xFFFFFFFFFFFFF;           // 2^52 - 1
    let sum_low52: u64 = (sum as u64) & mask52;  // s = sum mod 2^52
    let product: u128 = (sum_low52 as u128) * (LFACTOR as u128);
    let p: u64 = (product as u64) & mask52;      // p = (s * LFACTOR) mod 2^52
    let total: u128 = sum + (p as u128) * (L[0] as u128);
    let carry: u128 = total >> 52;
    (carry, p)
}
```

## Specification

```rust
requires sum < 2^108
ensures  p < 2^52
ensures  sum + p * L[0] == carry << 52
```

## Constants

| Constant | Value | Notes |
|----------|-------|-------|
| `L[0]` | `0x0002631a5cf5d3ed` | ≈ 2^50 |
| `LFACTOR` | `0x51da312547e1b` | 52 bits |
| `2^52` | `0x10000000000000` | Limb modulus |

---

# Part 1: Mathematical Proof

## Key Property: LFACTOR

LFACTOR is the **negated modular inverse** of L[0] modulo 2^52:

```
LFACTOR * L[0] ≡ -1 (mod 2^52)
```

Equivalently: `(1 + LFACTOR * L[0]) % 2^52 = 0`

This can be verified by direct computation.

## Main Theorem: Divisibility

**Goal**: Prove `(s + p * L[0]) % 2^52 = 0` where:
- `s = sum % 2^52` (low 52 bits of sum)
- `p = (s * LFACTOR) % 2^52`

**Proof**:

```
1. (1 + LFACTOR * L[0]) % 2^52 = 0           [LFACTOR property]

2. s * (1 + LFACTOR * L[0]) % 2^52 = 0       [scale by s: if x ≡ 0, then k*x ≡ 0]

3. s * (1 + LFACTOR * L[0]) = s + s*LFACTOR*L[0]   [distributivity]

4. p * L[0] ≡ s * LFACTOR * L[0] (mod 2^52)  [since p = s*LFACTOR mod 2^52]

5. (s + p * L[0]) % 2^52 = 0                 [combine steps 2-4]  ∎
```

## Extension to Full Sum

**Goal**: If `(s + p*L[0]) % 2^52 = 0`, then `(sum + p*L[0]) % 2^52 = 0`

**Proof**: Since `s = sum % 2^52`, we have `sum ≡ s (mod 2^52)`. Adding `p*L[0]` to both sides preserves the congruence.

## Final Step: Shift Round-Trip

**Goal**: Prove `sum + p*L[0] == carry << 52` where `carry = (sum + p*L[0]) >> 52`

**Proof**: If `x % 2^52 = 0` and `x` fits in u128, then `(x >> 52) << 52 = x`.

---

# Part 2: Verus Implementation

The proof uses **two lemmas** that mirror the mathematical structure, with a **two-phase approach** to eliminate bitvector solver calls.

## Design Philosophy

Following reviewer feedback, the proof converts bitwise operations to arithmetic equivalents early, then proceeds with pure arithmetic reasoning:

1. **Phase 1**: Convert bitwise ops → arithmetic using dedicated lemmas
2. **Phase 2**: Chain of arithmetic proofs using `pow2` and modulo lemmas

This approach reduces bitvector solver overhead and makes the proof structure mirror the mathematical reasoning.

## Lemma 1: `lemma_part1_divisible`

**Purpose**: Core divisibility proof (steps 1-5 of the math proof).

```rust
proof fn lemma_part1_divisible(s: u64, p: nat)
    requires
        s < pow2(52),
        p == (s * LFACTOR) % pow2(52),
    ensures
        (s + p * L[0]) % pow2(52) == 0
```

**Proof structure**:
1. Assert LFACTOR property: `(1 + LFACTOR * L[0]) % 2^52 = 0` via `by (compute)`
2. Scale by `s`: use `lemma_mul_mod_noop_right`
3. Expand via distributivity: use `lemma_mul_is_distributive_add`
4. Connect `p*L[0]` to `s*LFACTOR*L[0]`: use `lemma_mul_mod_noop_left`
5. Conclude with `lemma_add_mod_noop`

## Lemma 2: `lemma_part1_correctness`

**Purpose**: Main lemma proving the postcondition (includes extension and shift round-trip).

```rust
proof fn lemma_part1_correctness(sum: u128)
    requires sum < 2^108
    ensures  p < 2^52 && sum + p*L[0] == carry << 52
```

### Phase 1: Bitwise-to-Arithmetic Conversions (used in multiple places)

These conversions are established at the top level because they're used in multiple Phase 2 assertions:

| Conversion | Lemma Used | Used In |
|------------|------------|---------|
| `pow2(52) == 0x10000000000000` | `lemma2_to64_rest` | L0 bound, pow2_adds, mod_bound |
| `(1u64 << 52) == pow2(52)` | `lemma_u64_shift_is_pow2` | Postcondition `p < (1u64 << 52)` |
| `sum_low52 == sum % pow2(52)` | `lemma_u128_truncate_and_mask` | (1) sum_low52 < p52, (2) mod_add_eq |
| `p == product % pow2(52)` | `lemma_u128_truncate_and_mask` | (1) p < p52, (2) divisibility |

### Phase 2: Arithmetic Proofs

Each goal is proven with its preconditions nested inside where they're needed:

| Goal | Nested Preconditions | Lemmas Used |
|------|---------------------|-------------|
| `p < pow2(52)` | — | `lemma_pow2_pos`, `lemma_mod_bound` |
| `(s + p*L[0]) % pow2(52) == 0` | `sum_low52 < pow2(52)` | `lemma_part1_divisible` |
| `p * L[0] < pow2(102)` | `L0 < pow2(50)`, `pow2(52)*pow2(50) == pow2(102)` | `lemma_pow2_adds`, `lemma_mul_strict_inequality` |
| No overflow | `(1u128 << 108) == pow2(108)`, overflow bound chain | `lemma_pow2_strictly_increases`, `lemma_pow2_unfold` |
| `(total >> 52) << 52 == total` | `total % pow2(52) == 0` via mod_add_eq | `lemma_u128_right_left_shift_divisible` |

---

# Supporting Lemmas

| Lemma | Location | Purpose |
|-------|----------|---------|
| `lemma_part1_divisible` | `montgomery_reduce_lemmas.rs` | Core divisibility from LFACTOR property |
| `lemma_u128_truncate_and_mask` | `montgomery_reduce_lemmas.rs` | `(x as u64) & mask52 == x % pow2(52)` |
| `lemma_u128_shl_is_mul` | `shift_lemmas.rs` | `x << n == x * pow2(n)` for u128 |
| `lemma_u64_shift_is_pow2` | `shift_lemmas.rs` | `1 << n == pow2(n)` for u64 |
| `lemma_u128_right_left_shift_divisible` | `shift_lemmas.rs` | Shift round-trip when divisible |
| `lemma_mod_add_eq` | `div_mod_lemmas.rs` | `a ≡ b (mod m) ⟹ (a+c) ≡ (b+c) (mod m)` |
| `lemma_pow2_adds` | `vstd` | `pow2(a) * pow2(b) == pow2(a+b)` |

---

# Proof Structure Diagram

```
                    MATHEMATICAL                           VERUS
                    ═══════════                           ═════

              LFACTOR * L[0] ≡ -1 (mod 2^52)
                        │
                        ▼
┌─────────────────────────────────────────┐    ┌────────────────────────────────────┐
│  (s + p*L[0]) % 2^52 = 0                │ ←→ │ lemma_part1_divisible(s, p)        │
│  where p = s*LFACTOR mod 2^52           │    │   • by(compute) for LFACTOR        │
│                                         │    │   • vstd mul/mod lemmas            │
└─────────────────────────────────────────┘    └────────────────────────────────────┘
                        │                                     │
                        │                                     │
                        ▼                                     ▼
┌─────────────────────────────────────────┐    ┌────────────────────────────────────┐
│  Phase 1: Bitwise → Arithmetic          │    │ lemma_part1_correctness(sum)       │
│    • mask & truncate → % pow2(52)       │    │   PHASE 1: Conversions             │
│    • shift → * pow2(n)                  │    │     • lemma_u128_truncate_and_mask │
│                                         │    │     • lemma_u64_shift_is_pow2      │
├─────────────────────────────────────────┤    ├────────────────────────────────────┤
│  Phase 2: Pure Arithmetic               │    │   PHASE 2: Arithmetic              │
│    • p < 2^52 from mod bound            │    │     • lemma_mod_bound              │
│    • divisibility from LFACTOR          │    │     • calls lemma_part1_divisible  │
│    • no overflow from bounds            │    │     • lemma_mul_strict_inequality  │
│    • shift round-trip                   │    │     • lemma_right_left_shift_div   │
│                                         │    │                                    │
│  ∴ sum + p*L[0] == carry << 52         │    │                                    │
└─────────────────────────────────────────┘    └────────────────────────────────────┘
```

---

# Notes

1. **Placeholder lemmas**: Some `u128` bitwise-to-arithmetic lemmas (e.g., `lemma_u128_shl_is_mul`, `lemma_u128_truncate_and_mask`) currently use `assume(false)` and need proper proofs.

2. **Original code** used `wrapping_mul` which Verus can't handle in `by (bit_vector)`. The refactored code extracts low 52 bits first, avoiding wrapping semantics.
