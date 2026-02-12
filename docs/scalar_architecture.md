# Scalar Architecture

This document describes the architecture for scalar representations and their spec functions in the Verus-verified curve25519-dalek codebase.

## Overview

Scalars represent integers modulo the group order `L = 2^252 + 27742317777372353535851937790883648493`. The codebase uses two representations:

| Type | Location | Representation | Primary Use |
|------|----------|----------------|-------------|
| `Scalar` | `scalar.rs` | 32 bytes (little-endian) | Public API, serialization |
| `Scalar52` | `backend/serial/u64/scalar.rs` | 5 × 52-bit limbs | Internal arithmetic |

---

## Type Definitions

### `Scalar` (High-level)

```rust
pub struct Scalar {
    pub bytes: [u8; 32],
}
```

- **Invariant:** Canonical scalars satisfy `u8_32_as_nat(&bytes) < group_order()`
- **Usage:** Public API, serialization, external interfaces

### `Scalar52` (Low-level)

```rust
pub struct Scalar52 {
    pub limbs: [u64; 5],
}
```

- **Representation:** 5 limbs × 52 bits = 260 bits (covers 253-bit group order with room for carries)
- **Invariant:** Well-formed scalars have `limbs[i] < 2^52` for all i
- **Usage:** Montgomery multiplication, internal arithmetic

---

## Spec Functions

### Value Interpretation

| Function | Location | Definition | Purpose |
|----------|----------|------------|---------|
| `scalar_as_nat` | `scalar_specs.rs` | `u8_32_as_nat(&s.bytes)` | Scalar → nat |
| `scalar52_to_nat` | `scalar52_specs.rs` | `limbs52_to_nat(&s.limbs)` | Scalar52 → nat |
| `spec_scalar` | `scalar_specs.rs` | `u8_32_as_nat(&s.bytes) % group_order()` | Scalar → nat mod L |
| `spec_scalar52` | `scalar52_specs.rs` | `scalar52_to_nat(s) % group_order()` | Scalar52 → nat mod L |

### Validity Predicates

| Predicate | Location | Definition | Purpose |
|-----------|----------|------------|---------|
| `is_canonical_scalar` | `scalar_specs.rs` | `u8_32_as_nat(&s.bytes) < group_order() && s.bytes[31] <= 127` | Canonical Scalar |
| `is_canonical_scalar52` | `scalar52_specs.rs` | `limbs_bounded(s) && scalar52_to_nat(s) < group_order()` | Canonical Scalar52 |
| `limbs_bounded` | `scalar52_specs.rs` | `∀i. limbs[i] < 2^52` | Well-formed limbs |

### Constants

| Function | Location | Value | Purpose |
|----------|----------|-------|---------|
| `group_order()` | `scalar52_specs.rs` | `2^252 + 27742317777372353535851937790883648493` | L (group order) |
| `montgomery_radix()` | `scalar52_specs.rs` | `2^260` | Montgomery R |
| `inv_montgomery_radix()` | `scalar52_specs.rs` | R⁻¹ mod L | Montgomery inverse |

---

## Representation Relationship

```
┌─────────────────────────────────────────────────────────────────┐
│                         Scalar (bytes)                          │
│  ┌──────┬──────┬──────┬─────────────────────────────┬──────┐   │
│  │ b[0] │ b[1] │ b[2] │ ...                         │b[31] │   │
│  └──────┴──────┴──────┴─────────────────────────────┴──────┘   │
│    8-bit   8-bit  8-bit                               8-bit     │
│                                                                  │
│  scalar_as_nat = Σ b[i] × 2^(8i)  for i ∈ [0, 31]              │
└─────────────────────────────────────────────────────────────────┘
                              ↕
                    from_bytes / pack
                              ↕
┌─────────────────────────────────────────────────────────────────┐
│                       Scalar52 (limbs)                          │
│  ┌──────────┬──────────┬──────────┬──────────┬──────────┐      │
│  │ limbs[0] │ limbs[1] │ limbs[2] │ limbs[3] │ limbs[4] │      │
│  └──────────┴──────────┴──────────┴──────────┴──────────┘      │
│     52-bit     52-bit     52-bit     52-bit     52-bit          │
│                                                                  │
│  scalar52_to_nat = Σ limbs[i] × 2^(52i)  for i ∈ [0, 4]        │
└─────────────────────────────────────────────────────────────────┘
```

**Key invariant:** After `Scalar52::from_bytes(&bytes)`:
```rust
u8_32_as_nat(bytes) == scalar52_to_nat(&s)
```

---

## Conversion Functions

### Bytes → Limbs

```rust
impl Scalar52 {
    /// Unpack 32 bytes into 5 × 52-bit limbs
    pub fn from_bytes(bytes: &[u8; 32]) -> Scalar52
        ensures
            u8_32_as_nat(bytes) == scalar52_to_nat(&s),
            limbs_bounded(&s),
    
    /// Reduce 64 bytes mod L into canonical Scalar52
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar52
        ensures
            is_canonical_scalar52(&s),
            scalar52_to_nat(&s) == bytes_seq_as_nat(bytes@) % group_order(),
}
```

### Limbs → Bytes

```rust
impl Scalar52 {
    /// Pack 5 × 52-bit limbs into 32 bytes
    pub fn pack(&self) -> Scalar
        requires
            limbs_bounded(self),
        ensures
            scalar52_to_nat(self) < group_order() ==> is_canonical_scalar(&result),
}
```

---

## Montgomery Arithmetic

All internal scalar arithmetic uses Montgomery form with R = 2^260.

### Montgomery Operations

| Function | Postcondition |
|----------|---------------|
| `montgomery_mul(a, b)` | `(result × R) % L == (a × b) % L` |
| `montgomery_square(self)` | `(result × R) % L == (self × self) % L` |
| `to_montgomery(self)` | `result % L == (self × R) % L` |
| `from_montgomery(self)` | `(result × R) % L == self % L`, `is_canonical_scalar52(&result)` |

### Why Montgomery?

Montgomery multiplication avoids expensive division by L. Instead:
1. Convert to Montgomery form: `a' = a × R mod L`
2. Multiply in Montgomery form: `a' × b' × R⁻¹ mod L`
3. Convert back: `result × R⁻¹ mod L`

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              PUBLIC API                                      │
│                                                                              │
│  Scalar::from(u64)  Scalar::from_bytes()  Scalar::from_bytes_mod_order()    │
│         │                    │                         │                     │
└─────────┼────────────────────┼─────────────────────────┼─────────────────────┘
          │                    │                         │
          ▼                    ▼                         ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Scalar (scalar.rs)                                   │
│                                                                              │
│  struct Scalar { bytes: [u8; 32] }                                          │
│                                                                              │
│  Specs:                                                                      │
│    scalar_as_nat(&s) = u8_32_as_nat(&s.bytes)                             │
│    is_canonical_scalar(&s) = value < L && high_bit_clear                    │
│                                                                              │
└─────────────────────────────────┬───────────────────────────────────────────┘
                                  │
                    unpack()      │      pack()
                        │         │         │
                        ▼         │         ▲
┌─────────────────────────────────┼───────────────────────────────────────────┐
│                    Scalar52 (backend/serial/u64/scalar.rs)                   │
│                                                                              │
│  struct Scalar52 { limbs: [u64; 5] }                                        │
│                                                                              │
│  Specs:                                                                      │
│    scalar52_to_nat(&s) = limbs52_to_nat(&s.limbs)                           │
│    is_canonical_scalar52(&s) = limbs_bounded(s) && value < L                │
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                      Montgomery Arithmetic                              │ │
│  │                                                                         │ │
│  │  to_montgomery() ←──────────────────────────────────→ from_montgomery() │ │
│  │        │                                                     ▲          │ │
│  │        ▼                                                     │          │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │          │ │
│  │  │ montgomery_mul  montgomery_square  montgomery_reduce   │─┘          │ │
│  │  └─────────────────────────────────────────────────────────┘            │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                              │
│  Other operations:                                                           │
│    add(a, b)    sub(a, b)    mul(a, b)    invert()                          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Spec Functions Hierarchy

```
scalar_specs.rs                      scalar52_specs.rs
───────────────                      ───────────────────

scalar_as_nat(&Scalar)               scalar52_to_nat(&Scalar52)
       │                                    │
       └──→ u8_32_as_nat                  └──→ limbs52_to_nat
                  │                                    │
                  │                                    └──→ seq_to_nat_52
                  │
                  └──────────────────────────────────────────────┐
                                                                 │
                              core_specs.rs                      │
                              ─────────────                      │
                                                                 │
                              u8_32_as_nat ◄───────────────────┘
                              bytes_seq_as_nat
                              words_as_nat_gen
```

---

## Current State vs Potential Improvements

### ✅ Current Strengths

1. **Clear separation:** `Scalar` (bytes) vs `Scalar52` (limbs)
2. **Canonical predicates:** `is_canonical_scalar` and `is_canonical_scalar52`
3. **Montgomery encapsulation:** Internal representation hidden from public API
4. **Bridge lemmas:** `from_bytes` proves `u8_32_as_nat(bytes) == scalar52_to_nat(&s)`

### 🔧 Potential Improvements

#### 1. Unify `*_to_nat` definitions through a common base

Currently:
- `scalar_as_nat` → `u8_32_as_nat` (8-bit radix)
- `scalar52_to_nat` → `seq_to_nat_52` (52-bit radix)

**Potential:** Define both in terms of `words_as_nat_gen`:
```rust
// Theoretical unification (not necessarily better for SMT solver)
pub open spec fn u8_32_as_nat(bytes: &[u8; 32]) -> nat {
    words_as_nat_gen(bytes@.map(|i, x| x as nat), 32, 8)
}

pub open spec fn scalar52_to_nat(s: &Scalar52) -> nat {
    words_as_nat_gen(s.limbs@.map(|i, x| x as nat), 5, 52)
}
```

**Trade-off:** Current explicit forms are better for SMT solver efficiency.

#### 2. ✅ `spec_scalar52` (analogous to `spec_scalar`)

Already implemented:
```rust
/// Returns the mathematical value of a Scalar52 modulo the group order.
pub open spec fn spec_scalar52(s: &Scalar52) -> nat {
    scalar52_to_nat(s) % group_order()
}
```

#### 3. Add Montgomery-form spec functions

```rust
/// Value in Montgomery form: represents x where actual value is x × R⁻¹ mod L
pub open spec fn montgomery_value(s: &Scalar52) -> nat {
    (scalar52_to_nat(s) * inv_montgomery_radix()) % group_order()
}
```

#### 4. Consolidate canonical predicates

The relationship between canonicity at different levels could be made more explicit:

```rust
// Lemma: canonical Scalar52 packs to canonical Scalar
proof fn lemma_canonical_pack(s: &Scalar52)
    requires is_canonical_scalar52(s)
    ensures is_canonical_scalar(&s.pack())
```

## Related Files

- `curve25519-dalek/src/scalar.rs` — High-level `Scalar` type and public API
- `curve25519-dalek/src/backend/serial/u64/scalar.rs` — `Scalar52` implementation
- `curve25519-dalek/src/specs/scalar_specs.rs` — `Scalar` spec functions
- `curve25519-dalek/src/specs/scalar52_specs.rs` — `Scalar52` spec functions
- `curve25519-dalek/src/specs/core_specs.rs` — Core `u8_32_as_nat`, etc.
- `curve25519-dalek/src/lemmas/scalar_lemmas.rs` — Scalar arithmetic lemmas
- `curve25519-dalek/src/lemmas/scalar_montgomery_lemmas.rs` — Montgomery lemmas
- `curve25519-dalek/src/constants.rs` — `L`, `R`, `RR`, `LFACTOR` constants

🤖 Generated with Claude Opus 4.5