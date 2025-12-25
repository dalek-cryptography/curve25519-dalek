# Limb Bounds Analysis: Scalar52 and FieldElement51

This document systematically analyzes which functions create and consume `Scalar52` and `FieldElement51`, and how bounds are established and maintained.

## Summary

| Type | `*_to_nat` function | Bounds predicate | Canonical predicate |
|------|---------------------|------------------|---------------------|
| `Scalar52` | `scalar52_to_nat` | `limbs_bounded` (< 2^52) | `is_canonical_scalar52` |
| `FieldElement51` | `u64_5_as_nat` / `spec_field_element_as_nat` | `fe51_limbs_bounded(fe, bit_limit)` | - |

**Key insight:** The `*_to_nat` functions are "raw" polynomial interpretations without built-in bounds guarantees. Bounds are established via preconditions and maintained via postconditions.

---

## Part 1: Scalar52

### Creators (functions that produce Scalar52)

| Function | Postcondition: bounds | Postcondition: value |
|----------|----------------------|----------------------|
| `from_bytes` | `limbs_bounded(&s)` | `bytes32_to_nat(bytes) == scalar52_to_nat(&s)` |
| `from_bytes_wide` | `is_canonical_scalar52(&s)` | `scalar52_to_nat(&s) == bytes_seq_to_nat(bytes@) % group_order()` |
| `add` | `is_canonical_scalar52(&s)` | `scalar52_to_nat(&s) == (a + b) % group_order()` |
| `sub` | `is_canonical_scalar52(&s)` | `scalar52_to_nat(&s) == (a - b) % group_order()` |
| `mul` | `is_canonical_scalar52(&result)` | `scalar52_to_nat(&result) % L == (a * b) % L` |
| `square` | (implicit via mul) | `scalar52_to_nat(&result) == (self * self) % L` |
| `montgomery_mul` | `limbs_bounded(&result)` | Montgomery property |
| `montgomery_square` | `limbs_bounded(&result)` | Montgomery property |
| `as_montgomery` | `limbs_bounded(&result)` | Montgomery property |
| `from_montgomery` | `is_canonical_scalar52(&result)` | Montgomery property |

### Consumers (functions that take Scalar52 as input)

| Function | Precondition: bounds | Precondition: value |
|----------|---------------------|---------------------|
| `add` | `limbs_bounded(a), limbs_bounded(b)` | `< group_order()` for both |
| `sub` | `limbs_bounded(a), limbs_bounded(b)` | difference in range |
| `mul` | `limbs_bounded(a), limbs_bounded(b)` | - |
| `square` | `limbs_bounded(self)` | - |
| `mul_internal` | `limbs_bounded(a), limbs_bounded(b)` | - |
| `square_internal` | `limbs_bounded(a)` | - |
| `montgomery_mul` | `limbs_bounded(a), limbs_bounded(b)` | - |
| `montgomery_square` | `limbs_bounded(self)` | - |
| `as_montgomery` | `limbs_bounded(self)` | - |
| `from_montgomery` | `limbs_bounded(self)` | - |
| `conditional_add_l` | `limbs_bounded(self)` | `+ L < 2^260` |
| `as_bytes` | `limbs_bounded(self)` | - |
| `pack` | `limbs_bounded(self)` | - |

### Serialization: as_bytes

The `as_bytes` function deserves special attention as it's the inverse of `from_bytes`:

```rust
// Scalar52::as_bytes (scalar.rs:472)
pub fn as_bytes(self) -> (s: [u8; 32])
    requires
        limbs_bounded(&self),
    ensures
        bytes32_to_nat(&s) == scalar52_to_nat(&self) % pow2(256),
```

**Note:** The postcondition includes `% pow2(256)` because `scalar52_to_nat` can produce values up to 2^260 (5 limbs × 52 bits). When serializing to 32 bytes, only the low 256 bits are preserved. For canonical scalars (< group_order < 2^256), this modulus is a no-op.

### Analysis: Scalar52 bounds chain

```
                         CREATORS
                            │
from_bytes(bytes)     ──ensures──> limbs_bounded(&s)
from_bytes_wide(bytes) ─ensures──> is_canonical_scalar52(&s)
                            │
                            ▼
                    [operations require limbs_bounded]
                            │
                            ▼
                    results ensure limbs_bounded or is_canonical_scalar52
                            │
                         CONSUMERS
                            │
            ┌───────────────┼───────────────┐
            │               │               │
            ▼               ▼               ▼
       as_bytes()       pack()        operations
            │               │               │
            ▼               ▼               ▼
     [u8; 32]         Scalar         Scalar52
     (raw bytes)      (verified)     (verified)
```

**Roundtrip property:**
- `from_bytes → as_bytes`: `bytes32_to_nat(&as_bytes(from_bytes(b))) == bytes32_to_nat(b) % pow2(256)`
- For 32-byte inputs: value is preserved exactly

**Conclusion:** 
- All creators establish at least `limbs_bounded`
- `mul`/`square` only require `limbs_bounded` → works with any creator
- `add`/`sub` require `limbs_bounded` AND `< group_order()` → only works with `is_canonical_scalar52` results
- `from_bytes` produces values that may be `>= group_order()`, so cannot be directly used with `add`/`sub`

---

## Part 2: FieldElement51

### Creators (functions that produce FieldElement51)

| Function | Postcondition: bounds | Postcondition: value |
|----------|----------------------|----------------------|
| `from_bytes` | `fe51_limbs_bounded(&r, 51)` | `spec_field_element_as_nat(&r) == bytes32_to_nat(bytes) % pow2(255)` |
| `from_limbs` | - (direct construction) | `result.limbs == limbs` |
| `reduce` | `limbs[i] < 2^52` | Value mod p preserved |
| `add` | (depends on inputs) | `spec_field_element_as_nat` sum |
| `sub` | (after reduce) | `spec_field_element` preserved mod p |
| `neg` | `limbs[i] < 2^52` | `spec_field_element` negated mod p |
| `pow2k` | (depends on inputs) | Repeated squaring mod p |
| `square` | (depends on inputs) | `spec_field_element` squared mod p |
| `square2` | (depends on inputs) | `2 * spec_field_element` squared mod p |
| `conditional_select` | (from inputs) | Selected value |

### Consumers (functions that take FieldElement51 as input)

| Function | Precondition: bounds |
|----------|---------------------|
| `add` / `add_assign` | `sum_of_limbs_bounded(a, b, u64::MAX)` |
| `sub` | `fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(rhs, 54)` |
| `mul` / `mul_assign` | `fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(rhs, 54)` |
| `pow2k` | `limbs[i] < 2^54` |
| `square` | `limbs[i] < 2^54` |
| `square2` | `limbs[i] < 2^54` |
| `as_bytes` / `to_bytes` | (implicit - handles internally) |

### Serialization: as_bytes / to_bytes

The `as_bytes` function for FieldElement51:

```rust
// FieldElement51::as_bytes (field.rs:1007)
pub fn as_bytes(self) -> (r: [u8; 32])
    ensures
        bytes32_to_nat(&r) == spec_field_element(&self),
```

**Note:** Unlike Scalar52, there's no explicit `% pow2(256)` because:
1. Field elements are always reduced mod p = 2^255 - 19
2. The function internally reduces before encoding
3. Result is guaranteed to be < p < 2^255

### Analysis: FieldElement51 bounds chain

**Key difference from Scalar52:** Field uses a parameterized bound `fe51_limbs_bounded(fe, bit_limit)` because:
- Fresh values from `from_bytes` have 51-bit limbs
- After operations, limbs can grow to 52-54 bits before reduction
- `reduce()` brings limbs back to < 52 bits

```
                         CREATORS
                            │
from_bytes(bytes)     ──ensures──> fe51_limbs_bounded(&r, 51)
                            │
                            ▼
                    [operations may grow limbs to 54 bits]
                            │
                            ▼
                    fe51_limbs_bounded(&result, 52..54)
                            │
                         CONSUMERS
                            │
            ┌───────────────┼───────────────┐
            │               │               │
            ▼               ▼               ▼
       as_bytes()      operations      reduce()
            │               │               │
            ▼               ▼               ▼
     [u8; 32]       FieldElement51   limbs < 52 bits
    (canonical)      (may need reduce)
```

**Roundtrip property:**
- `from_bytes → as_bytes`: `bytes32_to_nat(&as_bytes(from_bytes(b))) == bytes32_to_nat(b) % p()`
- High bit of byte[31] is cleared on input (bit 255 ignored)
- Output is always canonical (< p)

---

## Part 3: Comparison

| Aspect | Scalar52 | FieldElement51 |
|--------|----------|----------------|
| Limb radix | 52 bits | 51 bits |
| Total bits | 5 × 52 = 260 | 5 × 51 = 255 |
| Bounds predicate | `limbs_bounded` (fixed at 52) | `fe51_limbs_bounded(fe, bit_limit)` (parameterized) |
| Canonical predicate | `is_canonical_scalar52` (< L) | - |
| Value preservation | `bytes32_to_nat == scalar52_to_nat` | `bytes32_to_nat % 2^255 == u64_5_as_nat` |

### Canonicity Differences

**Scalar52: Eager reduction**
- Most operations (`add`, `sub`, `mul`, `from_bytes_wide`) produce canonical results
- Postconditions guarantee `is_canonical_scalar52(&result)`
- This is because group order L is used for cryptographic operations

**FieldElement51: Lazy reduction**
- Operations like `add`, `sub`, `mul` produce values in [0, 2*p) (NOT canonical)
- Postcondition typically: `reduce()` ensures `u64_5_as_nat(r.limbs) < 2 * p()`
- Full reduction to [0, p) only happens in `as_bytes` / `to_bytes`
- `from_bytes` produces values in [0, 2^255) which may be >= p

**Where FieldElement51 canonicity applies:**
- After `as_bytes` round-trip: `from_bytes(fe.as_bytes())` is canonical
- In `compute_q` lemmas: determines if final reduction step is needed
- NOT after most arithmetic operations (they use lazy reduction)

---

## Part 4: Key Lemmas

### Scalar52 bounds lemmas

| Lemma | What it proves |
|-------|----------------|
| `lemma_bound_scalar` | `limbs_bounded(a) ==> scalar52_to_nat(&a) < pow2(260)` |
| `lemma_general_bound` | Generic version for any length |
| `lemma_scalar52_lt_pow2_256_if_canonical` | `limbs_bounded(a) && < L ==> < pow2(256)` |

### FieldElement51 bounds lemmas

| Lemma | What it proves |
|-------|----------------|
| `proof_reduce` | `reduce` produces bounded limbs |

🤖 Generated with Claude Opus 4.5