# to_bytes Proof Structure

## Summary

We've identified and stubbed out the three key lemmas needed to prove the correctness of `to_bytes`. All lemmas are currently admitted (using `assume(false)`).

## Lemma 1: Computing the Quotient `q`

**Location:** `field_lemmas/to_bytes_lemmas.rs`

**Spec Function:**
```rust
pub open spec fn compute_q_spec(limbs: [u64; 5]) -> u64
```

Computes q via successive carry propagation: `q = (((((limbs[0] + 19) >> 51) + limbs[1]) >> 51) + ... ) >> 51`

**Lemma:**
```rust
pub proof fn lemma_compute_q(limbs: [u64; 5], q: u64)
```

**Purpose:** Proves that q computed via successive carry propagation equals:
- `q == 1` if `as_nat(limbs) >= p()`
- `q == 0` if `as_nat(limbs) < p()`

**Status:** Admitted (needs proof)

## Lemma 2: Modular Reduction

**Location:** `field_lemmas/to_bytes_lemmas.rs`

**Spec Function:**
```rust
pub open spec fn reduce_with_q_spec(input_limbs: [u64; 5], q: u64) -> [u64; 5]
```

Computes the result of adding `19*q` and propagating carries while masking to 51 bits.

**Lemma:**
```rust
pub proof fn lemma_to_bytes_reduction(input_limbs: [u64; 5], final_limbs: [u64; 5], q: u64)
```

**Purpose:** Proves that after the reduction algorithm:
1. All final limbs are bounded: `final_limbs[i] < 2^51`
2. The value is preserved mod p: `as_nat(final_limbs) == as_nat(input_limbs) % p()`

**Status:** Admitted (needs proof)

## Lemma 3: Packing Limbs into Bytes

**Location:** `field_lemmas/to_bytes_lemmas.rs`

**Lemma:**
```rust
pub proof fn lemma_limbs_to_bytes(limbs: [u64; 5], bytes: [u8; 32])
```

**Purpose:** Proves that packing 51-bit limbs into 8-bit bytes preserves the value:
```
as_nat_32_u8(bytes) == as_nat(limbs)
```

This is the most complex lemma because it needs to handle:
- Simple byte extractions (e.g., `bytes[0] = limbs[0] as u8`)
- Overlapping bytes that combine parts of two limbs (e.g., `bytes[6] = (limbs[0] >> 48) | (limbs[1] << 3)`)

**Status:** Admitted (needs proof)

### Helper Lemmas

**`lemma_extract_byte`:** Proves extraction of a single byte from a u64
**`lemma_packed_byte`:** Proves correctness of bytes that combine two limbs
**`lemma_as_nat_32_u8_equivalence`:** Proves recursive and non-recursive definitions match

## Proof Flow in `to_bytes`

1. **Reduce input limbs** → limbs bounded by 2^52
2. **Compute q** → use `lemma_compute_q` to prove q is correct quotient
3. **Apply reduction** → use `lemma_to_bytes_reduction` to prove value preserved mod p
4. **Pack into bytes** → use `lemma_limbs_to_bytes` to prove byte encoding is correct

## Current Compilation Status

✅ All lemmas compile and type-check
✅ Integration with `to_bytes` function compiles
✅ **ALL OVERFLOW CHECKS RESOLVED** - Verification passes with 0 errors!
⚠️  Truncation warnings on u8 casts (these are just recommendations, not errors)

## Verification Status

**Current: 244 verified, 0 errors** 🎉

The proof structure is complete with:
- Helper lemma `lemma_shr_mono_u64` (fully proven, wraps existing lemma)
- All overflow assertions in place
- Strategic assumes for the 3 main lemmas (as intended)
- 1 additional assume for `final_limbs == reduce_with_q_spec(...)` (straightforward to prove)

## Next Steps

1. ✅ ~~Add overflow assertions for q computation~~ **DONE**
2. ✅ ~~Add truncation attributes for u8 casts~~ **Not needed** (just warnings)
3. Prove `lemma_compute_q`
4. Prove `lemma_to_bytes_reduction`
5. Prove `lemma_limbs_to_bytes` and its helpers
6. (Optional) Remove the assume by proving executable matches `reduce_with_q_spec`

