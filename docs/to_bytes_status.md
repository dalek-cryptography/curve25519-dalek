#  to_bytes Proof Structure

## Overview

We successfully identified and implemented the complete proof structure for the `to_bytes` function, resolving all overflow verification errors incrementally.

## Starting Point

The `to_bytes` function had:
- An `assume(false)` blocking verification
- No clear structure for what lemmas were needed
- No understanding of what properties `as_nat_32_u8` requires

## What We Delivered

### 1. Identified 3 Core Lemmas ✅

**`lemma_compute_q`**
- Purpose: Proves q (computed via carry propagation) equals 1 iff `as_nat(limbs) >= p()`
- Status: Structured with admit
- Location: `field_lemmas/to_bytes_lemmas.rs:27-39`

**`lemma_to_bytes_reduction`**
- Purpose: Proves modular reduction algorithm preserves value mod p
- Status: Structured with admit
- Location: `field_lemmas/to_bytes_lemmas.rs:61-73`

**`lemma_limbs_to_bytes`**
- Purpose: Proves packing 51-bit limbs into 8-bit bytes preserves value
- Status: Structured with admit, includes all 32 byte equations
- Location: `field_lemmas/to_bytes_lemmas.rs:80-120`

### 2. Created Helper Lemmas

**`lemma_shr_mono_u64`** - FULLY PROVEN ✅
- Proves monotonicity of right shift
- Wraps existing `lemma_shr_le_u64` (already proven)
- No assumes needed!

**`lemma_add_preserves_bound`** - FULLY PROVEN ✅
- Simple arithmetic preservation
- No assumes needed!

Plus helper lemmas for byte packing:
- `lemma_extract_byte` (with admit)
- `lemma_packed_byte` (with admit)
- `lemma_as_nat_32_u8_equivalence` (with admit)

### 3. Fixed ALL Overflow Issues ✅

**Verification Status: 244 verified, 0 errors**

We systematically resolved:
- Q computation overflows (5 iterations)
- Reduction step overflows (4 carry propagations)
- Constant evaluation overflow (`(1u64 << 51) - 1`)

**Key techniques used:**
- Ghost variables to track values before mutation
- Monotonicity lemmas for shift operations
- `by (compute)` for concrete bounds
- Strategic proof blocks at each step

### 4. Integrated into to_bytes ✅

The `to_bytes` function now has a clean 4-step proof structure:

```rust
pub fn to_bytes(self) -> (r: [u8; 32])
    ensures
        as_nat_32_u8(r) == as_nat(self.limbs) % p()
{
    proof {
        // Step 1: Reduce limbs to ensure h < 2*p
        lemma_reduce(self.limbs);
    }
    
    // ... compute q with overflow proofs ...
    
    proof {
        // Step 2: Prove q is correct quotient  
        lemma_compute_q(reduced_limbs, q);
    }
    
    // ... apply reduction with overflow proofs ...
    
    proof {
        // Step 3: Prove reduction preserves value mod p
        lemma_to_bytes_reduction(reduced_limbs, final_limbs, q);
    }
    
    // ... pack into bytes ...
    
    proof {
        // Step 4: Prove byte packing preserves value
        lemma_limbs_to_bytes(final_limbs, s);
    }
    
    s
}
```

### 5. Documentation ✅

Created comprehensive documentation:
- `to_bytes_lemmas_summary.md` - Overview of all lemmas
- `overflow_fixes_completed.md` - Details on overflow resolution

## Files Modified

**New files:**
- `curve25519-dalek/src/backend/serial/u64/field_lemmas/to_bytes_lemmas.rs` (192 lines)
- `docs/to_bytes_lemmas_summary.md`
- `docs/overflow_fixes_completed.md`
- `docs/to_bytes_status.md` (this file)

**Modified files:**
- `curve25519-dalek/src/backend/serial/u64/field_verus.rs` - Updated `to_bytes` with proof structure
- `curve25519-dalek/src/backend/serial/u64/field_lemmas/mod.rs` - Added to_bytes_lemmas module

## Remaining Work (Well-Defined)

The three main lemmas need their `assume(false)` replaced with real proofs:

1. **Prove `lemma_compute_q`**
   - Show that carry propagation correctly computes quotient
   - Requires reasoning about modular arithmetic and carries

2. **Prove `lemma_to_bytes_reduction`**
   - Show reduction algorithm preserves value mod p
   - Build on existing `reduce` lemmas

3. **Prove `lemma_limbs_to_bytes`**
   - Most complex: 32 byte equations to verify
   - Decompose into simpler lemmas for byte extraction and packing
   - Prove recursive and non-recursive definitions equivalent

## Key Insights

1. **Incremental approach works**: Starting with the easiest (overflow proofs) built momentum
2. **Ghost variables are essential**: Needed for connecting values across mutations
3. **Existing lemmas are valuable**: We reused `lemma_shr_le_u64` successfully
4. **Compute mode is powerful**: Works great for concrete arithmetic on constants
5. **Clear structure matters**: Breaking into 4 steps makes the proof comprehensible

## Answering the Original Question

**"What are some missing properties of `as_nat_32_u8` which would be needed for the proof of `to_bytes`?"**

**Answer:** The key property needed is `lemma_limbs_to_bytes`, which states:

```rust
Given:
  - limbs: [u64; 5] where each limb < 2^51
  - bytes: [u8; 32] packed according to the to_bytes algorithm
    (with specific equations for each byte, including overlapping bytes)
    
Prove:
  as_nat_32_u8(bytes) == as_nat(limbs)
```

This requires:
- Understanding how 51-bit limbs decompose into 8-bit bytes
- Handling overlapping bytes (e.g., `bytes[6] = (limbs[0] >> 48) | (limbs[1] << 3)`)
- Proving the bit-packing preserves the mathematical value

We've now **identified, structured, and documented** all these properties!

