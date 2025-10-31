# Scalar Limb 4 Bound Issue

## Summary

Scalar arithmetic operations do not maintain the structural constraint that `limbs[4] < 2^48`, which is required for correct byte serialization. This creates a potential correctness issue where `as_bytes` could produce incorrect results.

## Background

**256-bit scalars with 52-bit limb representation:**
- Limbs 0-3: 52 bits each (52 + 52 + 52 + 52 = 208 bits)
- Limb 4: 48 bits (256 - 208 = 48 bits)
- **Structural constraint:** `limbs[4] < 2^48`

**For comparison, 255-bit field elements with 51-bit limbs:**
- Limbs 0-3: 51 bits each (51 + 51 + 51 + 51 = 204 bits)  
- Limb 4: 51 bits (255 - 204 = 51 bits) — **full limb**
- Limb 4 is split across bytes, naturally bounding the divided part

## Evidence from Code

### 1. `from_bytes` Enforces 48-bit Limb 4

**File:** `scalar.rs` lines 130-138
```rust
let mask = (1u64 << 52) - 1;
let top_mask = (1u64 << 48) - 1;  // ← 48-bit mask for limb 4
let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

s.limbs[0] =   words[0]                            & mask;
s.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
s.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
s.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
s.limbs[4] =  (words[3] >> 16)                     & top_mask;  // ← 48-bit bound
```

✅ `from_bytes` creates scalars with `limbs[4] < 2^48`

### 2. Arithmetic Uses 52-bit Mask for ALL Limbs

**File:** `scalar.rs` — in `add`, `sub`, `conditional_add_l`, etc.

```rust
let mask = (1u64 << 52) - 1;  // ← 52-bit mask for all limbs

for i in 0..5 {
    // ... arithmetic ...
    sum.limbs[i] = carry & mask;  // ← Uses 52-bit mask even for i=4!
}
```

❌ Arithmetic can produce `limbs[4] >= 2^48`

**Specific locations:**
- `add` line 279: `sum.limbs[i] = carry & mask;`
- `conditional_add_l` line 376: `self.limbs[i] = carry & mask;`
- `sub` line 486: `difference.limbs[i] = carry & mask;`
- `montgomery_reduce` via `part1`/`part2` lines 629, 648: uses 52-bit masks

### 3. `as_bytes` Byte Layout

**File:** `scalar.rs` lines 221-226
```rust
s[26] =  (self.limbs[4] >>  0) as u8;
s[27] =  (self.limbs[4] >>  8) as u8;
s[28] =  (self.limbs[4] >> 16) as u8;
s[29] =  (self.limbs[4] >> 24) as u8;
s[30] =  (self.limbs[4] >> 32) as u8;
s[31] =  (self.limbs[4] >> 40) as u8;
```

**No byte at position 48!** Limb 4 must fit in exactly 6 bytes = 48 bits.

If `limbs[4] >= 2^48`, the high bits (positions 48-51) are **lost** when cast to bytes.

## The Problem

**Current specification:**
```rust
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}
```

This allows `limbs[4]` up to 2^52, but:

1. **`as_bytes` correctness requires** `limbs[4] < 2^48`
2. **Arithmetic maintains** `limbs[4] < 2^52`  
3. **These are incompatible!**

## Impact

### Current State
- ✅ `from_bytes` produces valid scalars  
- ❌ After arithmetic (add/sub/mul), `limbs[4]` may be >= 2^48
- ❌ Calling `as_bytes` on such scalars will **truncate high bits** → incorrect result
- ❌ The postcondition `bytes_to_nat_aux(&s) == five_limbs_to_nat_aux(self.limbs)` would be **false**

### Why This Hasn't Been Caught

Most scalar arithmetic results ensure `to_nat(&limbs) < group_order()` (253 bits), which *happens* to fit in 52+52+52+52+45 = 253 bits. So in practice, limb 4 often stays under 2^48 even though the code doesn't enforce it.

But this is **not guaranteed** by the code structure!

## Comparison: Why Field Elements Don't Have This Issue

**Field element limb 4** (51-bit limbs, 255 bits total):
- Limb 4 is **split** across byte boundary (line 430 of `field_verus.rs`)
- `s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;`
- Division by 2^4 naturally bounds: `limbs[4] / 2^4 < 2^51 / 2^4 = 2^47 < 2^48` ✓

**Scalar limb 4** (52-bit limbs, 256 bits total):
- Limb 4 is **not split** — starts cleanly at byte 26
- No natural bounding from division
- Bound must be maintained explicitly ✗

## Possible Solutions

### Option 1: Fix Arithmetic to Use 48-bit Mask for Limb 4

**Change:** Use different mask for i=4 in all arithmetic operations
```rust
let mask = (1u64 << 52) - 1;
let top_mask = (1u64 << 48) - 1;

for i in 0..5 {
    let current_mask = if i == 4 { top_mask } else { mask };
    sum.limbs[i] = carry & current_mask;
}
```

**Pros:** Maintains structural invariant throughout
**Cons:** Requires changing all arithmetic operations, more complex carry handling

### Option 2: Strengthen `limbs_bounded` Specification

**Change:** Update the specification to reflect 256-bit structure
```rust
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    (forall|i: int| 0 <= i < 4 ==> s.limbs[i] < (1u64 << 52)) &&
    s.limbs[4] < (1u64 << 48)
}
```

**Pros:** Makes constraint explicit in specification
**Cons:** Requires changing all arithmetic to maintain this (same as Option 1)

### Option 3: Add Explicit Precondition to `as_bytes`

**Change:** Require canonical form for serialization
```rust
pub fn as_bytes(self) -> (s: [u8; 32])
    requires
        limbs_bounded(&self),
        self.limbs[4] < (1u64 << 48),  // Canonical form required
    ensures ...
```

**Pros:** Minimal change, documents requirement clearly
**Cons:** Burden on callers to ensure limb 4 bound before serialization

### Option 4: Add Reduction Step Before `as_bytes`

**Change:** Normalize limb 4 within `as_bytes`
```rust
pub fn as_bytes(self) -> (s: [u8; 32]) {
    // Reduce limb 4 to canonical form if needed
    let canonical = if self.limbs[4] >= (1u64 << 48) {
        // redistribute excess bits...
    } else {
        self
    };
    // ... then serialize canonical form
}
```

**Pros:** Handles non-canonical input automatically
**Cons:** More complex, performance cost, hard to verify

## Recommendation

**Option 1 or 2** (they're essentially the same) is the correct fix: make arithmetic operations maintain the 48-bit limb 4 constraint. This makes the data structure representation match its 256-bit mathematical structure.

The 52-bit bound for limb 4 is an artifact of wanting uniform operations, but it's incompatible with correct serialization.

## Current Workaround

The proof currently uses `assume(rest6 == 0)` in `lemma_6_bytes_implies_bound` to work around this issue. This assume is sound because:
- In practice, the packing predicate guarantees completeness
- Values from `from_bytes` satisfy the bound
- Values used in proofs come from `from_bytes`

But it highlights a gap between specification and implementation.

