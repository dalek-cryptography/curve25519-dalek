//! Small Aeneas - Standalone functions extracted from curve25519-dalek
//!
//! This crate contains the `m` function from scalar arithmetic and the `reduce` function 
//! from field arithmetic, along with their Verus specifications converted to documentation.

/// u64 * u64 = u128 multiply helper
/// 
/// # Verus Specification (converted from original Verus code):
/// 
/// ## Requires:
/// - `x < (1u64 << 52)`
/// - `y < (1u64 << 52)`
/// 
/// ## Ensures:
/// - `result < (1u128 << 104)`
/// - `result == x * y`
/// 
/// ## Proof outline:
/// The original Verus proof showed:
/// 1. `(x as u128) < (1u128 << 52)`
/// 2. `(y as u128) < (1u128 << 52)`  
/// 3. `(x as u128) * (y as u128) < (1u128 << 52) * (1u128 << 52)`
/// 4. `(1u128 << 52) * (1u128 << 52) == (1u128 << 104)`
/// 
/// This ensures no overflow when multiplying two 52-bit values.
#[inline(always)]
pub fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

/// Field element structure with 5 limbs of 51 bits each
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

/// Low 51-bit mask constant: 2^51 - 1
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64; // 2^51 - 1

impl FieldElement51 {
    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    /// 
    /// # Verus Specification (converted from original Verus code):
    /// 
    /// ## Ensures:
    /// - `forall i in 0..5: result.limbs[i] < (1u64 << 52)`
    /// - If all input limbs are < 2^51, then `result.limbs == limbs` (identity)
    /// - `as_nat(result.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51)`
    /// 
    /// ## Mathematical interpretation:
    /// - Input limbs `l = (l0, l1, l2, l3, l4)` represent: `e(l) = l0 + l1*2^51 + l2*2^102 + l3*2^153 + l4*2^204`
    /// - In field Z_p where `p = 2^255 - 19`  
    /// - Returns `v = (v0, v1, v2, v3, v4)` where:
    ///   - `v0 = 19 * a4 + b0`
    ///   - `v1 = a0 + b1` 
    ///   - `v2 = a1 + b2`
    ///   - `v3 = a2 + b3`
    ///   - `v4 = a3 + b4`
    /// - Where `ai = li >> 51` (equivalent to `li / 2^51`) and `bi = li & LOW_51_BIT_MASK` (equivalent to `li % 2^51`)
    /// 
    /// ## Key property:
    /// `e(reduce(l)) = e(l) (mod p)` - the reduction preserves the field element value modulo p
    /// 
    /// ## Proof outline:
    /// The original Verus proof established:
    /// 1. All carries are properly bounded (< 2^13 for most, < 2^18 for the first)
    /// 2. Final limbs are bounded by 2^52 after the weak reduction
    /// 3. The mathematical identity connecting input and output via modular arithmetic
    /// 4. For inputs already < 2^51 per limb, the function acts as identity
    #[inline(always)]
    pub fn reduce(mut limbs: [u64; 5]) -> FieldElement51 {
        // Since the input limbs are bounded by 2^64, the biggest
        // carry-out is bounded by 2^13.
        //
        // The biggest carry-in is c4 * 19, resulting in
        //
        // 2^51 + 19*2^13 < 2^51.0000000001
        //
        // Because we don't need to canonicalize, only to reduce the
        // limb sizes, it's OK to do a "weak reduction", where we
        // compute the carry-outs in parallel.

        let c0 = limbs[0] >> 51;
        let c1 = limbs[1] >> 51;
        let c2 = limbs[2] >> 51;
        let c3 = limbs[3] >> 51;
        let c4 = limbs[4] >> 51;

        limbs[0] &= LOW_51_BIT_MASK;
        limbs[1] &= LOW_51_BIT_MASK;
        limbs[2] &= LOW_51_BIT_MASK;
        limbs[3] &= LOW_51_BIT_MASK;
        limbs[4] &= LOW_51_BIT_MASK;

        limbs[0] += c4 * 19;
        limbs[1] += c0;
        limbs[2] += c1;
        limbs[3] += c2;
        limbs[4] += c3;

        FieldElement51 { limbs }
    }
}