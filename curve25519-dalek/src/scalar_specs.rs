//! Specification functions for high-level Scalar operations

use crate::backend::serial::u64::scalar_specs::*;
use crate::scalar::Scalar;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Convert a boolean array (bits in little-endian order) to a natural number
pub open spec fn bits_to_nat(bits: &[bool; 256]) -> nat {
    bits_to_nat_rec(bits, 0)
}

pub open spec fn bits_to_nat_rec(bits: &[bool; 256], index: int) -> nat
decreases 256 - index
{
    if index >= 256 {
        0
    } else {
        let bit_value = if bits[index] { 1nat } else { 0nat };
        bit_value * pow2(index as nat) + bits_to_nat_rec(bits, index + 1)
    }
}

/// Returns true iff a and b are multiplicative inverses modulo group_order
/// i.e., a * b ≡ 1 (mod group_order)
pub open spec fn is_inverse(a: &Scalar, b: &Scalar) -> bool {
    (bytes_to_nat(&a.bytes) * bytes_to_nat(&b.bytes)) % group_order() == 1
}

/// Spec function to compute product of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
pub open spec fn product_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len()
{
    if scalars.len() == 0 {
        1
    } else {
        let last_scalar = scalars[scalars.len() - 1];
        let rest = scalars.subrange(0, scalars.len() - 1);
        (product_of_scalars(rest) * bytes_to_nat(&last_scalar.bytes)) % group_order()
    }
}

/// Returns true iff a scalar's byte representation equals the given natural number (mod group_order)
pub open spec fn scalar_congruent_nat(s: &Scalar, n: nat) -> bool {
    bytes_to_nat(&s.bytes) % group_order() == n % group_order()
}

/// Returns true iff a scalar is the inverse of a natural number (mod group_order)
pub open spec fn is_inverse_of_nat(s: &Scalar, n: nat) -> bool {
    (bytes_to_nat(&s.bytes) * n) % group_order() == 1
}

/// Uninterpreted spec function to model randomness
pub uninterp spec fn is_random_scalar(scalar: &Scalar) -> bool;


} // verus!
