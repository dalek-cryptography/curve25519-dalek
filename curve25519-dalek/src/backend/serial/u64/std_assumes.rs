//! External specifications for selected std/core functions used in verification
use crate::backend::serial::u64::scalar_specs::*;
use crate::Scalar;
use vstd::prelude::*;

#[cfg(feature = "rand_core")]
use rand_core::RngCore;

use digest::Digest;

verus! {

// Build a Seq<u8> from fixed arrays (for specs)
pub open spec fn seq_from2(b: &[u8; 2]) -> Seq<u8> { Seq::new(2, |i: int| b[i]) }
pub open spec fn seq_from4(b: &[u8; 4]) -> Seq<u8> { Seq::new(4, |i: int| b[i]) }
pub open spec fn seq_from8(b: &[u8; 8]) -> Seq<u8> { Seq::new(8, |i: int| b[i]) }
pub open spec fn seq_from16(b: &[u8; 16]) -> Seq<u8> { Seq::new(16, |i: int| b[i]) }

#[verifier::external_body]
pub fn u16_to_le_bytes(x: u16) -> (bytes: [u8; 2])
    ensures
        bytes_seq_to_nat(seq_from2(&bytes)) == x as nat
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u32_to_le_bytes(x: u32) -> (bytes: [u8; 4])
    ensures
        bytes_seq_to_nat(seq_from4(&bytes)) == x as nat
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u64_to_le_bytes(x: u64) -> (bytes: [u8; 8])
    ensures
        bytes_seq_to_nat(seq_from8(&bytes)) == x as nat
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u128_to_le_bytes(x: u128) -> (bytes: [u8; 16])
    ensures
        bytes_seq_to_nat(seq_from16(&bytes)) == x as nat
{
    x.to_le_bytes()
}

// annotations for random values
pub uninterp spec fn is_random(x: u8) -> bool;
pub uninterp spec fn is_random_bytes(bytes: &[u8]) -> bool;
pub uninterp spec fn is_random_scalar(scalar: &Scalar) -> bool;



#[cfg(feature = "rand_core")]
#[verifier::external_body]
pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64])
    ensures is_random_bytes(bytes)
{
        rng.fill_bytes(bytes)
}


#[cfg(feature = "digest")]
#[verifier::external_body]
pub fn sha512_hash_bytes(input: &[u8]) -> (result: [u8; 64])
    ensures
        is_random_bytes(input) ==> is_random_bytes(&result),
{
    use digest::Digest;
    let mut hasher = sha2::Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

} // verus!
