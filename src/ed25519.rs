// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! A Rust implementation of ed25519 key generation, signing, and verification.

use std::fmt::Debug;

use crypto::digest::Digest;
use crypto::sha2::Sha512;

use rand::Rng;

use curve25519_dalek::curve;
use curve25519_dalek::curve::CompressedPoint;
use curve25519_dalek::curve::ExtendedPoint;
use curve25519_dalek::curve::ProjectivePoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::util::arrays_equal_ct;


/// An ed25519 signature.
#[derive(Copy)]
pub struct Signature(pub [u8; 64]);

impl Clone for Signature {
    fn clone(&self) -> Self { *self }
}

impl Debug for Signature {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Signature: {:?}", &self.0[..])
    }
}

impl Signature {
    /// View this signature as an array of 32 bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; 64] {
        self.0
    }
}

/// An ed25519 private key.
pub struct SecretKey(pub [u8; 64]);

impl Debug for SecretKey {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "SecretKey: {:?}", &self.0[..])
    }
}

impl SecretKey {
    /// View this secret key as an array of 32 bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; 64] {
        self.0
    }

    /// Sign a message with this keypair's secret key.
    pub fn sign(&self, message: &[u8]) -> Signature {
        let mut h: Sha512 = Sha512::new();
        let mut hash: [u8; 64] = [0u8; 64];
        let signature_bytes: Vec<u8>;
        let mut expanded_key_secret: Scalar;
        let mesg_digest: Scalar;
        let hram_digest: Scalar;
        let r: ExtendedPoint;
        let s: Scalar;
        let t: CompressedPoint;

        let secret_key: &[u8; 32] = array_ref!(&self.0,  0, 32);
        let public_key: &[u8; 32] = array_ref!(&self.0, 32, 32);

        h.input(secret_key);
        h.result(&mut hash);

        expanded_key_secret = Scalar(*array_ref!(&hash, 0, 32));
        expanded_key_secret[0]  &= 248;
        expanded_key_secret[31] &=  63;
        expanded_key_secret[31] |=  64;

        h.reset();
        h.input(public_key);
        h.input(&message);
        h.result(&mut hash);

        mesg_digest = Scalar::reduce(&hash);

        r = ExtendedPoint::basepoint_mult(&mesg_digest);

        h.reset();
        h.input(&r.compress().to_bytes()[..]);
        h.input(public_key);
        h.input(&message);
        h.result(&mut hash);

        hram_digest = Scalar::reduce(&hash);

        s = Scalar::multiply_add(&hram_digest, &expanded_key_secret, &mesg_digest);
        t = r.compress();

        signature_bytes = [t.0, s.0].concat();
        Signature(*array_ref!(&signature_bytes, 0, 64))
    }
}

/// An ed25519 public key.
#[derive(Copy, Clone)]
pub struct PublicKey(pub CompressedPoint);

impl Debug for PublicKey {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "PublicKey( CompressedPoint( {:?} ))", self.0)
    }
}

impl PublicKey {
    /// View this public key as an array of 32 bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// Convert this public key to its underlying extended twisted Edwards coordinate.
    #[inline]
    fn decompress(&self) -> Option<ExtendedPoint> {
        self.0.decompress()
    }

    /// Verify a signature on a message with this keypair's public key.
    ///
    /// # Return
    ///
    /// Returns true if the signature was successfully verified, and
    /// false otherwise.
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        let mut h: Sha512 = Sha512::new();
        let mut a: ExtendedPoint;
        let ao:  Option<ExtendedPoint>;
        let r: ProjectivePoint;
        let mut digest: [u8; 64];
        let digest_reduced: Scalar;

        if signature.0[63] & 224 != 0 {
            return false;
        }
        ao = self.decompress();

        if ao.is_some() {
            a = ao.unwrap();
        } else {
            return false;
        }
        a = -(&a);

        digest = [0u8; 64];

        let top_half:    &[u8; 32] = array_ref!(&signature.0, 32, 32);
        let bottom_half: &[u8; 32] = array_ref!(&signature.0,  0, 32);

        h.input(&bottom_half[..]);
        h.input(&self.to_bytes());
        h.input(&message);
        h.result(&mut digest);

        digest_reduced = Scalar::reduce(&digest);
        r = curve::double_scalar_mult_vartime(&digest_reduced, &a, &Scalar(*top_half));

        if arrays_equal_ct(bottom_half, &r.compress().to_bytes()) == 1 {
            return true
        } else {
            return false
        }
    }
}

/// An ed25519 keypair.
#[derive(Debug)]
pub struct Keypair {
    /// The public half of this keypair.
    pub public: PublicKey,
    /// The secret half of this keypair.
    pub secret: SecretKey,
}

impl Keypair {
    /// Generate an ed25519 keypair.
    ///
    /// # Input
    ///
    /// A CSPRING with a `fill_bytes()` method, e.g. the one returned
    /// from `rand::OsRng::new()` (in the `rand` crate).
    // we reassign 0 bytes to the temp variable t to overwrite it
    #[allow(unused_assignments)]
    pub fn generate<T: Rng>(cspring: &mut T) -> Keypair {
        let mut h: Sha512 = Sha512::new();
        let mut hash: [u8; 64] = [0u8; 64];
        let mut t:    [u8; 32] = [0u8; 32];
        let mut sk:   [u8; 64] = [0u8; 64];
        let     pk:   [u8; 32];
        let mut digest: &mut [u8; 32];

        cspring.fill_bytes(&mut t);

        h.input(&t);
        h.result(&mut hash);

        digest = array_mut_ref!(&mut hash, 0, 32);
        digest[0]  &= 248;
        digest[31] &= 127;
        digest[31] |= 64;

        pk = ExtendedPoint::basepoint_mult(&Scalar(*digest)).compress().to_bytes();

        for i in  0..32 {
            sk[i]    = t[i];
            sk[i+32] = pk[i];
            t[i]     = 0;
        }

        Keypair{
            public: PublicKey(CompressedPoint(pk)),
            secret: SecretKey(sk),
        }
    }

    /// Sign a message with this keypair's secret key.
    pub fn sign(&self, message: &[u8]) -> Signature {
        self.secret.sign(message)
    }

    /// Verify a signature on a message with this keypair's public key.
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        self.public.verify(message, signature)
    }
}

#[cfg(test)]
mod test {
    use test::Bencher;
    use curve25519_dalek::curve::ExtendedPoint;
    use rand::OsRng;
    use rand::Rng;
    use super::*;

    /// A fake RNG which simply returns zeroes.
    struct ZeroRng;

    impl ZeroRng {
        fn new() -> ZeroRng {
            ZeroRng
        }
    }

    impl Rng for ZeroRng {
        fn next_u32(&mut self) -> u32 { 0u32 }

        fn fill_bytes(&mut self, bytes: &mut [u8]) {
            for i in 0 .. bytes.len() {
                bytes[i] = 0;
            }
        }
    }

    #[test]
    fn test_unmarshal_marshal() {  // TestUnmarshalMarshal
        let mut cspring: OsRng;
        let mut keypair: Keypair;
        let mut x: Option<ExtendedPoint>;
        let a: ExtendedPoint;
        let public: PublicKey;

        cspring = OsRng::new().unwrap();

        // from_bytes() fails if vx²-u=0 and vx²+u=0
        loop {
            keypair = Keypair::generate(&mut cspring);
            x = keypair.public.decompress();

            if x.is_some() {
                a = x.unwrap();
                break;
            }
        }
        public = PublicKey(a.compress());

        assert!(keypair.public.0 == public.0);
    }

    #[test]
    fn test_sign_verify() {  // TestSignVerify
        let mut cspring: OsRng;
        let keypair: Keypair;
        let good_sig: Signature;
        let bad_sig:  Signature;

        let good: &[u8] = "test message".as_bytes();
        let bad:  &[u8] = "wrong message".as_bytes();

        cspring  = OsRng::new().unwrap();
        keypair  = Keypair::generate(&mut cspring);
        good_sig = keypair.sign(&good);
        bad_sig  = keypair.sign(&bad);

        assert!(keypair.verify(&good, &good_sig) == true,
                "Verification of a valid signature failed!");
        assert!(keypair.verify(&good, &bad_sig)  == false,
                "Verification of a signature on a different message passed!");
        assert!(keypair.verify(&bad,  &good_sig) == false,
                "Verification of a signature on a different message passed!");
    }

    #[bench]
    fn bench_sign(b: &mut Bencher) {
        let mut cspring: OsRng = OsRng::new().unwrap();
        let keypair: Keypair = Keypair::generate(&mut cspring);
        let msg: &[u8] = "test message".as_bytes();

        b.iter(| | keypair.sign(msg));
    }

    #[bench]
    fn bench_verify(b: &mut Bencher) {
        let mut cspring: OsRng = OsRng::new().unwrap();
        let keypair: Keypair = Keypair::generate(&mut cspring);
        let msg: &[u8] = "test message".as_bytes();
        let sig: Signature = keypair.sign(msg);

        b.iter(| | keypair.verify(msg, &sig));
    }

    #[bench]
    fn bench_key_generation(b: &mut Bencher) {
        let mut rng: ZeroRng = ZeroRng::new();

        b.iter(| | Keypair::generate(&mut rng));
    }
}
