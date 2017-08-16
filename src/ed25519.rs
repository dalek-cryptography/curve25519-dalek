// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! A Rust implementation of ed25519 EdDSA key generation, signing, and
//! verification.

use core::fmt::Debug;

#[cfg(feature = "std")]
use rand::Rng;

use digest::BlockInput;
use digest::Digest;
use digest::Input;
use digest::FixedOutput;

use generic_array::typenum::U64;

use curve25519_dalek::constants;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::edwards::ExtendedPoint;
use curve25519_dalek::scalar::Scalar;

use subtle::slices_equal;

/// The length of an ed25519 EdDSA `Signature`, in bytes.
pub const SIGNATURE_LENGTH: usize = 64;

/// The length of an ed25519 EdDSA `SecretKey`, in bytes.
pub const SECRET_KEY_LENGTH: usize = 32;

/// The length of an ed25519 EdDSA `PublicKey`, in bytes.
pub const PUBLIC_KEY_LENGTH: usize = 32;

/// An EdDSA signature.
///
/// # Note
///
/// These signatures, unlike the ed25519 signature reference implementation, are
/// "detached"—that is, they do **not** include a copy of the message which has
/// been signed.
#[derive(Copy)]
#[repr(C)]
pub struct Signature(pub [u8; SIGNATURE_LENGTH]);

impl Clone for Signature {
    fn clone(&self) -> Self { *self }
}

impl Debug for Signature {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "Signature([{:?}])", &self.0[..])
    }
}

impl Eq for Signature {}

impl PartialEq for Signature {
    fn eq(&self, other: &Signature) -> bool {
        let mut equal: u8 = 0;

        for i in 0..64 {
            equal |= self.0[i] ^ other.0[i];
        }

        if equal == 0 {
            return true;
        } else {
            return false;
        }
    }
}

impl Signature {
    /// View this `Signature` as a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SIGNATURE_LENGTH] {
        self.0
    }

    /// View this `Signature` as a byte array.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; SIGNATURE_LENGTH] {
        &self.0
    }

    /// Construct a `Signature` from a slice of bytes.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Signature {
        Signature(*array_ref!(bytes, 0, SIGNATURE_LENGTH))
    }
}

/// An EdDSA secret key.
#[repr(C)]
pub struct SecretKey(pub [u8; SECRET_KEY_LENGTH]);

impl Debug for SecretKey {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "SecretKey: {:?}", &self.0[..])
    }
}

impl SecretKey {
    /// Convert this secret key to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_LENGTH] {
        self.0
    }

    /// View this secret key as a byte array.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; SECRET_KEY_LENGTH] {
        &self.0
    }

    /// Construct a `SecretKey` from a slice of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate ed25519_dalek;
    /// # fn main() {
    /// use ed25519_dalek::SecretKey;
    /// use ed25519_dalek::SECRET_KEY_LENGTH;
    ///
    /// let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = [
    ///    157, 097, 177, 157, 239, 253, 090, 096,
    ///    186, 132, 074, 244, 146, 236, 044, 196,
    ///    068, 073, 197, 105, 123, 050, 105, 025,
    ///    112, 059, 172, 003, 028, 174, 127, 096, ];
    ///
    /// let secret_key: SecretKey = SecretKey::from_bytes(&secret_key_bytes[..]);
    /// # }
    /// ```
    ///
    /// # Returns
    ///
    /// An EdDSA `SecretKey`.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> SecretKey {
        SecretKey(*array_ref!(bytes, 0, SECRET_KEY_LENGTH))
    }

    /// Generate a `SecretKey` from a `csprng`.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate rand;
    /// extern crate sha2;
    /// extern crate ed25519_dalek;
    ///
    /// # fn main() {
    ///
    /// use rand::Rng;
    /// use rand::OsRng;
    /// use sha2::Sha512;
    /// use ed25519_dalek::PublicKey;
    /// use ed25519_dalek::SecretKey;
    /// use ed25519_dalek::Signature;
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    ///
    /// # }
    /// ```
    ///
    /// Afterwards, you can generate the corresponding public—provided you also
    /// supply a hash function which implements the `Digest` and `Default`
    /// traits, and which returns 512 bits of output—via:
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # fn main() {
    /// #
    /// # use rand::Rng;
    /// # use rand::OsRng;
    /// # use sha2::Sha512;
    /// # use ed25519_dalek::PublicKey;
    /// # use ed25519_dalek::SecretKey;
    /// # use ed25519_dalek::Signature;
    /// #
    /// # let mut csprng: OsRng = OsRng::new().unwrap();
    /// # let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    ///
    /// let public_key: PublicKey = PublicKey::from_secret::<Sha512>(&secret_key);
    /// # }
    /// ```
    ///
    /// The standard hash function used for most ed25519 libraries is SHA-512,
    /// which is available with `use sha2::Sha512` as in the example above.
    /// Other suitable hash functions include Keccak-512 and Blake2b-512.
    ///
    /// # Input
    ///
    /// A CSPRING with a `fill_bytes()` method, e.g. the one returned
    /// from `rand::OsRng::new()` (in the `rand` crate).
    ///
    #[cfg(feature = "std")]
    pub fn generate(csprng: &mut Rng) -> SecretKey {
        let mut sk: SecretKey = SecretKey([0u8; 32]);

        csprng.fill_bytes(&mut sk.0);

        sk
    }
}

/// An ed25519 public key.
#[derive(Copy, Clone)]
#[repr(C)]
pub struct PublicKey(pub CompressedEdwardsY);

impl Debug for PublicKey {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "PublicKey( CompressedPoint( {:?} ))", self.0)
    }
}

impl PublicKey {
    /// Convert this public key to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; PUBLIC_KEY_LENGTH] {
        self.0.to_bytes()
    }

    /// View this public key as a byte array.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; PUBLIC_KEY_LENGTH] {
        &(self.0).0
    }

    /// Construct a `PublicKey` from a slice of bytes.
    ///
    /// # Warning
    ///
    /// The caller is responsible for ensuring that the bytes passed into this
    /// method actually represent a `curve25519_dalek::curve::CompressedEdwardsY`
    /// and that said compressed point is actually a point on the curve.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate ed25519_dalek;
    /// # fn main() {
    /// use ed25519_dalek::PublicKey;
    /// use ed25519_dalek::PUBLIC_KEY_LENGTH;
    ///
    /// let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = [
    ///    215,  90, 152,   1, 130, 177,  10, 183, 213,  75, 254, 211, 201, 100,   7,  58,
    ///     14, 225, 114, 243, 218, 166,  35,  37, 175,   2,  26, 104, 247,   7,   81, 26];
    ///
    /// let public_key: PublicKey = PublicKey::from_bytes(&public_key_bytes);
    /// # }
    /// ```
    ///
    /// # Returns
    ///
    /// A `PublicKey`.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> PublicKey {
        PublicKey(CompressedEdwardsY(*array_ref!(bytes, 0, 32)))
    }

    /// Convert this public key to its underlying extended twisted Edwards coordinate.
    #[inline]
    fn decompress(&self) -> Option<ExtendedPoint> {
        self.0.decompress()
    }

    /// Derive this public key from its corresponding `SecretKey`.
    #[cfg(feature = "std")]
    #[allow(unused_assignments)]
    pub fn from_secret<D>(secret_key: &SecretKey) -> PublicKey
            where D: Digest<OutputSize = U64> + Default {

        let mut h:           D = D::default();
        let mut hash: [u8; 64] = [0u8; 64];
        let     pk:   [u8; 32];
        let mut digest: &mut [u8; 32];

        h.input(secret_key.as_bytes());
        hash.copy_from_slice(h.fixed_result().as_slice());

        digest = array_mut_ref!(&mut hash, 0, 32);
        digest[0]  &= 248;
        digest[31] &= 127;
        digest[31] |= 64;

        pk = (&Scalar(*digest) * &constants::ED25519_BASEPOINT_TABLE).compress_edwards().to_bytes();

        PublicKey(CompressedEdwardsY(pk))
    }

    /// Verify a signature on a message with this keypair's public key.
    ///
    /// # Return
    ///
    /// Returns true if the signature was successfully verified, and
    /// false otherwise.
    pub fn verify<D>(&self, message: &[u8], signature: &Signature) -> bool
            where D: Digest<OutputSize = U64> + Default {

        use curve25519_dalek::edwards::vartime;

        let mut h: D = D::default();
        let mut a: ExtendedPoint;
        let ao:  Option<ExtendedPoint>;
        let r: ExtendedPoint;
        let digest: [u8; 64];
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

        let top_half:    &[u8; 32] = array_ref!(&signature.0, 32, 32);
        let bottom_half: &[u8; 32] = array_ref!(&signature.0,  0, 32);

        h.input(&bottom_half[..]);
        h.input(&self.to_bytes());
        h.input(&message);

        let digest_bytes = h.fixed_result();
        digest = *array_ref!(digest_bytes, 0, 64);
        digest_reduced = Scalar::reduce(&digest);
        r = vartime::double_scalar_mult_basepoint(&digest_reduced, &a, &Scalar(*top_half));

        if slices_equal(bottom_half, &r.compress_edwards().to_bytes()) == 1 {
            return true
        } else {
            return false
        }
    }
}

/// An ed25519 keypair.
#[derive(Debug)]
#[repr(C)]
pub struct Keypair {
    /// The public half of this keypair.
    pub public: PublicKey,
    /// The secret half of this keypair.
    pub secret: SecretKey,
}

impl Keypair {
    /// Construct a `Keypair` from the bytes of a `PublicKey` and `SecretKey`.
    ///
    /// # Inputs
    ///
    /// * `public`: a `[u8; 32]` representing the compressed Edwards-Y
    ///    coordinate of a point on curve25519.
    /// * `secret`: a `[u8; 32]` representing the corresponding secret key.
    ///
    /// # Warning
    ///
    /// Absolutely no validation is done on the key.  If you give this function
    /// bytes which do not represent a valid point, or which do not represent
    /// corresponding parts of the key, then your `Keypair` will be broken and
    /// it will be your fault.
    ///
    /// # Returns
    ///
    /// A `Keypair`.
    pub fn from_bytes<'a>(public: &'a [u8; 32], secret: &'a [u8; 32]) -> Keypair {
        Keypair{ public: PublicKey::from_bytes(public),
                 secret: SecretKey::from_bytes(secret), }
    }

    /// Generate an ed25519 keypair.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate rand;
    /// extern crate sha2;
    /// extern crate ed25519_dalek;
    ///
    /// # fn main() {
    ///
    /// use rand::Rng;
    /// use rand::OsRng;
    /// use sha2::Sha512;
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    ///
    /// let mut cspring: OsRng = OsRng::new().unwrap();
    /// let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
    ///
    /// # }
    /// ```
    ///
    /// # Input
    ///
    /// A CSPRNG with a `fill_bytes()` method, e.g. the one returned
    /// from `rand::OsRng::new()` (in the `rand` crate).
    ///
    /// The caller must also supply a hash function which implements the
    /// `Digest` and `Default` traits, and which returns 512 bits of output.
    /// The standard hash function used for most ed25519 libraries is SHA-512,
    /// which is available with `use sha2::Sha512` as in the example above.
    /// Other suitable hash functions include Keccak-512 and Blake2b-512.
    #[cfg(feature = "std")]
    pub fn generate<D>(csprng: &mut Rng) -> Keypair
            where D: Digest<OutputSize = U64> + Default {
        let sk: SecretKey = SecretKey::generate(csprng);
        let pk: PublicKey = PublicKey::from_secret::<D>(&sk);

        Keypair{ public: pk, secret: sk }
    }

    /// Sign a message with this keypair's secret key.
    pub fn sign<D>(&self, message: &[u8]) -> Signature
            where D: Digest<OutputSize = U64> + Default {

        let mut h: D = D::default();
        let mut hash: [u8; 64] = [0u8; 64];
        let mut signature_bytes: [u8; 64] = [0u8; SIGNATURE_LENGTH];
        let mut expanded_key_secret: Scalar;
        let mesg_digest: Scalar;
        let hram_digest: Scalar;
        let r: ExtendedPoint;
        let s: Scalar;
        let t: CompressedEdwardsY;

        let secret_key: &[u8; 32] = self.secret.as_bytes();
        let public_key: &[u8; 32] = self.public.as_bytes();

        h.input(secret_key);
        hash.copy_from_slice(h.fixed_result().as_slice());

        expanded_key_secret = Scalar(*array_ref!(&hash, 0, 32));
        expanded_key_secret[0]  &= 248;
        expanded_key_secret[31] &=  63;
        expanded_key_secret[31] |=  64;

        h = D::default();
        h.input(&hash[32..]);
        h.input(&message);
        hash.copy_from_slice(h.fixed_result().as_slice());

        mesg_digest = Scalar::reduce(&hash);

        r = &mesg_digest * &constants::ED25519_BASEPOINT_TABLE;

        h = D::default();
        h.input(&r.compress_edwards().to_bytes()[..]);
        h.input(public_key);
        h.input(&message);
        hash.copy_from_slice(h.fixed_result().as_slice());

        hram_digest = Scalar::reduce(&hash);

        s = Scalar::multiply_add(&hram_digest, &expanded_key_secret, &mesg_digest);
        t = r.compress_edwards();

        signature_bytes[..32].copy_from_slice(&t.0);
        signature_bytes[32..64].copy_from_slice(&s.0);
        Signature(*array_ref!(&signature_bytes, 0, 64))
    }

    /// Verify a signature on a message with this keypair's public key.
    pub fn verify<D>(&self, message: &[u8], signature: &Signature) -> bool
            where D: FixedOutput<OutputSize = U64> + BlockInput + Default + Input {
        self.public.verify::<D>(message, signature)
    }
}

#[cfg(test)]
mod test {
    use std::io::BufReader;
    use std::io::BufRead;
    use std::fs::File;
    use std::string::String;
    use std::vec::Vec;
    use curve25519_dalek::edwards::ExtendedPoint;
    use rand::OsRng;
    use rustc_serialize::hex::FromHex;
    use sha2::Sha512;
    use super::*;

    #[test]
    fn unmarshal_marshal() {  // TestUnmarshalMarshal
        let mut cspring: OsRng;
        let mut keypair: Keypair;
        let mut x: Option<ExtendedPoint>;
        let a: ExtendedPoint;
        let public: PublicKey;

        cspring = OsRng::new().unwrap();

        // from_bytes() fails if vx²-u=0 and vx²+u=0
        loop {
            keypair = Keypair::generate::<Sha512>(&mut cspring);
            x = keypair.public.decompress();

            if x.is_some() {
                a = x.unwrap();
                break;
            }
        }
        public = PublicKey(a.compress_edwards());

        assert!(keypair.public.0 == public.0);
    }

    #[test]
    fn sign_verify() {  // TestSignVerify
        let mut cspring: OsRng;
        let keypair: Keypair;
        let good_sig: Signature;
        let bad_sig:  Signature;

        let good: &[u8] = "test message".as_bytes();
        let bad:  &[u8] = "wrong message".as_bytes();

        cspring  = OsRng::new().unwrap();
        keypair  = Keypair::generate::<Sha512>(&mut cspring);
        good_sig = keypair.sign::<Sha512>(&good);
        bad_sig  = keypair.sign::<Sha512>(&bad);

        assert!(keypair.verify::<Sha512>(&good, &good_sig) == true,
                "Verification of a valid signature failed!");
        assert!(keypair.verify::<Sha512>(&good, &bad_sig)  == false,
                "Verification of a signature on a different message passed!");
        assert!(keypair.verify::<Sha512>(&bad,  &good_sig) == false,
                "Verification of a signature on a different message passed!");
    }

    // TESTVECTORS is taken from sign.input.gz in agl's ed25519 Golang
    // package. It is a selection of test cases from
    // http://ed25519.cr.yp.to/python/sign.input
    #[cfg(test)]
    #[cfg(not(release))]
    #[test]
    fn golden() { // TestGolden
        let mut line: String;
        let mut lineno: usize = 0;

        let f = File::open("TESTVECTORS");
        if f.is_err() {
            println!("This test is only available when the code has been cloned \
                      from the git repository, since the TESTVECTORS file is large \
                      and is therefore not included within the distributed crate.");
            panic!();
        }
        let file = BufReader::new(f.unwrap());

        for l in file.lines() {
            lineno += 1;
            line = l.unwrap();

            let parts: Vec<&str> = line.split(':').collect();
            assert_eq!(parts.len(), 5, "wrong number of fields in line {}", lineno);

            let sec_bytes: &[u8] = &parts[0].from_hex().unwrap();
            let pub_bytes: &[u8] = &parts[1].from_hex().unwrap();
            let message:   &[u8] = &parts[2].from_hex().unwrap();
            let sig_bytes: &[u8] = &parts[3].from_hex().unwrap();

		    // The signatures in the test vectors also include the message
		    // at the end, but we just want R and S.
            let sig1: Signature = Signature::from_bytes(sig_bytes);

            let keypair: Keypair = Keypair::from_bytes(
                array_ref!(*pub_bytes, 0, PUBLIC_KEY_LENGTH),
                array_ref!(*sec_bytes, 0, SECRET_KEY_LENGTH));

            let sig2: Signature = keypair.sign::<Sha512>(&message);

            assert!(sig1 == sig2, "Signature bytes not equal on line {}", lineno);
            assert!(keypair.verify::<Sha512>(&message, &sig2),
                    "Signature verification failed on line {}", lineno);
        }
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use test::Bencher;
    use rand::OsRng;
    use sha2::Sha512;
    use super::*;

    /// A fake RNG which simply returns zeroes.
    struct ZeroRng;

    impl ZeroRng {
        pub fn new() -> ZeroRng {
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

    #[bench]
    fn sign(b: &mut Bencher) {
        let mut cspring: OsRng = OsRng::new().unwrap();
        let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
        let msg: &[u8] = b"";

        b.iter(| | keypair.sign::<Sha512>(msg));
    }

    #[bench]
    fn verify(b: &mut Bencher) {
        let mut cspring: OsRng = OsRng::new().unwrap();
        let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
        let msg: &[u8] = b"";
        let sig: Signature = keypair.sign::<Sha512>(msg);

        b.iter(| | keypair.verify::<Sha512>(msg, &sig));
    }

    #[bench]
    fn key_generation(b: &mut Bencher) {
        let mut rng: ZeroRng = ZeroRng::new();

        b.iter(| | Keypair::generate::<Sha512>(&mut rng));
    }

    #[bench]
    fn underlying_scalar_mult_basepoint(b: &mut Bencher) {
        use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;

        let scalar: Scalar = Scalar([  20, 130, 129, 196, 247, 182, 211, 102,
                                       11, 168, 169, 131, 159,  69, 126,  35,
                                      109, 193, 175,  54, 118, 234, 138,  81,
                                       60, 183,  80, 186,  92, 248, 132,  13, ]);

        b.iter(| | &scalar * &ED25519_BASEPOINT_TABLE);
    }
}
