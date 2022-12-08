//! This is used mocking / proxying the below for tests:
//! - random_test() to Scalar::random() depending on feature `rand_core`

use crate::ristretto::RistrettoPoint;
use crate::scalar::Scalar;

use rand_core::{CryptoRng, RngCore};

pub struct MockScalar;
impl MockScalar {
    #[cfg(feature = "rand_core")]
    /// Proxy Scalar::random() for random_test
    pub fn random<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> Scalar {
        Scalar::random(rng)
    }

    #[cfg(not(feature = "rand_core"))]
    /// Mock Scalar::random() for random_test
    pub fn random<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> Scalar {
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Scalar::from_bytes_mod_order_wide(&scalar_bytes)
    }
}

pub struct MockRistrettoPoint;
impl MockRistrettoPoint {
    #[cfg(feature = "rand_core")]
    /// Proxy RistrettoPoint::random() for random_test
    pub fn random<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> RistrettoPoint {
        RistrettoPoint::random(rng)
    }

    #[cfg(not(feature = "rand_core"))]
    /// Mock RistrettoPoint::random() for random_test
    pub fn random<R: RngCore + CryptoRng + ?Sized>(rng: &mut R) -> RistrettoPoint {
        let mut uniform_bytes = [0u8; 64];
        rng.fill_bytes(&mut uniform_bytes);

        RistrettoPoint::from_uniform_bytes(&uniform_bytes)
    }
}
