use super::*;

use kolmogorov_smirnov as ks;
use rand::{thread_rng, RngCore};
use rand_distr::{Binomial, Distribution};
use std::vec::Vec;

struct BitCounts {
    counts: [[u64; 100]; 32 * 8],
    entries: usize,
}

impl BitCounts {
    fn new() -> Self {
        BitCounts {
            counts: [[0u64; 100]; 256],
            entries: 0,
        }
    }
    fn entry(&mut self, arr: &[u8; 32]) {
        for (i, arr_byte) in arr.iter().enumerate() {
            for j in 0..8 {
                self.counts[i * 8 + j][self.entries % 100] += ((arr_byte >> j) & 0x01) as u64;
            }
        }
        self.entries += 1;
    }
    fn outliers(&self) -> Vec<usize> {
        let mut rng = thread_rng();
        let binomial_100 = Binomial::new(100, 0.5).expect("failed to build binomial distribution");
        let expected_dist: [u64; 100] = binomial_100
            .sample_iter(&mut rng)
            .take(100)
            .collect::<Vec<u64>>()
            .try_into()
            .expect("failed to build example binomial expected distribution");
        // this is a high confidence, but we want to avoid this test failing
        // due to statistical variability on repeat runs.
        let confidence = 0.95;
        let mut outlier_indices = vec![];

        for (n, bit_trial) in self.counts.iter().enumerate() {
            let result = ks::test(bit_trial, &expected_dist, confidence);
            // require reject_probability == 1.0 to avoid statistical variability on re-runs
            if result.is_rejected && result.reject_probability == 1.0 {
                // samples definitely not from same distribution
                outlier_indices.push(n);
                println!(
                    "{n}, {} {} {} {}",
                    result.statistic,
                    result.reject_probability,
                    result.critical_value,
                    result.confidence
                );
                if n == 255 {
                    println!("{:?}\n{:?}", bit_trial, expected_dist);
                }
            }
        }
        outlier_indices
    }
}

#[test]
/// If we use a "random" value for the tweak the high order bits will be
/// set such that the representative is:
/// 1) unchanged w.r.t. the public key value derived from the representative
///    i.e) it still derives the same public key value from the (clamped)
///         representative that we get from the private key.
/// 2) statistically indistinguishable from uniform random.
/// 4) computationally indistinguishable from random strings for the `a ?= sqrt(a^2)` test.
///
/// (To see this test fail change `rng.next_u32() as u8` to `0u8`)
fn bitwise_entropy() {
    const ITERATIONS: usize = 10000;
    // number of iterations
    let mut i = 0usize;
    let mut rng = thread_rng();
    let mut privkey = [0u8; 32];

    // count of occurences of a 1 per bit in the representative
    let mut bitcounts = BitCounts::new();

    while i < ITERATIONS {
        rng.fill_bytes(&mut privkey);
        let alice_representative =
            match Randomized::to_representative(&privkey, rng.next_u32() as u8).into() {
                None => continue,
                Some(r) => r,
            };

        bitcounts.entry(&alice_representative);

        let pub_from_repr =
            MontgomeryPoint::from_representative::<Randomized>(&alice_representative)
                .expect("failed pub from repres");
        let pub_from_priv = Randomized::mul_base_clamped(privkey).to_montgomery();
        assert_eq!(
            hex::encode(pub_from_priv.as_bytes()),
            hex::encode(pub_from_repr.as_bytes()),
            "failed pubkey match at iteration {i}"
        );

        i += 1;
    }

    let outliers = bitcounts.outliers();
    assert!(outliers.is_empty(), "bad bits: {:?}", outliers);
}

/// TLDR: The sqrt_ratio_i function is canonical so this library does not
/// suffer from the describbed computational distinguisher.
///
/// The specific issue that this is testing for can be described as:
/// ```txt
/// An instantiation of Elligator is parameterized by what might be called
/// a “canonical” square root function, one with the property that
/// `√a2 = √(−a)2` for all field elements `a`. That is, we designate just
/// over half the field elements as “non-negative,” and the image of the
/// square root function consists of exactly those elements. A convenient
/// definition of “non-negative” for Curve25519, suggested by its authors,
/// is the lower half of the field, the elements `{0, 1, …, (q − 1) / 2}`.
/// When there are two options for a square root, take the smaller of the two.
/// ```
///
/// Any Elligator implementation that does not do this canonicalization of
/// the final square root, and instead it maps a given input systematically
/// to either its negative or non-negative root is vulnerable to the
/// following computational distinguisher.
///
/// ```txt
/// [An adversary could] observe a representative, interpret it as a field
/// element, square it, then take the square root using the same
/// non-canonical square root algorithm. With representatives produced by
/// an affected version of [the elligator2 implementation], the output of
/// the square-then-root operation would always match the input. With
/// random strings, the output would match only half the time.
/// ```
///
/// For a more in-depth explanation see:
/// https://github.com/agl/ed25519/issues/27
/// https://www.bamsoftware.com/papers/fep-flaws/
#[test]
fn test_canonical() {
    const ITERATIONS: usize = 10000;
    // number of iterations
    let mut i = 0usize;
    let mut rng = thread_rng();
    let mut privkey = [0u8; 32];

    // number of times the representative (interpreted as a point) squared, then square_rooted,
    // equals the original representative. Should happen w/ 50% probability.
    let mut squares_equal = 0usize;

    while i < ITERATIONS {
        rng.fill_bytes(&mut privkey);
        let alice_representative = match Randomized::to_representative(&privkey, 0u8).into() {
            None => continue,
            Some(r) => r,
        };

        if is_canonical(&alice_representative) {
            squares_equal += 1;
        }
        i += 1;
    }

    let expected_range = 4500..5500; // if truly binomial n=10000, p=0.5 then this should "always" pass (> 10x std dev)
    assert!(
        expected_range.contains(&squares_equal),
        "squares_equal: {squares_equal} is not in [4500:5500]"
    );
}

fn is_canonical(repres: &[u8; 32]) -> bool {
    let r_fe = FieldElement::from_bytes(repres);
    let (ok, r_fe_prime) = FieldElement::sqrt_ratio_i(&r_fe.square(), &FieldElement::ONE);
    (r_fe.ct_eq(&r_fe_prime) & ok).into()
}
