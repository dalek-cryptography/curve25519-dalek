#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use vstd::calc_macro::*;

// Placeholder until u128 lemma gets into vstd;
verus! {

macro_rules! lemma_pow2_no_overflow {
    ($name:ident, $uN:ty) => {
        verus! {
        pub broadcast proof fn $name(n: nat)
            requires
                0 <= n < <$uN>::BITS,
            ensures
                0 < #[trigger] pow2(n) < <$uN>::MAX,
        {
            lemma_pow2_pos(n);
            lemma2_to64();
            lemma2_to64_rest();
        }
        }
    };
}

lemma_pow2_no_overflow!(lemma_u128_pow2_no_overflow, u128);

macro_rules! lemma_low_bits_mask_is_mod {
    ($name:ident, $and_split_low_bit:ident, $no_overflow:ident, $uN:ty) => {
        verus! {
        pub broadcast proof fn $name(x: $uN, n: nat)
            requires
                n < <$uN>::BITS,
            ensures
                #[trigger] (x & (low_bits_mask(n) as $uN)) == x % (pow2(n) as $uN),
            decreases n,
        {
            // Bounds.
            $no_overflow(n);
            lemma_pow2_pos(n);

            // Inductive proof.
            if n == 0 {
                assert(low_bits_mask(0) == 0) by (compute_only);
                assert(x & 0 == 0) by (bit_vector);
                assert(pow2(0) == 1) by (compute_only);
                assert(x % 1 == 0);
            } else {
                lemma_pow2_unfold(n);
                assert((x % 2) == ((x % 2) & 1)) by (bit_vector);
                calc!{ (==)
                    x % (pow2(n) as $uN);
                        {}
                    x % ((2 * pow2((n-1) as nat)) as $uN);
                        {
                            lemma_pow2_pos((n-1) as nat);
                            lemma_mod_breakdown(x as int, 2, pow2((n-1) as nat) as int);
                        }
                    add(mul(2, (x / 2) % (pow2((n-1) as nat) as $uN)), x % 2);
                        {
                            $name(x/2, (n-1) as nat);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask((n-1) as nat) as $uN)), x % 2);
                        {
                            lemma_low_bits_mask_div2(n);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask(n) as $uN / 2)), x % 2);
                        {
                            lemma_low_bits_mask_is_odd(n);
                        }
                    add(mul(2, (x / 2) & (low_bits_mask(n) as $uN / 2)), (x % 2) & ((low_bits_mask(n) as $uN) % 2));
                        {
                            $and_split_low_bit(x as $uN, low_bits_mask(n) as $uN);
                        }
                    x & (low_bits_mask(n) as $uN);
                }
            }
        }

        // Helper lemma breaking a bitwise-and operation into the low bit and the rest.
        proof fn $and_split_low_bit(x: $uN, m: $uN)
            by (bit_vector)
            ensures
                x & m == add(mul(((x / 2) & (m / 2)), 2), (x % 2) & (m % 2)),
        {
        }
        }
    };
}

lemma_low_bits_mask_is_mod!(
    lemma_u128_low_bits_mask_is_mod,
    lemma_u128_and_split_low_bit,
    lemma_u128_pow2_no_overflow,
    u128
);
}
