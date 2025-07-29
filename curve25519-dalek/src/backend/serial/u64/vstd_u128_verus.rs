#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::calc_macro::*;
use vstd::prelude::*;

// vstd does _not_ export this macro, so if we want to use it for u128 we have to ugly-copy it.
macro_rules! lemma_shr_is_div {
    ($name:ident, $uN:ty) => {
        verus! {
        pub broadcast proof fn $name(x: $uN, shift: $uN)
            requires
                0 <= shift < <$uN>::BITS,
            ensures
                #[trigger] (x >> shift) == x as nat / pow2(shift as nat),
            decreases shift,
        {
            reveal(pow2);
            if shift == 0 {
                assert(x >> 0 == x) by (bit_vector);
                reveal(pow);
                assert(pow2(0) == 1) by (compute_only);
            } else {
                assert(x >> shift == (x >> ((sub(shift, 1)) as $uN)) / 2) by (bit_vector)
                    requires
                        0 < shift < <$uN>::BITS,
                ;
                calc!{ (==)
                    (x >> shift) as nat;
                        {}
                    ((x >> ((sub(shift, 1)) as $uN)) / 2) as nat;
                        { $name(x, (shift - 1) as $uN); }
                    (x as nat / pow2((shift - 1) as nat)) / 2;
                        {
                            lemma_pow2_pos((shift - 1) as nat);
                            lemma2_to64();
                            lemma_div_denominator(x as int, pow2((shift - 1) as nat) as int, 2);
                        }
                    x as nat / (pow2((shift - 1) as nat) * pow2(1));
                        {
                            lemma_pow2_adds((shift - 1) as nat, 1);
                        }
                    x as nat / pow2(shift as nat);
                }
            }
        }
        }
    };
}

lemma_shr_is_div!(lemma_u128_shr_is_div, u128);
