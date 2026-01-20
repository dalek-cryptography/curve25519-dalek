#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::mul_lemmas::*;
use super::pow_lemmas::*;

verus! {

// Specialization of lemma_uN_shl_is_mul for x = 1
macro_rules! lemma_shift_is_pow2 {
    ($name:ident, $le_max:ident, $shl_is_mul:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(k: nat)
            requires
                k < <$uN>::BITS,
            ensures
                (1 as $uN << k) == pow2(k),
        {
            assert(1 as $uN * pow2(k) == pow2(k)) by {
                lemma_mul_basics_4(pow2(k) as int);
            }
            assert(pow2(k) <= <$uN>::MAX) by {
                $le_max(k);
            }
            $shl_is_mul(1 as $uN, k as $uN);
        }
    }
    };
}

lemma_shift_is_pow2!(lemma_u8_shift_is_pow2, lemma_u8_pow2_le_max, lemma_u8_shl_is_mul, u8);

lemma_shift_is_pow2!(lemma_u16_shift_is_pow2, lemma_u16_pow2_le_max, lemma_u16_shl_is_mul, u16);

lemma_shift_is_pow2!(lemma_u32_shift_is_pow2, lemma_u32_pow2_le_max, lemma_u32_shl_is_mul, u32);

lemma_shift_is_pow2!(lemma_u64_shift_is_pow2, lemma_u64_pow2_le_max, lemma_u64_shl_is_mul, u64);

// =============================================================================
// u128 left-shift is multiplication (NOT IN VSTD YET)
// =============================================================================
pub broadcast proof fn lemma_u128_shl_is_mul(x: u128, shift: u128)
    requires
        0 <= shift < 128,
        x * pow2(shift as nat) <= u128::MAX,
    ensures
        #[trigger] (x << shift) == x * pow2(shift as nat),
{
    assume(false);  // TODO: prove properly when vstd adds this
}

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_shift_is_pow2!(lemma_u128_shift_is_pow2, lemma_u128_pow2_le_max, lemma_u128_shl_is_mul, u128);

// Proofs that left-shift by 0 is a no-op
macro_rules! lemma_shl_zero_is_id {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub broadcast proof fn $name(v: $uN)
            by (bit_vector)
            ensures
                #![trigger v << 0]
                v << 0 == v,
        {}
    }
    };
}

lemma_shl_zero_is_id!(lemma_u8_shl_zero_is_id, u8);

lemma_shl_zero_is_id!(lemma_u16_shl_zero_is_id, u16);

lemma_shl_zero_is_id!(lemma_u32_shl_zero_is_id, u32);

lemma_shl_zero_is_id!(lemma_u64_shl_zero_is_id, u64);

lemma_shl_zero_is_id!(lemma_u128_shl_zero_is_id, u128);

// Proofs that v << (a + b) == (v << a) << b
macro_rules! lemma_shl_by_sum {
    ($name:ident, $shl_is_mul:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub broadcast proof fn $name(v: $uN, a: nat, b: nat)
            requires
                (a + b) < <$uN>::BITS,
                v * pow2(a + b) <= <$uN>::MAX,
            ensures
                #[trigger] (v << (a + b)) == ((v << a) << b),
        {
            assert(pow2(a + b) == pow2(a) * pow2(b)) by {
                lemma_pow2_adds(a, b);
            }
            assert(pow2(a) <= pow2(a + b)) by {
                if (b > 0) {
                    lemma_pow2_strictly_increases(a, a + b);
                }
            }
            assert(v * pow2(a) <= v * pow2(a + b) <= <$uN>::MAX) by {
                assert(pow2(a) * v <= pow2(a + b) * v) by {
                    lemma_mul_inequality(pow2(a) as int, pow2(a + b) as int, v as int);
                }
                lemma_mul_is_commutative(v as int, pow2(a) as int);
                lemma_mul_is_commutative(v as int, pow2(a + b) as int);
            }
            assert( v << (a + b) == v * pow2(a + b)) by {
                $shl_is_mul(v, (a + b) as $uN);
            }
            assert( v << a == v * pow2(a)) by {
                $shl_is_mul(v, a as $uN);
            }
            assert((v * pow2(a)) * pow2(b) == v * (pow2(a) * pow2(b))) by {
                lemma_mul_is_associative(v as int, pow2(a) as int, pow2(b) as int);
            }
            assert( (v * pow2(a)) as $uN << b == (v * pow2(a)) * pow2(b)) by {
                $shl_is_mul((v * pow2(a)) as $uN, b as $uN);
            }
        }
    }
    };
}

lemma_shl_by_sum!(lemma_u8_shl_by_sum, lemma_u8_shl_is_mul, u8);

lemma_shl_by_sum!(lemma_u16_shl_by_sum, lemma_u16_shl_is_mul, u16);

lemma_shl_by_sum!(lemma_u32_shl_by_sum, lemma_u32_shl_is_mul, u32);

lemma_shl_by_sum!(lemma_u64_shl_by_sum, lemma_u64_shl_is_mul, u64);

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_shl_by_sum!(lemma_u128_shl_by_sum, lemma_u128_shl_is_mul, u128);

// Proofs that [<<] preserves [<=]
macro_rules! lemma_shl_le {
    ($name:ident, $shl_is_mul:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: $uN, b: $uN, k: nat)
            requires
                a <= b,
                k < <$uN>::BITS,
                (b * pow2(k)) <= <$uN>::MAX,
            ensures
                (a << k) <= (b << k),
        {
            assert(a * pow2(k) <= b * pow2(k)) by {
                lemma_mul_inequality(a as int, b as int, pow2(k) as int);
            }
            $shl_is_mul(a, k as $uN);
            $shl_is_mul(b, k as $uN);
        }
    }
    };
}

lemma_shl_le!(lemma_u8_shl_le, lemma_u8_shl_is_mul, u8);

lemma_shl_le!(lemma_u16_shl_le, lemma_u16_shl_is_mul, u16);

lemma_shl_le!(lemma_u32_shl_le, lemma_u32_shl_is_mul, u32);

lemma_shl_le!(lemma_u64_shl_le, lemma_u64_shl_is_mul, u64);

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_shl_le!(lemma_u128_shl_le, lemma_u128_shl_is_mul, u128);

// Proofs that if a <= b then v << a <= v << b (up to overflow)
macro_rules! lemma_shl_nondecreasing {
    ($name:ident, $shl_by_sum:ident, $shl_is_mul:ident, $shl_le:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(v: $uN, a: nat, b: nat)
            requires
                a <= b < <$uN>::BITS,
                v * pow2(b) <=<$uN>::MAX,
            ensures
                (v << a) <= (v << b),
        {
            let d = (b - a) as nat;

            assert(v << b == (v << d) << a) by {
                $shl_by_sum(v, d, a);
            }

            assert(v << d == v * pow2(d)) by {
                assert(pow2(d) <= pow2(b)) by {
                    if (d < b){
                        lemma_pow2_strictly_increases(d, b);
                    }
                }
                assert(v * pow2(d) <= v * pow2(b) <= <$uN>::MAX) by {
                    assert(pow2(d) * v <= pow2(b) * v) by {
                        lemma_mul_inequality(pow2(d) as int, pow2(b) as int, v as int);
                    }
                    lemma_mul_is_commutative(v as int, pow2(d) as int);
                    lemma_mul_is_commutative(v as int, pow2(b) as int);
                }

                $shl_is_mul(v, d as $uN);
            }

            assert(v <= v * pow2(d)) by {
                assert(v == 1 * v) by {
                    lemma_mul_basics_4(v as int);
                }
                assert(pow2(d) >= 1) by {
                    lemma_pow2_pos(d);
                }
                assert(v * pow2(d) == pow2(d) * v) by {
                    lemma_mul_is_commutative(v as int, pow2(d) as int);
                }
                lemma_mul_inequality(1, pow2(d) as int, v as int);
            }

            assert(pow2(b) == pow2(d) * pow2(a)) by {
                lemma_pow2_adds(d, a);
            }

            assert((v << (d as $uN)) * pow2(a) <= <$uN>::MAX) by {
                lemma_mul_is_associative(v as int, pow2(d) as int, pow2(a) as int);
            }

            // [v <= v << d] => [(v << a) <= (v << d) << a]
            $shl_le(v, v << (d as $uN), a);
        }
    }
    };
}

lemma_shl_nondecreasing!(lemma_u8_shl_nondecreasing, lemma_u8_shl_by_sum, lemma_u8_shl_is_mul, lemma_u8_shl_le, u8);

lemma_shl_nondecreasing!(lemma_u16_shl_nondecreasing, lemma_u16_shl_by_sum, lemma_u16_shl_is_mul, lemma_u16_shl_le, u16);

lemma_shl_nondecreasing!(lemma_u32_shl_nondecreasing, lemma_u32_shl_by_sum, lemma_u32_shl_is_mul, lemma_u32_shl_le, u32);

lemma_shl_nondecreasing!(lemma_u64_shl_nondecreasing, lemma_u64_shl_by_sum, lemma_u64_shl_is_mul, lemma_u64_shl_le, u64);

// TODO: missing lemma_u128_shl_is_mul from vstd
// lemma_shl_nondecreasing!(lemma_u128_shl_nondecreasing, lemma_u128_shl_by_sum, lemma_u128_shl_is_mul, lemma_u128_shl_le, u128);
// Proofs that right-shift by 0 is a no-op
macro_rules! lemma_shr_zero_is_id {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub broadcast proof fn $name(v: $uN)
            by (bit_vector)
            ensures
                #![trigger v >> 0]
                v >> 0 == v,
        {}
    }
    };
}

lemma_shr_zero_is_id!(lemma_u8_shr_zero_is_id, u8);

lemma_shr_zero_is_id!(lemma_u16_shr_zero_is_id, u16);

lemma_shr_zero_is_id!(lemma_u32_shr_zero_is_id, u32);

lemma_shr_zero_is_id!(lemma_u64_shr_zero_is_id, u64);

lemma_shr_zero_is_id!(lemma_u128_shr_zero_is_id, u128);

// Proofs that v >> (a + b) == (v >> a) >> b
macro_rules! lemma_shr_by_sum {
    ($name:ident, $pow2_le_max:ident, $shr_is_div:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub broadcast proof fn $name(v: $uN, a: nat, b: nat)
            requires
                (a + b) < <$uN>::BITS, // todo: generalize to a + b <= MAX
            ensures
                #[trigger] (v >> (a + b)) == ((v >> a) >> b),
        {
            assert(pow2(a) == pow2(a) as $uN) by {
                $pow2_le_max(a);
            }
            assert(pow2(b) == pow2(b) as $uN) by {
                $pow2_le_max(b);
            }

            // 2^k > 0
            lemma_pow2_pos(a);
            lemma_pow2_pos(b);

            assert(pow2(a + b) == pow2(a) * pow2(b)) by {
                lemma_pow2_adds(a, b);
            }
            assert(v >> (a + b) == v as nat/ pow2(a + b)) by {
                $shr_is_div(v, (a + b) as $uN);
            }
            assert(v >> a == v as nat/ pow2(a)) by {
                $shr_is_div(v, a as $uN);
            }

            assert((v as nat/ pow2(a)) as $uN >> b == (v as nat/ pow2(a)) / pow2(b)) by {
                $shr_is_div(v / (pow2(a) as $uN), b as $uN);
            }

            assert( (v as nat/ pow2(a)) / pow2(b) == v as nat / pow2(a + b)) by {
                lemma_div_denominator(v as int, pow2(a) as int, pow2(b) as int);
            }
        }
    }
    };
}

lemma_shr_by_sum!(lemma_u8_shr_by_sum, lemma_u8_pow2_le_max, lemma_u8_shr_is_div, u8);

lemma_shr_by_sum!(lemma_u16_shr_by_sum, lemma_u16_pow2_le_max, lemma_u16_shr_is_div, u16);

lemma_shr_by_sum!(lemma_u32_shr_by_sum, lemma_u32_pow2_le_max, lemma_u32_shr_is_div, u32);

lemma_shr_by_sum!(lemma_u64_shr_by_sum, lemma_u64_pow2_le_max, lemma_u64_shr_is_div, u64);

lemma_shr_by_sum!(lemma_u128_shr_by_sum, lemma_u128_pow2_le_max, lemma_u128_shr_is_div, u128);

// Proofs that [>>] preserves [<=]
macro_rules! lemma_shr_le {
    ($name:ident, $shr_is_div:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: $uN, b: $uN, k: nat)
            requires
                a <= b,
                k <= <$uN>::MAX,
            ensures
                (a >> k) <= (b >> k),
        {
            if (k >= <$uN>::BITS) {
                let k_uN = k as $uN;
                assert(a >> k_uN == 0) by (bit_vector) requires k_uN >= <$uN>::BITS;
                assert(b >> k_uN == 0) by (bit_vector) requires k_uN >= <$uN>::BITS;
            }
            else {
                assert(pow2(k) > 0) by {
                    lemma_pow2_pos(k);
                }
                assert(a >> k == a as nat / pow2(k)) by {
                    $shr_is_div(a, k as $uN);
                }
                assert(b >> k == b as nat / pow2(k)) by {
                    $shr_is_div(b, k as $uN);
                }
                lemma_div_is_ordered(a as int, b as int, pow2(k) as int);
            }
        }
    }
    };
}

lemma_shr_le!(lemma_u8_shr_le, lemma_u8_shr_is_div, u8);

lemma_shr_le!(lemma_u16_shr_le, lemma_u16_shr_is_div, u16);

lemma_shr_le!(lemma_u32_shr_le, lemma_u32_shr_is_div, u32);

lemma_shr_le!(lemma_u64_shr_le, lemma_u64_shr_is_div, u64);

lemma_shr_le!(lemma_u128_shr_le, lemma_u128_shr_is_div, u128);

// Proofs that if a <= b then v >> a >= v >> b
macro_rules! lemma_shr_nonincreasing {
    ($name:ident, $shr_by_sum:ident, $shr_le:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(v: $uN, a: nat, b: nat)
            requires
                a <= b <= <$uN>::MAX,
            ensures
                v >> b <= v >> a,
        {
            if (b >= <$uN>::BITS) {
                let b_uN = b as $uN;
                assert(v >> b_uN == 0) by (bit_vector) requires b_uN >= <$uN>::BITS;
            } else {
                let d = (b - a) as $uN;
                assert(v >> b == (v >> d) >> a) by {
                    $shr_by_sum(v, d as nat, a);
                }
                assert(v >> d <= v) by (bit_vector);
                assert( (v >> d) >> a <= v >> a) by {
                    $shr_le(v >> d, v, a);
                }
            }
        }
    }
    };
}

lemma_shr_nonincreasing!(lemma_u8_shr_nonincreasing, lemma_u8_shr_by_sum, lemma_u8_shr_le, u8);

lemma_shr_nonincreasing!(lemma_u16_shr_nonincreasing, lemma_u16_shr_by_sum, lemma_u16_shr_le, u16);

lemma_shr_nonincreasing!(lemma_u32_shr_nonincreasing, lemma_u32_shr_by_sum, lemma_u32_shr_le, u32);

lemma_shr_nonincreasing!(lemma_u64_shr_nonincreasing, lemma_u64_shr_by_sum, lemma_u64_shr_le, u64);

lemma_shr_nonincreasing!(lemma_u128_shr_nonincreasing, lemma_u128_shr_by_sum, lemma_u128_shr_le, u128);

// uN::MAX = 2^N - 1
// uN::MAX >> k = 2^(N - k) - 1
// 1 << (N - k) = 2^(N - k)
macro_rules! lemma_max_shifting {
    ($name:ident,
        $shr_by_sum:ident,
        $pow2_le_max:ident,
        $shl_by_sum:ident,
        $shr_is_div:ident,
        $shift_is_pow2:ident,
        $shl_is_mul:ident,
        $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(k: nat)
            requires
                1 <= k < <$uN>::BITS,
            ensures
                <$uN>::MAX >> k < (1 as $uN) << (<$uN>::BITS - k) as $uN,
            decreases <$uN>::BITS - k
        {
            let M = <$uN>::MAX;
            let N = <$uN>::BITS;
            let N_min1 = (N - 1) as nat;
            let one = 1 as $uN;

            // recursion base case
            if (k == N_min1) {
                assert(<$uN>::MAX >> (<$uN>::BITS - 1) < (1 as $uN) << 1) by (compute);
            } else {
                // recursion case
                assert(M >> (k + 1) < one << (N_min1 - k) as $uN) by {
                    $name(k + 1);
                }

                assert(M >> (k + 1) == (M >> k) >> 1) by {
                    $shr_by_sum(M, k, 1);
                }

                lemma_pow2_strictly_increases((N_min1 - k) as nat, (N - k) as nat);

                assert(one * pow2((N - k) as nat) <= one * pow2(N_min1)) by {
                    if (k == 1) {
                        // N - k = N - 1
                        // tautology
                    } else {
                        // N - k < N - 1
                        lemma_pow2_strictly_increases((N - k) as nat, N_min1);
                    }
                    lemma_mul_le(1, 1, pow2((N - k) as nat), pow2(N_min1));
                }

                assert(one * pow2(N_min1) <= M) by {
                    assert(one * pow2(N_min1) == pow2(N_min1)) by {
                        lemma_mul_basics_4(pow2(N_min1) as int);
                    }
                    assert(pow2(N_min1) <= M) by {
                        $pow2_le_max(N_min1);
                    }
                }

                assert( one << (N - k) as nat == (one << (N_min1 - k) as nat) << 1) by {
                    $shl_by_sum(1, (N_min1 - k) as nat, 1);
                }

                assert((M >> k) >> 1 == (M >> k) as nat / pow2(1)) by {
                    $shr_is_div(M >> k, 1);
                }

                // shl_is_mul(x, n) precondition: x * pow2(n) <= M
                assert((one << ((N_min1 - k) as nat)) * pow2(1) <= M) by {
                    $shift_is_pow2((N_min1 - k) as nat);
                    lemma_pow2_adds((N_min1 - k) as nat, 1);
                }

                assert((one << (N_min1 - k) as nat) << 1 == (one << (N_min1 - k) as nat) * pow2(1)) by {
                    $shl_is_mul(one << ((N_min1 - k) as nat), 1);
                }

                lemma2_to64();  // pow2(1) = 2

                assert((one << ((N - k) as $uN)) / 2 == (one << ((N_min1 - k) as $uN))) by {
                    lemma_div_multiples_vanish((one << (N_min1 - k) as $uN) as int, 2);
                }
            }
        }
    }
    };
}

lemma_max_shifting!(lemma_u8_max_shifting,
    lemma_u8_shr_by_sum,
    lemma_u8_pow2_le_max,
    lemma_u8_shl_by_sum,
    lemma_u8_shr_is_div,
    lemma_u8_shift_is_pow2,
    lemma_u8_shl_is_mul,
    u8
);

lemma_max_shifting!(lemma_u16_max_shifting,
    lemma_u16_shr_by_sum,
    lemma_u16_pow2_le_max,
    lemma_u16_shl_by_sum,
    lemma_u16_shr_is_div,
    lemma_u16_shift_is_pow2,
    lemma_u16_shl_is_mul,
    u16
);

lemma_max_shifting!(lemma_u32_max_shifting,
    lemma_u32_shr_by_sum,
    lemma_u32_pow2_le_max,
    lemma_u32_shl_by_sum,
    lemma_u32_shr_is_div,
    lemma_u32_shift_is_pow2,
    lemma_u32_shl_is_mul,
    u32
);

lemma_max_shifting!(lemma_u64_max_shifting,
    lemma_u64_shr_by_sum,
    lemma_u64_pow2_le_max,
    lemma_u64_shl_by_sum,
    lemma_u64_shr_is_div,
    lemma_u64_shift_is_pow2,
    lemma_u64_shl_is_mul,
    u64
);

// TODO: missing lemma_u128_shl_is_mul from vstd
// lemma_max_shifting!(lemma_u128_max_shifting,
//     lemma_u128_shr_by_sum,
//     lemma_u128_pow2_le_max, // MISSING
//     lemma_u128_shl_by_sum, // MISSING
//     lemma_u128_shr_is_div,
//     lemma_u128_shift_is_pow2, // MISSING
//     lemma_u128_shl_is_mul, // MISSING
//     u128
// );
// Corollary of lemma_max_shifting, since for any
// v: uN it holds that v <= uN::MAX and >> preserves [<=]
macro_rules! lemma_shifted_lt {
    ($name:ident, $shl_zero:ident, $shr_le:ident, $max_shifting:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(v: $uN, k: nat)
            requires
                1 <= k <= <$uN>::BITS,
            ensures
                v >> k < (1 as $uN) << (<$uN>::BITS - k),
        {
            if (k == <$uN>::BITS) {
                assert(v >> <$uN>::BITS == 0) by (bit_vector);
                $shl_zero(1 as $uN);
            } else {
                assert(v >> k <= (<$uN>::MAX) >> k) by {
                    $shr_le(v, <$uN>::MAX, k);
                }
                $max_shifting(k);
            }
        }
    }
    };
}

lemma_shifted_lt!(lemma_u8_shifted_lt, lemma_u8_shl_zero_is_id, lemma_u8_shr_le, lemma_u8_max_shifting, u8);

lemma_shifted_lt!(lemma_u16_shifted_lt, lemma_u16_shl_zero_is_id, lemma_u16_shr_le, lemma_u16_max_shifting, u16);

lemma_shifted_lt!(lemma_u32_shifted_lt, lemma_u32_shl_zero_is_id, lemma_u32_shr_le, lemma_u32_max_shifting, u32);

lemma_shifted_lt!(lemma_u64_shifted_lt, lemma_u64_shl_zero_is_id, lemma_u64_shr_le, lemma_u64_max_shifting, u64);

// TODO: missing lemma_u128_shl_is_mul from vstd
// lemma_shifted_lt!(lemma_u128_shifted_lt, lemma_u128_shl_zero_is_id, lemma_u128_shr_le, lemma_u128_max_shifting, u128);
// Proofs that shifting left then right is the same as shifting left once by the difference.
macro_rules! lemma_left_right_shift {
    ($name:ident, $shl_is_mul:ident, $shr_is_div:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(v: $uN, sl: $uN, sr: $uN)
            requires
                sr <= sl < <$uN>::BITS,
                v * pow2(sl as nat) <= <$uN>::MAX,
            ensures
                (v << sl) >> sr == v << (sl - sr),
        {
            let d = (sl - sr) as nat;

            assert(v << sl == v * pow2(sl as nat)) by {
                $shl_is_mul(v, sl);
            }

            assert(pow2(sl as nat) == pow2(d) * pow2(sr as nat)) by {
                lemma_pow2_adds(d, sr as nat);
            }

            let w = (v * pow2(sl as nat)) as nat;

            assert(w as $uN >> sr == w / pow2(sr as nat)) by {
                $shr_is_div(w as $uN, sr);
            }

            assert(w == pow2(sr as nat) * (v * pow2(d))) by {
                lemma_mul_is_associative(v as int, pow2(d) as int, pow2(sr as nat) as int);
            }

            assert(pow2(sr as nat) > 0) by {
                lemma_pow2_pos(sr as nat);
            }

            assert(w / pow2(sr as nat) == v * pow2(d)) by {
                lemma_div_multiples_vanish((v * pow2(d)) as int, pow2(sr as nat) as int);
            }

            assert(v * pow2(d) == v << (d as $uN)) by {
                $shl_is_mul(v, d as $uN);
            }
        }
    }
    };
}

lemma_left_right_shift!(lemma_u8_left_right_shift, lemma_u8_shl_is_mul, lemma_u8_shr_is_div, u8);

lemma_left_right_shift!(lemma_u16_left_right_shift, lemma_u16_shl_is_mul, lemma_u16_shr_is_div, u16);

lemma_left_right_shift!(lemma_u32_left_right_shift, lemma_u32_shl_is_mul, lemma_u32_shr_is_div, u32);

lemma_left_right_shift!(lemma_u64_left_right_shift, lemma_u64_shl_is_mul, lemma_u64_shr_is_div, u64);

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_left_right_shift!(lemma_u128_left_right_shift, lemma_u128_shl_is_mul, lemma_u128_shr_is_div, u128);

// =============================================================================
// Right-Left Shift Lemmas (general form)
// =============================================================================
// For any x, (x >> n) << n == x - (x % pow2(n))
// Equivalently: (x >> n) << n == x - (x & low_bits_mask(n))
// This shows that right-shift followed by left-shift zeros out the low n bits.
macro_rules! lemma_right_left_shift {
    ($name:ident, $shl_is_mul:ident, $shr_is_div:ident, $pow2_le_max:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        /// Right-shift then left-shift by n zeros out the low n bits.
        /// Mathematical reasoning:
        /// - x >> n == x / 2^n (integer division, drops low n bits)
        /// - (x / 2^n) << n == (x / 2^n) * 2^n
        /// - By division/mod identity: x == (x / 2^n) * 2^n + (x % 2^n)
        /// - Therefore: (x / 2^n) * 2^n == x - (x % 2^n)
        pub proof fn $name(x: $uN, n: $uN)
            requires
                n < <$uN>::BITS,
            ensures
                (x >> n) << n == x - ((x as nat) % pow2(n as nat)) as $uN,
        {
            let n_nat = n as nat;
            let q = (x as nat) / pow2(n_nat);
            let r = (x as nat) % pow2(n_nat);

            // pow2(n) > 0 and pow2(n) <= MAX
            assert(pow2(n_nat) > 0) by { lemma_pow2_pos(n_nat); }
            assert(pow2(n_nat) <= <$uN>::MAX) by { $pow2_le_max(n_nat); }

            assert((x >> n) << n == x - r) by {
                // x >> n == x / 2^n == q
                assert(x >> n == q) by { $shr_is_div(x, n); }

                // By fundamental division/mod identity: x == q * 2^n + r
                assert(x == q * pow2(n_nat) + r) by {
                    lemma_fundamental_div_mod(x as int, pow2(n_nat) as int);
                    // r = x % pow2(n) < pow2(n) <= MAX, so r fits in $uN
                    assert(r < pow2(n_nat)) by {
                        vstd::arithmetic::div_mod::lemma_mod_bound(x as int, pow2(n_nat) as int);
                    }
                }

                // q * 2^n <= x <= MAX, so q * 2^n fits in $uN
                // (follows from x == q * 2^n + r and r >= 0)

                // (x >> n) << n == q << n == q * 2^n
                assert((x >> n) << n == q * pow2(n_nat)) by {
                    $shl_is_mul(q as $uN, n);
                }

                // q * 2^n == x - r (rearranging x == q * 2^n + r)
            }
        }
    }
    };
}

lemma_right_left_shift!(lemma_u8_right_left_shift, lemma_u8_shl_is_mul, lemma_u8_shr_is_div, lemma_u8_pow2_le_max, u8);

lemma_right_left_shift!(lemma_u16_right_left_shift, lemma_u16_shl_is_mul, lemma_u16_shr_is_div, lemma_u16_pow2_le_max, u16);

lemma_right_left_shift!(lemma_u32_right_left_shift, lemma_u32_shl_is_mul, lemma_u32_shr_is_div, lemma_u32_pow2_le_max, u32);

lemma_right_left_shift!(lemma_u64_right_left_shift, lemma_u64_shl_is_mul, lemma_u64_shr_is_div, lemma_u64_pow2_le_max, u64);

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_right_left_shift!(lemma_u128_right_left_shift, lemma_u128_shl_is_mul, lemma_u128_shr_is_div, lemma_u128_pow2_le_max, u128);

// =============================================================================
// Right-Left Shift Divisible Lemmas (corollary of the general form)
// =============================================================================
// If x is divisible by 2^n, then (x >> n) << n == x
// This is a corollary of the general lemma: when x % 2^n == 0, we get x - 0 == x
macro_rules! lemma_right_left_shift_divisible {
    ($name:ident, $general_lemma:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        /// If x is divisible by 2^n, then right-shift then left-shift gives back x.
        ///
        /// This is a corollary of the general lemma: (x >> n) << n == x - (x % 2^n).
        /// When x % 2^n == 0, this simplifies to x - 0 == x.
        pub proof fn $name(x: $uN, n: $uN)
            requires
                n < <$uN>::BITS,
                (x as nat) % pow2(n as nat) == 0,
            ensures
                (x >> n) << n == x,
        {
            // Use the general lemma
            $general_lemma(x, n);
            // (x >> n) << n == x - (x % 2^n) == x - 0 == x
        }
    }
    };
}

lemma_right_left_shift_divisible!(lemma_u8_right_left_shift_divisible, lemma_u8_right_left_shift, u8);

lemma_right_left_shift_divisible!(lemma_u16_right_left_shift_divisible, lemma_u16_right_left_shift, u16);

lemma_right_left_shift_divisible!(lemma_u32_right_left_shift_divisible, lemma_u32_right_left_shift, u32);

lemma_right_left_shift_divisible!(lemma_u64_right_left_shift_divisible, lemma_u64_right_left_shift, u64);

// NOTE: depends on lemma_u128_shl_is_mul which uses assume(false)
lemma_right_left_shift_divisible!(lemma_u128_right_left_shift_divisible, lemma_u128_right_left_shift, u128);

} // verus!
