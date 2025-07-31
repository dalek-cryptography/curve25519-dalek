// scalar_verus.rs
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
// use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

// use the shared verus definitions
use super::common_verus::*;

verus! {


// ## Specification for: `clamp_integer(mut bytes: [u8; 32]) -> [u8; 32]`
// 
// Let n denote the 32 byte output interpreted as an integer in little endian format (`as_nat_32_u8`)
//
// 1. 2^254 ≤ n
// 2. n < 2^255
// 3. n is divisible by 8 (the cofactor of curve25519)
// 4. If the input is uniformly random then the output is uniformly random
//
// [Further info](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/)


}
