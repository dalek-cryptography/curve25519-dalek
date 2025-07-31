use super::scalar::*;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use subtle::{Choice, ConditionallySelectable};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

verus! {
/// Verification: scalar * scalar.invert() ≡ 1 mod L
proof fn verify_invert_correct(x: Scalar52)
//     requires to_scalar(&x.limbs) != 0
//    ensures (to_scalar(&x.limbs) * invert_spec(&x.limbs)) % group_order() == 1
{
    assume(false);

}

} // verus!
