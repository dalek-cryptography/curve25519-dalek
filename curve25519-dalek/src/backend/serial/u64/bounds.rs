use vstd::prelude::*;
use vstd::calc;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus!{

pub proof fn lemma_52_52(x: u64, y: u64)
requires
    x < (1u64 << 52),
    y < (1u64 << 52),
ensures (x as u128) * (y as u128) < (1u128 << 104)
{
    assert(1u128 << 52 == 1u64 << 52) by (bit_vector);
    calc! {
        (<)
        (x as u128) * (y as u128); (<=) {
            if x > 0 {
                lemma_mul_strict_inequality(y as int, (1u128 << 52) as int, x as int);
                assert( x * y < x * (1u128 << 52)  );
            } else {
                assert((0 as u128) * (y as u128) == 0);
            }
        }
        (x as u128) * (1u128 << 52); (<) {
            lemma_mul_strict_inequality(x as int, (1u128 << 52) as int, (1u128 << 52) as int);
        }
        (1u128 << 52) * (1u128 << 52);
    }
    assert((1u128 << 52) * (1u128 << 52) == (1u128 << 104)) by (compute);
}
} // verus!
