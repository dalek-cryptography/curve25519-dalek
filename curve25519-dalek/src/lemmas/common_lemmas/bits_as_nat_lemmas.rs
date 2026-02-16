#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::specs::core_specs::*;

verus! {

/// Connect `bits_as_nat_rec` (absolute indexing with powers of two) with
/// `bits_from_index_to_nat` (relative indexing from `start`).
pub proof fn lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits: &[bool; 256], start: nat)
    requires
        start <= 256,
    ensures
        bits_as_nat_rec(bits, start as int) == pow2(start) * bits_from_index_to_nat(
            bits,
            start,
            (256 - start) as nat,
        ),
    decreases 256 - start,
{
    if start == 256 {
        assert(bits_as_nat_rec(bits, 256) == 0);
        assert(bits_from_index_to_nat(bits, 256, 0) == 0);
        assert(pow2(256) * 0nat == 0nat) by { lemma_mul_basics_3(pow2(256) as int) }
    } else {
        let bit_value = if bits[start as int] {
            1nat
        } else {
            0nat
        };
        lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits, (start + 1) as nat);

        assert(bits_as_nat_rec(bits, start as int) == bit_value * pow2(start) + bits_as_nat_rec(
            bits,
            (start + 1) as int,
        ));
        assert(bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value + 2
            * bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat));

        assert(pow2(1) == 2) by {
            lemma2_to64();
        }
        assert(pow2((start + 1) as nat) == pow2(start) * 2) by {
            assert(pow2((start + 1) as nat) == pow2(start) * pow2(1)) by { lemma_pow2_adds(start, 1)
            }
        }

        let tail = bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat);
        assert(pow2(start) * bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value
            * pow2(start) + pow2((start + 1) as nat) * tail) by (nonlinear_arith)
            requires
                bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value + 2 * tail,
                pow2((start + 1) as nat) == pow2(start) * 2,
        {}

        assert(bits_as_nat_rec(bits, (start + 1) as int) == pow2((start + 1) as nat)
            * bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat));

        assert(bits_as_nat_rec(bits, start as int) == pow2(start) * bits_from_index_to_nat(
            bits,
            start,
            (256 - start) as nat,
        ));
    }
}

pub proof fn lemma_bits_as_nat_eq_bits_from_index(bits: &[bool; 256])
    ensures
        bits_as_nat(bits) == bits_from_index_to_nat(bits, 0, 256),
{
    lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits, 0);
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(bits_as_nat(bits) == bits_as_nat_rec(bits, 0));
    assert(bits_as_nat_rec(bits, 0) == pow2(0) * bits_from_index_to_nat(bits, 0, 256));
    assert(pow2(0) * bits_from_index_to_nat(bits, 0, 256) == bits_from_index_to_nat(bits, 0, 256))
        by { lemma_mul_basics_3(bits_from_index_to_nat(bits, 0, 256) as int) }
}

/// Decompose `bits_from_index_to_nat` by peeling off the last bit.
pub proof fn lemma_bits_from_index_to_nat_split_last(bits: &[bool; 256], start: nat, len: nat)
    requires
        start + len + 1 <= 256,
    ensures
        bits_from_index_to_nat(bits, start, (len + 1) as nat) == bits_from_index_to_nat(
            bits,
            start,
            len,
        ) + (if bits[(start + len) as int] {
            1nat
        } else {
            0nat
        }) * pow2(len),
    decreases len,
{
    if len == 0 {
        assert(bits_from_index_to_nat(bits, start, 1) == (if bits[start as int] {
            1nat
        } else {
            0nat
        }));
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
    } else {
        let b0 = if bits[start as int] {
            1nat
        } else {
            0nat
        };
        assert(bits_from_index_to_nat(bits, start, (len + 1) as nat) == b0 + 2
            * bits_from_index_to_nat(bits, (start + 1) as nat, len));
        assert(bits_from_index_to_nat(bits, start, len) == b0 + 2 * bits_from_index_to_nat(
            bits,
            (start + 1) as nat,
            (len - 1) as nat,
        ));

        lemma_bits_from_index_to_nat_split_last(bits, (start + 1) as nat, (len - 1) as nat);

        assert(bits_from_index_to_nat(bits, (start + 1) as nat, len) == bits_from_index_to_nat(
            bits,
            (start + 1) as nat,
            (len - 1) as nat,
        ) + (if bits[(start + len) as int] {
            1nat
        } else {
            0nat
        }) * pow2((len - 1) as nat));

        assert(pow2(1) == 2) by {
            lemma2_to64();
        }
        assert(pow2(len) == 2 * pow2((len - 1) as nat)) by {
            assert(len == (len - 1) + 1);
            assert(pow2(len) == pow2((len - 1) as nat) * pow2(1)) by {
                lemma_pow2_adds((len - 1) as nat, 1)
            }
            assert(pow2((len - 1) as nat) * pow2(1) == pow2(1) * pow2((len - 1) as nat)) by {
                lemma_mul_is_commutative(pow2((len - 1) as nat) as int, pow2(1) as int);
            }
        }

        let last_bit = if bits[(start + len) as int] {
            1nat
        } else {
            0nat
        };
        let t = bits_from_index_to_nat(bits, (start + 1) as nat, (len - 1) as nat);
        assert(bits_from_index_to_nat(bits, start, (len + 1) as nat) == (b0 + 2 * t) + last_bit
            * pow2(len)) by (nonlinear_arith)
            requires
                bits_from_index_to_nat(bits, start, (len + 1) as nat) == b0 + 2
                    * bits_from_index_to_nat(bits, (start + 1) as nat, len),
                bits_from_index_to_nat(bits, (start + 1) as nat, len) == t + last_bit * pow2(
                    (len - 1) as nat,
                ),
                pow2(len) == 2 * pow2((len - 1) as nat),
        {}
        assert(bits_from_index_to_nat(bits, start, (len + 1) as nat) == bits_from_index_to_nat(
            bits,
            start,
            len,
        ) + last_bit * pow2(len));
    }
}

/// If a 256-bit little-endian bitvector represents a value strictly less than `2^255`,
/// then the top bit (bit 255) must be false.
pub proof fn lemma_bits_as_nat_lt_pow2_255_implies_msb_false(bits: &[bool; 256])
    requires
        bits_as_nat(bits) < pow2(255),
    ensures
        !bits[255],
{
    lemma_bits_as_nat_eq_bits_from_index(bits);
    lemma_bits_from_index_to_nat_split_last(bits, 0, 255);

    if bits[255] {
        assert((if bits[255] {
            1nat
        } else {
            0nat
        }) == 1nat);
        assert(bits_from_index_to_nat(bits, 0, 256) == bits_from_index_to_nat(bits, 0, 255) + pow2(
            255,
        ));

        let lo = bits_from_index_to_nat(bits, 0, 255);
        assert(lo + pow2(255) >= pow2(255));
        assert(bits_from_index_to_nat(bits, 0, 256) >= pow2(255));
        assert(bits_as_nat(bits) == bits_from_index_to_nat(bits, 0, 256));
        assert(bits_as_nat(bits) >= pow2(255));
        assert(false);
    }
}

/// Relate `bits_be_as_nat` on a reversed big-endian view to the corresponding
/// little-endian `bits_from_index_to_nat` range.
pub proof fn lemma_bits_be_as_nat_eq_bits_from_index(
    bits_le: &[bool; 256],
    bits_be: &[bool],
    len: nat,
)
    requires
        len <= 255,
        bits_be.len() == 255,
        forall|i: int| 0 <= i < 255 ==> #[trigger] bits_be[i] == bits_le[254 - i],
    ensures
        bits_be_as_nat(bits_be, len as int) == bits_from_index_to_nat(
            bits_le,
            (255 - len) as nat,
            len,
        ),
    decreases len,
{
    if len == 0 {
        assert(bits_be_as_nat(bits_be, 0) == 0);
        assert(bits_from_index_to_nat(bits_le, 255, 0) == 0);
    } else {
        lemma_bits_be_as_nat_eq_bits_from_index(bits_le, bits_be, (len - 1) as nat);
        let start = (255 - len) as nat;
        let bit_value = if bits_le[start as int] {
            1nat
        } else {
            0nat
        };

        assert(bits_be[len as int - 1] == bits_le[start as int]) by {
            assert((len - 1) < 255);
            assert(bits_be[(len - 1) as int] == bits_le[254 - (len - 1) as int]);
            assert(254 - (len - 1) as int == start as int);
        }
        assert(bits_be_as_nat(bits_be, len as int) == (if bits_be[len as int - 1] {
            1nat
        } else {
            0nat
        }) + 2 * bits_be_as_nat(bits_be, (len - 1) as int));

        assert(bits_from_index_to_nat(bits_le, start, len) == bit_value + 2
            * bits_from_index_to_nat(bits_le, (start + 1) as nat, (len - 1) as nat));

        assert(bits_be_as_nat(bits_be, len as int) == bit_value + 2 * bits_be_as_nat(
            bits_be,
            (len - 1) as int,
        ));
        assert(bits_be_as_nat(bits_be, (len - 1) as int) == bits_from_index_to_nat(
            bits_le,
            (start + 1) as nat,
            (len - 1) as nat,
        ));
        assert(bits_be_as_nat(bits_be, len as int) == bit_value + 2 * bits_from_index_to_nat(
            bits_le,
            (start + 1) as nat,
            (len - 1) as nat,
        ));
        assert(bits_be_as_nat(bits_be, len as int) == bits_from_index_to_nat(bits_le, start, len));
    }
}

} // verus!
