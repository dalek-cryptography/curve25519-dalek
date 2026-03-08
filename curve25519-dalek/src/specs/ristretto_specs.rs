// Specifications for mathematical operations on the Ristretto group
//
// ## References
//
// The mathematical formulas and specifications in this file are based on:
//
// - [RISTRETTO] Ristretto Group Specification
//   https://ristretto.group/
//   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448
//
// - [DECAF] Hamburg, M. (2015). "Decaf: Eliminating cofactors through point compression"
//   https://eprint.iacr.org/2015/673.pdf
//
// - The Ristretto group is a prime-order quotient group constructed from the
//   cofactor-8 Edwards curve Curve25519.
//
//   The curve E has order 8ℓ. Ristretto eliminates the cofactor 8 in two steps:
//     1. Restrict to even subgroup 2E (points that are doubles): gives a subgroup of order 4ℓ
//     2. Group points into equivalence classes: P ~ Q if P - Q ∈ E[4].
//        E[4] = {P : 4P = O} is the 4-torsion subgroup (4 points that vanish when multiplied by 4).
//        Each class has 4 points, so 4ℓ points form ℓ classes.
//
//   Result: a prime-order group of order ℓ with equivalence classes [P] = {P + T : T ∈ E[4]} for P ∈ 2E.
//
// TODO: Add subgroup-preservation lemmas (e.g., closure of 2*E under edwards_add)
//       once group-law lemmas for Edwards points are available.
#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants as u64_constants;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::spec_eight_torsion;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::lemma_sqrt_ad_minus_one_nonzero;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_nonzero_product;
#[allow(unused_imports)]
use crate::ristretto::{CompressedRistretto, RistrettoPoint};
use vstd::prelude::*;

verus! {

// =============================================================================
// Ristretto Compression (Encoding)
// =============================================================================
/// Ristretto encoding from extended coordinates (X : Y : Z : T).
///
/// Given projective coordinates with Z·T = X·Y, computes the canonical
/// 32-byte Ristretto encoding. The algorithm selects the unique representative
/// from the coset P + E[4] whose encoding s satisfies s ≥ 0.
///
/// Reference: [RISTRETTO] §5.3; [DECAF] §6; https://ristretto.group/formulas/encoding.html
pub open spec fn ristretto_compress_extended(x: nat, y: nat, z: nat, t: nat) -> [u8; 32] {
    let u1 = field_mul(field_add(z, y), field_sub(z, y));
    let u2 = field_mul(x, y);
    let invsqrt = nat_invsqrt(field_mul(u1, field_square(u2)));
    let i1 = field_mul(invsqrt, u1);
    let i2 = field_mul(invsqrt, u2);
    let z_inv = field_mul(i1, field_mul(i2, t));
    let den_inv = i2;

    let iX = field_mul(x, sqrt_m1());
    let iY = field_mul(y, sqrt_m1());
    let enchanted_denominator = field_mul(
        i1,
        fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D),
    );

    let rotate = is_negative(field_mul(t, z_inv));
    let x_rot = if rotate {
        iY
    } else {
        x
    };
    let y_rot = if rotate {
        iX
    } else {
        y
    };
    let den_inv_rot = if rotate {
        enchanted_denominator
    } else {
        den_inv
    };

    let y_final = if is_negative(field_mul(x_rot, z_inv)) {
        field_neg(y_rot)
    } else {
        y_rot
    };
    let s = field_mul(den_inv_rot, field_sub(z, y_final));
    let s_final = if is_negative(s) {
        field_neg(s)
    } else {
        s
    };

    u8_32_from_nat(s_final)
}

/// Ristretto encoding from a RistrettoPoint (delegates to extended coordinates).
///
/// Reference: [RISTRETTO] §5.3
pub open spec fn spec_ristretto_compress(point: RistrettoPoint) -> [u8; 32] {
    let (x, y, z, t) = edwards_point_as_nat(point.0);
    ristretto_compress_extended(x, y, z, t)
}

/// Ristretto encoding from affine coordinates (x, y).
///
/// Sets Z = 1, T = x·y (the Segre invariant Z·T = X·Y).
///
/// Reference: [RISTRETTO] §5.3
pub open spec fn ristretto_compress_affine(x: nat, y: nat) -> [u8; 32] {
    ristretto_compress_extended(x, y, 1, field_mul(x, y))
}

// =============================================================================
// Ristretto Decompression (Decoding)
// =============================================================================
// Reference: [RISTRETTO] §5.2; [DECAF] §6; https://ristretto.group/formulas/decoding.html
//
// Decode formula (given canonical non-negative field element s):
//
//   s²  = s · s
//   u1  = 1 - s²
//   u2  = 1 + s²
//   v   = -d·u1² - u2²
//   (ok, I) = invsqrt(v · u2²)
//   Dx  = I · u2
//   Dy  = I · Dx · v
//   x   = |2s · Dx|                   (conditional negate to non-negative)
//   y   = u1 · Dy
//   t   = x · y
//
/// Full Ristretto decode for field element s.
/// Returns (x, y, ok) where ok indicates the invsqrt succeeded (square case).
pub open spec fn ristretto_decode_inner(s: nat) -> (nat, nat, bool) {
    let ss = field_square(s);
    let u1 = field_sub(1, ss);
    let u2 = field_add(1, ss);
    let u2_sqr = field_square(u2);
    let neg_d = field_neg(fe51_as_canonical_nat(&EDWARDS_D));
    let u1_sqr = field_square(u1);
    let v = field_sub(field_mul(neg_d, u1_sqr), u2_sqr);

    let v_u2_sqr = field_mul(v, u2_sqr);
    let invsqrt = nat_invsqrt(v_u2_sqr);
    let ok = is_sqrt_ratio(1, v_u2_sqr, invsqrt);

    let dx = field_mul(invsqrt, u2);
    let dy = field_mul(invsqrt, field_mul(dx, v));
    let x_tmp = field_mul(field_add(s, s), dx);
    let x = if is_negative(x_tmp) {
        field_neg(x_tmp)
    } else {
        x_tmp
    };
    let y = field_mul(u1, dy);

    (x, y, ok)
}

/// The x coordinate from decoding field element s.
pub open spec fn ristretto_decode_x(s: nat) -> nat {
    ristretto_decode_inner(s).0
}

/// The y coordinate from decoding field element s.
pub open spec fn ristretto_decode_y(s: nat) -> nat {
    ristretto_decode_inner(s).1
}

/// Whether decoding field element s succeeded (the invsqrt "square" case).
pub open spec fn ristretto_decode_ok(s: nat) -> bool {
    ristretto_decode_inner(s).2
}

/// Ristretto decompression: bytes -> Option<(x, y, 1, x·y)>.
///
/// Returns None when any of these checks fail:
///   1. s < p  (canonical encoding)
///   2. s mod 2 = 0  (non-negative)
///   3. invsqrt succeeds, t = x·y ≥ 0, and y ≠ 0
///
/// On success, returns extended coordinates (x, y, 1, x·y) where (x, y)
/// are computed by the decode formula (see `ristretto_decode_inner`).
///
/// Reference: [RISTRETTO] §5.2; [DECAF] §6; https://ristretto.group/formulas/decoding.html
pub open spec fn spec_ristretto_decompress(bytes: [u8; 32]) -> Option<(nat, nat, nat, nat)> {
    let s = field_element_from_bytes(&bytes);

    if !(u8_32_as_nat(&bytes) < p()) || is_negative(s) {
        None
    } else {
        let (x, y, ok) = ristretto_decode_inner(s);
        let t = field_mul(x, y);

        if !ok || is_negative(t) || y == 0 {
            None
        } else {
            Some((x, y, 1nat, t))
        }
    }
}

// =============================================================================
// Ristretto Basepoint
// =============================================================================
/// Ristretto basepoint = [B] where B is the Ed25519 basepoint.
pub open spec fn spec_ristretto_basepoint() -> (nat, nat) {
    spec_ed25519_basepoint()
}

// =============================================================================
// Ristretto Elligator Map (Hash-to-Group)
// =============================================================================
/// The constant sqrt(-d - 1), precomputed for Ristretto's Elligator map.
pub open spec fn spec_sqrt_ad_minus_one() -> nat {
    fe51_as_canonical_nat(&u64_constants::SQRT_AD_MINUS_ONE)
}

/// Elligator map for Ristretto (MAP function): field element r_0 -> affine point (x, y).
///
/// Maps a field element to a Ristretto point deterministically. Computes a
/// completed point from r_0 via sqrt_ratio_i, then converts to affine.
///
/// Given i = sqrt(-1), d = Edwards curve constant, c₀ = -1:
///
///   r   = i · r_0²
///   N_s = (r + 1)(1 - d²)
///   D   = (c₀ - d·r)(r + d)
///   (was_square, s) = sqrt_ratio_i(N_s, D)
///   s'  = -|s · r_0|                      (negate to ensure negative)
///   if !was_square: s = s', c = r          else: s = s, c = c₀
///   N_t = c·(r - 1)·(d - 1)² - D
///
/// Completed point:  X = 2sD,  Y = 1 - s²,  Z = N_t · sqrt(-d - 1),  T = 1 + s²
/// Affine output:    x = X/Z,  y = Y/T
///
/// Reference: [RISTRETTO] §4.3.4; https://ristretto.group/formulas/elligator.html
pub open spec fn spec_elligator_ristretto_flavor(r_0: nat) -> (nat, nat) {
    let (s, n_t, d_val) = elligator_intermediates(r_0);
    let s_sq = field_square(s);

    let sqrt_ad_minus_one = spec_sqrt_ad_minus_one();
    let x_completed = field_mul(field_mul(2, s), d_val);
    let z_completed = field_mul(n_t, sqrt_ad_minus_one);
    let y_completed = field_sub(1, s_sq);
    let t_completed = field_add(1, s_sq);

    let x_affine = field_mul(x_completed, field_inv(z_completed));
    let y_affine = field_mul(y_completed, field_inv(t_completed));

    (x_affine, y_affine)
}

/// Spec helper: first 32 bytes of a 64-byte input.
pub open spec fn uniform_bytes_first(bytes: &[u8; 64]) -> [u8; 32] {
    choose|b: [u8; 32]| b@ == bytes@.subrange(0, 32)
}

/// Spec helper: second 32 bytes of a 64-byte input.
pub open spec fn uniform_bytes_second(bytes: &[u8; 64]) -> [u8; 32] {
    choose|b: [u8; 32]| b@ == bytes@.subrange(32, 64)
}

/// Hash-to-group: constructs a Ristretto point from 64 uniform random bytes.
///
///   b1, b2 = bytes[0..32], bytes[32..64]
///   r1, r2 = from_bytes(b1), from_bytes(b2)
///   result = elligator(r1) + elligator(r2)
///
/// Reference: [RISTRETTO] §4.3.4; https://ristretto.group/formulas/encoding.html
pub open spec fn ristretto_from_uniform_bytes(bytes: &[u8; 64]) -> (nat, nat) {
    let b1 = uniform_bytes_first(bytes);
    let b2 = uniform_bytes_second(bytes);
    let r1 = field_element_from_bytes(&b1);
    let r2 = field_element_from_bytes(&b2);
    let p1 = spec_elligator_ristretto_flavor(r1);
    let p2 = spec_elligator_ristretto_flavor(r2);
    edwards_add(p1.0, p1.1, p2.0, p2.1)
}

// =============================================================================
// Ristretto Equivalence Classes (Cosets)
// =============================================================================
/// True when the point is the double of some curve point (i.e., lies in 2E).
pub open spec fn is_in_even_subgroup(point: EdwardsPoint) -> bool {
    exists|q: EdwardsPoint|
        edwards_point_as_affine(point) == edwards_scalar_mul(
            #[trigger] edwards_point_as_affine(q),
            2,
        )
}

/// True when the 4 points form a coset base + E[4] (one Ristretto equivalence class).
///
/// E[4] has elements T[0] (identity), T[2], T[4], T[6] from the 8-torsion table.
pub open spec fn is_ristretto_coset(points: [EdwardsPoint; 4], base: EdwardsPoint) -> bool {
    let base_affine = edwards_point_as_affine(base);
    let t2 = edwards_point_as_affine(spec_eight_torsion()[2]);
    let t4 = edwards_point_as_affine(spec_eight_torsion()[4]);
    let t6 = edwards_point_as_affine(spec_eight_torsion()[6]);

    // points[0] = base (T[0] is identity)
    edwards_point_as_affine(points[0])
        == base_affine
    // points[1] = base + T[2]
     && edwards_point_as_affine(points[1]) == edwards_add(
        base_affine.0,
        base_affine.1,
        t2.0,
        t2.1,
    )
    // points[2] = base + T[4]
     && edwards_point_as_affine(points[2]) == edwards_add(
        base_affine.0,
        base_affine.1,
        t4.0,
        t4.1,
    )
    // points[3] = base + T[6]
     && edwards_point_as_affine(points[3]) == edwards_add(base_affine.0, base_affine.1, t6.0, t6.1)
}

/// The 4 affine points forming the Ristretto coset base + E[4].
///
/// Returns `[base, base+T₂, base+T₄, base+T₆]` as affine `(nat, nat)` tuples.
pub open spec fn ristretto_coset_affine(x: nat, y: nat) -> [(nat, nat); 4] {
    let t2 = edwards_point_as_affine(spec_eight_torsion()[2]);
    let t4 = edwards_point_as_affine(spec_eight_torsion()[4]);
    let t6 = edwards_point_as_affine(spec_eight_torsion()[6]);
    [
        (x, y),
        edwards_add(x, y, t2.0, t2.1),
        edwards_add(x, y, t4.0, t4.1),
        edwards_add(x, y, t6.0, t6.1),
    ]
}

/// Two points are Ristretto-equivalent when their difference is a 4-torsion element.
pub open spec fn ristretto_equivalent(p1: EdwardsPoint, p2: EdwardsPoint) -> bool
    recommends
        is_well_formed_edwards_point(p1),
        is_well_formed_edwards_point(p2),
{
    let p1_affine = edwards_point_as_affine(p1);
    let p2_affine = edwards_point_as_affine(p2);
    let diff = edwards_sub(p1_affine.0, p1_affine.1, p2_affine.0, p2_affine.1);

    // The difference must be a 4-torsion element (one of T[0], T[2], T[4], T[6])
    let t0 = edwards_point_as_affine(spec_eight_torsion()[0]);
    let t2 = edwards_point_as_affine(spec_eight_torsion()[2]);
    let t4 = edwards_point_as_affine(spec_eight_torsion()[4]);
    let t6 = edwards_point_as_affine(spec_eight_torsion()[6]);

    diff == t0 || diff == t2 || diff == t4 || diff == t6
}

// =============================================================================
// Elligator Map Helpers
// =============================================================================
/// Extract the Elligator intermediate values (s, n_t, d_val) from r_0.
/// These are the values computed partway through elligator_ristretto_flavor,
/// before the final completed-point construction.
///
/// Returns (s, n_t, d_val) where:
///   s     = the final s value after conditional assignment
///   n_t   = N_t = c·(r−1)·(d−1)² − D
///   d_val = D = (c₀ − d·r)(r + d)
pub open spec fn elligator_intermediates(r_0: nat) -> (nat, nat, nat) {
    let i = sqrt_m1();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let one_minus_d_sq = field_mul(field_sub(1, d), field_add(1, d));
    let d_minus_one_sq = field_square(field_sub(d, 1));
    let c_init: nat = field_neg(1);

    let r = field_mul(i, field_square(r_0));
    let n_s = field_mul(field_add(r, 1), one_minus_d_sq);
    let d_val = field_mul(field_sub(c_init, field_mul(d, r)), field_add(r, d));

    let invsqrt_val = nat_invsqrt(field_mul(n_s, d_val));
    let s_if_square = field_abs(field_mul(invsqrt_val, n_s));
    let was_square = is_sqrt_ratio(n_s, d_val, s_if_square);

    let s_prime_raw = field_mul(s_if_square, r_0);
    let s_prime = if !is_negative(s_prime_raw) {
        field_neg(s_prime_raw)
    } else {
        s_prime_raw
    };

    let s = if was_square {
        s_if_square
    } else {
        s_prime
    };
    let c = if was_square {
        c_init
    } else {
        r
    };
    let n_t = field_sub(field_mul(field_mul(c, field_sub(r, 1)), d_minus_one_sq), d_val);

    (s, n_t, d_val)
}

// =============================================================================
// Batch Double-and-Compress
// =============================================================================
/// Spec function for the batch compression loop body.
///
/// Given BatchCompressState fields (e, f, g, h, eg, fh) and the
/// batch-inverted value inv = 1/(eg·fh), computes the Ristretto
/// encoding. This mirrors the exec code in
/// `double_and_compress_batch_verus` loop body.
///
/// Reference: [DECAF] §6; https://ristretto.group/formulas/encoding.html
pub open spec fn batch_compress_body(
    e: nat,
    f: nat,
    g: nat,
    h: nat,
    eg: nat,
    fh: nat,
    inv: nat,
) -> [u8; 32] {
    let zinv = field_mul(eg, inv);
    let tinv = field_mul(fh, inv);

    let invsqrt_a_minus_d = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);

    let negcheck1 = is_negative(field_mul(eg, zinv));

    let minus_e = field_neg(e);
    let f_times_sqrta = field_mul(f, sqrt_m1());

    let e_rot = if negcheck1 {
        g
    } else {
        e
    };
    let g_rot = if negcheck1 {
        minus_e
    } else {
        g
    };
    let h_rot = if negcheck1 {
        f_times_sqrta
    } else {
        h
    };
    let magic = if negcheck1 {
        sqrt_m1()
    } else {
        invsqrt_a_minus_d
    };

    let negcheck2 = is_negative(field_mul(field_mul(h_rot, e_rot), zinv));

    let g_final = if negcheck2 {
        field_neg(g_rot)
    } else {
        g_rot
    };

    let s = field_mul(field_sub(h_rot, g_final), field_mul(magic, field_mul(g_final, tinv)));
    let s_final = if is_negative(s) {
        field_neg(s)
    } else {
        s
    };

    u8_32_from_nat(s_final)
}

} // verus!
