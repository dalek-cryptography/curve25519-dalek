//! Specifications for the Lizard reversible encoding.
//!
//! Lizard is a *reversible encoding* of 16 bytes (128 bits) into a Ristretto point.
//! It is intended for applications that need to embed a short message into a group
//! element and later recover it **iff** the point was produced by the encoding
//! procedure.
//!
//! Lizard is **not** a hash-to-curve function: it does not model a random oracle
//! into the group.
//!
//! ## Example application: Signal's anonymous credentials
//!
//! Signal's zkgroup library uses Lizard to embed a 16-byte UUID into a
//! Ristretto point. The point can then be encrypted and used in zero-knowledge
//! proofs, while remaining decodable back to the UUID on decryption.
//!
//! ```text
//! // Encoding (uid_struct.rs):
//! let point = RistrettoPoint::lizard_encode::<Sha256>(&uuid_bytes);
//!
//! // Decoding (uid_encryption.rs):
//! match point.lizard_decode::<Sha256>() {
//!     Some(bytes) => { /* recovered UUID */ }
//!     None        => { /* not a Lizard-encoded point */ }
//! }
//! ```
//!
//! ## Mathematical objects and notation
//!
//! - The message is a 16-byte string `m ∈ {0,1}^{128}` (represented as `Seq<u8>` with `len == 16`).
//! - `SHA256 : {0,1}^* → {0,1}^{256}` is modeled as the uninterpreted function
//!   `crate::core_assumes::spec_sha256`.
//! - `F_p` is the prime field with `p = 2^255 - 19`. We represent field elements as `nat` in
//!   `[0, p)` using `fe51_as_canonical_nat`.
//! - `Elligator : F_p → E(F_p)` is the Ristretto Elligator map, modeled as
//!   `spec_elligator_ristretto_flavor`, returning affine Edwards coordinates `(x, y)` in `F_p × F_p`.
//!
//! ## Encoding pipeline (`lizard_encode_verus` / `spec_lizard_encode`)
//!
//! ```text
//!          b(·)              r(·)            Elligator
//!   m  ──────────►  b(m)  ────────►  r(m)  ───────────►  P(m)
//!   16 B            32 B             ∈ F_p               ∈ E(F_p)
//! ```
//!
//!   - `b(m) = mask(splice(SHA256(m), m))` — spec: `lizard_fe_bytes` below
//!     - `SHA256(m)`: 32-byte pseudorandom envelope
//!     - `splice`: overwrite bytes 8..24 with `m` (recoverable payload)
//!     - `mask`: `b[0] &= 254` (positive — Elligator maps ±r identically),
//!       `b[31] &= 63` (below 2²⁵⁴ < p — `from_bytes` injective)
//!   - `r(m) = from_bytes(b(m)) mod p` — spec: `lizard_r` below
//!   - `P(m) = Elligator(r(m))` — spec: `spec_lizard_encode` below
//!
//! ## Decoding pipeline (`lizard_decode_verus` / `spec_lizard_decode`)
//!
//! ```text
//!          Elligator⁻¹          as_bytes          extract         b(mⱼ)==bⱼ?
//!   P  ──────────────►  {r₁..r₈}  ──────►  {b₁..b₈}  ──────►  {m₁..m₈}  ──────────►  m or None
//!   ∈ E(F_p)            ≤ 8 candidates      32 B each         mⱼ=bⱼ[8..24]      1 pass→Some(m)
//!                                                                                 else→None
//! ```
//!
//!   - `Elligator⁻¹`: up to 8 candidate field elements (4 coset reps × 2 signs)
//!   - `as_bytes`: convert each rⱼ to 32-byte string bⱼ
//!   - `extract`: extract mⱼ = bⱼ[8..24]
//!   - `b(mⱼ)==bⱼ?`: verify `b(mⱼ) == bⱼ` (SHA-256 consistency)
//!   - exactly one match → `Some(m)`; zero or ≥2 → `None`
//!
//! Decode returns `None` when `n_found ≠ 1`:
//!
//!   - `n_found == 0` — point was not produced by Lizard (no candidate passes
//!     the SHA-256 consistency check).
//!   - `n_found ≥ 2` — two distinct messages `m₁ ≠ m₂` encode to the same
//!     point. Their `r` values are distinct (bytes 8..24 differ ⟹ `from_bytes`
//!     injective) but land in the same Elligator fiber (≤ 8 field elements per
//!     Ristretto point). Negligible probability — see go-ristretto reference.
//!     This is modeled by `lizard_has_unique_preimage`; `lemma_lizard_roundtrip`
//!     proves correctness conditionally on the absence of such collisions.
//!
//! ## References
//!
//! - Westerbaan, B. (2019). Lizard encoding for Ristretto.
//!   Reference Go implementation (v1.1.0) with algorithm description and
//!   probability analysis for non-decodable inputs:
//!   <https://github.com/bwesterb/go-ristretto/blob/master/ristretto.go>
//!   (see `Point.SetLizard`, `Point.LizardInto`).
//!   The quick Ristretto-Elligator inversion is joint work with Mike Hamburg.
//! - Signal usage: `libsignal/rust/zkgroup/src/crypto/uid_struct.rs` (encode),
//!   `libsignal/rust/zkgroup/src/crypto/uid_encryption.rs` (decode).
//! - Executable code: `crate::lizard::lizard_ristretto`
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use super::ristretto_specs::*;
#[allow(unused_imports)]
use crate::core_assumes::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Lizard encoding (16 bytes -> field element bytes -> Ristretto Elligator)
// =============================================================================
/// Construct the 32-byte string `b(m)` used by Lizard before interpreting it as
/// a field element.
///
/// ```text
/// m ──► [b(m)] ──► r(m) ──► P(m)
///        ^^^^
/// ```
///
/// 1. `SHA256(m)` — pseudorandom padding
/// 2. Overwrite bytes 8..24 with `m` — recoverable payload
/// 3. `b[0] &= 254` — ensure positive (Elligator maps ±r identically)
/// 4. `b[31] &= 63` — canonical range (< 2²⁵⁴)
pub open spec fn lizard_fe_bytes(data: Seq<u8>) -> [u8; 32]
    recommends
        data.len() == 16,
{
    let digest = spec_sha256(data);
    let s = Seq::new(
        32,
        |i: int|
            if 8 <= i < 24 {
                data[i - 8]
            } else {
                digest[i]
            },
    );
    let s = s.update(0, s[0] & 254u8);
    let s = s.update(31, s[31] & 63u8);
    seq_to_array_32(s)
}

/// Field element `r(m) ∈ F_p` — deterministic Elligator input derived from `b(m)`.
///
/// ```text
/// m ──► b(m) ──► [r(m)] ──► P(m)
///                 ^^^^
/// ```
pub open spec fn lizard_r(fe_bytes: &[u8; 32]) -> nat {
    fe51_as_canonical_nat(&spec_fe51_from_bytes(fe_bytes))
}

/// Point `P(m) = Elligator(r(m))` — the Lizard encoding.
///
/// ```text
/// m ──► b(m) ──► r(m) ──► [P(m)]
///                          ^^^^^
/// ```
///
/// The message rides inside the Elligator preimage at bytes 8..24.
/// Returns `(x, y) ∈ F_p × F_p`.  Top-level spec for `lizard_encode_verus`.
pub open spec fn spec_lizard_encode(data: Seq<u8>) -> (nat, nat)
    recommends
        data.len() == 16,
{
    spec_elligator_ristretto_flavor(lizard_r(&lizard_fe_bytes(data)))
}

// =============================================================================
// Jacobi quartic ↔ Edwards conversion
// =============================================================================
//
// A Jacobi quartic is an elliptic curve of the form T² = S⁴ + 2αS² + 1,
// birationally equivalent to the Edwards curve but better suited to Elligator.
// The Ristretto Elligator map factors through this quartic:
//
//     r ∈ F_p  ──Elligator──►  (S,T) on quartic  ──►  (x,y) on Edwards
//
// `jacobi_to_edwards_affine` is the second arrow.  Its inverse
// (`to_jacobi_quartic_ristretto` in `lizard_ristretto.rs`) decomposes a
// Ristretto point into 4 Jacobi quartic points — one per coset member in
// self + E[4].  Each Jacobi point (and its dual) may then have an Elligator
// preimage (`elligator_inv` in `jacobi_quartic.rs`), giving up to 8
// candidate field elements for Lizard decoding.
//
// Reference: Ristretto group §4.3 (https://ristretto.group/formulas/elligator.html),
// go-ristretto `lizard.go` (https://github.com/bwesterb/go-ristretto/blob/v1.2.3/edwards25519/elligator.go)
/// Map from Jacobi quartic point `(S, T)` to affine Edwards coordinates `(x, y)`.
///
/// The Jacobi quartic associated to `−x² + y² = 1 + d·x²·y²` (with `a = −1`) is
/// `T² = S⁴ + 2(a − 2d)·S² + 1`.
///
/// ```text
///   y = (1 − S²) / (1 + S²)
///   x = −2·S / (T · √(ad − 1))
/// ```
///
/// where `√(ad − 1) = √(−d − 1)` is `spec_sqrt_ad_minus_one()`.
///
/// Derivation: from `to_jacobi_quartic_ristretto`, `S = γ·Y²·(Z−Y)·X` and
/// `T = (−2/√(a−d))·Z·γ·Y²·(Z−Y)`, so `S/T = −√(a−d)·x/2`, giving
/// `x = −2·S/(T·√(ad−1))`.  The `y` formula follows from `S² = (Z−Y)/(Z+Y)`.
///
/// Requires `1 + S² ≠ 0` and `T · √(ad−1) ≠ 0` (division denominators).
///
/// Used in:
/// - `to_jacobi_quartic_ristretto` ensures (coset correctness)
/// - `elligator_inv` ensures (round-trip with `spec_elligator_ristretto_flavor`)
pub open spec fn jacobi_to_edwards_affine(s: nat, t: nat) -> (nat, nat)
    recommends
        field_add(1, field_square(s)) != 0,
        field_mul(t, spec_sqrt_ad_minus_one()) != 0,
{
    // y = (1 − S²) / (1 + S²)
    let s_sq = field_square(s);
    let y = field_mul(field_sub(1, s_sq), field_inv(field_add(1, s_sq)));
    // x = −2S / (T · √(ad−1))
    let sqrt_ad_m1 = spec_sqrt_ad_minus_one();
    let x = field_mul(field_neg(field_mul(2, s)), field_inv(field_mul(t, sqrt_ad_m1)));
    (x, y)
}

// =============================================================================
// Decoding: P ──Elligator⁻¹──► {r₁..r₈} ──as_bytes──► {b₁..b₈} ──check──► m or None
//
//   Elligator⁻¹: up to 8 candidate field elements (4 coset reps × 2 signs)
//   as_bytes:     convert each rⱼ back to 32-byte string bⱼ
//   check:        extract mⱼ = bⱼ[8..24], verify b(mⱼ) == bⱼ  (SHA-256 consistency)
//   result:       exactly one match → Some(m); zero or ≥2 → None
// =============================================================================
/// True iff `encode(data) == point`.
pub open spec fn is_lizard_preimage(data: Seq<u8>, point: (nat, nat)) -> bool
    recommends
        data.len() == 16,
{
    spec_lizard_encode(data) == point
}

/// ∃! m ∈ {0,1}¹²⁸ such that `encode(m) == point`.
///
/// Guards `spec_lizard_decode`: `Some(m)` iff this holds, `None` otherwise.
pub open spec fn lizard_has_unique_preimage(point: (nat, nat)) -> bool {
    exists|data: Seq<u8>|
        data.len() == 16 && #[trigger] is_lizard_preimage(data, point) && forall|data2: Seq<u8>|
            data2.len() == 16 && #[trigger] is_lizard_preimage(data2, point) ==> data2 == data
}

/// Return the unique preimage, or `None` (collision / no preimage).
pub closed spec fn spec_lizard_decode(point: (nat, nat)) -> Option<Seq<u8>> {
    if lizard_has_unique_preimage(point) {
        Some(
            choose|data: Seq<u8>|
                data.len() == 16 && #[trigger] is_lizard_preimage(data, point) && forall|
                    data2: Seq<u8>,
                |
                    data2.len() == 16 && #[trigger] is_lizard_preimage(data2, point) ==> data2
                        == data,
        )
    } else {
        None
    }
}

// =============================================================================
// Ristretto-level decoding (over the 4-element coset P + E[4])
// =============================================================================
//
// A Ristretto point is an equivalence class {P, P+T₂, P+T₄, P+T₆}.
// Decoding searches all 4 representatives, so predicates quantify over
// the entire coset:  encode(m) ∈ coset(P).
/// True iff `encode(data)` equals some element of `coset`.
///
/// `data`: 16-byte message.  `coset`: the 4 affine points `{P, P+T₂, P+T₄, P+T₆}`.
pub open spec fn is_lizard_preimage_coset(data: Seq<u8>, coset: [(nat, nat); 4]) -> bool
    recommends
        data.len() == 16,
{
    let enc = spec_lizard_encode(data);
    enc == coset[0] || enc == coset[1] || enc == coset[2] || enc == coset[3]
}

/// ∃! m ∈ {0,1}¹²⁸ such that `encode(m) ∈ coset(x, y)`.
///
/// `(x, y)`: affine Edwards coordinates of any coset representative.
/// Returns `true` iff exactly one such `m` exists.
pub open spec fn lizard_ristretto_has_unique_preimage(x: nat, y: nat) -> bool {
    let coset = ristretto_coset_affine(x, y);
    exists|data: Seq<u8>|
        data.len() == 16 && #[trigger] is_lizard_preimage_coset(data, coset) && forall|
            data2: Seq<u8>,
        |
            data2.len() == 16 && #[trigger] is_lizard_preimage_coset(data2, coset) ==> data2 == data
}

/// Return the unique preimage over `coset(x, y)`, or `None`.
///
/// `(x, y)`: affine Edwards coordinates.  Returns `Some(m)` with `|m| == 16`.
/// Top-level spec for `lizard_decode_verus`.
pub closed spec fn spec_lizard_decode_ristretto(x: nat, y: nat) -> Option<Seq<u8>> {
    let coset = ristretto_coset_affine(x, y);
    if lizard_ristretto_has_unique_preimage(x, y) {
        Some(
            choose|data: Seq<u8>|
                data.len() == 16 && #[trigger] is_lizard_preimage_coset(data, coset),
        )
    } else {
        None
    }
}

// =============================================================================
// Proved properties (point-level)
// =============================================================================
/// Soundness: `decode(P) == Some(m)` ⟹ `encode(m) == P`.
pub proof fn lemma_lizard_decode_sound(point: (nat, nat), data: Seq<u8>)
    ensures
        spec_lizard_decode(point) == Some(data) ==> spec_lizard_encode(data) == point,
{
    reveal(spec_lizard_decode);
}

/// Roundtrip: `decode(encode(m)) == Some(m)`, conditional on no collision.
pub proof fn lemma_lizard_roundtrip(data: Seq<u8>)
    requires
        data.len() == 16,
    ensures
        lizard_has_unique_preimage(spec_lizard_encode(data)) ==> spec_lizard_decode(
            spec_lizard_encode(data),
        ) == Some(data),
{
    reveal(spec_lizard_decode);
    assert(is_lizard_preimage(data, spec_lizard_encode(data)));
}

// =============================================================================
// Proved properties (Ristretto-level)
// =============================================================================
/// Soundness: `decode_ristretto(x, y) == Some(m)` ⟹ `encode(m) ∈ coset(x, y)`.
pub proof fn lemma_lizard_decode_ristretto_sound(x: nat, y: nat, data: Seq<u8>)
    ensures
        spec_lizard_decode_ristretto(x, y) == Some(data) ==> is_lizard_preimage_coset(
            data,
            ristretto_coset_affine(x, y),
        ),
{
    reveal(spec_lizard_decode_ristretto);
}

/// Roundtrip: `decode_ristretto(encode(m)) == Some(m)`, conditional on unique coset preimage.
pub proof fn lemma_lizard_roundtrip_ristretto(data: Seq<u8>)
    requires
        data.len() == 16,
    ensures
        lizard_ristretto_has_unique_preimage(spec_lizard_encode(data).0, spec_lizard_encode(data).1)
            ==> spec_lizard_decode_ristretto(spec_lizard_encode(data).0, spec_lizard_encode(data).1)
            == Some(data),
{
    reveal(spec_lizard_decode_ristretto);
    let enc = spec_lizard_encode(data);
    let coset = ristretto_coset_affine(enc.0, enc.1);
    assert(is_lizard_preimage_coset(data, coset));
}

} // verus!
