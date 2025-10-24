// Lemmas and spec functions only used in field_verus.rs
// A lemma should be in this module instead of `common_verus` if:
//  - It references some constant prominent in `field_verus` (e.g. 51 for bit operations, 2^255 -19)
//  - It defines or reasons about a spec function relevant only to `field_verus`
pub mod as_nat_lemmas;

pub mod field_core;

pub mod from_bytes_lemmas;

pub mod negate_lemmas;

pub mod pow2_51_lemmas;

pub mod pow2k_lemmas;

pub mod reduce_lemmas;

pub mod load8_lemmas;

pub mod compute_q_lemmas;
pub mod limbs_to_bytes_lemmas;
pub mod to_bytes_reduction_lemmas;
