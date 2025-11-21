// Lemmas and spec functions only used in field_verus.rs
// A lemma should be in this module instead of `common_lemmas` if:
//  - It references some constant prominent in `field_verus` (e.g. 51 for bit operations, 2^255 -19)
//  - It defines or reasons about a spec function relevant only to `field_verus`
pub mod add_lemmas;

pub mod as_bytes_lemmas;

pub mod u64_5_as_nat_lemmas;

pub mod u8_32_as_nat_injectivity_lemmas;

pub mod from_bytes_lemmas;

pub mod negate_lemmas;

pub mod pow2_51_lemmas;

pub mod pow2k_lemmas;

pub mod reduce_lemmas;

pub mod load8_lemmas;

pub mod compute_q_lemmas;
pub mod limbs_to_bytes_lemmas;
pub mod to_bytes_reduction_lemmas;

pub mod invert_lemmas;
pub mod pow22501_t19_lemma;
pub mod pow22501_t3_lemma;
pub mod pow_chain_lemmas;
pub mod pow_p58_lemma;
