//! Table generation module. This module is public but should be treated as
//! unstable. The API may change without notice.

use bytemuck::{Pod, Zeroable};
use std::mem::size_of;

use crate::constants::RISTRETTO_BASEPOINT_POINT;
use crate::field::FieldElement;
use crate::traits::Identity;
use crate::{EdwardsPoint, RistrettoPoint, Scalar};

use super::affine_montgomery::AffineMontgomeryPoint;

pub(crate) const L2: usize = 9; // corresponds to a batch size of 256 and a T2 table of a few Ko.
pub(crate) const BATCH_SIZE: usize = 1 << (L2 - 1);

pub(crate) const I_BITS: usize = L2 - 1;
pub(crate) const I_MAX: usize = (1 << I_BITS) + 1; // there needs to be one more element in T2
pub(crate) const CUCKOO_K: usize = 3; // number of cuckoo lookups before giving up

// Note: file layout is just T2 followed by T1 keys and then T1 values.
// We just do casts using `bytemuck` since everything are PODs.

/// A view into an ECDLP precomputed table. This is a wrapper around a read-only byte array, which you could back by an mmaped file, for example.
pub struct ECDLPTablesFileView<'a, const L1: usize> {
    bytes: &'a [u8],
}

impl<'a, const L1: usize> ECDLPTablesFileView<'a, L1> {
    const J_BITS: usize = L1 - 1;
    const J_MAX: usize = 1 << Self::J_BITS;
    const CUCKOO_LEN: usize = (Self::J_MAX as f64 * 1.3) as _;

    /// ECDLP algorithm may panic if the alignment or size of `bytes` is wrong.
    pub fn from_bytes(bytes: &'a [u8]) -> Self {
        // TODO(merge): check align/size of `bytes` here
        Self { bytes }
    }

    pub(crate) fn get_t1(&self) -> CuckooT1HashMapView<'_, L1> {
        let t1_keys_values: &[u32] =
            bytemuck::cast_slice(&self.bytes[(size_of::<T2MontgomeryCoordinates>() * I_MAX)..]);

        CuckooT1HashMapView {
            keys: &t1_keys_values[0..Self::CUCKOO_LEN],
            values: &t1_keys_values[Self::CUCKOO_LEN..],
        }
    }

    pub(crate) fn get_t2(&self) -> T2LinearTableView<'_> {
        let t2: &[T2MontgomeryCoordinates] =
            bytemuck::cast_slice(&self.bytes[0..(size_of::<T2MontgomeryCoordinates>() * I_MAX)]);
        T2LinearTableView(t2)
    }
}

/// Canonical FieldElement type.
type CompressedFieldElement = [u8; 32];

#[repr(C, align(32))]
#[derive(Clone, Copy, Default, Pod, Zeroable, Debug)]
/// An entry in the T2 table. Represents a (u,v) coordinate on the Montgomery curve.
pub(crate) struct T2MontgomeryCoordinates {
    /// The `u` coordinate.
    pub u: CompressedFieldElement,
    /// The `v` coordinate.
    pub v: CompressedFieldElement,
}

impl From<T2MontgomeryCoordinates> for AffineMontgomeryPoint {
    fn from(e: T2MontgomeryCoordinates) -> Self {
        Self {
            u: FieldElement::from_bytes(&e.u),
            v: FieldElement::from_bytes(&e.v),
        }
    }
}

impl From<AffineMontgomeryPoint> for T2MontgomeryCoordinates {
    fn from(e: AffineMontgomeryPoint) -> Self {
        Self {
            u: e.u.as_bytes(),
            v: e.v.as_bytes(),
        }
    }
}

/// A view into the T2 table.
pub(crate) struct T2LinearTableView<'a>(pub &'a [T2MontgomeryCoordinates]);

impl T2LinearTableView<'_> {
    pub fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let T2MontgomeryCoordinates { u, v } = self.0[index - 1];
        AffineMontgomeryPoint::from_bytes(&u, &v)
    }
}

/// A view into the T1 table.
pub(crate) struct CuckooT1HashMapView<'a, const L1: usize> {
    /// Cuckoo keys
    pub keys: &'a [u32],
    /// Cuckoo values
    pub values: &'a [u32],
}

impl<'a, const L1: usize> CuckooT1HashMapView<'a, L1> {
    pub(crate) fn lookup(
        &self,
        x: &[u8],
        mut is_problem_answer: impl FnMut(u64) -> bool,
    ) -> Option<u64> {
        for i in 0..CUCKOO_K {
            let start = i * 8;
            let end = start + 4;
            let key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
            let h = u32::from_be_bytes(x[start..start + 4].try_into().unwrap()) as usize
                % ECDLPTablesFileView::<L1>::CUCKOO_LEN;
            if self.keys[h as usize] == key {
                let value = self.values[h as usize] as u64;
                if is_problem_answer(value) {
                    return Some(value);
                }
            }
        }
        None
    }
}

pub mod table_generation {
    //! Generate the precomputed tables.
    use super::*;

    fn t1_cuckoo_setup(
        cuckoo_len: usize,
        j_max: usize,
        all_entries: &[CompressedFieldElement],
        t1_values: &mut [u32],
        t1_keys: &mut [u32],
    ) {
        use core::mem::swap;

        /// Dumb cuckoo rehashing threshold.
        const CUCKOO_MAX_INSERT_SWAPS: usize = 500;

        let mut hash_index = vec![0u8; cuckoo_len];

        for i in 0..=j_max {
            let mut v = i as _;
            let mut old_hash_id = 1u8;

            if i % (j_max / 1000 + 1) == 0 {
                log::info!("T1 hashmap generation [{}/{}]", i, j_max);
            }

            for j in 0..CUCKOO_MAX_INSERT_SWAPS {
                let x = all_entries[v as usize].as_ref();
                let start = (old_hash_id as usize - 1) * 8;
                let end = start as usize + 4;
                let mut key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
                let h1 = u32::from_be_bytes(x[start..start + 4].try_into().unwrap()) as usize;
                let h = h1 % cuckoo_len;

                if hash_index[h] == 0 {
                    hash_index[h] = old_hash_id;
                    t1_values[h] = v;
                    t1_keys[h] = key;
                    break;
                } else {
                    swap(&mut old_hash_id, &mut hash_index[h]);
                    swap(&mut v, &mut t1_values[h]);
                    swap(&mut key, &mut t1_keys[h]);
                    old_hash_id = old_hash_id % 3 + 1;

                    if j == CUCKOO_MAX_INSERT_SWAPS - 1 {
                        // We actually don't have to implement the case where we need to rehash the
                        // whole map.
                        panic!("Cuckoo hashmap insert needs rehashing.")
                    }
                }
            }
        }
    }

    fn create_t1_table(l1: usize, dest: &mut [u8]) -> std::io::Result<()> {
        let j_max = 1 << (l1 - 1);
        let cuckoo_len = (j_max as f64 * 1.3) as usize;

        let mut all_entries = vec![Default::default(); j_max + 1];

        log::info!("Computing all the points...");
        let acc = RistrettoPoint::identity().0;
        let step = RISTRETTO_BASEPOINT_POINT.0.mul_by_cofactor(); // table is based on number*cofactor
        
        let mut acc = AffineMontgomeryPoint::from(&acc);
        let step = AffineMontgomeryPoint::from(&step);
        for i in 0..=j_max {
            // acc is i * G
            let point = acc; // i * G

            if i % (j_max / 1000 + 1) == 0 {
                log::info!("T1 point computation [{}/{}]", i, j_max);
            }

            all_entries[i] = point.u.as_bytes();
            acc = acc.addition_not_ct(&step);
        }

        // We don't directly write to `dest` as our writes will be very random-access-y and `dest` is probably an mmaped file.
        let mut t1_keys = vec![0u32; cuckoo_len];
        let mut t1_values = vec![0u32; cuckoo_len];

        log::info!("Setting up the cuckoo hashmap...");
        t1_cuckoo_setup(
            cuckoo_len,
            j_max,
            &all_entries,
            &mut t1_values,
            &mut t1_keys,
        );

        let (t1_keys_dest, t1_values_dest) = dest.split_at_mut(cuckoo_len * size_of::<u32>());
        let t1_keys_dest: &mut [u32] = bytemuck::cast_slice_mut(t1_keys_dest);
        let t1_values_dest: &mut [u32] = bytemuck::cast_slice_mut(t1_values_dest);

        t1_keys_dest.copy_from_slice(&t1_keys);
        t1_values_dest.copy_from_slice(&t1_values);

        log::info!("Done :)");
        Ok(())
    }

    fn create_t2_table(l1: usize, dest: &mut [u8]) -> std::io::Result<()> {
        let two_to_l1 = EdwardsPoint::mul_base(&Scalar::from(1u32 << l1)); // 2^l1
        let two_to_l1 = two_to_l1.mul_by_cofactor(); // clear cofactor

        let arr: &mut [T2MontgomeryCoordinates] = bytemuck::cast_slice_mut(dest);

        let two_to_l1 = AffineMontgomeryPoint::from(&two_to_l1);
        let mut acc = two_to_l1;
        for j in 1..I_MAX {
            arr[j - 1] = acc.into();
            acc = acc.addition_not_ct(&two_to_l1);
        }

        Ok(())
    }

    /// Length of the table file for a given `l1` const.
    pub fn table_file_len(l1: usize) -> usize {
        let j_max = 1 << (l1 - 1);
        let cuckoo_len = (j_max as f64 * 1.3) as usize;

        I_MAX * size_of::<T2MontgomeryCoordinates>() + (cuckoo_len * 2) * size_of::<u32>()
    }

    /// Generate the ECDLP precomputed tables file.
    /// To prepare `dest`, you should use an mmaped file or a 32-byte aligned byte array.
    /// The byte array length should be the return value of [`table_file_len`].
    pub fn create_table_file(l1: usize, dest: &mut [u8]) -> std::io::Result<()> {
        let (t2_bytes, t1_bytes) = dest.split_at_mut(I_MAX * size_of::<T2MontgomeryCoordinates>());
        create_t2_table(l1, t2_bytes)?;
        create_t1_table(l1, t1_bytes)
    }
}
