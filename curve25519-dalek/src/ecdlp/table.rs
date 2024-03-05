//! Table generation module. This module is public but should be treated as
//! unstable. The API may change without notice.

use bytemuck::{Pod, Zeroable};
use std::{fs::File, io::Write};
use std::{mem::size_of, path::Path};

use crate::constants::RISTRETTO_BASEPOINT_POINT;
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

/// ECDLP tables loaded from a file. The `L1` const-generic needs to match the one
/// used during table generation.
pub struct ECDLPTablesFile<const L1: usize> {
    content: memmap::Mmap,
}
impl<const L1: usize> ECDLPTablesFile<L1> {
    /// Load the ECDLP tables from a file.
    /// As of now, the file layout is unstable and may change.
    pub fn load_from_file(filename: impl AsRef<Path>) -> std::io::Result<Self> {
        let f = File::open(filename)?;

        // Safety: mmap does not have any safety comment, but see
        // https://github.com/danburkert/memmap-rs/issues/99
        let content = unsafe { memmap::MmapOptions::new().map(&f)? };

        assert_eq!(
            content.len(),
            size_of::<T2MontgomeryCoordinates>() * I_MAX + size_of::<u32>() * Self::CUCKOO_LEN * 2
        );

        Ok(Self { content })
    }
}

impl<const L1: usize> PrecomputedECDLPTables for ECDLPTablesFile<L1> {
    const L1: usize = L1;

    fn get_t1(&self) -> CuckooT1HashMapView<'_> {
        let t1_keys_values: &[u32] =
            bytemuck::cast_slice(&self.content[(size_of::<T2MontgomeryCoordinates>() * I_MAX)..]);

        CuckooT1HashMapView {
            keys: &t1_keys_values[0..Self::CUCKOO_LEN],
            values: &t1_keys_values[Self::CUCKOO_LEN..],
        }
    }

    fn get_t2(&self) -> T2LinearTableView<'_> {
        let t2: &[T2MontgomeryCoordinates] =
            bytemuck::cast_slice(&self.content[0..(size_of::<T2MontgomeryCoordinates>() * I_MAX)]);
        T2LinearTableView(t2)
    }
}

/// Trait to expose access to the ECDLP precomputed tables to the algorithm.
/// You should probably use [`ECDLPTablesFile`], which implements this trait -
/// this trait only exists as a way to implement your own way of storing the tables,
/// in case you are running on `no_std` or don't have access to `mmap`.
pub trait PrecomputedECDLPTables {
    /// The `L1` constant used to generate the table.
    const L1: usize;

    /// Hashmap <i * G => i | i in \[1, 2^(l1-1)\]>.
    /// Cuckoo hash table, each entry is 8 bytes long - but there are 1.3 times the needed slots.
    /// Total map size is then 1.3*8*2^(l1-1) bytes.
    /// The hashing function is just indexing the bytes of the point for efficiency.
    fn get_t1(&self) -> CuckooT1HashMapView<'_>;

    /// Linear map \[j * 2^l1 * G | j in \[1, 2^(l2-1)\]\].
    fn get_t2(&self) -> T2LinearTableView<'_>;
}

// Hoist these constants to a private trait to make them non-overrideable.
pub(crate) trait ECDLPTablesConstants {
    const J_BITS: usize;
    const J_MAX: usize;
    const CUCKOO_LEN: usize;
}
impl<T: PrecomputedECDLPTables> ECDLPTablesConstants for T {
    const J_BITS: usize = Self::L1 - 1;
    const J_MAX: usize = 1 << Self::J_BITS;
    const CUCKOO_LEN: usize = (Self::J_MAX as f64 * 1.3) as _;
}

/// Canonical FieldElement type.
type CompressedFieldElement = [u8; 32];

#[repr(C)]
#[derive(Clone, Copy, Default, Pod, Zeroable, Debug)]
/// An entry in the T2 table. Represents a (u,v) coordinate on the Montgomery curve.
pub struct T2MontgomeryCoordinates {
    /// The `u` coordinate.
    pub u: CompressedFieldElement,
    /// The `v` coordinate.
    pub v: CompressedFieldElement,
}

/// A view into the T2 table.
pub struct T2LinearTableView<'a>(pub &'a [T2MontgomeryCoordinates]);

impl T2LinearTableView<'_> {
    pub(crate) fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let T2MontgomeryCoordinates { u, v } = self.0[index - 1];
        AffineMontgomeryPoint::from_bytes(&u, &v)
    }
}

/// A view into the T1 table.
pub struct CuckooT1HashMapView<'a> {
    /// Cuckoo keys
    pub keys: &'a [u32],
    /// Cuckoo values
    pub values: &'a [u32],
}

impl CuckooT1HashMapView<'_> {
    pub(crate) fn lookup<TS: PrecomputedECDLPTables>(
        &self,
        x: &[u8],
        mut is_problem_answer: impl FnMut(u64) -> bool,
    ) -> Option<u64> {
        for i in 0..CUCKOO_K {
            let start = i * 8;
            let end = start + 4;
            let key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
            let h = u32::from_be_bytes(x[start..start + 4].try_into().unwrap()) as usize
                % TS::CUCKOO_LEN;
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
        all_entries: &[impl AsRef<[u8]>],
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
                log::info!("[{}/{}]", i, j_max);
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

    fn create_t1_table(l1: usize, file: &mut impl Write) -> std::io::Result<()> {
        let j_max = 1 << (l1 - 1);
        let cuckoo_len = (j_max as f64 * 1.3) as usize;

        let mut all_entries = vec![Default::default(); j_max + 1];

        log::info!("Computing all the points...");
        let mut acc = RistrettoPoint::identity().0;
        let step = RISTRETTO_BASEPOINT_POINT.0.mul_by_cofactor(); // table is based on number*cofactor
        for i in 0..=j_max {
            let point = acc; // i * G

            if i % (j_max / 1000 + 1) == 0 {
                log::info!("[{}/{}]", i, j_max);
            }

            let u = point.to_montgomery();
            let bytes = u.to_bytes();

            all_entries[i] = bytes;
            acc += step;
        }

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

        log::info!("Writing to file...");

        file.write_all(bytemuck::cast_slice(&t1_keys))?;
        file.write_all(bytemuck::cast_slice(&t1_values))?;

        log::info!("Done :)");
        Ok(())
    }

    fn create_t2_table(l1: usize, file: &mut impl Write) -> std::io::Result<()> {
        let i_max = (1 << (L2 - 1)) + 1;
        let two_to_l1 = EdwardsPoint::mul_base(&Scalar::from(1u32 << l1)); // 2^l1
        let two_to_l1 = two_to_l1.mul_by_cofactor(); // clear cofactor

        let mut arr = vec![
            T2MontgomeryCoordinates {
                u: Default::default(),
                v: Default::default()
            };
            i_max
        ];

        let mut acc = two_to_l1;
        for j in 1..i_max {
            let p = AffineMontgomeryPoint::from(&acc);
            let (u, v) = (p.u.as_bytes(), p.v.as_bytes());
            arr[j - 1] = T2MontgomeryCoordinates { u, v };
            acc += two_to_l1;
        }

        file.write_all(bytemuck::cast_slice(&arr)).unwrap();
        Ok(())
    }

    /// Generate the ECDLP precomputed tables file.
    pub fn create_combined_table(l1: usize, file: &mut impl Write) -> std::io::Result<()> {
        create_t2_table(l1, file)?;
        create_t1_table(l1, file)
    }
}
