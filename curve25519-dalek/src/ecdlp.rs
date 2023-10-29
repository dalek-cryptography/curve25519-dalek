use crate::traits::Identity;
use crate::{
    backend::serial::u64::constants::MONTGOMERY_A_NEG, constants::RISTRETTO_BASEPOINT_POINT as G,
    field::FieldElement, EdwardsPoint, RistrettoPoint, Scalar,
};
use itertools::Itertools;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

pub const L: usize = 40;
pub const L1: usize = 26;
pub const L2: usize = L - L1;

const I_BITS: usize = L2 - 1;
const I_MAX: usize = 1 << I_BITS + 1; // there needs to be one more element in T2

const J_BITS: usize = L1 - 1;
const J_MAX: usize = 1 << J_BITS;

const CUCKOO_LEN: usize = (J_MAX as f64 * 1.3) as _;
const CUCKOO_K: usize = 3;

const BATCH_SIZE: usize = 256;

/// Hack to control the alignment of `include_bytes!`.
#[repr(align(64))]
struct IncludeBytesAlignHack<Bytes: ?Sized>(Bytes);

/// Hashmap <i * G => i | i in [1, 2^(l1-1)]>.
/// Cuckoo hash table, each entry is 8 bytes long - but there are 1.3 times the needed slots.
/// Total map size is then 1.3*8*2^(l1-1) bytes.
/// The hashing function is just indexing the bytes of the point for efficiency.
#[cfg(not(feature = "precompute_table_gen"))]
const T1: &CuckooT1HashMap = {
    const T1_BYTE_LEN: usize = core::mem::size_of::<CuckooT1HashMap>();
    const ALIGNED: &IncludeBytesAlignHack<[u8; T1_BYTE_LEN]> =
        &IncludeBytesAlignHack(*include_bytes!("t1.bin"));

    // Safety:
    // * CuckooT1Table is two [u32; CUCKOO_LEN], so it can be considered Plain Old Data.
    // * alignment is handled through IncludeBytesAlignHack, and size is checked via the type system.
    // * lifetime is 'static in source and target
    // it do be looking ugly tho
    unsafe { core::mem::transmute(ALIGNED) }
};

/// Linear map [j * 2^l1 * G] | j in [1, 2^(l2-1)].
#[cfg(not(feature = "precompute_table_gen"))]
const T2: &T2LinearTable = {
    const T2_BYTE_LEN: usize = core::mem::size_of::<T2LinearTable>();
    const ALIGNED: &IncludeBytesAlignHack<[u8; T2_BYTE_LEN]> =
        &IncludeBytesAlignHack(*include_bytes!("t2.bin"));

    // Safety: same safety argument as T1.
    unsafe { core::mem::transmute(ALIGNED) }
};

type CompressedFieldElement = [u8; 32];

/// (X, Y) pairs.
#[repr(C, align(64))] // repr(C): layout must be stable across compilations.
struct T2LinearTable([(CompressedFieldElement, CompressedFieldElement); I_MAX]);

impl T2LinearTable {
    fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let (u, v) = self.0[index];
        AffineMontgomeryPoint {
            u: FieldElement::from_bytes(&u),
            v: FieldElement::from_bytes(&v),
        }
    }
}

#[derive(Clone, Copy)]
struct AffineMontgomeryPoint {
    u: FieldElement,
    v: FieldElement,
}

impl From<&'_ EdwardsPoint> for AffineMontgomeryPoint {
    #[allow(non_snake_case)]
    fn from(eddy: &EdwardsPoint) -> Self {
        let ALPHA = FieldElement::from_bytes(&[
            6, 126, 69, 255, 170, 4, 110, 204, 130, 26, 125, 75, 209, 211, 161, 197, 126, 79, 252,
            3, 220, 8, 123, 210, 187, 6, 160, 96, 244, 237, 38, 15,
        ]);
        // u = (1+y)/(1-y) = (Z+Y)/(Z-Y),
        // v = (1+y)/(x(1-y)) * alpha = (Z+Y)/(X-T) * alpha.
        //  where alpha is a constant https://ristretto.group/details/isogenies.html.
        let Z_plus_Y = &eddy.Z + &eddy.Y;
        let Z_minus_Y = &eddy.Z - &eddy.Y;
        let X_minus_T = &eddy.X - &eddy.T;
        AffineMontgomeryPoint {
            u: &Z_plus_Y * &Z_minus_Y.invert(),
            v: &(&Z_plus_Y * &X_minus_T.invert()) * &ALPHA,
        }
    }
}

#[repr(C, align(64))] // repr(C): layout must be stable across compilations.
struct CuckooT1HashMap {
    keys: [u32; CUCKOO_LEN],
    values: [u32; CUCKOO_LEN],
}

impl CuckooT1HashMap {
    fn lookup(&self, x: &[u8]) -> Option<u64> {
        // println!("Lookup {x:?}");
        for i in 0..CUCKOO_K {
            let start = i * 8;
            let end = start + 4;
            let key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
            let h = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize % CUCKOO_LEN;
            if self.keys[h as usize] == key {
                return Some(self.values[h as usize] as u64);
            }
        }
        None
    }

    #[cfg(feature = "precompute_table_gen")]
    fn setup(&mut self, all_entries: &[impl AsRef<[u8]>]) {
        use core::mem::swap;

        /// Dumb cuckoo rehashing threshold.
        const CUCKOO_MAX_INSERT_SWAPS: usize = 500;

        let mut hash_index = vec![0u8; CUCKOO_LEN];

        for i in 1..=J_MAX {
            let mut v = i as _;
            let mut old_hash_id = 1u8;

            for j in 0..CUCKOO_MAX_INSERT_SWAPS {
                let x = all_entries[v as usize - 1].as_ref();
                let start = (old_hash_id as usize - 1) * 8;
                let end = start as usize + 4;
                let mut key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
                let h1 = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize;
                let h = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize % CUCKOO_LEN;

                if hash_index[h] == 0 {
                    println!("Putting {:?} [{} - {h1}] => {}", x, h, v);
                    hash_index[h] = old_hash_id;
                    self.values[h] = v;
                    self.keys[h] = key;
                    break;
                } else {
                    println!(
                        "Swapping {:?} [{} - {h1}] for {} (swap #{}) -- {CUCKOO_LEN}",
                        x,
                        h,
                        v,
                        j + 1
                    );
                    swap(&mut old_hash_id, &mut hash_index[h]);
                    swap(&mut v, &mut self.values[h]);
                    swap(&mut key, &mut self.keys[h]);
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
}

#[cfg(not(feature = "precompute_table_gen"))]
pub fn decode(
    point: RistrettoPoint,
    range_start: i64,
    range_end: i64,
    pseudo_constant_time: bool,
) -> Option<i64> {
    let amplitude = (range_end - range_start).max(0);
    if amplitude > (1 << L) {
        panic!(
            "Precomputed table does not cover range of amplitude: {} (max: {})",
            amplitude,
            1 << L
        );
    }

    // Normalize the range into [-2^(L-1), 2^(L-1)[.
    let offset = range_start + (amplitude / 2);
    let normalized = &point - &i64_to_scalar(offset) * G;

    let j_end = (amplitude >> (L1 + 1)) + 1; // amplitude / 2^(L1 + 1) + 1

    fast_ecdlp(normalized, 0, j_end as _, 1, pseudo_constant_time).map(|v| v as i64 + offset)
}

#[cfg(not(feature = "precompute_table_gen"))]
fn fast_ecdlp(
    target_point: RistrettoPoint,
    j_start: u64,
    j_end: u64,
    chunk_step: usize,
    pseudo_constant_time: bool,
) -> Option<u64> {
    // convert to montgomery (u, v) affine coordinates
    let target_montgomery = AffineMontgomeryPoint::from(&target_point.0);

    let mut found_m1_m2 = None;

    let into_chunks = (j_start..j_end).chunks(BATCH_SIZE);
    let chunks = into_chunks.into_iter();

    let mut batch = [FieldElement::ONE; BATCH_SIZE];
    let mut batch_j = [0u64; BATCH_SIZE];
    'outer: for chunk in chunks.step_by(chunk_step) {
        // Z = T2[j]_x - Pm_x
        let mut b_item_count = 0;
        for (batch_index, j) in chunk.enumerate() {
            let t2_point = T2.index(j as _);
            let diff = &t2_point.u - &target_montgomery.u;
            if diff == FieldElement::ZERO {
                // Montgomery substraction: exceptional case when T2[j] = Pm.
                // Also catches the exceptional case when Pm is the identity.
                // m1 = j * 2^L1, m2 = -j * 2^L1
                found_m1_m2 = found_m1_m2.or(Some((((j as i64) << L1), (-(j as i64) << L1))));
                if !pseudo_constant_time {
                    break 'outer;
                }
            }
            batch[batch_index] = diff;
            batch_j[batch_index] = j;
            b_item_count += 1usize;
        }

        // nu = Z^-1
        FieldElement::batch_invert(&mut batch);

        for (&j, nu) in batch_j.iter().zip(batch.iter()).take(b_item_count) {
            if j == 0 {
                // Montgomery substraction: exceptional case when t2_point is the identity

                if let Some(i) = T1.lookup(&target_montgomery.u.as_bytes()) {
                    found_m1_m2 = found_m1_m2.or(Some((
                        (-(j as i64) << L1) + i as i64,
                        (-(j as i64) << L1) - i as i64,
                    )));
                    if !pseudo_constant_time {
                        break 'outer;
                    }
                }
            } else {
                // Montgomery substraction: general case

                let t2_point = T2.index(j as _);

                let alpha = &(&MONTGOMERY_A_NEG - &t2_point.u) - &target_montgomery.u;

                // lambda = (T2[j]_y - Pm_y) * nu
                // Q_x = lambda^2 - A - T2[j]_x - Pm_x
                let lambda = &(&t2_point.v - &target_montgomery.v) * &nu;
                let qx = &lambda.square() + &alpha;

                if let Some(i) = T1.lookup(&qx.as_bytes()) {
                    // m1 = -j * 2^L1 + i, m2 = -j * 2^L1 - i
                    found_m1_m2 = found_m1_m2.or(Some((
                        (-(j as i64) << L1) + i as i64,
                        (-(j as i64) << L1) - i as i64,
                    )));
                    if !pseudo_constant_time {
                        break 'outer;
                    }
                }

                // lambda = (p - T2[j]_y - Pm_y) * nu
                // Q_x = lambda^2 - A - T2[j]_x - Pm_x
                let lambda = &(&-&t2_point.v - &target_montgomery.v) * &nu;
                let qx = &lambda.square() + &alpha;

                if let Some(i) = T1.lookup(&qx.as_bytes()) {
                    // m1 = j * 2^L1 + i, m2 = j * 2^L1 - i
                    found_m1_m2 = found_m1_m2.or(Some((
                        ((j as i64) << L1) + i as i64,
                        ((j as i64) << L1) - i as i64,
                    )));
                    if !pseudo_constant_time {
                        break 'outer;
                    }
                }
            }
        }
    }

    found_m1_m2.map(|(m1, m2)| {
        // select between m1 or m2
        ConditionallySelectable::conditional_select(
            &m1,
            &m2,
            (i64_to_scalar(m2) * G).ct_eq(&target_point),
        ) as u64
    })
}

#[cfg(feature = "precompute_table_gen")]
fn create_t1_table() -> alloc::boxed::Box<CuckooT1HashMap> {
    let mut all_entries = vec![Default::default(); J_MAX];

    let mut acc = G;
    for i in 1..=J_MAX {
        let point = acc; // i * G

        let u = point.0.to_montgomery();
        let bytes = u.to_bytes();

        all_entries[i - 1] = bytes;
        acc += G;
    }

    // let mut t1 = alloc::boxed::Box::new(CuckooT1HashMap {
    //     keys: [0; CUCKOO_LEN],
    //     values: [0; CUCKOO_LEN],
    // }); // stack overflow because rust doesnt do placement new :(

    let mut t1 = vec![0u8; core::mem::size_of::<CuckooT1HashMap>()];
    let mut b = t1.into_boxed_slice();
    let mut t1 =
    unsafe { alloc::boxed::Box::<CuckooT1HashMap>::from_raw(alloc::boxed::Box::leak(b).as_mut_ptr().cast()) };

    t1.setup(&all_entries);
    t1
}

#[cfg(feature = "precompute_table_gen")]
fn create_t2_table() -> alloc::boxed::Box<T2LinearTable> {
    use crate::traits::Identity;

    let two_to_l1 = EdwardsPoint::mul_base(&Scalar::from(1u32 << L1)); // 1^l1

    let mut arr = vec![(Default::default(), Default::default()); I_MAX];

    let mut acc = EdwardsPoint::identity();
    for j in 0..I_MAX {
        let p = AffineMontgomeryPoint::from(&acc);
        let (u, v) = (p.u.as_bytes(), p.v.as_bytes());

        // println!("Putting {j} => {u:?} {v:?}");

        println!("{j} * 2^l1 * G = {u:?} {v:?}");

        arr[j] = (u, v);
        acc += two_to_l1;
    }

    let mut b = arr.into_boxed_slice();

    unsafe { alloc::boxed::Box::from_raw(alloc::boxed::Box::leak(b).as_mut_ptr().cast()) }
}

fn i64_to_scalar(n: i64) -> Scalar {
    if n >= 0 {
        Scalar::from(n as u64)
    } else {
        -&Scalar::from((-n) as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::constants::MONTGOMERY_A;

    #[test]
    #[cfg(feature = "precompute_table_gen")]
    fn gen_t2() {
        let t2 = create_t2_table();

        let bytes: alloc::boxed::Box<[u8; core::mem::size_of::<T2LinearTable>()]> =
            unsafe { core::mem::transmute(t2) };

        use std::{fs::File, io::Write, path::PathBuf};
        let mut f = File::create(PathBuf::from("src/t2.bin")).unwrap();
        f.write_all(bytes.as_ref()).unwrap();

        println!("Done :)");
    }

    #[test]
    #[cfg(feature = "precompute_table_gen")]
    fn gen_t1() {
        let t1 = create_t1_table();

        let bytes: alloc::boxed::Box<[u8; core::mem::size_of::<CuckooT1HashMap>()]> =
            unsafe { core::mem::transmute(t1) };

        use std::{fs::File, io::Write, path::PathBuf};
        let mut f = File::create(PathBuf::from("src/t1.bin")).unwrap();
        f.write_all(bytes.as_ref()).unwrap();

        println!("Done :)");
    }

    #[test]
    #[cfg(feature = "precompute_table_gen")]
    fn gen_t1_t2() {
        gen_t1();
        gen_t2();
    }

    #[test]
    #[cfg(not(feature = "precompute_table_gen"))]
    fn test_fast_ecdlp() {
        fn decode_(num: u64) -> Option<i64> {
            decode(Scalar::from(num) * G, 0, 1 << L, true)
            // fast_ecdlp(Scalar::from(num) * G, 0, J_MAX, chunk_step)
        }

        for i in 0..(1 << L) {
            println!("Running {i:?}");
            assert_eq!(Some(i as i64), decode_(i));
        }
    }

    #[test]
    fn test_const_alpha() {
        let alpha = FieldElement::from_bytes(&[
            6, 126, 69, 255, 170, 4, 110, 204, 130, 26, 125, 75, 209, 211, 161, 197, 126, 79, 252,
            3, 220, 8, 123, 210, 187, 6, 160, 96, 244, 237, 38, 15,
        ]);

        // Constant comes from https://ristretto.group/details/isogenies.html (birational mapping from E2 = E_(a2,d2) to M_(B,A))
        // alpha = sqrt((A + 2) / (B * a_2)) with B = 1 and a_2 = -1.
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let (is_sq, v) =
            FieldElement::sqrt_ratio_i(&(&MONTGOMERY_A + &two), &FieldElement::MINUS_ONE);
        assert!(bool::from(is_sq));

        assert_eq!(alpha.as_bytes(), v.as_bytes());
    }
}
