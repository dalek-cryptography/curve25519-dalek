use core::{
    ops::ControlFlow,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::{
    backend::serial::u64::constants::MONTGOMERY_A,
    constants::{MONTGOMERY_A_NEG, RISTRETTO_BASEPOINT_POINT as G},
    field::FieldElement,
    traits::Identity,
    EdwardsPoint, RistrettoPoint, Scalar,
};
use bytemuck::{Pod, Zeroable};
use itertools::Itertools;

const L2: usize = 9; // corresponds to a batch size of 256 and a T2 table of a few Ko.
const BATCH_SIZE: usize = 1 << (L2 - 1);

const I_BITS: usize = L2 - 1;
const I_MAX: usize = (1 << I_BITS) + 1; // there needs to be one more element in T2

pub trait PrecomputedECDLPTables {
    const L1: usize;

    const J_BITS: usize = Self::L1 - 1;
    const J_MAX: usize = 1 << Self::J_BITS;

    const CUCKOO_LEN: usize = (Self::J_MAX as f64 * 1.3) as _;
    const CUCKOO_K: usize = 3;

    /// Hashmap <i * G => i | i in [1, 2^(l1-1)]>.
    /// Cuckoo hash table, each entry is 8 bytes long - but there are 1.3 times the needed slots.
    /// Total map size is then 1.3*8*2^(l1-1) bytes.
    /// The hashing function is just indexing the bytes of the point for efficiency.
    fn get_t1(&self) -> CuckooT1HashMapView<'_>;

    /// Linear map [j * 2^l1 * G] | j in [1, 2^(l2-1)].
    fn get_t2(&self) -> T2LinearTableView<'_>;
}

macro_rules! embed_t1_in_binary {
    (L1 = $L1:expr, PATH = $T1_PATH:expr) => {{
        // due to limitations in rustc there is no way to reuse these constants from the PrecomputedECDLPTables trait.
        const J_BITS: usize = $L1 - 1;
        const J_MAX: usize = 1 << J_BITS;
        const CUCKOO_LEN: usize = (J_MAX as f64 * 1.3) as _;

        // use ::curve25519_dalek::ecdlp as ecdlp;
        use crate::ecdlp as ecdlp;

        /// Hack to control the alignment of `include_bytes!`.
        #[repr(C, align(64))]
        struct IncludeBytesAlignHack<Bytes: ?Sized>(Bytes);

        #[repr(C)] // repr(C): layout must be stable across compilations.
        struct CuckooT1HashMap {
            keys: [u32; CUCKOO_LEN],
            values: [u32; CUCKOO_LEN],
        }

        const T1: &CuckooT1HashMap = {
            const T1_BYTE_LEN: usize = core::mem::size_of::<CuckooT1HashMap>();
            const ALIGNED: &IncludeBytesAlignHack<[u8; T1_BYTE_LEN]> =
                &IncludeBytesAlignHack(*include_bytes!($T1_PATH));

            // Safety:
            // * CuckooT1Table is two [u32; CUCKOO_LEN], so it can be considered Plain Old Data.
            // * alignment is handled through IncludeBytesAlignHack, and size is checked via the type system.
            // * lifetime is 'static in source and target
            // it do be looking ugly tho
            unsafe { core::mem::transmute(ALIGNED) }
        };

        ecdlp::CuckooT1HashMapView { keys: &T1.keys, values: &T1.values }
    }}
}
macro_rules! embed_t2_in_binary {
    ( PATH = $T2_PATH:expr) => {{
        // use ::curve25519_dalek::ecdlp as ecdlp;
        use crate::ecdlp;

        #[repr(C, align(64))]
        struct IncludeBytesAlignHack<Bytes: ?Sized>(Bytes);
        #[repr(C, align(64))]
        struct T2LinearTable([T2MontgomeryCoordinates; I_MAX]);

        const T2: &T2LinearTable = {
            const T2_BYTE_LEN: usize = core::mem::size_of::<T2LinearTable>();
            const ALIGNED: &IncludeBytesAlignHack<[u8; T2_BYTE_LEN]> =
                &IncludeBytesAlignHack(*include_bytes!($T2_PATH));

            // Safety: same safety argument as T1.
            unsafe { core::mem::transmute(ALIGNED) }
        };

        ecdlp::T2LinearTableView(&T2.0)
    }};
}

/// Canonical FieldElement type.
type CompressedFieldElement = [u8; 32];
#[derive(Clone, Copy)]
struct AffineMontgomeryPoint {
    u: FieldElement,
    v: FieldElement,
}

impl AffineMontgomeryPoint {
    fn addition_not_constant_time(&self, p2: &Self) -> AffineMontgomeryPoint {
        let p1 = self;
        if p1.u == FieldElement::ZERO && p1.v == FieldElement::ZERO {
            // p2 + P_inf = p2
            *p2
        } else if p2.u == FieldElement::ZERO && p2.v == FieldElement::ZERO {
            // p1 + P_inf = p1
            *p1
        } else if p1.u == p2.u && p1.v == -&p2.v {
            // p1 = -p2 = (u1, -v1), meaning p1 + p2 = P_inf
            AffineMontgomeryPoint {
                u: FieldElement::ZERO,
                v: FieldElement::ZERO,
            }
        } else {
            let lambda = if p1.u == p2.u {
                // doubling case

                // (3*u1^2 + 2*A*u1 + 1) / (2*v1)
                // todo this is ugly
                let u1_sq = p1.u.square();
                let u1_sq_3 = &(&u1_sq + &u1_sq) + &u1_sq;
                let u1_ta = &MONTGOMERY_A * &p1.u;
                let u1_ta_2 = &u1_ta + &u1_ta;
                let den = &p1.v + &p1.v;
                let num = &(&u1_sq_3 + &u1_ta_2) + &FieldElement::ONE;

                &num * &den.invert()
            } else {
                // (v1 - v2) / (u1 - u2)
                &(&p1.v - &p2.v) * &(&p1.u - &p2.u).invert()
            };

            // u3 = lambda^2 - A - u1 - u2
            // v3 = lambda * (u1 - u3) - v1
            let new_u = &(&lambda.square() - &MONTGOMERY_A) - &(&p1.u + &p2.u);
            let new_v = &(&lambda * &(&p1.u - &new_u)) - &p1.v;

            AffineMontgomeryPoint { u: new_u, v: new_v }
        }
    }
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

#[repr(C)]
#[derive(Clone, Copy, Default, Pod, Zeroable, Debug)]
pub struct T2MontgomeryCoordinates {
    pub u: CompressedFieldElement,
    pub v: CompressedFieldElement,
}

/// (u, v) Montgomery pairs.
pub struct T2LinearTableView<'a>(pub &'a [T2MontgomeryCoordinates]);

impl T2LinearTableView<'_> {
    fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let T2MontgomeryCoordinates { u, v } = self.0[index - 1];
        AffineMontgomeryPoint {
            u: FieldElement::from_bytes(&u),
            v: FieldElement::from_bytes(&v),
        }
    }
}

pub struct CuckooT1HashMapView<'a> {
    pub keys: &'a [u32],
    pub values: &'a [u32],
}

impl CuckooT1HashMapView<'_> {
    fn lookup<TS: PrecomputedECDLPTables>(
        &self,
        x: &[u8],
        mut is_problem_answer: impl FnMut(u64) -> bool,
    ) -> Option<u64> {
        for i in 0..TS::CUCKOO_K {
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

pub trait ProgressReportFunction {
    fn report(&self, progress: f64) -> ControlFlow<()>;
}
pub struct NoopReportFn;
impl ProgressReportFunction for NoopReportFn {
    #[inline(always)]
    fn report(&self, _progress: f64) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }
}
impl<F: Fn(f64) -> ControlFlow<()> + Send> ProgressReportFunction for F {
    #[inline(always)]
    fn report(&self, progress: f64) -> ControlFlow<()> {
        self(progress)
    }
}

pub struct ECDLPArguments<R: ProgressReportFunction = NoopReportFn> {
    range_start: i64,
    range_end: i64,
    pseudo_constant_time: bool,
    n_threads: usize,
    progress_report_function: R,
}

impl ECDLPArguments<NoopReportFn> {
    pub fn new_with_range(range_start: i64, range_end: i64) -> Self {
        Self {
            range_start,
            range_end,
            pseudo_constant_time: false,
            progress_report_function: NoopReportFn,
            n_threads: 1,
        }
    }
}

impl<F: ProgressReportFunction> ECDLPArguments<F> {
    pub fn best_effort_constant_time(self, pseudo_constant_time: bool) -> Self {
        Self {
            pseudo_constant_time,
            ..self
        }
    }

    pub fn progress_report_function<R: ProgressReportFunction>(
        self,
        progress_report_function: R,
    ) -> ECDLPArguments<R> {
        ECDLPArguments {
            progress_report_function,
            range_start: self.range_start,
            range_end: self.range_end,
            pseudo_constant_time: self.pseudo_constant_time,
            n_threads: self.n_threads,
        }
    }

    pub fn n_threads(self, n_threads: usize) -> Self {
        Self { n_threads, ..self }
    }
}

// #[cfg(feature = "std")]
// pub fn par_decode<TS: PrecomputedECDLPTables + Sync, R: ProgressReportFunction + Sync>(
//     precomputed_tables: &TS,
//     point: RistrettoPoint,
//     args: ECDLPArguments<R>,
// ) -> Option<i64> {
//     use alloc::vec::Vec;

//     let amplitude = (args.range_end.unwrap_or(1 << TS::L) - args.range_start).max(0);
//     if amplitude > (1 << TS::L) {
//         panic!(
//             "Precomputed table does not cover range of amplitude: {} (max: {})",
//             amplitude,
//             1 << TS::L
//         );
//     }

//     // Normalize the range into [-2^(L-1), 2^(L-1)[.
//     let offset = args.range_start + (amplitude / 2);
//     let normalized = &point - &i64_to_scalar(offset) * G;

//     let j_end = ((amplitude >> (TS::L1 + 1)) + 1) as usize; // amplitude / 2^(L1 + 1) + 1

//     // This will dispatch the j values evenly accross threads, in a batched way, so that
//     // if, for example we have n_threads=3, j_end=194 and BATCH_SIZE=64,
//     // we get: thread #0 gets batch_1 = 0..64 and batch_2 = 192..193,
//     // thread #1 batch_1 = 64..128
//     // thread #2 batch_1 = 128..192
//     // This allows small unknown numbers to get decoded faster when pseudo_constant_time is off.
//     //
//     // On top of that, we are counting from the end (.rev()) because since our range is normalized to the negatives,
//     // the true 0 will correspond the last J.
//     let batch_iterator = (0..j_end)
//         .step_by(BATCH_SIZE)
//         .enumerate()
//         .map(|(i, j)| {
//             let count = if j_end / BATCH_SIZE == i {
//                 j_end % BATCH_SIZE // last chunk
//             } else {
//                 BATCH_SIZE
//             };
//             // let batch = j..(j + count);
//             let progress = i as f64 / (j_end as f64 / BATCH_SIZE as f64);

//             (j, count, progress)
//         })
//         .rev();

//     let end_flag = AtomicBool::new(false);

//     let res = std::thread::scope(|s| {
//         let handles = (0..args.n_threads)
//             .map(|thread_i| {
//                 let thread_batch_iterator = batch_iterator
//                     .clone()
//                     .skip(thread_i)
//                     .step_by(args.n_threads);

//                 let end_flag = &end_flag;

//                 let progress_report = &args.progress_report_function;

//                 let progress_report = |progress| {
//                     if !args.pseudo_constant_time && end_flag.load(Ordering::SeqCst) {
//                         ControlFlow::Break(())
//                     } else {
//                         progress_report.report(progress)
//                     }
//                 };

//                 let handle = s.spawn(move || {
//                     let res = fast_ecdlp(
//                         precomputed_tables,
//                         normalized,
//                         thread_batch_iterator,
//                         -(args.n_threads as i64),
//                         args.pseudo_constant_time,
//                         &progress_report,
//                     );

//                     if !args.pseudo_constant_time && res.is_some() {
//                         end_flag.store(true, Ordering::SeqCst);
//                     }

//                     res
//                 });

//                 handle
//             })
//             .collect::<Vec<_>>();

//         let mut res = None;
//         for el in handles {
//             res = res.or(el.join().expect("child thread panicked"));
//         }

//         res
//     });

//     res.map(|v| v as i64 + offset)
// }

pub fn decode<TS: PrecomputedECDLPTables, R: ProgressReportFunction>(
    precomputed_tables: &TS,
    point: RistrettoPoint,
    args: ECDLPArguments<R>,
) -> Option<i64> {
    let amplitude = (args.range_end - args.range_start).max(0);

    let offset = args.range_start + ((1 << (L2 - 1)) << TS::L1) + (1 << (TS::L1 - 1));
    let normalized = &point - &i64_to_scalar(offset) * G;

    let j_end = (amplitude >> TS::L1) as usize; // amplitude / 2^(L1 + 1)

    let batch_n = (j_end + (1 << L2) - 1) / (1 << L2); // divceil(j_end, 2^NEW_L2)

    let batch_iterator = (0..batch_n).enumerate().map(|(i, j)| {
        let progress = i as f64 / batch_n as f64;
        (j * (1 << L2), progress)
    });

    fast_ecdlp(
        precomputed_tables,
        normalized,
        batch_iterator,
        -1,
        args.pseudo_constant_time,
        args.progress_report_function,
    )
    .map(|v| v as i64 + offset)
}

fn fast_ecdlp<TS: PrecomputedECDLPTables>(
    precomputed_tables: &TS,
    target_point: RistrettoPoint,
    j_batch_iterator: impl Iterator<Item = (usize, f64)>,
    batch_step: i64,
    pseudo_constant_time: bool,
    progress_report: impl ProgressReportFunction,
) -> Option<u64> {
    // convert to montgomery (u, v) affine coordinates
    let mut target_montgomery = AffineMontgomeryPoint::from(&target_point.0);
    let batch_step = batch_step * (1 << TS::L1) * (1 << L2);
    let batch_step_montgomery = AffineMontgomeryPoint::from(&(i64_to_scalar(batch_step) * G).0);

    let t1_table = precomputed_tables.get_t1();
    let t2_table = precomputed_tables.get_t2();

    let mut found = None;
    let mut consider_candidate = |m| {
        if i64_to_scalar(m) * G == target_point {
            found = found.or(Some(m as u64));
            true
        } else {
            false
        }
    };

    let mut batch = [FieldElement::ZERO; BATCH_SIZE];
    'outer: for (j_start, progress) in j_batch_iterator {
        if let ControlFlow::Break(_) = progress_report.report(progress) {
            break 'outer;
        }

        // Case 0: target is 0. Has to be handled separately.
        if target_montgomery.u == FieldElement::ZERO {
            consider_candidate((j_start as i64) << TS::L1);
            if !pseudo_constant_time {
                break 'outer;
            }
        }

        // Case 2: j=0. Has to be handled separately.
        if t1_table
            .lookup::<TS>(&target_montgomery.u.as_bytes(), |i| {
                consider_candidate(((j_start as i64) << TS::L1) + i as i64)
                    || consider_candidate(((j_start as i64) << TS::L1) - i as i64)
            })
            .is_some()
        {
            if !pseudo_constant_time {
                break 'outer;
            }
        }

        // Z = T2[j]_x - Pm_x
        for batch_i in 0..BATCH_SIZE {
            let j = batch_i + 1;
            let t2_point = t2_table.index(j as _);
            let diff = &t2_point.u - &target_montgomery.u;

            if diff == FieldElement::ZERO {
                // Case 1: (Montgomery addition) exceptional case when T2[j] = Pm.
                // m1 = j * 2^L1, m2 = -j * 2^L1
                let found = consider_candidate((j_start as i64 + j as i64) << TS::L1)
                    || consider_candidate((j_start as i64 - j as i64) << TS::L1);
                if !pseudo_constant_time && found {
                    break 'outer;
                }
            }
            batch[batch_i] = diff;
        }

        // nu = Z^-1
        FieldElement::batch_invert(&mut batch);

        for (batch_i, nu) in batch.iter().enumerate() {
            let j = batch_i + 1;
            // Montgomery addition: general case

            let t2_point = t2_table.index(j as _);

            let alpha = &(&MONTGOMERY_A_NEG - &t2_point.u) - &target_montgomery.u;

            // lambda = (T2[j]_y - Pm_y) * nu
            // Q_x = lambda^2 - A - T2[j]_x - Pm_x
            let lambda = &(&t2_point.v - &target_montgomery.v) * &nu;
            let qx = &lambda.square() + &alpha;

            // Case 3: general case, negative j.
            if t1_table
                .lookup::<TS>(&qx.as_bytes(), |i| {
                    consider_candidate(((j_start as i64 - j as i64) << TS::L1) + i as i64)
                        || consider_candidate(((j_start as i64 - j as i64) << TS::L1) - i as i64)
                })
                .is_some()
            {
                // m1 = -j * 2^L1 + i, m2 = -j * 2^L1 - i
                if !pseudo_constant_time {
                    break 'outer;
                }
            }

            // lambda = (p - T2[j]_y - Pm_y) * nu
            // Q_x = lambda^2 - A - T2[j]_x - Pm_x
            let lambda = &(&-&t2_point.v - &target_montgomery.v) * &nu;
            let qx = &lambda.square() + &alpha;

            // Case 4: general case, positive j.
            if t1_table
                .lookup::<TS>(&qx.as_bytes(), |i| {
                    consider_candidate(((j_start as i64 + j as i64) << TS::L1) + i as i64)
                        || consider_candidate(((j_start as i64 + j as i64) << TS::L1) - i as i64)
                })
                .is_some()
            {
                // m1 = j * 2^L1 + i, m2 = j * 2^L1 - i
                if !pseudo_constant_time {
                    break 'outer;
                }
            }
        }

        // Move the target point by the batch step.
        target_montgomery = AffineMontgomeryPoint::addition_not_constant_time(
            &target_montgomery,
            &batch_step_montgomery,
        );
    }

    found
}

#[cfg(feature = "precompute_table_gen")]
mod table_generation {
    use std::{fs::File, io::Write};

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
                println!("[{}/{}]", i, j_max);
            }

            for j in 0..CUCKOO_MAX_INSERT_SWAPS {
                let x = all_entries[v as usize].as_ref();
                let start = (old_hash_id as usize - 1) * 8;
                let end = start as usize + 4;
                let mut key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
                let h1 = u32::from_be_bytes(x[start..start + 4].try_into().unwrap()) as usize;
                let h = u32::from_be_bytes(x[start..start + 4].try_into().unwrap()) as usize
                    % cuckoo_len;

                if hash_index[h] == 0 {
                    // println!("Putting {:?} [{} - {h1}] => {}", x, h, v);
                    hash_index[h] = old_hash_id;
                    t1_values[h] = v;
                    t1_keys[h] = key;
                    break;
                } else {
                    // println!(
                    //     "Swapping {:?} [{} - {h1}] for {} (swap #{}) -- {cuckoo_len}",
                    //     x,
                    //     h,
                    //     v,
                    //     j + 1
                    // );
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

    pub fn create_t1_table(l1: usize, file: &mut File) {
        let j_max = 1 << (l1 - 1);
        let cuckoo_len = (j_max as f64 * 1.3) as usize;

        let mut all_entries = vec![Default::default(); j_max + 1];

        println!("Computing all the points...");
        let mut acc = RistrettoPoint::identity();
        for i in 0..=j_max {
            let point = acc; // i * G

            if i % (j_max / 1000 + 1) == 0 {
                println!("[{}/{}]", i, j_max);
            }

            let u = point.0.to_montgomery();
            let bytes = u.to_bytes();

            all_entries[i] = bytes;
            acc += G;
        }

        let mut t1_keys = vec![0u32; cuckoo_len];
        let mut t1_values = vec![0u32; cuckoo_len];

        println!("Setting up the cuckoo hashmap...");
        t1_cuckoo_setup(
            cuckoo_len,
            j_max,
            &all_entries,
            &mut t1_values,
            &mut t1_keys,
        );

        println!("Writing to file...");

        file.write_all(bytemuck::cast_slice(&t1_keys)).unwrap();
        file.write_all(bytemuck::cast_slice(&t1_values)).unwrap();

        println!("Done :)")
    }

    pub fn create_t2_table(l1: usize, file: &mut File) {
        use crate::traits::Identity;
        let i_max = (1 << (L2 - 1)) + 1;
        let two_to_l1 = EdwardsPoint::mul_base(&Scalar::from(1u32 << l1)); // 2^l1

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
            // println!("{j} * 2^l1 * G = {u:?} {v:?}");
            arr[j - 1] = T2MontgomeryCoordinates { u, v };
            acc += two_to_l1;
        }

        file.write_all(bytemuck::cast_slice(&arr)).unwrap();
    }
}

// TODO: should be an impl From<i64> for Scalar
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
    fn gen_t1_t2() {
        use std::fs::File;
        // let l1 = 25;
        // let l2 = 48 - l1;

        let l1 = 26;
        table_generation::create_t1_table(l1, &mut File::create(format!("t1_{l1}.bin")).unwrap());
        table_generation::create_t2_table(l1, &mut File::create(format!("t2_{l1}.bin")).unwrap())
    }

    #[cfg(not(feature = "precompute_table_gen"))]
    const T1: CuckooT1HashMapView<'static> = embed_t1_in_binary! { L1 = 8, PATH = "../t1_8.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    const T2: T2LinearTableView<'static> = embed_t2_in_binary! { PATH = "../t2_8.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    struct ECDLPTables16L8;
    #[cfg(not(feature = "precompute_table_gen"))]
    impl PrecomputedECDLPTables for ECDLPTables16L8 {
        const L1: usize = 8;

        fn get_t1(&self) -> CuckooT1HashMapView<'_> {
            T1
        }
        fn get_t2(&self) -> T2LinearTableView<'_> {
            T2
        }
    }

    #[cfg(not(feature = "precompute_table_gen"))]
    const T1_3: CuckooT1HashMapView<'static> = embed_t1_in_binary! { L1 = 3, PATH = "../t1_3.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    const T2_3: T2LinearTableView<'static> = embed_t2_in_binary! { PATH = "../t2_3.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    struct ECDLPTables16L3;
    #[cfg(not(feature = "precompute_table_gen"))]
    impl PrecomputedECDLPTables for ECDLPTables16L3 {
        const L1: usize = 3;

        fn get_t1(&self) -> CuckooT1HashMapView<'_> {
            T1_3
        }
        fn get_t2(&self) -> T2LinearTableView<'_> {
            T2_3
        }
    }

    #[test]
    #[cfg(not(feature = "precompute_table_gen"))]
    fn test_fast_ecdlp() {
        for i in 0..(1 << 16) {
            assert_eq!(
                Some(i as i64),
                decode(
                    &ECDLPTables16L8,
                    Scalar::from(i as u64) * G,
                    ECDLPArguments::new_with_range(0, 1 << 16).best_effort_constant_time(true),
                )
            );
        }
    }

    #[test]
    #[cfg(not(feature = "precompute_table_gen"))]
    fn test_fast_ecdlp_16l3() {
        // for i in [31411, 33459] {
        for i in 0..(1 << 16) {
            println!(
                "{:?} {:?}",
                // assert_eq!(
                Some(i as i64),
                decode(
                    &ECDLPTables16L3,
                    Scalar::from(i as u64) * G,
                    ECDLPArguments::new_with_range(0, 1 << 16).best_effort_constant_time(true),
                )
            );
        }
    }

    #[cfg(not(feature = "precompute_table_gen"))]
    const T1_22: CuckooT1HashMapView<'static> =
        embed_t1_in_binary! { L1 = 22, PATH = "../t1_22.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    const T2_22: T2LinearTableView<'static> = embed_t2_in_binary! { PATH = "../t2_22.bin" };
    #[cfg(not(feature = "precompute_table_gen"))]
    struct ECDLPTables22L10;
    #[cfg(not(feature = "precompute_table_gen"))]
    impl PrecomputedECDLPTables for ECDLPTables22L10 {
        const L1: usize = 22;

        fn get_t1(&self) -> CuckooT1HashMapView<'_> {
            T1_22
        }
        fn get_t2(&self) -> T2LinearTableView<'_> {
            T2_22
        }
    }

    #[cfg(not(feature = "precompute_table_gen"))]
    #[test]
    fn test_fast_ecdlp_22l32() {
        for i in (0..(1 << 32)).step_by(1 << 6) {
            if i % (1 << 14) == 0 {
                println!("Testing {}", i);
            }
            assert_eq!(
                Some(i),
                decode(
                    &ECDLPTables22L10,
                    Scalar::from(i as u64) * G,
                    ECDLPArguments::new_with_range(0, 1 << 32),
                )
            );
        }
    }

    use proptest::prelude::*;
    #[cfg(not(feature = "precompute_table_gen"))]
    proptest! {
        #[test]
        fn test_pt_fast_ecdlp_22l32(i in 0i64..4294967296i64) {
            println!("Testing {}", i);
            assert_eq!(
                Some(i),
                decode(
                    &ECDLPTables22L10,
                    Scalar::from(i as u64) * G,
                    ECDLPArguments::new_with_range(0, 1 << 32),
                )
            );
        }
    }

    // #[test]
    // #[cfg(not(feature = "precompute_table_gen"))]
    // fn test_par_decode() {
    //     for i in 0..(1u64 << ECDLPTables16L8::L) {
    //         assert_eq!(
    //             Some(i as i64),
    //             par_decode(
    //                 &ECDLPTables16L8,
    //                 Scalar::from(i) * G,
    //                 ECDLPArguments::default()
    //                     .best_effort_constant_time(true)
    //                     .n_threads(4)
    //             )
    //         );
    //     }
    // }

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
