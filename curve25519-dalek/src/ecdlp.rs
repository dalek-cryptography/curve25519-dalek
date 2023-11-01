use core::{
    ops::ControlFlow,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::{
    constants::{MONTGOMERY_A_NEG, RISTRETTO_BASEPOINT_POINT as G},
    field::FieldElement,
    EdwardsPoint, RistrettoPoint, Scalar,
};
use bytemuck::{Pod, Zeroable};
use itertools::Itertools;

pub trait PrecomputedECDLPTables {
    const L: usize;
    const L1: usize;
    const L2: usize = Self::L - Self::L1;

    const I_BITS: usize = Self::L2 - 1;
    const I_MAX: usize = (1 << Self::I_BITS) + 1; // there needs to be one more element in T2

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
    (L = $L:expr, L1 = $L1:expr, PATH = $T1_PATH:expr) => {{
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
    (L = $L:expr, L1 = $L1:expr, PATH = $T2_PATH:expr) => {{
        const L2: usize = $L - $L1;
        const I_BITS: usize = L2 - 1;
        const I_MAX: usize = (1 << I_BITS) + 1;

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

const BATCH_SIZE: usize = 256;

/// Canonical FieldElement type.
type CompressedFieldElement = [u8; 32];
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

#[repr(C)]
#[derive(Clone, Copy, Default, Pod, Zeroable)]
pub struct T2MontgomeryCoordinates {
    pub u: CompressedFieldElement,
    pub v: CompressedFieldElement,
}

/// (u, v) Montgomery pairs.
pub struct T2LinearTableView<'a>(pub &'a [T2MontgomeryCoordinates]);

impl T2LinearTableView<'_> {
    fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let T2MontgomeryCoordinates { u, v } = self.0[index];
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
    fn lookup<TS: PrecomputedECDLPTables>(&self, x: &[u8]) -> Option<u64> {
        for i in 0..TS::CUCKOO_K {
            let start = i * 8;
            let end = start + 4;
            let key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
            let h = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize % TS::CUCKOO_LEN;
            if self.keys[h as usize] == key {
                return Some(self.values[h as usize] as u64);
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
    range_end: Option<i64>,
    pseudo_constant_time: bool,
    n_threads: usize,
    progress_report_function: R,
}

impl Default for ECDLPArguments<NoopReportFn> {
    fn default() -> Self {
        Self {
            range_start: 0,
            range_end: None,
            pseudo_constant_time: false,
            progress_report_function: NoopReportFn,
            n_threads: 1,
        }
    }
}

impl<F: ProgressReportFunction> ECDLPArguments<F> {
    pub fn decode_range(self, range_start: i64, range_end: i64) -> Self {
        Self {
            range_start,
            range_end: Some(range_end),
            ..self
        }
    }

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

#[cfg(feature = "std")]
pub fn par_decode<TS: PrecomputedECDLPTables + Sync, R: ProgressReportFunction + Sync>(
    precomputed_tables: &TS,
    point: RistrettoPoint,
    args: ECDLPArguments<R>,
) -> Option<i64> {
    use alloc::vec::Vec;

    let amplitude = (args.range_end.unwrap_or(1 << TS::L) - args.range_start).max(0);
    if amplitude > (1 << TS::L) {
        panic!(
            "Precomputed table does not cover range of amplitude: {} (max: {})",
            amplitude,
            1 << TS::L
        );
    }

    // Normalize the range into [-2^(L-1), 2^(L-1)[.
    let offset = args.range_start + (amplitude / 2);
    let normalized = &point - &i64_to_scalar(offset) * G;

    let j_end = ((amplitude >> (TS::L1 + 1)) + 1) as usize; // amplitude / 2^(L1 + 1) + 1

    // This will dispatch the j values evenly accross threads, in a batched way, so that
    // if, for example we have n_threads=3, j_end=194 and BATCH_SIZE=64,
    // we get: thread #0 gets batch_1 = 0..64 and batch_2 = 192..193,
    // thread #1 batch_1 = 64..128
    // thread #2 batch_1 = 128..192
    // This allows small unknown numbers to get decoded faster when pseudo_constant_time is off.
    // 
    // On top of that, we are counting from the end (.rev()) because since our range is normalized to the negatives,
    // the true 0 will correspond the last J.
    let batch_iterator = (0..j_end).step_by(BATCH_SIZE).enumerate().map(|(i, j)| {
        let batch = (j..(j + BATCH_SIZE)).take(if j_end / BATCH_SIZE == i {
            j_end % BATCH_SIZE // last chunk
        } else {
            BATCH_SIZE
        });
        let progress = i as f64 / (j_end as f64 / BATCH_SIZE as f64);

        (batch, progress)
    }).rev();

    let end_flag = AtomicBool::new(false);

    let res = std::thread::scope(|s| {
        let handles = (0..args.n_threads)
            .map(|thread_i| {
                let thread_batch_iterator = batch_iterator
                    .clone()
                    .skip(thread_i)
                    .step_by(args.n_threads);

                let end_flag = &end_flag;

                let progress_report = &args.progress_report_function;

                let progress_report = |progress| {
                    if !args.pseudo_constant_time && end_flag.load(Ordering::SeqCst) {
                        ControlFlow::Break(())
                    } else {
                        progress_report.report(progress)
                    }
                };

                let handle = s.spawn(move || {
                    let res = fast_ecdlp(
                        precomputed_tables,
                        normalized,
                        thread_batch_iterator,
                        args.pseudo_constant_time,
                        &progress_report,
                    );

                    if !args.pseudo_constant_time && res.is_some() {
                        end_flag.store(true, Ordering::SeqCst);
                    }

                    res
                });

                handle
            })
            .collect::<Vec<_>>();

        let mut res = None;
        for el in handles {
            res = res.or(el.join().expect("child thread panicked"));
        }

        res
    });

    res.map(|v| v as i64 + offset)
}

pub fn decode<TS: PrecomputedECDLPTables, R: ProgressReportFunction>(
    precomputed_tables: &TS,
    point: RistrettoPoint,
    args: ECDLPArguments<R>,
) -> Option<i64> {
    let amplitude = (args.range_end.unwrap_or(1 << TS::L) - args.range_start).max(0);
    if amplitude > (1 << TS::L) {
        panic!(
            "Precomputed table does not cover range of amplitude: {} (max: {})",
            amplitude,
            1 << TS::L
        );
    }

    // Normalize the range into [-2^(L-1), 2^(L-1)[.
    let offset = args.range_start + (amplitude / 2);
    let normalized = &point - &i64_to_scalar(offset) * G;

    let j_end = ((amplitude >> (TS::L1 + 1)) + 1) as usize; // amplitude / 2^(L1 + 1) + 1

    let batch_iterator = (0..j_end).step_by(BATCH_SIZE).enumerate().map(|(i, j)| {
        let count = if j_end / BATCH_SIZE == i {
            j_end % BATCH_SIZE // last chunk
        } else {
            BATCH_SIZE
        };
        let batch = j..(j + count);
        let progress = i as f64 / (j_end as f64 / BATCH_SIZE as f64);

        (batch, progress)
    }).rev();

    fast_ecdlp(
        precomputed_tables,
        normalized,
        batch_iterator,
        args.pseudo_constant_time,
        args.progress_report_function,
    )
    .map(|v| v as i64 + offset)
}

fn fast_ecdlp<TS: PrecomputedECDLPTables>(
    precomputed_tables: &TS,
    target_point: RistrettoPoint,
    j_batch_iterator: impl Iterator<Item = (impl Iterator<Item = usize>, f64)>,
    pseudo_constant_time: bool,
    progress_report: impl ProgressReportFunction,
) -> Option<u64> {
    // convert to montgomery (u, v) affine coordinates
    let target_montgomery = AffineMontgomeryPoint::from(&target_point.0);

    let t1_table = precomputed_tables.get_t1();
    let t2_table = precomputed_tables.get_t2();

    let mut found = None;
    let mut consider_candidate = |m| {
        if i64_to_scalar(m) * G == target_point {
            found = found.or(Some(m as u64));
        }
        found.is_some()
    };

    let mut batch = [FieldElement::ONE; BATCH_SIZE];
    let mut batch_j = [0usize; BATCH_SIZE];
    'outer: for (chunk, progress) in j_batch_iterator {
        if let ControlFlow::Break(_) = progress_report.report(progress) {
            break 'outer;
        }

        // Z = T2[j]_x - Pm_x
        let mut b_item_count = 0;
        for (batch_index, j) in chunk.enumerate() {
            let t2_point = t2_table.index(j as _);
            let diff = &t2_point.u - &target_montgomery.u;
            if diff == FieldElement::ZERO {
                // Montgomery substraction: exceptional case when T2[j] = Pm.
                // Also catches the exceptional case when Pm is the identity.
                // m1 = j * 2^L1, m2 = -j * 2^L1
                let found = consider_candidate((j as i64) << TS::L1)
                    || consider_candidate(-(j as i64) << TS::L1);
                if !pseudo_constant_time && found {
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

                if let Some(i) = t1_table.lookup::<TS>(&target_montgomery.u.as_bytes()) {
                    let found = consider_candidate((-(j as i64) << TS::L1) + i as i64)
                        || consider_candidate((-(j as i64) << TS::L1) - i as i64);
                    if !pseudo_constant_time && found {
                        break 'outer;
                    }
                }
            } else {
                // Montgomery substraction: general case

                let t2_point = t2_table.index(j as _);

                let alpha = &(&MONTGOMERY_A_NEG - &t2_point.u) - &target_montgomery.u;

                // lambda = (T2[j]_y - Pm_y) * nu
                // Q_x = lambda^2 - A - T2[j]_x - Pm_x
                let lambda = &(&t2_point.v - &target_montgomery.v) * &nu;
                let qx = &lambda.square() + &alpha;

                if let Some(i) = t1_table.lookup::<TS>(&qx.as_bytes()) {
                    // m1 = -j * 2^L1 + i, m2 = -j * 2^L1 - i
                    let found = consider_candidate((-(j as i64) << TS::L1) + i as i64)
                        || consider_candidate((-(j as i64) << TS::L1) - i as i64);
                    if !pseudo_constant_time && found {
                        break 'outer;
                    }
                }

                // lambda = (p - T2[j]_y - Pm_y) * nu
                // Q_x = lambda^2 - A - T2[j]_x - Pm_x
                let lambda = &(&-&t2_point.v - &target_montgomery.v) * &nu;
                let qx = &lambda.square() + &alpha;

                if let Some(i) = t1_table.lookup::<TS>(&qx.as_bytes()) {
                    // m1 = j * 2^L1 + i, m2 = j * 2^L1 - i
                    let found = consider_candidate(((j as i64) << TS::L1) + i as i64)
                        || consider_candidate(((j as i64) << TS::L1) - i as i64);
                    if !pseudo_constant_time && found {
                        break 'outer;
                    }
                }
            }
        }
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

        for i in 1..=j_max {
            let mut v = i as _;
            let mut old_hash_id = 1u8;

            if i % (j_max / 1000 + 1) == 0 {
                println!("[{}/{}]", i, j_max);
            }

            for j in 0..CUCKOO_MAX_INSERT_SWAPS {
                let x = all_entries[v as usize - 1].as_ref();
                let start = (old_hash_id as usize - 1) * 8;
                let end = start as usize + 4;
                let mut key = u32::from_be_bytes(x[end..end + 4].try_into().unwrap());
                let h1 = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize;
                let h = u32::from_be_bytes(x[start..end].try_into().unwrap()) as usize % cuckoo_len;

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

        let mut all_entries = vec![Default::default(); j_max];

        println!("Computing all the points...");
        let mut acc = G;
        for i in 1..=j_max {
            let point = acc; // i * G

            if i % (j_max / 1000 + 1) == 0 {
                println!("[{}/{}]", i, j_max);
            }

            let u = point.0.to_montgomery();
            let bytes = u.to_bytes();

            all_entries[i - 1] = bytes;
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

    pub fn create_t2_table(l1: usize, l2: usize, file: &mut File) {
        use crate::traits::Identity;
        let i_max = (1 << (l2 - 1)) + 1;
        let two_to_l1 = EdwardsPoint::mul_base(&Scalar::from(1u32 << l1)); // 2^l1

        let mut arr = vec![
            T2MontgomeryCoordinates {
                u: Default::default(),
                v: Default::default()
            };
            i_max
        ];

        let mut acc = EdwardsPoint::identity();
        for j in 0..i_max {
            let p = AffineMontgomeryPoint::from(&acc);
            let (u, v) = (p.u.as_bytes(), p.v.as_bytes());
            // println!("{j} * 2^l1 * G = {u:?} {v:?}");
            arr[j] = T2MontgomeryCoordinates { u, v };
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
        let l1 = 25;
        let l2 = 48 - l1;

        // let l1 = 8;
        // let l2 = 16 - l1;
        table_generation::create_t1_table(l1, &mut File::create(format!("t1_{l1}.bin")).unwrap());
        table_generation::create_t2_table(
            l1,
            l2,
            &mut File::create(format!("t2_{l1}_{l2}.bin")).unwrap(),
        )
    }

    const T1: CuckooT1HashMapView<'static> =
        embed_t1_in_binary! { L = 16, L1 = 8, PATH = "../t1_8.bin" };
    const T2: T2LinearTableView<'static> =
        embed_t2_in_binary! { L = 16, L1 = 8, PATH = "../t2_8_8.bin" };
    struct ECDLPTables16L8;
    impl PrecomputedECDLPTables for ECDLPTables16L8 {
        const L: usize = 16;
        const L1: usize = 8;

        fn get_t1(&self) -> CuckooT1HashMapView<'_> {
            T1
        }
        fn get_t2(&self) -> T2LinearTableView<'_> {
            T2
        }
    }

    #[test]
    #[cfg(not(feature = "precompute_table_gen"))]
    fn test_fast_ecdlp() {
        fn decode_(num: u64) -> Option<i64> {
            decode(
                &ECDLPTables16L8,
                Scalar::from(num) * G,
                ECDLPArguments::default()
                    .best_effort_constant_time(true)
            )
        }

        for i in 0..(1 << ECDLPTables16L8::L) {
            assert_eq!(Some(i as i64), decode_(i));
        }
    }

    #[test]
    #[cfg(not(feature = "precompute_table_gen"))]
    fn test_par_decode() {
        for i in 0..(1u64 << ECDLPTables16L8::L) {
            assert_eq!(
                Some(i as i64),
                par_decode(
                    &ECDLPTables16L8,
                    Scalar::from(i) * G,
                    ECDLPArguments::default()
                        .best_effort_constant_time(true)
                        .n_threads(4)
                )
            );
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
