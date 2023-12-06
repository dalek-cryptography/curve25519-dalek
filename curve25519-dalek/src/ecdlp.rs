//! # Elliptic Curve Discrete Logarithm Problem (ECDLP)
//!
//! This file enables the decoding of integers from [`RistrettoPoint`]s. As this requires
//! a bruteforce operation, this can take quite a long time (multiple seconds) for large input spaces.
//! 
//! The algorithm depends on a constant `L1` parameter, which enables changing the space/time tradeoff.
//! To use a given `L1` constant, you need to generate a precomputed tables file, or download a pre-generated one.
//! The resulting file may be quite big, which is why it is recommanded to load it at runtime using [`ecdlp::ECDLPTablesFile`].
//! 
//! The algorithm works for any range, but keep in mind that the time the algorithm takes grows exponentially: with the same
//! precomputed tables, decoding an `n+1`-bit integer will take 2x as long as an `n`-bit integer. By default, unless the "pseudo"
//! constant time mode is enabled, integers which are closer to the start of the range will be found exponentially faster: for 
//! example, integers in the `n-1`-bit first half of the `n`-bit decoding range will take 1/2 of the time compared to the second half,
//! and numbers near the very beginning will be found almost immediately.
//!
//! # Space / Time tradeoff and benchmarks
//!
//! To choose an `L1` constant, you may to see benchmark performance and tables size [here](ecdlp_perf.md).
//!
//! # Table generation
//!
//! For now, table generation can be done using the `gen_t1_t2` test, or using the unstable [`ecdlp::table_generation`] module.
//!
//! # Constant time
//!
//! This algorithm cannot be constant-time because of hashmap lookups. However a "pseudo"
//! constant time mode is implemented which lets the algorithm continue to run even when it
//! has found the answer.
//!
//! # Example
//!
//! Decoding a 48bit number using a L1=26 precomputed tables file.
//! ```
//! use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_POINT as G};
//!
//! let precomputed_tables = ECDLPTablesFile::<26>::load_from_file("ecdlp_table_26.bin")
//!     .unwrap();
//!
//! let num = 258383831730230u64;
//! let to_decode = Scalar::from(num) * G;
//!
//! assert_eq!(
//!     decode(precomputed_tables, to_decode, ECDLPArguments::new_with_range(0, 1 << 48)),
//!     Some(num)
//! );
//! ```

// Notes of the ECDLP implementation.
mod ecdlp_notes {
    //! The algorithm implemented here is BSGS (Baby Step Giant Step), and the implementation
    //! details are based on [Solving Small Exponential ECDLP in EC-based Additively Homomorphic Encryption and Applications][fast-ecdlp-paper].
    //!
    //! The gist of BSGS goes as follows:
    //! - Our target point, which we want to decode, represents an integer in the range \[0, 2^(L1 + L2)\].
    //! - We have a T1 hash table, where the key is the curve point and value is the decoded
    //!   point. T1 = <i * G => i | i in \[1, 2^l1\]>
    //! - We have a T2 linear table (an array), where T2 = \[j * 2^l1 * G | j in \[1, 2^l2\]\]
    //! - For each j in 0..2^l2
    //!     Compute the difference between T2\[j\] and the target point
    //!     if let Some(i) = T1.get(the difference) => the decoded integer is j * 2^L1 + i.
    //!
    //! On top of this regular BSGS algorithm, we add the following optimizations:
    //! - Batching. The paper uses a tree-based Montgomery trick - instead, we use the batched
    //!   inversion which is implemented in FieldElement.
    //! - T1 only contains the truncated x coordinates. The table uses Cuckoo hashing, and
    //!   the hash of a point is directly just a subset of the bytes of the point.
    //! - We need a canonical encoding of a point before any hashmap lookup: this means that
    //!   we must work with affine coordinates. Addition of affine Montgomery points requires
    //!   less inversions than Edwards points, so we use that instead.  
    //! - Using the fact -(x, y) = (x, -y) on the Montgomery curve, we can shift the inputs so
    //!   that we only need half of T1 and T2 and half of the modular inversions.
    //! - The L2 constant has been fixed here, because we can just shift the input after every
    //!   batch. This means that L2 has a constant size of about 16Ko, which is preferable
    //!   to >100Mo when L2 = 22, for example. This results in slightly more modular inversions,
    //!   however this has no visible impact on performance. Shifting the inputs like this
    //!   also means that we support arbitrary decoding ranges for a given constant tables file.
    //!
    //! [fast-ecdlp-paper]: https://eprint.iacr.org/2022/1573
}

use core::{
    ops::ControlFlow,
    sync::atomic::{AtomicBool, Ordering},
};
use std::{fs::File, mem::size_of, path::Path};

use crate::{
    backend::serial::u64::constants::MONTGOMERY_A,
    constants::{MONTGOMERY_A_NEG, RISTRETTO_BASEPOINT_POINT as G},
    field::FieldElement,
    traits::Identity,
    EdwardsPoint, RistrettoPoint, Scalar,
};
use bytemuck::{Pod, Zeroable};

const L2: usize = 9; // corresponds to a batch size of 256 and a T2 table of a few Ko.
const BATCH_SIZE: usize = 1 << (L2 - 1);

const I_BITS: usize = L2 - 1;
const I_MAX: usize = (1 << I_BITS) + 1; // there needs to be one more element in T2
const CUCKOO_K: usize = 3; // number of cuckoo lookups before giving up

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
trait ECDLPTablesConstants {
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
#[derive(Clone, Copy)]
struct AffineMontgomeryPoint {
    u: FieldElement,
    v: FieldElement,
}

impl AffineMontgomeryPoint {
    /// Add two `AffineMontgomeryPoint` together.
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

// FIXME(upstream): FieldElement::from_bytes should probably be const
// see test for correctness of this const
fn edwards_to_montgomery_alpha() -> FieldElement {
    // Constant comes from https://ristretto.group/details/isogenies.html (birational mapping from E2 = E_(a2,d2) to M_(B,A))
    // alpha = sqrt((A + 2) / (B * a_2)) with B = 1 and a_2 = -1.
    FieldElement::from_bytes(&[
        6, 126, 69, 255, 170, 4, 110, 204, 130, 26, 125, 75, 209, 211, 161, 197, 126, 79, 252, 3,
        220, 8, 123, 210, 187, 6, 160, 96, 244, 237, 38, 15,
    ])
}

impl From<&'_ EdwardsPoint> for AffineMontgomeryPoint {
    #[allow(non_snake_case)]
    fn from(eddy: &EdwardsPoint) -> Self {
        let ALPHA = edwards_to_montgomery_alpha();

        // u = (1+y)/(1-y) = (Z+Y)/(Z-Y),
        // v = (1+y)/(x(1-y)) * alpha = (Z+Y)/(X-T) * alpha.
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
    fn index(&self, index: usize) -> AffineMontgomeryPoint {
        let T2MontgomeryCoordinates { u, v } = self.0[index - 1];
        AffineMontgomeryPoint {
            u: FieldElement::from_bytes(&u),
            v: FieldElement::from_bytes(&v),
        }
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
    fn lookup<TS: PrecomputedECDLPTables>(
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

/// A trait to represent progress report functions.
/// It is auto-implemented on any `F: Fn(f64) -> ConstrolFlow<()>`.
pub trait ProgressReportFunction {
    /// Run the progress report function.
    fn report(&self, progress: f64) -> ControlFlow<()>;
}
impl<F: Fn(f64) -> ControlFlow<()>> ProgressReportFunction for F {
    #[inline(always)]
    fn report(&self, progress: f64) -> ControlFlow<()> {
        self(progress)
    }
}
/// The Noop (no operation) report function. It does nothing and will never break.
pub struct NoopReportFn;
impl ProgressReportFunction for NoopReportFn {
    #[inline(always)]
    fn report(&self, _progress: f64) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }
}

/// Builder for the ECDLP algorithm parameters.
pub struct ECDLPArguments<R: ProgressReportFunction = NoopReportFn> {
    range_start: i64,
    range_end: i64,
    pseudo_constant_time: bool,
    n_threads: usize,
    progress_report_function: R,
}

impl ECDLPArguments<NoopReportFn> {
    /// Creates a new `ECDLPArguments` with default arguments, to run on a specific range.
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
    /// Enable the "pseudo constant-time" mode. This means that the algorithm will not stop
    /// once it has found the answer. Keep in mind that **this is not actually constant-time**,
    /// in fact, the algorithm cannot be constant-time because it relies on hashmap lookups.
    /// This setting is also useful for benchmarking, as any input will result in roughly the same
    /// execution time.
    pub fn pseudo_constant_time(self, pseudo_constant_time: bool) -> Self {
        Self {
            pseudo_constant_time,
            ..self
        }
    }

    /// Sets the progress report function.
    ///
    /// This function will be periodically called when the algorithm is running.
    /// The `progress` argument represents the current progress, from `0.0` to `1.0`.
    /// Returning `ControlFlow::Break(())` will stop the algorithm.
    ///
    /// Please keep in mind that this report function should not take too long or nuke
    /// the cache, as it would impact the performance of the algorithm.
    /// 
    /// # Example
    /// 
    /// ```
    /// let ecdlp_args = ECDLPArguments::new_with_range(0, 1 << 48)
    ///     .progress_report_function(|_progress| {
    ///         // do something with `progress`
    ///         ControlFlow::Continue(())
    ///     });
    /// ```
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

    /// Configures the number of threads used.
    /// This only affects the execution of the [`par_decode`] function.
    ///
    /// # Example
    ///
    /// ```
    /// let n_threads = std::thread::available_parallelism()
    ///     .expect("cannot get available parallelism")
    ///     .get();
    /// let ecdlp_args = ECDLPArguments::new_with_range(0, 1 << 48)
    ///     .n_threads(n_threads);
    /// ```
    pub fn n_threads(self, n_threads: usize) -> Self {
        Self { n_threads, ..self }
    }
}

/// Offset calculations common to [`par_decode`] and [`decode`].
fn decode_prep<TS: PrecomputedECDLPTables, R: ProgressReportFunction>(
    _precomputed_tables: &TS,
    point: RistrettoPoint,
    args: &ECDLPArguments<R>,
    _n_threads: usize,
) -> (i64, RistrettoPoint, usize) {
    let amplitude = (args.range_end - args.range_start).max(0);

    let offset = args.range_start + ((1 << (L2 - 1)) << TS::L1) + (1 << (TS::L1 - 1));
    let normalized = &point - &i64_to_scalar(offset) * G;

    let j_end = (amplitude >> TS::L1) as usize; // amplitude / 2^(L1 + 1)

    // FIXME: is there a better way to divceil other than pulling the `num` crate?
    let divceil = |a, b| (a + b - 1) / b;

    let num_batches = divceil(j_end, 1 << L2); // divceil(j_end, 2^NEW_L2)

    (offset, normalized, num_batches)
}

/// Returns an iterator of batches for a given thread. Common to [`par_decode`] and [`decode`].
/// Iterator item is (index, j_start, target_montgomery, progress).
fn make_point_iterator<TS: PrecomputedECDLPTables>(
    _precomputed_tables: &TS,
    normalized: RistrettoPoint,
    num_batches: usize,
    n_threads: usize,
    thread_i: usize,
) -> impl Iterator<Item = (usize, usize, AffineMontgomeryPoint, f64)> {
    let batch_iterator = (0..num_batches).map(move |j| {
        let progress = j as f64 / num_batches as f64;
        (j, j * (1 << L2), progress)
    });

    let thread_iter = batch_iterator.skip(thread_i).step_by(n_threads);

    let els_per_batch = 1 << (L2 + TS::L1);

    // starting point for this thread
    let t_normalized = &normalized - &i64_to_scalar((thread_i * els_per_batch) as i64) * G;

    let mut target_montgomery = AffineMontgomeryPoint::from(&t_normalized.0);
    let batch_step = -(n_threads as i64) * els_per_batch as i64;
    let batch_step_montgomery = AffineMontgomeryPoint::from(&(i64_to_scalar(batch_step) * G).0);

    thread_iter.map(move |(j, j_start, progress)| {
        let current = target_montgomery;

        target_montgomery = AffineMontgomeryPoint::addition_not_constant_time(
            &target_montgomery,
            &batch_step_montgomery,
        );

        (j, j_start, current, progress)
    })
}

/// Decode a [`RistrettoPoint`] to the represented integer.
/// This may take a long time, so if you are running on an event-loop such as `tokio`, you
/// should wrap this in a `tokio::block_on` task.
pub fn decode<TS: PrecomputedECDLPTables, R: ProgressReportFunction>(
    precomputed_tables: &TS,
    point: RistrettoPoint,
    args: ECDLPArguments<R>,
) -> Option<i64> {
    let (offset, normalized, num_batches) = decode_prep(precomputed_tables, point, &args, 1);
    let point_iter = make_point_iterator(precomputed_tables, normalized, num_batches, 1, 0);
    fast_ecdlp(
        precomputed_tables,
        normalized,
        point_iter,
        args.pseudo_constant_time,
        args.progress_report_function,
    )
    .map(|v| v as i64 + offset)
}

/// Decode a [`RistrettoPoint`] to the represented integer, in parallel.
/// This uses [`std::thread`] as a threading primitive, and as such, it is only available when the `std` feature is enabled.
/// This may take a long time, so if you are running on an event-loop such as `tokio`, you
/// should wrap this in a `tokio::block_on` task.
pub fn par_decode<TS: PrecomputedECDLPTables + Sync, R: ProgressReportFunction + Sync>(
    precomputed_tables: &TS,
    point: RistrettoPoint,
    args: ECDLPArguments<R>,
) -> Option<i64> {
    let end_flag = AtomicBool::new(false);
    let (offset, normalized, num_batches) =
        decode_prep(precomputed_tables, point, &args, args.n_threads);

    let res = std::thread::scope(|s| {
        let handles = (0..args.n_threads)
            .map(|thread_i| {
                let end_flag = &end_flag;

                let progress_report = &args.progress_report_function;
                let progress_report = |progress| {
                    if !args.pseudo_constant_time && end_flag.load(Ordering::SeqCst) {
                        ControlFlow::Break(())
                    } else {
                        let ret = progress_report.report(progress);
                        if ret.is_break() {
                            // we need to tell the other threads that the user requested to stop
                            end_flag.store(true, Ordering::SeqCst);
                        }
                        ret
                    }
                };

                let handle = s.spawn(move || {
                    let point_iter = make_point_iterator(
                        precomputed_tables,
                        normalized,
                        num_batches,
                        args.n_threads,
                        thread_i,
                    );
                    let res = fast_ecdlp(
                        precomputed_tables,
                        normalized,
                        point_iter,
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

fn fast_ecdlp<TS: PrecomputedECDLPTables>(
    precomputed_tables: &TS,
    target_point: RistrettoPoint,
    point_iterator: impl Iterator<Item = (usize, usize, AffineMontgomeryPoint, f64)>,
    pseudo_constant_time: bool,
    progress_report: impl ProgressReportFunction,
) -> Option<u64> {
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
    'outer: for (index, j_start, target_montgomery, progress) in point_iterator {
        // amortize the potential cost of the report function
        if index % 256 == 0 {
            if let ControlFlow::Break(_) = progress_report.report(progress) {
                break 'outer;
            }
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
    }

    found
}

/// Table generation module. This module is public but should be treated as
/// unstable. The API may change without notice.
pub mod table_generation {
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
                let h = h1 % cuckoo_len;

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

    fn create_t1_table(l1: usize, file: &mut File) -> std::io::Result<()> {
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

        file.write_all(bytemuck::cast_slice(&t1_keys))?;
        file.write_all(bytemuck::cast_slice(&t1_values))?;

        println!("Done :)");
        Ok(())
    }

    fn create_t2_table(l1: usize, file: &mut File) -> std::io::Result<()> {
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
        Ok(())
    }

    /// Generate the ECDLP precomputed tables file.
    pub fn create_combined_table(l1: usize, file: &mut File) -> std::io::Result<()> {
        create_t2_table(l1, file)?;
        create_t1_table(l1, file)
    }
}

// FIXME(upstrean): should be an impl From<i64> for Scalar
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
    fn gen_t1_t2() {
        for l1 in 10..=28 {
            table_generation::create_combined_table(
                l1,
                &mut File::create(format!("ecdlp_table_{l1}.bin")).unwrap(),
            )
            .unwrap();
        }
    }

    #[test]
    fn test_const_alpha() {
        // Constant comes from https://ristretto.group/details/isogenies.html (birational mapping from E2 = E_(a2,d2) to M_(B,A))
        // alpha = sqrt((A + 2) / (B * a_2)) with B = 1 and a_2 = -1.
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let (is_sq, v) =
            FieldElement::sqrt_ratio_i(&(&MONTGOMERY_A + &two), &FieldElement::MINUS_ONE);
        assert!(bool::from(is_sq));

        assert_eq!(edwards_to_montgomery_alpha().as_bytes(), v.as_bytes());
    }
}
