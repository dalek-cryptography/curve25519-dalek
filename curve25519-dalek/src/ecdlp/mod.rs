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
    //! Note: We are dealing with a curve which has cofactors; as such, we need to multiply
    //! by the cofactor before running ECDLP to clear it and guarantee a canonical encoding of our points.
    //! The tables also need to be based on `num * cofactor` to match.
    //!
    //! [fast-ecdlp-paper]: https://eprint.iacr.org/2022/1573
}

mod affine_montgomery;
mod table;

use crate::{
    backend::serial::u64::constants::MONTGOMERY_A_NEG, constants::RISTRETTO_BASEPOINT_POINT as G,
    field::FieldElement, RistrettoPoint, Scalar,
};
use affine_montgomery::AffineMontgomeryPoint;
use core::{
    ops::ControlFlow,
    sync::atomic::{AtomicBool, Ordering},
};

pub use table::{
    table_generation, CuckooT1HashMapView, ECDLPTablesFile, PrecomputedECDLPTables,
    T2LinearTableView, T2MontgomeryCoordinates,
};

use table::{BATCH_SIZE, L2};

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
    let normalized = &point - RistrettoPoint::mul_base(&i64_to_scalar(offset));

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

    // clear the cofactor, we want the repr to be canonical
    let normalized = RistrettoPoint(normalized.0.mul_by_cofactor());

    let thread_iter = batch_iterator.skip(thread_i).step_by(n_threads);

    let els_per_batch = 1 << (L2 + TS::L1);

    // starting point for this thread
    let t_normalized = &normalized - &i64_to_scalar((thread_i * els_per_batch) as i64) * G;

    let mut target_montgomery = AffineMontgomeryPoint::from(&t_normalized.0);
    let batch_step = -(n_threads as i64) * els_per_batch as i64;
    let batch_step_montgomery =
        AffineMontgomeryPoint::from(&(i64_to_scalar(batch_step) * G).0.mul_by_cofactor());

    thread_iter.map(move |(j, j_start, progress)| {
        let current = target_montgomery;

        target_montgomery =
            AffineMontgomeryPoint::addition_not_ct(&target_montgomery, &batch_step_montgomery);

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
        if target_montgomery.is_identity_not_ct() {
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
    use std::fs::File;

    use rand::Rng;

    use super::*;

    #[test]
    fn gen_t1_t2() {
        // for l1 in 10..=28 {
        let l1 = 26;
        table_generation::create_combined_table(
            l1,
            &mut File::create(format!("ecdlp_table_{l1}.bin")).unwrap(),
        )
        .unwrap();
        // }
    }

    #[test]
    // #[cfg(ecdlp_test_needs_table_generated)]
    fn test_ecdlp_26_cofactors() {
        let tables = ECDLPTablesFile::<26>::load_from_file("ecdlp_table_26.bin").unwrap();

        for i in (0..(1u64 << 48)).step_by(1 << 26).take(1 << 14) {
            let delta = rand::thread_rng().gen_range(0..(1 << 26));

            let num = i as u64 + delta;
            let point = RistrettoPoint::mul_base(&Scalar::from(num));

            // take a random point from the coset4
            let coset_i = rand::thread_rng().gen_range(0..4);
            let point = point.coset4()[coset_i];
            // let point = point.compress().decompress().unwrap();

            let res = decode(
                &tables,
                RistrettoPoint(point),
                ECDLPArguments::new_with_range(0, 1 << 48),
            );
            assert_eq!(res, Some(num as i64));

            println!("tested {num} (coset4[{coset_i}])");
        }
    }

    #[test]
    // #[cfg(ecdlp_test_needs_table_generated)]
    fn test_ecdlp_26() {
        let tables = ECDLPTablesFile::<26>::load_from_file("ecdlp_table_26.bin").unwrap();

        for i in (0..(1u64 << 48)).step_by(1 << 26) {
            let num = i as u64; // rand::thread_rng().gen_range(0u64..(1 << 48));
            let mut point = RistrettoPoint::mul_base(&Scalar::from(num));

            if rand::thread_rng().gen() {
                // do a round of compression/decompression to mess up the Z and Ts
                // & ecdlp will need to clear the cofactor
                point = point.compress().decompress().unwrap();
            }

            let res = decode(&tables, point, ECDLPArguments::new_with_range(0, 1 << 48));
            assert_eq!(res, Some(num as i64));

            println!("tested {num}");
        }
    }
}
