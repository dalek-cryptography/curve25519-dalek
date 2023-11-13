use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT as G,
    ecdlp::{
        self, CuckooT1HashMapView, ECDLPArguments, PrecomputedECDLPTables, T2LinearTableView,
        T2MontgomeryCoordinates,
    },
    Scalar,
};
use memmap::{Mmap, MmapOptions};
use rand::Rng;
use std::{fs::File, io::Read};

/// T2 is embedded in the binary since it's small enough, however,
/// T1 will be loaded from a file.
enum ECDLPTables48L26 {
    Heap {
        t1_keys_values: Box<[u32]>,
        t2_table: Box<[T2MontgomeryCoordinates]>,
    },
    Mmap {
        t1_mmap: Mmap,
        t2_mmap: Mmap,
    },
}
impl ECDLPTables48L26 {
    fn load() -> std::io::Result<Self> {
        let mut t1_keys_values = vec![0u32; Self::CUCKOO_LEN * 2].into_boxed_slice(); // keys and values
        let mut t2_table = vec![T2MontgomeryCoordinates::default(); Self::I_MAX].into_boxed_slice();

        let mmap = true;

        let mut t1_file = File::open("t1_26.bin")?;
        let mut t2_file = File::open("t2_26_22.bin")?;

        if !mmap {
            t1_file.read_exact(bytemuck::cast_slice_mut(&mut t1_keys_values))?;
            assert_eq!(t1_file.bytes().count(), 0);
            t2_file.read_exact(bytemuck::cast_slice_mut(&mut t2_table))?;
            assert_eq!(t2_file.bytes().count(), 0);

            Ok(Self::Heap {
                t1_keys_values,
                t2_table,
            })
        } else {
            let t1_mmap = unsafe { MmapOptions::new().map(&t1_file)? };
            let t2_mmap = unsafe { MmapOptions::new().map(&t2_file)? };

            Ok(Self::Mmap { t1_mmap, t2_mmap })
        }
    }
}

impl PrecomputedECDLPTables for ECDLPTables48L26 {
    const L: usize = 48;
    const L1: usize = 26;

    fn get_t1(&self) -> CuckooT1HashMapView<'_> {
        match self {
            Self::Heap { t1_keys_values, .. } => CuckooT1HashMapView {
                keys: &t1_keys_values[0..Self::CUCKOO_LEN],
                values: &t1_keys_values[Self::CUCKOO_LEN..],
            },
            Self::Mmap { t1_mmap, .. } => {
                let t1_keys_values: &[u32] = bytemuck::cast_slice(&t1_mmap);

                CuckooT1HashMapView {
                    keys: &t1_keys_values[0..Self::CUCKOO_LEN],
                    values: &t1_keys_values[Self::CUCKOO_LEN..],
                }
            }
        }
    }

    fn get_t2(&self) -> T2LinearTableView<'_> {
        match self {
            Self::Heap { t2_table, .. } => T2LinearTableView(&t2_table),
            Self::Mmap { t2_mmap, .. } => {
                let t1_keys_values: &[T2MontgomeryCoordinates] = bytemuck::cast_slice(&t2_mmap);
                T2LinearTableView(t1_keys_values)
            }
        }
    }
}

pub fn ecdlp_bench(c: &mut Criterion) {
    let tables = ECDLPTables48L26::load().unwrap();

    c.bench_function("fast ecdlp", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(
                &tables,
                black_box(point),
                ECDLPArguments::default().best_effort_constant_time(true),
            );
            println!("{:?}, {:?}", res, Some(num as i64));
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("par fast ecdlp T=1", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::par_decode(
                &tables,
                black_box(point),
                ECDLPArguments::default()
                    .best_effort_constant_time(true)
                    .n_threads(1),
            );
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("par fast ecdlp T=2", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::par_decode(
                &tables,
                black_box(point),
                ECDLPArguments::default()
                    .best_effort_constant_time(true)
                    .n_threads(2),
            );
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("par fast ecdlp T=4", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::par_decode(
                &tables,
                black_box(point),
                ECDLPArguments::default()
                    .best_effort_constant_time(true)
                    .n_threads(4),
            );
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("par fast ecdlp T=8", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::par_decode(
                &tables,
                black_box(point),
                ECDLPArguments::default()
                    .best_effort_constant_time(true)
                    .n_threads(4),
            );
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("fast ecdlp find 0", |b| {
        let num: u64 = 0;
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(&tables, black_box(point), ECDLPArguments::default());
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function("par fast ecdlp find 0 T=4", |b| {
        let num: u64 = 0;
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::par_decode(
                &tables,
                black_box(point),
                ECDLPArguments::default().n_threads(4),
            );
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function(&format!("fast ecdlp for number < {}", (1 << ECDLPTables48L26::L - 4)), |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L - 4));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(&tables, black_box(point), ECDLPArguments::default());
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function(&format!("fast ecdlp for number < {}", (1 << ECDLPTables48L26::L - 8)), |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L - 4));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(&tables, black_box(point), ECDLPArguments::default());
            assert_eq!(res, Some(num as i64));
        });
    });

    c.bench_function(&format!("fast ecdlp for number < {}", (1 << ECDLPTables48L26::L - 2)), |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L - 4));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(&tables, black_box(point), ECDLPArguments::default());
            assert_eq!(res, Some(num as i64));
        });
    });
}

criterion_group!(ecdlp, ecdlp_bench);
criterion_main!(ecdlp);
