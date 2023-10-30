use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT as G,
    ecdlp::{
        self, CuckooT1HashMapView, PrecomputedECDLPTables, T2LinearTableView,
        T2MontgomeryCoordinates,
    },
    Scalar,
};
use rand::Rng;
use std::{fs::File, io::Read};

/// T2 is embedded in the binary since it's small enough, however,
/// T1 will be loaded from a file.
struct ECDLPTables48L26 {
    t1_keys: Box<[u32]>,
    t1_values: Box<[u32]>,
    t2_table: Box<[T2MontgomeryCoordinates]>,
}
impl ECDLPTables48L26 {
    fn load() -> std::io::Result<Self> {
        let mut t1_keys = vec![0u32; Self::CUCKOO_LEN].into_boxed_slice();
        let mut t1_values = vec![0u32; Self::CUCKOO_LEN].into_boxed_slice();
        let mut t2_table = vec![T2MontgomeryCoordinates::default(); Self::I_MAX].into_boxed_slice();

        let mut t1_file = File::open("t1_26.bin")?;
        t1_file.read_exact(bytemuck::cast_slice_mut(&mut t1_keys))?;
        t1_file.read_exact(bytemuck::cast_slice_mut(&mut t1_values))?;

        let mut t2_file = File::open("t2_26_22.bin")?;
        t2_file.read_exact(bytemuck::cast_slice_mut(&mut t2_table))?;

        Ok(Self {
            t1_keys,
            t1_values,
            t2_table,
        })
    }
}

impl PrecomputedECDLPTables for ECDLPTables48L26 {
    const L: usize = 48;
    const L1: usize = 26;

    fn get_t1(&self) -> CuckooT1HashMapView<'_> {
        CuckooT1HashMapView {
            keys: &self.t1_keys,
            values: &self.t1_values,
        }
    }
    fn get_t2(&self) -> T2LinearTableView<'_> {
        T2LinearTableView(&self.t2_table)
    }
}

pub fn ecdlp_bench(c: &mut Criterion) {
    let tables = ECDLPTables48L26::load().unwrap();

    c.bench_function("fast ecdlp", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ECDLPTables48L26::L));
        let point = Scalar::from(num) * G;
        b.iter(|| {
            let res = ecdlp::decode(&tables, black_box(point), 0, 1 << ECDLPTables48L26::L, true);
            assert_eq!(res, Some(num as i64));
        });
    });
}

criterion_group!(ecdlp, ecdlp_bench);
criterion_main!(ecdlp);
