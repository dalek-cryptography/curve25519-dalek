use std::{fs::File, io::Read};

use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT as G,
    ecdlp::{self, PrecomputedECDLPTables},
};

const T2: T2LinearTableView<'static> = embed_t2_in_binary! { L = 40, L1 = 26, PATH = "t2.bin" };

/// T2 is embedded in the binary since it's small enough, however,
/// T1 will be loaded from a file.
struct ECDLPTables40L26 {
    t1: Box<CuckooT1HashMap>,
}
impl ECDLPTables40L26 {
    fn load() -> std::io::Result<Self> {
        // Note, you should probably be using the `bytemuck` crate to do this without unsafe.

        #[repr(C, align(64))]
        struct CuckooT1HashMap {
            keys: [u32; Self::CUCKOO_LEN],
            values: [u32; Self::CUCKOO_LEN],
        }

        // hacky way to get a properly aligned vector
        #[repr(C, align(64))]
        struct AlignedBytesToT1([u8; core::mem::size_of::<CuckooT1HashMap>()]);

        // we are using vec! here since Box::new would make the stack overflow.
        let buf = vec![AlignedBytesToT1([0; _]); 1];
        let mut buf = buf.into_boxed_slice();

        File::open("curve25519-dalek/examples/t1.bin")?.read_exact(&mut buf[0].0)?;

        // Safety:
        // * alignment and size is garanteed using the hack
        // * CuckooT1HashMap is plain old data
        let t1: Box<CuckooT1HashMap> = unsafe { Box::from_raw(Box::leak(buf).as_mut_ptr().cast()) };
        Ok(Self { t1 })
    }
}

impl PrecomputedECDLPTables for ECDLPTables40L26 {
    const L: usize = 40;
    const L1: usize = 26;

    fn get_t1(&self) -> CuckooT1HashMapView<'_> {
        self.t1
    }
    fn get_t2(&self) -> T2LinearTableView<'_> {
        T2
    }
}

fn main() {
    let tables = ECDLPTables40L26::load().unwrap();

    let num = 23874982;

    let res = ecdlp::decode(tables, Scalar::from(num) * G, 0, 1 << 40, true);

    assert_eq!(res, Some(num))
}
