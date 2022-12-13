//! This selects the curve25519_dalek_bits either by default from target_pointer_width or explicitly set

#[allow(non_camel_case_types)]
enum DalekBits {
    #[cfg_attr(curve25519_dalek_bits = "64", allow(dead_code))]
    Dalek32,
    #[cfg_attr(curve25519_dalek_bits = "32", allow(dead_code))]
    Dalek64,
}

#[cfg(all(not(curve25519_dalek_bits = "64"), not(curve25519_dalek_bits = "32")))]
#[deny(dead_code)]
fn lotto_curve25519_dalek_bits() -> DalekBits {
    use platforms::target::PointerWidth;

    let target_triplet = std::env::var("TARGET").unwrap();
    let platform = platforms::Platform::find(&target_triplet).unwrap();

    #[allow(clippy::match_single_binding)]
    match platform.target_arch {
        //Issues: 449 and 456
        //TODO(Arm): Needs tests + benchmarks to back this up
        //platforms::target::Arch::Arm => DalekBits::Dalek64,
        //TODO(Wasm32): Needs tests + benchmarks to back this up
        //platforms::target::Arch::Wasm32 => DalekBits::Dalek64,
        _ => match platform.target_pointer_width {
            PointerWidth::U64 => DalekBits::Dalek64,
            PointerWidth::U32 => DalekBits::Dalek32,
            _ => DalekBits::Dalek32,
        },
    }
}

fn main() {
    #[cfg(curve25519_dalek_bits = "32")]
    let curve25519_dalek_bits = DalekBits::Dalek32;

    #[cfg(curve25519_dalek_bits = "64")]
    let curve25519_dalek_bits = DalekBits::Dalek64;

    #[cfg(all(not(curve25519_dalek_bits = "64"), not(curve25519_dalek_bits = "32")))]
    let curve25519_dalek_bits = lotto_curve25519_dalek_bits();

    match curve25519_dalek_bits {
        DalekBits::Dalek64 => println!("cargo:rustc-cfg=curve25519_dalek_bits=\"64\""),
        DalekBits::Dalek32 => println!("cargo:rustc-cfg=curve25519_dalek_bits=\"32\""),
    }
}
