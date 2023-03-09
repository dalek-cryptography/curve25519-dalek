//! This selects the curve25519_dalek_bits either by default from target_pointer_width or explicitly set

#![deny(clippy::unwrap_used, dead_code)]

#[allow(non_camel_case_types)]
enum DalekBits {
    #[cfg_attr(curve25519_dalek_bits = "64", allow(dead_code))]
    Dalek32,
    #[cfg_attr(curve25519_dalek_bits = "32", allow(dead_code))]
    Dalek64,
}

// Only when the curve25519_dalek_bits is not explicitly set.
// Error handling when the bits setting cannot be determined
#[cfg(all(not(curve25519_dalek_bits = "64"), not(curve25519_dalek_bits = "32")))]
fn determine_curve25519_dalek_bits_error(error_code: i32, trigger_msg: &str) -> ! {
    eprintln!("Error: {trigger_msg}");
    eprintln!("Please set cfg(curve25519_dalek_bits) explicitly either as 32 or 64.");
    std::process::exit(error_code)
}

// Only when the curve25519_dalek_bits is not explicitly set.
#[cfg(all(not(curve25519_dalek_bits = "64"), not(curve25519_dalek_bits = "32")))]
fn determine_curve25519_dalek_bits() -> DalekBits {
    use platforms::target::PointerWidth;

    // TARGET environment is supplied by Cargo
    // https://doc.rust-lang.org/cargo/reference/environment-variables.html
    let target_triplet = match std::env::var("TARGET") {
        Ok(t) => t,
        Err(_) => determine_curve25519_dalek_bits_error(
            10,
            "Standard Cargo TARGET environment variable is not set",
        ),
    };

    // platforms crate is the source of truth used to determine the platform
    // Custom target platforms require explicit settings.
    let platform = match platforms::Platform::find(&target_triplet) {
        Some(p) => p,
        None => determine_curve25519_dalek_bits_error(20, "Unrecognised Rust target"),
    };

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
            // Intended default solely for non-32/64 target pointer widths
            // Otherwise known target platforms only.
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
    let curve25519_dalek_bits = determine_curve25519_dalek_bits();

    match curve25519_dalek_bits {
        DalekBits::Dalek64 => println!("cargo:rustc-cfg=curve25519_dalek_bits=\"64\""),
        DalekBits::Dalek32 => println!("cargo:rustc-cfg=curve25519_dalek_bits=\"32\""),
    }
}
