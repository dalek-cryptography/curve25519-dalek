//! This selects the curve25519_dalek_bits either by default from target_pointer_width or explicitly set

fn main() {
    #[cfg(any(
        all(not(target_pointer_width = "64"), not(curve25519_dalek_bits = "64")),
        curve25519_dalek_bits = "32"
    ))]
    println!("cargo:rustc-cfg=curve25519_dalek_bits=\"32\"");

    #[cfg(any(
        all(target_pointer_width = "64", not(curve25519_dalek_bits = "32")),
        curve25519_dalek_bits = "64"
    ))]
    println!("cargo:rustc-cfg=curve25519_dalek_bits=\"64\"");
}
