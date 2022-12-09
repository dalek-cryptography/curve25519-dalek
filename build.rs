//! This selects the curve25519_dalek_bits either by default from target_pointer_width or explicitly set

#[cfg_attr(
    any(curve25519_dalek_serial = "fiat", curve25519_dalek_backend = "fiat"),
    deny(dead_code)
)]
#[cfg_attr(
    all(
        not(curve25519_dalek_backend = "fiat"),
        not(curve25519_dalek_serial = "fiat")
    ),
    allow(dead_code)
)]
fn fiat_backend(simd: bool) {
    println!("cargo:rustc-cfg=curve25519_dalek_serial=\"fiat\"");

    match simd {
        false => println!("cargo:rustc-cfg=curve25519_dalek_backend=\"fiat\""),
        true => println!("cargo:rustc-cfg=curve25519_dalek_backend=\"simd\""),
    }
}

fn main() {
    /***************************************************************************
     * Allow overriding the [fiat_][u32|u64] serial arithmetric PR#454
     ***************************************************************************/
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

    /***************************************************************************
     * Allow selection of fiat serial with simd backend Issue#437
     ***************************************************************************/
    #[cfg(any(
        all(
            curve25519_dalek_serial = "fiat",
            not(curve25519_dalek_backend = "simd")
        ),
        curve25519_dalek_backend = "fiat"
    ))]
    fiat_backend(false);

    #[cfg(all(curve25519_dalek_serial = "fiat", curve25519_dalek_backend = "simd"))]
    fiat_backend(true);
}
