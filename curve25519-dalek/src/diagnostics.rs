//! Build time diagnostics

// auto is assumed or selected
#[cfg(curve25519_dalek_backend = "auto")]
compile_error!("curve25519_dalek_backend is 'auto'");

// fiat was overridden
#[cfg(curve25519_dalek_backend = "fiat")]
compile_error!("curve25519_dalek_backend is 'fiat'");

// serial was assumed or overridden
#[cfg(curve25519_dalek_backend = "serial")]
compile_error!("curve25519_dalek_backend is 'serial'");

// simd was assumed over overridden
#[cfg(curve25519_dalek_backend = "simd")]
compile_error!("curve25519_dalek_backend is 'simd'");

// 32 bits target_pointer_width was assumed or overridden
#[cfg(curve25519_dalek_bits = "32")]
compile_error!("curve25519_dalek_bits is '32'");

// 64 bits target_pointer_width was assumed or overridden
#[cfg(curve25519_dalek_bits = "64")]
compile_error!("curve25519_dalek_bits is '64'");
