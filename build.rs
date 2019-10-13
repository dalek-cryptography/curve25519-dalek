#![cfg_attr(all(feature = "alloc", not(feature = "std")), feature(alloc))]
#![cfg_attr(feature = "nightly", feature(doc_cfg))]
#![cfg_attr(feature = "simd_backend", feature(stdsimd))]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(dead_code)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;
extern crate byteorder;
extern crate core;
extern crate digest;
extern crate rand_core;
extern crate subtle;
extern crate zeroize;

#[cfg(all(feature = "nightly", feature = "packed_simd"))]
extern crate packed_simd;

use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

// Replicate lib.rs in the build.rs, since we're effectively building the whole crate twice.
//
// This should be fixed up by refactoring our code to seperate the "minimal" parts from the rest.
//
// For instance, this shouldn't exist here at all, but it does.
#[cfg(feature = "serde")]
extern crate serde;

// Macros come first!
#[path = "src/macros.rs"]
#[macro_use]
mod macros;

// Public modules

#[path = "src/constants.rs"]
mod constants;
#[path = "src/edwards.rs"]
mod edwards;
#[path = "src/montgomery.rs"]
mod montgomery;
#[path = "src/ristretto.rs"]
mod ristretto;
#[path = "src/scalar.rs"]
mod scalar;
#[path = "src/traits.rs"]
mod traits;

// Internal modules

#[path = "src/backend/mod.rs"]
mod backend;
#[path = "src/field.rs"]
mod field;
#[path = "src/prelude.rs"]
mod prelude;
#[path = "src/window.rs"]
mod window;

use edwards::EdwardsBasepointTable;

fn main() {
    // Enable the "stage2_build" feature in the main build stage
    println!("cargo:rustc-cfg=feature=\"stage2_build\"\n");

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("basepoint_table.rs");
    let mut f = File::create(&dest_path).unwrap();

    // Generate a table of precomputed multiples of the basepoint
    let table = EdwardsBasepointTable::create(&constants::ED25519_BASEPOINT_POINT);

    f.write_all(
        format!(
            "\n
#[cfg(feature = \"u32_backend\")]
use backend::serial::u32::field::FieldElement2625;

#[cfg(feature = \"u64_backend\")]
use backend::serial::u64::field::FieldElement51;

use edwards::EdwardsBasepointTable;

use backend::serial::curve_models::AffineNielsPoint;

use window::LookupTable;

/// Table containing precomputed multiples of the Ed25519 basepoint \\\\(B = (x, 4/5)\\\\).
pub const ED25519_BASEPOINT_TABLE: EdwardsBasepointTable = ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN;

/// Inner constant, used to avoid filling the docs with precomputed points.
#[doc(hidden)]
pub const ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN: EdwardsBasepointTable = {:?};
\n\n",
            &table
        )
        .as_bytes(),
    )
    .unwrap();

    // Now generate AFFINE_ODD_MULTIPLES_OF_BASEPOINT
    // if we are going to build the serial scalar_mul backend
    #[cfg(not(all(
        feature = "simd_backend",
        any(target_feature = "avx2", target_feature = "avx512ifma")
    )))]
    {
        use backend::serial::curve_models::AffineNielsPoint;
        use window::NafLookupTable8;

        let B = &constants::ED25519_BASEPOINT_POINT;
        let odd_multiples = NafLookupTable8::<AffineNielsPoint>::from(B);

        f.write_all(
            format!(
                "\n
use window::NafLookupTable8;
/// Odd multiples of the basepoint `[B, 3B, 5B, 7B, 9B, 11B, 13B, 15B, ..., 127B]`.
pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT: NafLookupTable8<AffineNielsPoint> = {:?};
\n\n",
                &odd_multiples
            )
            .as_bytes(),
        )
        .unwrap();
    }
}
