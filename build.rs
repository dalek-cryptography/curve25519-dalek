#![cfg_attr(feature = "nightly", feature(i128_type))]
#![cfg_attr(feature = "nightly", feature(cfg_target_feature))]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate core;
extern crate subtle;
extern crate rand;
extern crate digest;
extern crate generic_array;
extern crate clear_on_drop;

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
#[cfg(feature = "yolocrypto")]
extern crate stdsimd;

// Macros come first!
#[path="src/macros.rs"]
#[macro_use]
mod macros;

// Public modules

#[path="src/scalar.rs"]
mod scalar;
#[path="src/montgomery.rs"]
mod montgomery;
#[path="src/edwards.rs"]
mod edwards;
#[path="src/ristretto.rs"]
mod ristretto;
#[path="src/constants.rs"]
mod constants;
#[path="src/traits.rs"]
mod traits;

// Internal modules

#[path="src/field.rs"]
mod field;
#[path="src/curve_models/mod.rs"]
mod curve_models;
#[path="src/backend/mod.rs"]
mod backend;
#[path="src/scalar_mul/mod.rs"]
mod scalar_mul;

use edwards::EdwardsBasepointTable;

fn main() {
    // Enable the "precomputed_tables" feature in the main build stage
    println!("cargo:rustc-cfg=feature=\"precomputed_tables\"\n");

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("basepoint_table.rs");
    let mut f = File::create(&dest_path).unwrap();

    // Generate a table of precomputed multiples of the basepoint
    let table = EdwardsBasepointTable::create(&constants::ED25519_BASEPOINT_POINT);

    f.write_all(format!("\n
#[cfg(feature=\"radix_51\")]
use backend::u64::field::FieldElement64;

#[cfg(not(feature=\"radix_51\"))]
use backend::u32::field::FieldElement32;

use edwards::EdwardsBasepointTable;

use curve_models::AffineNielsPoint;

use scalar_mul::window::LookupTable;

/// Table containing precomputed multiples of the Ed25519 basepoint \\\\(B = (x, 4/5)\\\\).
pub const ED25519_BASEPOINT_TABLE: EdwardsBasepointTable = ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN;

/// Inner constant, used to avoid filling the docs with precomputed points.
#[doc(hidden)]
pub const ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN: EdwardsBasepointTable = {:?};
    \n\n", &table).as_bytes()).unwrap();

    // Now generate AFFINE_ODD_MULTIPLES_OF_BASEPOINT
    let B = &constants::ED25519_BASEPOINT_POINT;
    let B2 = B.double();
    let mut odd_multiples = [B.to_affine_niels(); 8];
    for i in 0..7 {
        odd_multiples[i+1] = (&B2 + &odd_multiples[i]).to_extended().to_affine_niels();
    }

    f.write_all(format!("\n
/// Odd multiples of the basepoint `[B, 3B, 5B, 7B, 9B, 11B, 13B, 15B]`.
pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT: [AffineNielsPoint; 8] = {:?};
    \n\n", &odd_multiples).as_bytes()).unwrap();
}
