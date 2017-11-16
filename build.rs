#![cfg_attr(feature = "nightly", feature(i128_type))]
#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate core;
extern crate subtle;
extern crate rand;
extern crate digest;
extern crate generic_array;
#[macro_use]
extern crate arrayref;

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

#[path="src/field.rs"]
mod field;
#[cfg(not(feature="radix_51"))]
#[path="src/field_32bit.rs"]
mod field_32bit;
#[cfg(feature="radix_51")]
#[path="src/field_64bit.rs"]
mod field_64bit;

#[path="src/scalar.rs"]
mod scalar;
#[cfg(not(feature="radix_51"))]
#[path="src/scalar_32bit.rs"]
mod scalar_32bit;
#[cfg(feature="radix_51")]
#[path="src/scalar_64bit.rs"]
mod scalar_64bit;

#[path="src/montgomery.rs"]
mod montgomery;
#[path="src/edwards.rs"]
mod edwards;
#[path="src/ristretto.rs"]
mod ristretto;
#[path="src/utils.rs"]
mod utils;

#[path="src/constants.rs"]
mod constants;
#[cfg(not(feature="radix_51"))]
#[path="src/constants_32bit.rs"]
mod constants_32bit;
#[cfg(feature="radix_51")]
#[path="src/constants_64bit.rs"]
mod constants_64bit;

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
use field_64bit::FieldElement64;

#[cfg(not(feature=\"radix_51\"))]
use field_32bit::FieldElement32;

use edwards::AffineNielsPoint;
use edwards::EdwardsBasepointTable;

/// Table containing precomputed multiples of the basepoint `B = (x,4/5)`.
///
/// The table is defined so `constants::base[i][j-1] = j*(16^2i)*B`,
/// for `0 ≤ i < 32`, `1 ≤ j < 9`.
pub const ED25519_BASEPOINT_TABLE: EdwardsBasepointTable = {:?};
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
