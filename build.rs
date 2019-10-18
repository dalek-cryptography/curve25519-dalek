//Detect Host and choose backend to use

use rustc_version::{
    version_meta, 
    Channel
};
use std_detect::is_x86_feature_detected;

fn main() {

    if cfg!(target_pointer_width = "32") {
        println!("cargo:rustc-cfg=feature=\"u32_backend\"\n");
    } else {
        println!("cargo:rustc-cfg=feature=\"u64_backend\"\n");
    }

    if is_x86_feature_detected!("avx2") || is_x86_feature_detected!("avx512ifma") {
        println!("cargo:rustc-cfg=feature=\"simd_backend\"\n");
    } 

    // // XXX this should be replaced with autoselection logic.
    // // Enable the "stage2_build" feature in the main build stage
    // //println!("cargo:rustc-cfg=feature=\"stage2_build\"\n");

    match version_meta().unwrap().channel {
        Channel::Stable => {
            println!("cargo:rustc-cfg=stable");
            println!("cargo:rustc-cfg=feature=\"std\"\n");
        }
        Channel::Beta => {
            println!("cargo:rustc-cfg=beta");
            println!("cargo:rustc-cfg=feature=\"std\"\n");
        }
        Channel::Nightly => {
            println!("cargo:rustc-cfg=nightly");
            println!("cargo:rustc-cfg=feature=\"nightly\"\n");
            println!("cargo:rustc-cfg=feature=\"std\"\n");
        }
        Channel::Dev => {
            println!("cargo:rustc-cfg=dev");
            println!("cargo:rustc-cfg=feature=\"std\"\n");
        }
    }

    
}
