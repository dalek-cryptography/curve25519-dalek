use rustc_version::{version, version_meta, Channel};

fn main() {
    // XXX this should be replaced with autoselection logic.
    // Enable the "stage2_build" feature in the main build stage
    //println!("cargo:rustc-cfg=feature=\"stage2_build\"\n");

    match version_meta().unwrap().channel {
        Channel::Stable => {
            println!("cargo:rustc-cfg=stable");
        }
        Channel::Beta => {
            println!("cargo:rustc-cfg=beta");
        }
        Channel::Nightly => {
            println!("cargo:rustc-cfg=nightly");
            println!("cargo:rustc-cfg=feature=nightly");
        }
        Channel::Dev => {
            println!("cargo:rustc-cfg=dev");
        }
    }
}
