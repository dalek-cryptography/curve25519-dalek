use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(curve25519_cuda)");
    let target = env::var("TARGET").unwrap_or_default();
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let sppark_dir = manifest_dir.join("..").join("sppark");
    let blst_dir = sppark_dir.join("blst");
    let blst_lib = blst_dir.join("libblst.a");
    let cuda_file = sppark_dir
        .join("poc")
        .join("msm-cuda")
        .join("cuda")
        .join("pippenger_curve25519.cu");
    let all_gpus = sppark_dir.join("util").join("all_gpus.cpp");
    let blst_include = blst_dir.join("src");

    let nvcc = env::var("NVCC")
        .ok()
        .or_else(|| which::which("nvcc").ok().map(|p| p.display().to_string()));
    if nvcc.is_none() {
        println!("cargo:warning=NVCC not found; Curve25519 CUDA backend disabled");
        return;
    }

    if !blst_lib.exists() {
        let status = Command::new("./build.sh")
            .current_dir(&blst_dir)
            .status()
            .expect("failed to run blst build.sh");
        if !status.success() {
            panic!("blst build failed");
        }
    }

    if env::var("CXX").is_err() {
        let cxx = which::which("g++-12")
            .or_else(|_| which::which("g++"))
            .ok()
            .map(|p| p.display().to_string());
        if let Some(cxx) = cxx {
            unsafe {
                env::set_var("CXX", &cxx);
                if !target.is_empty() {
                    env::set_var(format!("CXX_{}", target), &cxx);
                }
            }
        }
    }

    let mut nvcc_build = cc::Build::new();
    nvcc_build
        .cuda(true)
        .flag("-std=c++17")
        .flag("-allow-unsupported-compiler")
        .flag("-Xcompiler")
        .flag("-std=gnu++17")
        .define("__ADX__", None)
        .include(&sppark_dir)
        .include(&blst_include)
        .file(&cuda_file)
        .file(&all_gpus);
    nvcc_build.compile("curve25519_cuda_msm");

    println!("cargo:rustc-link-search=native={}", blst_dir.display());
    println!("cargo:rustc-link-lib=static=blst");
    println!("cargo:rustc-link-lib=dylib=cudart");
    println!("cargo:rustc-cfg=curve25519_cuda");
    println!("cargo:rerun-if-changed={}", cuda_file.display());
    println!("cargo:rerun-if-changed={}", all_gpus.display());
}
