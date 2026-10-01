//! Links the plugin against the Binary Ninja core library that
//! `binaryninjacore-sys` located (the last-run install, or `BINARYNINJADIR`).

fn main() {
    let link_path = std::env::var("DEP_BINARYNINJACORE_PATH").expect("binaryninjacore-sys reports the core's location");
    println!("cargo::rustc-link-lib=dylib=binaryninjacore");
    println!("cargo::rustc-link-search={link_path}");
    #[cfg(not(target_os = "windows"))]
    println!("cargo::rustc-link-arg=-Wl,-rpath,{link_path},-L{link_path}");
}
