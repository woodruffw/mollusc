// This is an ugly little hack to get access to a reasonable "default"
// target triple when loading bitcode inputs that don't mention their triple.
// Based on: https://stackoverflow.com/a/51311222
fn main() {
    println!(
        "cargo:rustc-env=TARGET_TRIPLE={}",
        std::env::var("TARGET").unwrap()
    );
}
