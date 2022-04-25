fn main() {
    println!("cargo:rustc-link-lib=rcl");
    println!("cargo:rustc-link-lib=rcutils");
    println!("cargo:rustc-link-search=/opt/ros/galactic/lib");
}
