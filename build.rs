fn main() {
    println!("cargo:rustc-link-lib=rcl");
    println!("cargo:rustc-link-lib=rcutils");
    println!("cargo:rustc-link-lib=rmw");
    println!("cargo:rustc-link-lib=sample_msg__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=rosidl_runtime_c");
    println!("cargo:rustc-link-search=/opt/ros/galactic/lib");
    println!("cargo:rustc-link-search=supplements/ros2/install/sample_msg/lib");
}
