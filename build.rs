fn main() {
    println!("cargo:rustc-link-lib=rcl");
    println!("cargo:rustc-link-lib=rcl_action");
    println!("cargo:rustc-link-lib=rcutils");
    println!("cargo:rustc-link-lib=rmw");
    println!("cargo:rustc-link-lib=rosidl_runtime_c");

    println!("cargo:rustc-link-lib=actionlib_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=actionlib_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=action_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=action_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=builtin_interfaces__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=builtin_interfaces__rosidl_generator_c");
    println!("cargo:rustc-link-lib=diagnostic_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=diagnostic_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=geometry_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=geometry_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=nav_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=nav_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=sensor_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=sensor_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=shape_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=shape_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=std_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=std_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=std_srvs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=std_srvs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=stereo_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=stereo_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=trajectory_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=trajectory_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=unique_identifier_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=unique_identifier_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=visualization_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=visualization_msgs__rosidl_generator_c");
    println!("cargo:rustc-link-lib=rcl_interfaces__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=rcl_interfaces__rosidl_generator_c");
    println!("cargo:rustc-link-lib=action_msgs__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=action_msgs__rosidl_generator_c");

    if std::env::var_os("SAFE_DRIVE_TEST").is_some() {
        println!("cargo:rustc-link-lib=example_msg__rosidl_typesupport_c");
        println!("cargo:rustc-link-lib=example_msg__rosidl_generator_c");
        println!("cargo:rustc-link-search=supplements/ros2/install/example_msg/lib");
    }

    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(':') {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }

    println!("cargo:rerun-if-env-changed=ROS_DISTRO");
    let distro_name = std::env::var_os("ROS_DISTRO");
    match &*distro_name.and_then(|v| v.into_string().ok()).unwrap_or("".to_string()) {
        "iron" => {
            println!("cargo:rustc-link-lib=service_msgs__rosidl_typesupport_c");
            println!("cargo:rustc-link-lib=service_msgs__rosidl_generator_c");
            println!("cargo:rustc-cfg=feature=\"iron\"");
        }
        "humble" => println!("cargo:rustc-cfg=feature=\"humble\""),
        "galactic" => println!("cargo:rustc-cfg=feature=\"galactic\""),

        _ => {
            let default = "iron";

            println!("cargo:warning='ROS_DISTRO is not set properly. Defaulting to {default}.'");
            println!("cargo:rustc-link-lib=service_msgs__rosidl_typesupport_c");
            println!("cargo:rustc-link-lib=service_msgs__rosidl_generator_c");
            println!("cargo:rustc-cfg=feature=\"{default}\"");
        },
    }
}
