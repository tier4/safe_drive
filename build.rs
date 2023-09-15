#[cfg(target_os = "windows")]
// for windows find and add all ros2 libraries to avoid link issues
fn print_all_libs(path: std::path::PathBuf) {
    if path.exists() {
        if let Ok(entries) = std::fs::read_dir(&path) {
            for pp in entries
                .into_iter()
                .filter(|e| e.is_ok())
                .map(|e| e.unwrap().path())
                .filter(|p| p.is_file() && p.extension().is_some())
            {
                if let Some(p) = pp.to_str() {
                    if p.ends_with("_c.lib") {
                        println!(
                            "cargo:rustc-link-lib={}",
                            pp.file_stem().unwrap().to_str().unwrap()
                        );
                    }
                }
            }
        }
        if let Some(pp) = path.to_str() {
            println!("cargo:rustc-link-search={}", pp);
        }
    }
}

#[cfg(not(target_os = "windows"))]
fn print_all_libs(_path: std::path::PathBuf) {}

fn main() {
    println!("cargo:rustc-link-lib=rcl");
    println!("cargo:rustc-link-lib=rcl_action");
    println!("cargo:rustc-link-lib=rcutils");
    println!("cargo:rustc-link-lib=rmw");
    println!("cargo:rustc-link-lib=rosidl_runtime_c");

    if !cfg!(target_os = "windows") {
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
    }

    if std::env::var_os("SAFE_DRIVE_TEST").is_some() {
        println!("cargo:rustc-link-lib=example_msg__rosidl_typesupport_c");
        println!("cargo:rustc-link-lib=example_msg__rosidl_generator_c");
        println!("cargo:rustc-link-search=supplements/ros2/install/example_msg/lib");
    }

    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        if cfg!(target_os = "windows") {
            for path in env.split(';') {
                print_all_libs(std::path::Path::new(path).join("Lib"));
            }
        } else {
            for path in env.split(':') {
                println!("cargo:rustc-link-search={path}/lib");
            }
        }
    }
    if cfg!(target_os = "windows") {
        if let Some(e) = std::env::var_os("CMAKE_PREFIX_PATH") {
            let env = e.to_str().unwrap();
            for path in env.split(';') {
                print_all_libs(std::path::Path::new(path).join("lib"));
            }
        }
    }

    if let Some(e) = std::env::var_os("ROS_DISTRO") {
        match e.to_str().unwrap() {
            "iron" => {
                println!("cargo:rustc-link-lib=service_msgs__rosidl_typesupport_c");
                println!("cargo:rustc-link-lib=service_msgs__rosidl_generator_c");
                println!("cargo:rustc-cfg=feature=\"iron\"");
            }
            "humble" => println!("cargo:rustc-cfg=feature=\"humble\""),
            "galactic" => println!("cargo:rustc-cfg=feature=\"galactic\""),
            _ => (),
        }
    }
}
