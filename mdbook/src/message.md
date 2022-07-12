# User Defined Data Structure

## Installing `ros2msg_to_rs`

```text
$ git clone https://github.com/tier4/ros2msg_to_rs.git
$ cd ros2msg_to_rs
$ cargo build --release
$ cargo instal --path .
```

```text
$ mkdir -p msgtest/src
```

## Defining User Defined Type

```text
$ cd msgtest/src
$ ros2 pkg create --build-type ament_cmake my_interfaces
$ cd my_interfaces
$ mkdir msg
$ cd msg
```

`msgtest/src/my_interfaces/msg`

`msgtest/src/my_interfaces/msg/MyMsg.msg`

```text
string message
string[2] static_array_str
string[] dynamic_array_str
string[<=3] bounded_array_str

string<=10 bounded_str
string<=10[2] static_array_bounded_str
string<=10[] dynamic_array_bounded_str
string<=10[<=3] bounded_array_bounded_str
```

`msgtest/src/my_interfaces/msg/MyMsgs.msg`

```text
MyMsg msg1
MyMsg msg2
```


```text
$ cd msgtest/src
$ cargo new --lib my_interfaces_rs
$ ros2msg_to_rs -o my_interfaces_rs/src -i my_interfaces
$ generating: my_interfaces_rs/src/msg/msg/my_msg.rs
$ generating: my_interfaces_rs/src/msg/msg.rs
$ generating: my_interfaces_rs/src/mod.rs
$ generating: my_interfaces_rs/src/msg/mod.rs
```

```cmake
# msgtest/src/my_interfaces/CMakeLists.txt
find_package(rosidl_default_generators REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "msg/MyMsg.msg"
)
```

```xml
<!-- msgtest/src/my_interfaces/package.xml -->
<build_depend>rosidl_default_generators</build_depend>

<exec_depend>rosidl_default_runtime</exec_depend>

<member_of_group>rosidl_interface_packages</member_of_group>
```

## User Defined Type in Rust

```text
$ cd msgtest/src
$ create new --lib my_interfaces_rs
$ ros2msg_to_rs -o ./my_interfaces_rs/src -i ./
```

```rust
// msgtest/src/my_interfaces_rs/src/my_interfaces/msg/my_msg.rs
#[repr(C)]
#[derive(Debug)]
pub struct MyMsg {
    pub message: safe_drive::msg::RosString<0>,
    pub static_array_str: [safe_drive::msg::RosString<0>; 2],
    pub dynamic_array_str: safe_drive::msg::RosStringSeq<0, 0>,
    pub bounded_array_str: safe_drive::msg::RosStringSeq<0, 3>,
    pub bounded_str: safe_drive::msg::RosString<10>,
    pub static_array_bounded_str: [safe_drive::msg::RosString<10>; 2],
    pub dynamic_array_bounded_str: safe_drive::msg::RosStringSeq<10, 0>,
    pub bounded_array_bounded_str: safe_drive::msg::RosStringSeq<10, 3>,
}
```

```rust
// msgtest/src/my_interfaces_rs/src/my_interfaces/msg/my_msgs.rs
#[repr(C)]
#[derive(Debug)]
pub struct MyMsgs {
    pub msg1: MyMsg,
    pub msg2: MyMsg,
}
```

```rust
// msgtest/src/my_interfaces_rs/src/lib.rs
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::too_many_arguments)]

pub mod my_interfaces;
```

```xml
<!-- msgtest/src/my_interfaces_rs/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>my_interfaces_rs</name>
  <version>0.0.0</version>
  <description>My Interfaces in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

```rust
// msgtest/src/my_interfaces_rs/build.rs
fn main() {
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_generator_c");
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_typesupport_c");
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_typesupport_introspection_c");
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_typesupport_fastrtps_c");

    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(':') {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```
