# Service

```text
$ mkdir -p srvtest/src
$ cd srvtest/src
$ cargo new server
$ cargo new client
$ cargo new --lib srvmsg_rs
$ ros2 pkg create --build-type ament_cmake srvmsg
```

## Define Protocol

```text
$ cd srvtest/src/srvmsg
$ mkdir srv
```

`srvmsg/srv/AddTwoInts.srv`

```text
uint32 x
uint32 y
---
uint32 result
```

```cmake
# srvtest/src/srvmsg/CMakeLists.txt
find_package(rosidl_default_generators REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "srv/AddTwoInts.srv"
)
```

```xml
<!-- srvtest/src/srvmsg/package.xml -->
<build_depend>rosidl_default_generators</build_depend>

<exec_depend>rosidl_default_runtime</exec_depend>

<member_of_group>rosidl_interface_packages</member_of_group>
```

```text
$ cd srvtest/src
$ ros2msg_to_rs  -i ./ -o ./srvmsg_rs/src
generating: ./srvmsg_rs/src/srvmsg/srv/add_two_ints.rs
generating: ./srvmsg_rs/src/srvmsg/srv.rs
generating: ./srvmsg_rs/src/mod.rs
generating: ./srvmsg_rs/src/srvmsg/mod.rs
```

## `srvmsg_rs`

```rust
// srvtest/src/srvmsg_rs/src/lib.rs
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::too_many_arguments)]

pub mod srvmsg;
```

```toml
# srvtest/src/srvmsg_rs/Cargo.toml
[dependencies]
safe_drive = { path = "/root/safe_drive" }
```

```
// srvtest/src/srvmsg_rs/build.rs
fn main() {
    println!("cargo:rustc-link-lib=srvmsg__rosidl_generator_c");
    println!("cargo:rustc-link-lib=srvmsg__rosidl_typesupport_c");

    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(':') {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```

```xml
<!-- srvtest/src/srvmsg_rs/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>srvmsg_rs</name>
  <version>0.0.0</version>
  <description>Protocol Definition in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

## Server

```rust
use safe_drive::{context::Context, error::DynError, logger::Logger, pr_error, qos::Profile};
use srvmsg_rs::srvmsg::srv::{AddTwoInts, AddTwoIntsResponse};

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("server_node", None, Default::default())?;

    // Create a server.
    let server = node.create_server::<AddTwoInts>("my_service", Some(Profile::default()))?;

    // Create a selector.
    let mut selector = ctx.create_selector()?;

    // Create a logger.
    let logger = Logger::new("server");

    selector.add_server(
        server,
        Box::new(move |msg, _header| {
            let mut response = AddTwoIntsResponse::new().unwrap();
            pr_error!(logger, "recv: {:?}", msg);
            response.result = msg.x + msg.y;
            response
        }),
    );

    loop {
        selector.wait()?; // Spin.
    }
}
```

```toml
# srvtest/src/server/Cargo.toml
[dependencies]
safe_drive = { path = "/root/safe_drive" }
srvmsg_rs = { path = "../srvmsg_rs" }
```

```xml
<!-- srvtest/src/server/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>server</name>
  <version>0.0.0</version>
  <description>Server in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>srvmsg</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

Don't forget `<depend>srvmsg</depend>`.

## Client

```toml
# srvtest/src/client/Cargo.toml
[dependencies]
safe_drive = { path = "/root/safe_drive" }
srvmsg_rs = { path = "../srvmsg_rs" }
tokio = { version = "1", features = ["full"] }
```

```xml
<!-- srvtest/src/client/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>client</name>
  <version>0.0.0</version>
  <description>Client in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>srvmsg</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

Don't forget `<depend>srvmsg</depend>`.
