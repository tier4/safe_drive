# Zero Copy Publish and Subscribe

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/zerocopy).

In this chapter, we will introduce how to use zero copy communications by CycloneDDS.
To use CycloneDDS, please install it as [Eclipse Cyclone DDS](http://docs.ros.org.ros.informatik.uni-freiburg.de/en/humble/Installation/DDS-Implementations/Working-with-Eclipse-CycloneDDS.html).

## Create Project

First of all, create a project as follows.

```
$ cargo new zerocpy
```

The files we use are as follows. `cyclonedds.xml` will be created and used later.

| Files                   | What?                       |
|-------------------------|-----------------------------|
| zerocopy/Cargo.toml     | Cargo.toml                  |
| zerocopy/src/main.rs    | main.rs                     |
| zerocopy/cyclonedds.xml | configuration of CycloneDDS |

Add `safe_drive` to dependencies section of `Cargo.toml` as follows.

`Cargo.toml`

```toml
[dependencies]
safe_drive = "0.2"
```

## `main.rs`

`main.rs` can be implemented as follows,
but almost every lines are same as shown before.

`main.rs`

```rust
use safe_drive::{context::Context, msg::common_interfaces::std_msgs};
use std::{error::Error, time::Duration};

const TOPIC_NAME: &str = "pubsub_loaned";

fn main() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create a subscribe node
    let node_sub = ctx.create_node("loaned_sub_node", None, Default::default())?;

    // create a publish node
    let node_pub = ctx.create_node("loaned_pub_node", None, Default::default())?;

    std::thread::sleep(Duration::from_millis(500));

    // create a publisher and a subscriber
    let subscriber = node_sub.create_subscriber::<std_msgs::msg::Bool>(TOPIC_NAME, None)?;
    let publisher = node_pub.create_publisher::<std_msgs::msg::Bool>(TOPIC_NAME, None)?;

    let mut loaned = publisher.borrow_loaned_message()?;
    *loaned = std_msgs::msg::Bool::new().ok_or("failed to new Bool")?;
    loaned.data = false;
    publisher.send_loaned(loaned)?; // send message

    std::thread::sleep(Duration::from_millis(500));

    // wait messages
    let mut selector = ctx.create_selector()?;
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            assert!(!msg.data);
        }),
    );
    selector.wait()?;

    Ok(())
}
```

The important thing is using `borrow_loaned_message()` and `send_loaned()` methods as follows.

```rust
let mut loaned = publisher.borrow_loaned_message()?;
*loaned = std_msgs::msg::Bool::new().ok_or("failed to new Bool")?;
loaned.data = false;
publisher.send_loaned(loaned)?; // send message
```

`borrow_loaned_message()` borrows a memory region from CycloneDDS and
`send_loaned()` sends a message in the borrowed region.
`safe_drive` automatically check whether zero copy is available or not,
and it uses conventional copied APIs if zero copy is not available.

## Setting-up Zero Copy

To enable zero copy, please prepare cyclonedds.xml, which is a configuration file of CycloneDDS, as follows.
You can use arbitrary name for it.

`cyclonedds.xml`

```xml
<?xml version="1.0" encoding="UTF-8" ?>
<CycloneDDS xmlns="https://cdds.io/config" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="https://cdds.io/config https://raw.githubusercontent.com/eclipse-cyclonedds/cyclonedds/iceoryx/etc/cyclonedds.xsd">
    <Domain id="any">
        <SharedMemory>
            <Enable>true</Enable>
            <LogLevel>info</LogLevel>
        </SharedMemory>
    </Domain>
</CycloneDDS>
```

`<SharedMemory>` tag indicates the configuration of zero copy.

To use zero copy enabled CycloneDDS, please set environment arguments as follows.

```text
$ export RMW_IMPLEMENTATION=rmw_cyclonedds_cpp
$ export CYCLONEDDS_URI=file://path/to/cyclonedds.xml
```

In addition to that, CycloneDDS requires `iox-roudi` daemon to use zero copy.
It can be launched as follows.

```text
$ iox-roudi
```

## Execute

After that, zero copy communications can be performed!

```text
$ cargo run
```
