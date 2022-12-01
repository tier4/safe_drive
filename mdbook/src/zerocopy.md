# Zero Copy Publish and Subscribe

Under construction.

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

```text
$ iox-roudi
```
