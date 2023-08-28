use safe_drive::{context::Context, msg::common_interfaces::std_msgs};
use std::{error::Error, time::Duration};

#[test]
fn test_timer() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    let ctx = Context::new()?;
    let mut selector = ctx.create_selector()?;

    selector.add_timer(
        Duration::from_millis(100),
        Box::new(|| {
            println!("timer: 100[ms]");
        }),
    );

    selector.add_timer(
        Duration::from_millis(200),
        Box::new(|| {
            println!("timer: 200[ms]");
        }),
    );

    for _ in 0..2 {
        selector.wait()?;
    }

    Ok(())
}

/// ROS2's executor causes starvation.
///
/// [callback_group_based_sample_node.cpp](https://github.com/takam5f2/executer_exam/blob/main/src/nodes/callback_group_based_sample_node.cpp)
/// is an example of the starvation.
///
/// In contrast, our executor does not cause starvation.
#[test]
fn test_wall_timer() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    let ctx = Context::new()?;
    let mut selector = ctx.create_selector()?;

    // create a publish node
    let node = ctx.create_node("test_wall_timer_node", None, Default::default())?;

    // create a publisher and a subscriber
    #[cfg(any(feature = "humble", feature = "galactic"))]
    let publisher =
        node.create_publisher::<std_msgs::msg::String>("test_wall_timer_node_pubsub", None)?;

    #[cfg(any(feature = "humble", feature = "galactic"))]
    let subscriber =
        node.create_subscriber::<std_msgs::msg::String>("test_wall_timer_node_pubsub", None)?;

    #[cfg(not(any(feature = "humble", feature = "galactic")))]
    let publisher =
        node.create_publisher::<std_msgs::msg::String>("test_wall_timer_node_pubsub", None, true)?;

    #[cfg(not(any(feature = "humble", feature = "galactic")))]
    let subscriber =
        node.create_subscriber::<std_msgs::msg::String>("test_wall_timer_node_pubsub", None, true)?;

    // create wall timers
    selector.add_wall_timer(
        "timer1",
        Duration::from_millis(1000),
        Box::new(|| {
            println!("long timer: 1000[ms]");
            std::thread::sleep(Duration::from_millis(1000));
        }),
    );

    selector.add_wall_timer(
        "timer2",
        Duration::from_millis(200),
        Box::new(move || {
            println!("short timer: 200[ms]");
            let mut msg = std_msgs::msg::String::new().unwrap();
            msg.data.assign("Hello, World!");
            publisher.send(&msg).unwrap();
            std::thread::sleep(Duration::from_millis(100));
        }),
    );

    // set a callback for the subscriber
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            println!("recv: {}", msg.data);
        }),
    );

    // spin
    for _ in 0..20 {
        selector.wait()?;
    }

    Ok(())
}
