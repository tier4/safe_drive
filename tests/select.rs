pub mod common;

use safe_drive::{self, node::Node};
use std::{error::Error, sync::Arc, thread, time::Duration};

const TOPIC_NAME_1: &str = "test_select_1";
const TOPIC_NAME_2: &str = "test_select_2";
const TOPIC_NAME_3: &str = "test_select_3";
const INIT_1: i64 = 0;
const INIT_2: i64 = 100;
const COUNT: usize = 5;

#[test]
fn test_select_subscriptions() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create nodes
    let node_pub1 = ctx.create_node("test_select_pub1_node", None, Default::default())?;
    let node_pub2 = ctx.create_node("test_select_pub2_node", None, Default::default())?;
    let node_sub1 = ctx.create_node("test_select_sub1_node", None, Default::default())?;
    let node_sub2 = ctx.create_node("test_select_sub2_node", None, Default::default())?;

    // create publishers
    let p1 = thread::spawn(move || {
        pub_thread(node_pub1, TOPIC_NAME_1, Duration::from_millis(40), INIT_1)
    });
    let p2 = thread::spawn(move || {
        pub_thread(node_pub2, TOPIC_NAME_2, Duration::from_millis(20), INIT_2)
    });

    // create subscribers
    let s1 = common::create_subscriber(node_sub1, TOPIC_NAME_1).unwrap();
    let s2 = common::create_subscriber(node_sub2, TOPIC_NAME_2).unwrap();

    let mut selector = ctx.create_selector()?;

    // 1st subscriber
    let mut cnt1 = Box::new(INIT_1);
    selector.add_subscriber(
        s1,
        Box::new(move |msg| {
            assert_eq!(msg.num, *cnt1);
            *cnt1 += 1;
        }),
        false,
    );

    // 2nd subscriber
    let mut cnt2 = Box::new(INIT_2);
    selector.add_subscriber(
        s2,
        Box::new(move |msg| {
            assert_eq!(msg.num, *cnt2);
            *cnt2 += 1;
        }),
        false,
    );

    for _ in 0..COUNT {
        // wait messages
        selector.wait()?;
    }

    p1.join().unwrap();
    p2.join().unwrap();

    Ok(())
}

fn pub_thread(node: Arc<Node>, topic_name: &str, dur: Duration, init: i64) {
    // create a publisher
    let publisher = common::create_publisher(node, topic_name).unwrap();

    // publish messages
    for i in 0..COUNT {
        thread::sleep(dur);
        let n = init + i as i64;
        let msg = common::num::example_msg__msg__Num { num: n };
        publisher.send(msg).unwrap(); // send message
    }
}

#[test]
fn test_callback() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create nodes
    let node_pub = ctx.create_node("test_callback_pub_node", None, Default::default())?;
    let node_sub = ctx.create_node("test_callback_pub_node", None, Default::default())?;

    // create a publisher
    let p = thread::spawn(move || {
        pub_thread(node_pub, TOPIC_NAME_3, Duration::from_millis(40), INIT_1)
    });

    let subscriber = common::create_subscriber(node_sub, TOPIC_NAME_3).unwrap();

    // register callback
    let mut selector = ctx.create_selector()?;
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            println!("callback: num = {}", msg.num);
        }),
        false,
    );

    for _ in 0..COUNT {
        selector.wait()?;
    }

    p.join().unwrap();

    Ok(())
}
