pub mod common;

use safe_drive::{self, error::RCLError, node::Node, selector::Selector};
use std::{error::Error, rc::Rc, sync::Arc, thread, time::Duration};

const TOPIC_NAME_1: &str = "test_select_1";
const TOPIC_NAME_2: &str = "test_select_2";
const TOPIC_NAME_3: &str = "test_select_3";
const INIT_1: i64 = 0;
const INIT_2: i64 = 100;
const COUNT: usize = 5;

#[test]
fn test_select_subscriptions() -> Result<(), Box<dyn Error>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create nodes
    let node_pub1 = safe_drive::node::Node::new(
        ctx.clone(),
        "test_select_pub1_node",
        None,
        Default::default(),
    )?;
    let node_pub2 = safe_drive::node::Node::new(
        ctx.clone(),
        "test_select_pub2_node",
        None,
        Default::default(),
    )?;
    let node_sub1 = safe_drive::node::Node::new(
        ctx.clone(),
        "test_select_sub1_node",
        None,
        Default::default(),
    )?;
    let node_sub2 = safe_drive::node::Node::new(
        ctx.clone(),
        "test_select_sub2_node",
        None,
        Default::default(),
    )?;

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

    let mut selector = Selector::new(ctx)?;
    selector.add_subscriber(&s1, None, false);
    selector.add_subscriber(&s2, None, false);

    let mut cnt1 = INIT_1;
    let mut cnt2 = INIT_2;
    for _ in 0..COUNT {
        // wait messages
        selector.wait(None)?;

        // s1 receives a message
        match s1.try_recv() {
            Ok(msg) => {
                assert_eq!(msg.num, cnt1);
                cnt1 += 1;
            }
            Err(RCLError::SubscriptionTakeFailed) => (),
            _ => panic!(),
        }

        // s2 receives a message
        match s2.try_recv() {
            Ok(msg) => {
                assert_eq!(msg.num, cnt2);
                cnt2 += 1;
            }
            Err(RCLError::SubscriptionTakeFailed) => (),
            _ => panic!(),
        }
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
        let msg = common::num::sample_msg__msg__Num { num: n };
        publisher.send(msg).unwrap(); // send message
    }
}

#[test]
fn test_callback() -> Result<(), Box<dyn Error>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create nodes
    let node_pub = safe_drive::node::Node::new(
        ctx.clone(),
        "test_callback_pub_node",
        None,
        Default::default(),
    )?;
    let node_sub = safe_drive::node::Node::new(
        ctx.clone(),
        "test_callback_pub_node",
        None,
        Default::default(),
    )?;

    // create a publisher
    let p = thread::spawn(move || {
        pub_thread(node_pub, TOPIC_NAME_3, Duration::from_millis(40), INIT_1)
    });

    // create a subscriber
    let s = Rc::new(common::create_subscriber(node_sub, TOPIC_NAME_3).unwrap());
    let s2 = s.clone();

    // register callback
    let mut selector = Selector::new(ctx)?;
    selector.add_subscriber(
        &s2,
        Some(Box::new(move || {
            let n = s.try_recv().unwrap();
            println!("callback: num = {}", n.num);
        })),
        false,
    );

    for _ in 0..COUNT {
        selector.wait(None)?;
    }

    p.join().unwrap();

    Ok(())
}

#[test]
fn test_async() -> Result<(), Box<dyn Error>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create nodes
    let node_pub =
        safe_drive::node::Node::new(ctx.clone(), "test_sync_pub_node", None, Default::default())?;
    let node_sub =
        safe_drive::node::Node::new(ctx.clone(), "test_sync_pub_node", None, Default::default())?;

    Ok(())
}
