pub mod common;

#[allow(unused_imports)]
use async_std::{future, prelude::*};
use common::msgs::example_msg::msg::Num;
use safe_drive::{
    self,
    context::Context,
    topic::{
        publisher::Publisher,
        subscriber::{Subscriber, TakenMsg},
    },
};
use std::{error::Error, time::Duration};

const TOPIC_NAME: &str = "test_async_pubsub";

#[test]
fn test_async_pubsub() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create nodes
    let node_pub = ctx.create_node("test_async_pub_node", None, Default::default())?;
    let node_sub = ctx.create_node("test_async_sub_node", None, Default::default())?;

    // create a publisher
    let p = common::create_publisher(node_pub, TOPIC_NAME).unwrap();

    // create a subscriber
    let s = common::create_subscriber(node_sub, TOPIC_NAME).unwrap();

    // create tasks
    async_std::task::block_on(async {
        let p = async_std::task::spawn(run_publisher(p));
        let s = async_std::task::spawn(run_subscriber(s));
        p.await;
        s.await;
    });

    println!("finished");

    Ok(())
}

/// The publisher
async fn run_publisher(p: Publisher<Num>) {
    let dur = Duration::from_millis(100);
    for n in 0..3 {
        // publish a message periodically
        let mut loaned = p.borrow_loaned_message().unwrap();
        *loaned = Num { num: n };
        if let Err(e) = p.send_loaned(loaned) {
            println!("error: {e}");
            return;
        }

        // sleep 100[ms]
        async_std::task::sleep(dur).await;
        println!("async publish: msg = {n}");
    }
}

/// The subscriber
async fn run_subscriber(mut s: Subscriber<Num>) {
    let dur = Duration::from_millis(500);
    for n in 0.. {
        // receive a message specifying timeout of 500ms
        match future::timeout(dur, s.recv()).await {
            Ok(Ok(msg)) => {
                match &msg {
                    TakenMsg::Loaned(_) => println!("loaned!"),
                    TakenMsg::Copied(_) => println!("copied!"),
                }

                // received a message
                println!("async subscribe: msg = {}", msg.num);
                assert_eq!(msg.num, n);
            }
            Ok(Err(e)) => panic!("{}", e), // fatal error
            Err(_) => {
                // timeout
                println!("async subscribe: timeout");
                break;
            }
        }
    }
}
