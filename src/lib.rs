//! # safe_drive: Formally Specified Rust Bindings for ROS2
//!
//! `safe_drive` is a Rust bindings for ROS2.
//! This library provides formal specifications and tested the specifications by using a model checker.
//! Therefore, you can clearly understand how the scheduler work and the safeness of it.`safe_drive` is a ROS2 bindings
//!
//! ## Specifications
//!
//! Some algorithms we adopted are formally specified and tested the safeness by using TLA+.
//! Original ROS2's executor (rclcpp) is suffering from starvation.
//! In contrast, the starvation freedom of our executor has been validated by not only dynamic analysis but also
//! formal verification.
//!
//! See [specifications](https://github.com/tier4/safe_drive/tree/main/specifications).
//!
//! We specified and tested as follows.
//!
//! - Async/await Scheduler
//!   - Deadlock freedom
//!   - Starvation freedom
//! - Single Threaded Callback Execution
//!   - Deadlock freedom
//!   - Starvation freedom
//! - Initialize Once
//!   - Deadlock freedom
//!   - Termination
//!   - Initialization is performed just once
//!
//! # Important Types
//!
//! - Topic
//!   - [`topic::publisher::Publisher`]
//!   - [`topic::subscriber::Subscriber`]
//!
//! ## Examples
//!
//! `safe_drive` provides single threaded and multi threaded execution methods.
//! The single threaded execution is based on traditional callback based execution.
//! You need to register callback functions for subscribers, servers, clients, and timers.
//!
//! The multi threaded execution is performed by async/await fashion.
//! You can choose any async/await's runtime.
//!
//! ### Single Threaded Execution
//!
//! This code is an example of Pub/Sub.
//!
//! ```
//! use safe_drive::{context::Context, logger::Logger, msg::common_interfaces::std_msgs, pr_info};
//! use std::{cell::RefCell, rc::Rc, time::Duration};
//!
//! // First of all, you need create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a publish node.
//! let node_pub = ctx
//!     .create_node("publish_node", None, Default::default())
//!     .unwrap();
//!
//! // Create a subscribe node.
//! let node_sub = ctx
//!     .create_node("subscribe_node", None, Default::default())
//!     .unwrap();
//!
//! // Create a publisher.
//! // The 2nd argument is for QoS.
//! // If `None` is specified to the 2nd argument, the default QoS will be used.
//! let publisher = node_pub
//!     .create_publisher::<std_msgs::msg::String>("example_topic", None)
//!     .unwrap();
//!
//! // Create a subscriber.
//! let subscriber = node_sub
//!     .create_subscriber::<std_msgs::msg::String>("example_topic", None)
//!     .unwrap();
//!
//! // Use `Rc` and `RefCell` to share the subscriber by multiple callback functions,
//! let sub1 = Rc::new(RefCell::new(subscriber));
//! let sub2 = sub1.clone();
//!
//! // Create a selector, which is for IO multiplexing.
//! let mut selector = ctx.create_selector().unwrap();
//!
//! // Create loggers.
//! let logger_pub = Logger::new("example_publisher");
//! let logger_sub = Logger::new("example_subscriber");
//!
//! // Add subscriber to the selector.
//! // The 2nd argument is a callback function.
//! // If data arrive, the callback will be invoked.
//! // The 3rd argument is used to specify the callback will be invoked only once or infinitely.
//! // If the 3rd argument is `true`, the callback function is invoked once and unregistered.
//! selector.add_subscriber(
//!     &sub1.borrow(),
//!     Some(Box::new(move || {
//!         let sub = sub2.borrow();
//!
//!         // Receive messages;
//!         while let Ok(msg) = sub.try_recv() {
//!             pr_info!(logger_sub, "Received: msg = {}", msg.data); // Print a message.
//!         }
//!     })),
//!     false,
//! );
//!
//! // Create a wall timer, which invoke the callback periodically.
//! selector.add_wall_timer(
//!     Duration::from_millis(100),
//!     Box::new(move || {
//!         let mut msg = std_msgs::msg::String::new().unwrap();
//!         msg.data.assign("Hello, World!");
//!         pr_info!(logger_pub, "Send: msg = {}", msg.data); // Print a message.
//!         publisher.send(msg).unwrap();
//!     }),
//! );
//!
//! // Spin.
//! for _ in 0..10 {
//!     selector.wait().unwrap();
//! }
//! ```
//!
//! ### Multi Threaded Execution
//!
//! This code uses `async_std` as a async/await's runtime.
//! You can use other runtime such as `tokio`.
//!
//! ```
//! use safe_drive::{
//!     context::Context,
//!     error::DynError,
//!     logger::Logger,
//!     msg::common_interfaces::std_msgs,
//!     pr_info, pr_warn,
//!     topic::{publisher::Publisher, subscriber::Subscriber},
//! };
//! #[allow(unused_imports)]
//! use async_std::{future, prelude::*};
//! use std::time::Duration;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create nodes.
//! let node_pub = ctx
//!     .create_node("publish_node_async", None, Default::default())
//!     .unwrap();
//! let node_sub = ctx
//!     .create_node("subscribe_node_async", None, Default::default())
//!     .unwrap();
//!
//! // Create a publisher.
//! let publisher = node_pub
//!     .create_publisher::<std_msgs::msg::String>("example_topic_async", None)
//!     .unwrap();
//!
//! // Create a subscriber.
//! let subscriber = node_sub
//!     .create_subscriber::<std_msgs::msg::String>("example_topic_async", None)
//!     .unwrap();
//!
//! // Create tasks.
//! async_std::task::block_on(async {
//!     let p = async_std::task::spawn(run_publisher(publisher));
//!     let s = async_std::task::spawn(run_subscriber(subscriber));
//!     p.await;
//!     s.await;
//! });
//!
//! /// The publisher.
//! async fn run_publisher(publisher: Publisher<std_msgs::msg::String>) {
//!     let dur = Duration::from_millis(100);
//!     let logger = Logger::new("example_publisher_async");
//!     for _ in 0..10 {
//!         // Publish a message periodically.
//!         let mut msg = std_msgs::msg::String::new().unwrap();
//!         msg.data.assign("Hello, World!");
//!
//!         pr_info!(logger, "Send (async): msg = {}", msg.data);
//!         publisher.send(msg).unwrap();
//!
//!         // Sleep 100[ms].
//!         async_std::task::sleep(dur).await;
//!     }
//! }
//!
//! /// The subscriber
//! async fn run_subscriber(mut s: Subscriber<std_msgs::msg::String>) {
//!     let dur = Duration::from_millis(500);
//!     let logger = Logger::new("example_subscriber_async");
//!     loop {
//!         // receive a message specifying timeout of 500ms
//!         match future::timeout(dur, s.recv()).await {
//!             Ok(Ok(msg)) => {
//!                 // received a message
//!                 pr_info!(logger, "Received (async): msg = {}", msg.data);
//!             }
//!             Ok(Err(e)) => panic!("{}", e), // fatal error
//!             Err(_) => {
//!                 // timeout
//!                 pr_warn!(logger, "Subscribe (async): timeout");
//!                 break;
//!             }
//!         }
//!     }
//! }
//! ```

use std::{cell::Cell, marker::PhantomData, sync::MutexGuard};

pub mod context;
pub mod error;
pub mod logger;
pub mod msg;
pub mod node;
pub mod qos;
pub mod rcl;
pub mod selector;
pub mod service;
pub mod topic;

mod delta_list;
mod helper;
mod signal_handler;
mod time;

type PhantomUnsync = PhantomData<Cell<()>>;
type _PhantomUnsend = PhantomData<MutexGuard<'static, ()>>;

pub use signal_handler::is_halt;

#[cfg(test)]
mod tests {
    mod multi_threaded {
        use crate::{
            context::Context,
            error::DynError,
            logger::{pr_info_in, pr_warn_in, Logger},
            msg::common_interfaces::std_msgs,
            topic::{publisher::Publisher, subscriber::Subscriber},
        };
        #[allow(unused_imports)]
        use async_std::{future, prelude::*};
        use std::time::Duration;

        #[test]
        fn test_async() -> Result<(), DynError> {
            // Create a context.
            let ctx = Context::new()?;

            // Create nodes.
            let node_pub = ctx.create_node("publish_node_async", None, Default::default())?;
            let node_sub = ctx.create_node("subscribe_node_async", None, Default::default())?;

            // Create a publisher.
            let publisher = node_pub
                .create_publisher::<std_msgs::msg::String>("example_topic_async", None)
                .unwrap();

            // Create a subscriber.
            let subscriber = node_sub
                .create_subscriber::<std_msgs::msg::String>("example_topic_async", None)
                .unwrap();

            // Create tasks.
            async_std::task::block_on(async {
                let p = async_std::task::spawn(run_publisher(publisher));
                let s = async_std::task::spawn(run_subscriber(subscriber));
                p.await;
                s.await;
            });

            Ok(())
        }

        /// The publisher.
        async fn run_publisher(publisher: Publisher<std_msgs::msg::String>) {
            let dur = Duration::from_millis(100);
            let logger = Logger::new("example_publisher_async");
            for _ in 0..10 {
                // Publish a message periodically.
                let mut msg = std_msgs::msg::String::new().unwrap();
                msg.data.assign("Hello, World!");

                pr_info_in!(logger, "Send (async): msg = {}", msg.data);
                publisher.send(msg).unwrap();

                // Sleep 100[ms].
                async_std::task::sleep(dur).await;
            }
        }

        /// The subscriber
        async fn run_subscriber(mut s: Subscriber<std_msgs::msg::String>) {
            let dur = Duration::from_millis(500);
            let logger = Logger::new("example_subscriber_async");
            loop {
                // receive a message specifying timeout of 500ms
                match future::timeout(dur, s.recv()).await {
                    Ok(Ok(msg)) => {
                        // received a message
                        pr_info_in!(logger, "Received (async): msg = {}", msg.data);
                    }
                    Ok(Err(e)) => panic!("{}", e), // fatal error
                    Err(_) => {
                        // timeout
                        pr_warn_in!(logger, "Subscribe (async): timeout");
                        break;
                    }
                }
            }
        }
    }

    mod single_threaded {
        use crate::{
            context::Context,
            logger::{pr_info_in, Logger},
            msg::common_interfaces::std_msgs,
        };
        use std::{cell::RefCell, rc::Rc, time::Duration};

        #[test]
        fn test_single_threaded() {
            // First of all, you need create a context.
            let ctx = Context::new().unwrap();

            // Create a publish node.
            let node_pub = ctx
                .create_node("publish_node", None, Default::default())
                .unwrap();

            // Create a subscribe node.
            let node_sub = ctx
                .create_node("subscribe_node", None, Default::default())
                .unwrap();

            // Create a publisher.
            // The 2nd argument is for QoS.
            // If `None` is specified to the 2nd argument, the default QoS will be used.
            let publisher = node_pub
                .create_publisher::<std_msgs::msg::String>("example_topic", None)
                .unwrap();

            // Create a subscriber.
            let subscriber = node_sub
                .create_subscriber::<std_msgs::msg::String>("example_topic", None)
                .unwrap();

            // Use `Rc` and `RefCell` to share the subscriber by multiple callback functions,
            let sub1 = Rc::new(RefCell::new(subscriber));
            let sub2 = sub1.clone();

            // Create a selector, which is for IO multiplexing.
            let mut selector = ctx.create_selector().unwrap();

            // Create loggers.
            let logger_pub = Logger::new("example_publisher");
            let logger_sub = Logger::new("example_subscriber");

            // Add subscriber to the selector.
            // The 2nd argument is a callback function.
            // If data arrive, the callback will be invoked.
            // The 3rd argument is used to specify the callback will be invoked only once or infinitely.
            // If the 3rd argument is `true`, the callback function is invoked once and unregistered.
            selector.add_subscriber(
                &sub1.borrow(),
                Some(Box::new(move || {
                    let sub = sub2.borrow();

                    // Receive messages;
                    while let Ok(msg) = sub.try_recv() {
                        pr_info_in!(logger_sub, "Received: msg = {}", msg.data);
                        // Print a message.
                    }
                })),
                false,
            );

            // Create a wall timer, which invoke the callback periodically.
            selector.add_wall_timer(
                Duration::from_millis(100),
                Box::new(move || {
                    let mut msg = std_msgs::msg::String::new().unwrap();
                    msg.data.assign("Hello, World!");
                    pr_info_in!(logger_pub, "Send: msg = {}", msg.data); // Print a message.
                    publisher.send(msg).unwrap();
                }),
            );

            // Spin.
            for _ in 0..10 {
                selector.wait().unwrap();
            }
        }
    }
}
