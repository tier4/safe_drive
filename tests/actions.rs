pub mod common;

use common::action_msg::action::my_action::*;
use safe_drive::{
    self,
    action::{
        client::Client,
        handle::GoalHandle,
        server::{Server, ServerQosOption},
        GoalStatus,
    },
    context::Context,
    error::DynError,
    msg::{
        builtin_interfaces::UnsafeTime,
        interfaces::action_msgs::{msg::GoalInfo, srv::CancelGoalRequest},
        unique_identifier_msgs::msg::UUID,
    },
    RecvResult,
};
use std::{sync::Arc, thread, time::Duration};

fn create_server(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
    qos: Option<ServerQosOption>,
) -> Result<Server<MyAction>, DynError> {
    let node_server = ctx.create_node(node, None, Default::default()).unwrap();

    Server::new(node_server, action, qos).map_err(|e| e.into())
}

fn create_client(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
) -> Result<Client<MyAction>, DynError> {
    let options = safe_drive::node::NodeOptions::default();
    let node_client = ctx.create_node(node, None, options)?;
    Client::new(node_client, action, None).map_err(|e| e.into())
}

fn goal_handler(handle: GoalHandle<MyAction>, req: MyAction_SendGoal_Request) -> bool {
    println!("Goal request received: {:?}", req);

    std::thread::Builder::new()
        .name("worker".into())
        .spawn(move || {
            for c in 0..=5 {
                std::thread::sleep(Duration::from_secs(2));
                println!("server worker: sending feedback {c}");
                let feedback = MyAction_Feedback { c };
                handle.feedback(feedback).unwrap();
            }

            println!("server worker: sending result");
            handle.finish(MyAction_Result { b: 500 }).unwrap();

            loop {
                std::thread::sleep(Duration::from_secs(5));
            }
        })
        .unwrap();

    true
}

#[test]
fn test_action() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let client = create_client(&ctx, "test_action_client", "test_action")?;

    let mut selector = ctx.create_selector()?;
    let server = create_server(&ctx, "test_action_server", "test_action", None)?;

    // send goal request
    let uuid: [u8; 16] = rand::random();
    let uuid_ = uuid;
    let goal = MyAction_Goal { a: 10 };
    let mut recv = client.send_goal_with_uuid(goal, uuid)?;

    thread::sleep(Duration::from_millis(100));

    // You don't have to set handlers for incoming result requests since they are processed
    // automatically.
    selector.add_action_server(server, goal_handler, move |goal| {
        println!("Cancel request received for goal {:?}", goal);
        true
    });
    selector.wait()?;

    let client = loop {
        match recv.recv_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok((client, data, header)) => {
                println!(
                    "received goal response: accepted = {:?}, seq = {}",
                    data.accepted, header.sequence_number
                );
                break client;
            }
            RecvResult::RetryLater(receiver) => {
                recv = receiver;
            }
            RecvResult::Err(e) => panic!("{}", e),
        }
    };

    // get feedback (wait for five feedback messages)
    let mut received = 0;
    loop {
        match client.recv_feedback_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok(feedback) => {
                println!("received feedback: {:?}", feedback);
                received += 1;
                if received > 5 {
                    break;
                }
            }
            RecvResult::RetryLater(()) => {}
            RecvResult::Err(e) => panic!("{}", e),
        }
    }

    let mut goal_id = UUID::new().unwrap();
    goal_id.uuid = uuid_;
    let result_req = MyAction_GetResult_Request { goal_id };
    let mut recv = client.send_result_request(&result_req)?;

    selector.wait()?;

    loop {
        match recv.recv_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok((_, data, header)) => {
                println!(
                    "received result: result = {:?} status = {:?}, seq = {}",
                    data.result, data.status, header.sequence_number
                );
                break;
            }
            RecvResult::RetryLater(receiver) => {
                recv = receiver;
            }
            RecvResult::Err(e) => panic!("{}", e),
        };
    }

    Ok(())
}

#[test]
fn test_action_cancel() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let client = create_client(&ctx, "test_action_cancel_client", "test_action_cancel")?;

    let mut selector = ctx.create_selector()?;
    let server = create_server(
        &ctx,
        "test_action_cancel_server",
        "test_action_cancel",
        None,
    )?;

    // send goal request
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let mut recv = client.send_goal_with_uuid(goal, uuid)?;

    thread::sleep(Duration::from_millis(100));

    selector.add_action_server(server, goal_handler, move |goal| {
        println!("Cancel request received for goal {:?}", goal);
        true
    });
    selector.wait()?;

    let client = loop {
        match recv.recv_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok((client, data, header)) => {
                println!(
                    "received goal response: accepted = {:?}, seq = {}",
                    data.accepted, header.sequence_number
                );
                break client;
            }
            RecvResult::RetryLater(receiver) => {
                recv = receiver;
            }
            RecvResult::Err(e) => panic!("{}", e),
        }
    };

    let request = CancelGoalRequest {
        goal_info: GoalInfo {
            goal_id: UUID { uuid },
            stamp: UnsafeTime { sec: 0, nanosec: 0 },
        },
    };
    let mut recv = client.send_cancel_request(&request)?;

    loop {
        match recv.recv_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok((_client, data, header)) => {
                println!(
                    "received cancel goal response: data = {:?}, seq = {}",
                    data, header.sequence_number
                );
                break;
            }
            RecvResult::RetryLater(receiver) => {
                println!("retrying");
                recv = receiver;
            }
            RecvResult::Err(e) => panic!("{}", e),
        }
    }

    Ok(())
}

#[test]
fn test_action_status() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let client = create_client(&ctx, "test_action_status_client", "test_action_status")?;

    let mut selector = ctx.create_selector()?;
    let server = create_server(
        &ctx,
        "test_action_status_server",
        "test_action_status",
        None,
    )?;

    // send goal request
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let mut recv = client.send_goal_with_uuid(goal, uuid)?;

    thread::sleep(Duration::from_millis(100));

    selector.add_action_server(server, goal_handler, move |_goal| true);
    selector.wait()?;

    let client = loop {
        match recv.recv_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok((client, data, header)) => {
                println!(
                    "received goal response: accepted = {:?}, seq = {}",
                    data.accepted, header.sequence_number
                );
                break client;
            }
            RecvResult::RetryLater(receiver) => {
                recv = receiver;
            }
            RecvResult::Err(e) => panic!("{}", e),
        }
    };

    // get status
    loop {
        match client.recv_status_timeout(Duration::from_secs(3), &mut selector) {
            RecvResult::Ok(statuses) => {
                for stat in statuses.status_list.iter() {
                    if stat.goal_info.goal_id.uuid == uuid {
                        let status: GoalStatus = stat.status.into();
                        println!("received status = {:?}", status);

                        if status == GoalStatus::Succeeded {
                            return Ok(());
                        }
                    }
                }
            }
            RecvResult::RetryLater(()) => {}
            RecvResult::Err(e) => panic!("{}", e),
        }
    }
}
