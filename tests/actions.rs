pub mod common;

use common::msgs::example_msg::action::*;
use safe_drive::{
    self,
    action::{client::Client, server::Server},
    context::Context,
    error::DynError,
    msg::unique_identifier_msgs::msg::UUID,
    RecvResult,
};
use std::{sync::Arc, thread, time::Duration};

fn create_server(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
) -> Result<Server<MyAction>, DynError> {
    let node_server = ctx.create_node(node, None, Default::default()).unwrap();

    Server::new(node_server, action, None, |req| {
        println!("Goal request received: {:?}", req);
        true
    })
    .map_err(|e| e.into())
}

#[test]
fn test_action() -> Result<(), DynError> {
    let ctx = Context::new()?;

    // start the action server
    let mut server = create_server(&ctx, "test_action_server_node", "test_action")?;

    // start the action client
    let node_client = ctx.create_node("test_action_client_node", None, Default::default())?;
    let mut client: Client<MyAction> = Client::new(node_client, "test_action", None)?;

    // wait for action server
    // loop {
    // if client.is_server_available()? {
    // break;
    // }
    // }
    thread::sleep(Duration::from_millis(100));

    // send goal request
    let goal = MyAction_Goal { a: 10 };

    // TODO: generate UUID w/ uuid crate. rclcpp's ClientBase::generate_goal_id
    // does not conform to the UUID v4 standard, strictly speaking.
    let uuid = [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8];
    client.send_goal_with_uuid(goal, uuid, |resp| {
        println!(
            "Goal response received: accepted = {}, timestamp = {:?}",
            resp.accepted, resp.stamp
        );
    })?;

    // wait for goal request, then send response
    loop {
        match server.try_recv_goal_request() {
            RecvResult::Ok(_) => {
                println!("server: accepted goal");
                break;
            }
            RecvResult::RetryLater(_) => {
                println!("server: waiting for goal requests...");
            }
            RecvResult::Err(e) => println!("{:?}", e),
        }
        thread::sleep(Duration::from_secs(1));
    }

    // receive goal response
    loop {
        match client.try_recv_goal_response() {
            RecvResult::Ok(_) => break, // we wait for a single response here
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => return Err(e.into()),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    // get feedback (wait for five feedback messages)
    let mut received = 0;
    loop {
        match client.try_recv_feedback() {
            RecvResult::Ok(feedback) => {
                println!("Feedback received: {:?}", feedback);
                received += 1;
                if received > 5 {
                    break;
                }
            }
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => return Err(e.into()),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    // TODO: UUID can't be cloned?
    let mut goal_id = UUID::new().unwrap();
    goal_id.uuid = [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8];
    let result_req = MyAction_GetResult_Request { goal_id };
    client.send_result_request(
        &result_req,
        Box::new(|resp| {
            println!(
                "Result response received: status = {}, result = {}",
                resp.status, resp.result.b
            );
        }),
    )?;

    // get result
    loop {
        match client.try_recv_result_response() {
            RecvResult::Ok(_) => break, // we wait for a single result here
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => println!("Error: {}", e),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    Ok(())
}

#[test]
fn test_action_status() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let node_client = ctx.create_node("test_action_client_node", None, Default::default())?;

    let mut client: Client<MyAction> = Client::new(node_client, "test_action", None)?;

    thread::sleep(Duration::from_millis(100));

    // send goal request
    let goal = MyAction_Goal { a: 10 };
    let mut goal_id = UUID::new().unwrap();
    goal_id.uuid = [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 9];

    let goal_request = MyAction_SendGoal_Request { goal_id, goal };

    client.send_goal_request(
        &goal_request,
        Box::new(|resp| {
            println!(
                "Goal response received: accepted = {}, timestamp = {:?}",
                resp.accepted, resp.stamp
            );
        }),
    )?;

    // receive goal response
    loop {
        match client.try_recv_goal_response() {
            RecvResult::Ok(_) => break, // we wait for a single response here
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => return Err(e.into()),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    // Once the goal is accepted, get status for all the ongoing goals.
    // There should be at least one ongoing goal which has been requested earlier in this test.
    loop {
        match client.try_recv_status() {
            RecvResult::Ok(status_array) => {
                println!("Status received: {:?}", status_array);
                break;
            }
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => return Err(e.into()),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    Ok(())
}
