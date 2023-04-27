pub mod common;

use common::msgs::example_msg::action::*;
use safe_drive::{
    self,
    action::{
        client::Client,
        server::{Server, ServerQosOption},
    },
    context::Context,
    error::DynError,
    msg::unique_identifier_msgs::msg::UUID,
    qos::Profile,
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

    let goal_callback = |req| {
        println!("Goal request received: {:?}", req);
        true
    };
    let cancel_callback = |req| {
        println!("Cancel request received: {:?}", req);
        true
    };

    Server::new(node_server, action, qos, goal_callback, cancel_callback).map_err(|e| e.into())
}

fn create_client(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
) -> Result<Client<MyAction>, DynError> {
    let node_client = ctx.create_node(node, None, Default::default())?;
    Client::new(node_client, action, None).map_err(|e| e.into())
}

// wait for goal request, then send response by callback
fn server_recv_goal_request(server: &mut Server<MyAction>) {
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
}

fn client_recv_goal_response(client: &mut Client<MyAction>) -> Result<(), DynError> {
    loop {
        match client.try_recv_goal_response() {
            RecvResult::Ok(_) => return Ok(()), // we wait for a single response here
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => return Err(e),
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
}

fn handle_goal_response(resp: MyAction_SendGoal_Response) {
    println!(
        "Goal response received: accepted = {}, timestamp = {:?}",
        resp.accepted, resp.stamp
    );
}

#[test]
fn test_action() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let mut server = create_server(&ctx, "test_action_server_node", "test_action", None)?;
    let mut client = create_client(&ctx, "test_action_client_node", "test_action")?;

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
    let uuid_ = uuid.clone();
    client.send_goal_with_uuid(goal, uuid, handle_goal_response)?;

    server_recv_goal_request(&mut server);
    client_recv_goal_response(&mut client);

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
    goal_id.uuid = uuid_;
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
    #[cfg(feature = "galactic")]
    use safe_drive::qos::galactic::*;

    #[cfg(feature = "humble")]
    use safe_drive::qos::humble::*;

    let ctx = Context::new()?;

    let mut server = create_server(&ctx, "test_action_server_node", "test_action_status", None)?;
    let mut client = create_client(&ctx, "test_action_client_node", "test_action_status")?;

    thread::sleep(Duration::from_millis(100));

    // send goal request
    let goal = MyAction_Goal { a: 10 };
    let uuid = [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 9];

    client.send_goal_with_uuid(goal, uuid, handle_goal_response)?;

    server_recv_goal_request(&mut server);
    client_recv_goal_response(&mut client);

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
