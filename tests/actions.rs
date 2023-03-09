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
use std::{thread, time::Duration};

#[test]
fn test_action() -> Result<(), DynError> {
    let ctx = Context::new()?;

    let node_client = ctx.create_node("test_action_client_node", None, Default::default())?;

    let mut client: Client<MyAction> = Client::new(node_client, "test_action", None)?;

    // start the action server
    let handle = thread::spawn(move || {
        let node_server = ctx
            .create_node("test_action_server_node", None, Default::default())
            .unwrap();
        let mut server: Server<MyAction> = Server::new(node_server, "test_action", None, |req| {
            println!("Goal request received: {:?}", req);
            true
        })
        .unwrap();

        println!("server: waiting for goal requests...");
        match server.try_recv_goal_request() {
            RecvResult::Ok(_) => println!("server: accepted goal"),
            RecvResult::RetryLater(_) => {
                // println!("server: waiting for goal requests...");
            }
            RecvResult::Err(err) => println!("server: error: {:?}", err),
        }
    });

    thread::sleep(Duration::from_millis(100));

    // wait for action server
    // loop {
    // if client.is_server_available()? {
    // break;
    // }
    // }

    // send goal request
    let goal = MyAction_Goal { a: 100 };
    let mut goal_id = UUID::new().unwrap();
    goal_id.uuid = [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8];

    let goal_request = MyAction_SendGoal_Request { goal_id, goal };

    // TODO: ergonomic apis
    // TODO: generate UUID w/ uuid crate. rclcpp's ClientBase::generate_goal_id
    // does not conform to the UUID v4 standard, strictly speaking.
    client.send_goal_request(
        &goal_request,
        Box::new(|resp| {
            println!("Goal response received: {:?}", resp);
        }),
    )?;

    // receive goal response
    loop {
        match client.try_recv_goal_response() {
            // we wait for a single response here
            RecvResult::Ok(_) => break,
            RecvResult::RetryLater(_) => {
                println!("retrying...");
            }
            RecvResult::Err(e) => {
                println!("Error: {}", e);
            }
        }
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    // get feedback

    // get result

    handle.join().unwrap();

    Ok(())
}
