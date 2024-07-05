pub mod common;

use common::action_msg::action::my_action::*;
use safe_drive::{
    self,
    action::{client::Client, GoalStatus},
    context::Context,
    error::DynError,
    msg::unique_identifier_msgs::msg::UUID,
};
use std::{sync::Arc, thread, time::Duration};

fn create_client(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
) -> Result<Client<MyAction>, DynError> {
    let node_client = ctx.create_node(node, None, Default::default())?;
    Client::new(node_client, action, None).map_err(|e| e.into())
}

#[async_std::main]
async fn main() -> Result<(), DynError> {
    let ctx = Context::new()?;
    let client = create_client(
        &ctx,
        "safe_drive_example_action_client",
        "safe_drive_example",
    )?;

    // send a goal request
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    // receive a goal response
    let recv = receiver.recv();
    let client = match async_std::future::timeout(Duration::from_secs(10), recv).await {
        Ok(Ok((c, response, _header))) => {
            println!("client: goal response received: {:?}", response);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    };

    thread::sleep(Duration::from_secs(1));

    // receive status
    let mut client = client;
    let recv = client.recv_status();
    client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, status))) => {
            println!("client: status received: {:?}", status);
            // println!("client: status received: {:?}", GoalStatus::from(s.status));
            // #=> client: status received: GoalStatusArray { status_list: GoalStatusSeq { data: 0x0, size: 0, capacity: 0 } }

            // TODO: Status should be ACCEPTED

            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    };

    // receive feedback
    let mut client = client;
    loop {
        let recv = client.recv_feedback();
        client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
            Ok(Ok((c, feedback))) => {
                println!("client: feedback received: {:?}", feedback);

                if feedback.feedback.c == 5 {
                    client = c;
                    break;
                }
                c
            }
            Ok(Err(e)) => panic!("{e:?}"),
            Err(_) => panic!("timed out"),
        };
    }

    thread::sleep(Duration::from_secs(4));

    // send a result request
    println!("sending result request...");
    let receiver = client.send_result_request(&MyAction_GetResult_Request {
        goal_id: UUID { uuid },
    })?;
    let recv = receiver.recv();

    let client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, response, header))) => {
            println!("client: result response received: {:?}", response);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    };

    // receive status
    let mut client = client;
    let recv = client.recv_status();
    client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, status))) => {
            println!("client: status received: {:?}", status);
            // let s = status.status_list.as_slice().last().unwrap();
            // println!("client: status received: {:?}", GoalStatus::from(s.status));
            // TODO: Status should be FINISHED
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    };

    Ok(())
}
