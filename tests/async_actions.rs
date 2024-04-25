pub mod common;

use common::action_msg::action::my_action::*;
use safe_drive::{
    self,
    action::{
        client::Client,
        handle::GoalHandle,
        server::{Server, ServerQosOption},
    },
    context::Context,
    error::DynError,
    msg::{
        builtin_interfaces::UnsafeTime,
        interfaces::action_msgs::{msg::GoalInfo, srv::CancelGoalRequest},
        unique_identifier_msgs::msg::UUID,
        GetUUID,
    },
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
    let node_client = ctx.create_node(node, None, Default::default())?;
    Client::new(node_client, action, None).map_err(|e| e.into())
}

fn spawn_worker(handle: GoalHandle<MyAction>) {
    std::thread::Builder::new()
        .name("worker".into())
        .spawn(move || {
            for c in 0..=5 {
                if handle.is_canceling().unwrap() {
                    println!("server worker: canceling the goal");
                    handle.canceled(MyAction_Result { b: 1000 }).unwrap();
                    return;
                }

                println!("server worker: sending feedback {c}");
                let feedback = MyAction_Feedback { c };
                handle.feedback(feedback).unwrap();
                std::thread::sleep(Duration::from_secs(2));
            }

            println!("server worker: result is now available");
            handle.finish(MyAction_Result { b: 500 }).unwrap();

            loop {
                std::thread::sleep(Duration::from_secs(5));
            }
        })
        .unwrap();
}

async fn run_server(server: Server<MyAction>) -> Result<(), DynError> {
    let goal = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_goal_request().await;
                match result {
                    Ok((sender, req)) => {
                        println!("server: goal received: {:?}", req);

                        let s = sender
                            .accept(|handle| spawn_worker(handle))
                            .map_err(|(_sender, err)| err)
                            .expect("could not accept");
                        // let s = sender.reject().map_err(|(_sender, err)| err)?;

                        println!("server: goal response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let cancel = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_cancel_request().await;
                match result {
                    Ok((sender, candidates)) => {
                        println!("server: received cancel request for: {:?}", candidates);

                        let accepted = candidates; // filter requests if needed

                        sender
                            .accept(&accepted)
                            .expect("could not set status to CANCELING");

                        // perform shutdown operations for the goals here if needed
                        thread::sleep(Duration::from_secs(2));

                        // return cancel response
                        let s = sender
                            .send(accepted)
                            .map_err(|(_s, err)| err)
                            .expect("could not send cancel response");
                        println!("server: cancel response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let result = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_result_request().await;
                match result {
                    Ok((sender, req)) => {
                        println!("server: received result request for: {:?}", req);

                        // return result response
                        let s = sender
                            .send(req.get_uuid())
                            .map_err(|(_s, err)| err)
                            .expect("could not send");
                        println!("server: result response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let _ = goal.await;
    let _ = cancel.await;
    let _ = result.await;

    Ok(())
}

async fn run_client(mut client: Client<MyAction>) -> Result<(), DynError> {
    // send a goal request
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    // receive a goal response
    let recv = receiver.recv();
    let client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, response, _header))) => {
            println!("client: goal response received: {:?}", response);
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

    Ok(())
}

async fn run_client_cancel(mut client: Client<MyAction>) -> Result<(), DynError> {
    // send a goal request
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    // receive a goal response
    let recv = receiver.recv();
    // let client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
    let client = match async_std::future::timeout(Duration::from_secs(3600), recv).await {
        Ok(Ok((c, response, _header))) => {
            println!("client: goal response received: {:?}", response);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    };

    thread::sleep(Duration::from_secs(1));

    // send a cancel request
    let receiver = client.send_cancel_request(&CancelGoalRequest {
        goal_info: GoalInfo {
            goal_id: UUID { uuid },
            stamp: UnsafeTime { sec: 0, nanosec: 0 },
        },
    })?;
    println!("client: cancel request sent");

    match receiver.recv().await {
        Ok((_c, resp, _header)) => {
            println!("client: cancel response received: {:?}", resp);
        }
        Err(e) => panic!("client: could not cancel the goal: {e:?}"),
    }

    Ok(())
}

#[test]
fn test_async_action() -> Result<(), Box<dyn std::error::Error + Sync + Send + 'static>> {
    let ctx = Context::new()?;

    let client = create_client(&ctx, "test_async_action_client", "test_action")?;

    let server = create_server(&ctx, "test_async_action_server", "test_action", None)?;

    async_std::task::block_on(async {
        let (tx, rx) = crossbeam_channel::unbounded();

        async_std::task::spawn({
            let server = server.clone();
            run_server(server)
        });
        async_std::task::spawn(async move {
            let ret = run_client(client).await;
            let _ = tx.send(());
            ret
        });

        let _ = rx.recv();
    });

    Ok(())
}

#[test]
fn test_async_cancel() -> Result<(), DynError> {
    let ctx = Context::new()?;
    let client = create_client(
        &ctx,
        "test_async_action_client_cancel",
        "test_async_action_cancel",
    )?;
    let server = create_server(
        &ctx,
        "test_async_action_server_cancel",
        "test_async_action_cancel",
        None,
    )?;

    async_std::task::block_on(async {
        let (tx, rx) = crossbeam_channel::unbounded();

        async_std::task::spawn({
            let server = server.clone();
            run_server(server)
        });
        async_std::task::spawn(async move {
            let ret = run_client_cancel(client).await;
            let _ = tx.send(());
            ret
        });

        let _ = rx.recv();
    });

    Ok(())
}
