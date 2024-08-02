use safe_drive::{
    self,
    action::{
        handle::GoalHandle,
        server::{AsyncServer, Server, ServerCancelSend, ServerGoalSend, ServerQosOption},
    },
    context::Context,
    error::DynError,
};
use std::{sync::Arc, time::Duration};

mod my_action;
use my_action::{MyAction, MyAction_Feedback, MyAction_Result};

fn create_server(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
    qos: Option<ServerQosOption>,
) -> Result<Server<MyAction>, DynError> {
    let node_server = ctx.create_node(node, None, Default::default()).unwrap();

    Server::new(node_server, action, qos).map_err(|e| e.into())
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
                std::thread::sleep(Duration::from_secs(1));
            }

            println!("server worker: result is now available");
            handle.finish(MyAction_Result { b: 500 }).unwrap();
        })
        .unwrap();
}

async fn run_server(server: Server<MyAction>) -> Result<(), DynError> {
    let mut server = AsyncServer::new(server);

    let goal = move |sender: ServerGoalSend<MyAction>, req| {
        println!("server: goal received: {:?}", req);

        let s = sender
            .accept(spawn_worker)
            .map_err(|(_sender, err)| err)
            .expect("could not accept");
        // let s = sender.reject().map_err(|(_sender, err)| err)?;

        println!("server: goal response sent");

        s
    };

    let cancel = move |sender: ServerCancelSend<MyAction>, candidates| {
        println!("server: received cancel request for: {:?}", candidates);

        let accepted = candidates; // filter requests here if needed

        // return cancel response
        let s = sender
            .send(accepted)
            .map_err(|(_s, err)| err)
            .expect("could not send cancel response");

        // perform shutdown operations for the goals here if needed

        println!("server: cancel response sent");

        s
    };

    server.listen(goal, cancel).await
}

#[async_std::main]
async fn main() -> Result<(), DynError> {
    let ctx = Context::new()?;
    let server = create_server(
        &ctx,
        "safe_drive_example_action_server",
        "safe_drive_example",
        None,
    )?;

    run_server(server).await
}
