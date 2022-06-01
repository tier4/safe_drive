use super::guard_condition::GuardCondition;
use crate::{
    context::Context,
    error::DynError,
    service::{client::ClientData, server::ServerData},
    topic::subscriber::RCLSubscription,
};
use flume::{self, Receiver, Sender};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use std::{collections::BTreeMap, sync::Arc, thread};

pub(crate) static SELECTOR: Lazy<Mutex<AsyncSelector>> =
    Lazy::new(|| Mutex::new(AsyncSelector::new()));

pub(crate) enum Command {
    Subscription(Arc<RCLSubscription>, Box<dyn Fn() + Send + Sync + 'static>),
    RemoveSubscription(Arc<RCLSubscription>),
    Server(Arc<ServerData>, Box<dyn Fn() + Send + Sync + 'static>),
    RemoveServer(Arc<ServerData>),
    Client(Arc<ClientData>, Box<dyn Fn() + Send + Sync + 'static>),
    RemoveClient(Arc<ClientData>),
}

struct SelectorData {
    tx: Sender<Command>,
    _context: Arc<Context>,
    cond: Arc<GuardCondition>,
}

pub(crate) struct AsyncSelector {
    contexts: BTreeMap<usize, SelectorData>,
}

unsafe impl Sync for AsyncSelector {}
unsafe impl Send for AsyncSelector {}

impl AsyncSelector {
    fn new() -> Self {
        AsyncSelector {
            contexts: Default::default(),
        }
    }

    pub(crate) fn send_command(
        &mut self,
        context: &Arc<Context>,
        cmd: Command,
    ) -> Result<(), DynError> {
        loop {
            if let Some(SelectorData {
                tx,
                _context: _,
                cond,
            }) = self.contexts.get(&context.id)
            {
                tx.send(cmd)?;
                cond.trigger()?;
                return Ok(());
            } else {
                let (tx, rx) = flume::bounded(256);
                let guard = super::guard_condition::GuardCondition::new(context.clone())?;
                self.contexts.insert(
                    context.id,
                    SelectorData {
                        tx,
                        _context: context.clone(),
                        cond: guard.clone(),
                    },
                );
                let ctx = context.clone();
                thread::spawn(move || select(ctx, guard, rx));
            }
        }
    }
}

fn select(
    context: Arc<Context>,
    guard: Arc<GuardCondition>,
    rx: Receiver<Command>,
) -> Result<(), DynError> {
    let mut selector = super::Selector::new(context)?;

    selector.add_guard_condition(&guard, None);

    loop {
        for cmd in rx.try_iter() {
            match cmd {
                Command::Subscription(s, h) => selector.add_rcl_subscription(s, Some(h), true),
                Command::RemoveSubscription(s) => selector.remove_rcl_subscription(&s),
                Command::Server(s, h) => selector.add_server_data(s, Some(h), true),
                Command::RemoveServer(s) => selector.remove_server_data(&s),
                Command::Client(c, h) => selector.add_client_data(c, Some(h), true),
                Command::RemoveClient(c) => selector.remove_client_data(&c),
            }
        }

        selector.wait(None)?;
    }
}
