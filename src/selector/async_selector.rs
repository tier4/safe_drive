use super::guard_condition::GuardCondition;
use crate::{context::Context, subscriber::RCLSubscription};
use once_cell::sync::Lazy;
use std::{
    collections::BTreeMap,
    error::Error,
    sync::{
        mpsc::{sync_channel, Receiver, SyncSender},
        Arc, Mutex,
    },
    thread,
};

pub(crate) static SELECTOR: Lazy<Mutex<AsyncSelector>> =
    Lazy::new(|| Mutex::new(AsyncSelector::new()));

pub(crate) enum Command {
    Subscription(Arc<RCLSubscription>, Box<dyn Fn() + Send + Sync + 'static>),
}

struct SelectorData {
    tx: SyncSender<Command>,
    _context: Arc<Context>,
    cond: Arc<GuardCondition>,
}

pub(crate) struct AsyncSelector {
    contexts: BTreeMap<usize, SelectorData>,
}

impl AsyncSelector {
    fn new() -> Self {
        AsyncSelector {
            contexts: Default::default(),
        }
    }

    pub(crate) fn register(
        &mut self,
        context: &Arc<Context>,
        cmd: Command,
    ) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
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
                let (tx, rx) = sync_channel::<Command>(64);
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
) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
    let mut selector = super::Selector::new(context)?;

    selector.add_guard_condition(&guard, None);

    loop {
        for cmd in rx.try_iter() {
            match cmd {
                Command::Subscription(s, h) => selector.add_rcl_subscription(s, Some(h), true),
            }
        }

        selector.wait(None)?;
    }
}
