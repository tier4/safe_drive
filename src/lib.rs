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
