use std::{cell::Cell, marker::PhantomData, sync::MutexGuard};

pub mod context;
pub mod error;
mod helper;
pub mod logger;
pub mod msg;
pub mod node;
pub mod qos;
pub mod rcl;
pub mod selector;
pub mod service;
mod time;
pub mod topic;

type PhantomUnsync = PhantomData<Cell<()>>;
type _PhantomUnsend = PhantomData<MutexGuard<'static, ()>>;
