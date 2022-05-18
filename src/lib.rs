use std::{cell::Cell, marker::PhantomData, sync::MutexGuard};

pub mod context;
pub mod error;
pub mod node;
pub mod publisher;
pub mod qos;
mod rcl;
pub mod selector;
pub mod subscriber;
mod time;

type PhantomUnsync = PhantomData<Cell<()>>;
type _PhantomUnsend = PhantomData<MutexGuard<'static, ()>>;
