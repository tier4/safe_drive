use crate::{node::Node, qos::Profile};
use std::sync::{Arc, Mutex};

pub struct Publisher {
    _node: Arc<Mutex<Node>>,
}

impl Publisher {
    pub fn new(node: Arc<Mutex<Node>>, qos: &Profile) {}
}
