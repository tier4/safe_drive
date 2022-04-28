pub mod common;

use safe_drive::*;
use std::error::Error;

#[test]
fn test_create_node() -> Result<(), Box<dyn Error>> {
    let ctx = context::Context::new()?;
    let _node = node::Node::new(ctx, "test_create_node", None, Default::default());

    Ok(())
}
