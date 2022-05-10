pub mod context;
pub mod error;
pub mod node;
pub mod publisher;
pub mod qos;
mod rcl;
pub mod subscription;
mod time;

#[cfg(test)]
mod tests {
    use std::error::Error;

    #[test]
    fn test_create_node() -> Result<(), Box<dyn Error>> {
        use crate::*;
        let ctx = context::Context::new()?;
        let _node = node::Node::new(ctx, "test_create_node", None, Default::default());

        Ok(())
    }
}
