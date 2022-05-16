pub mod common;

use safe_drive;
use std::error::Error;

#[test]
fn test_publish() -> Result<(), Box<dyn Error>> {
    let ctx = safe_drive::context::Context::new()?;
    let node =
        safe_drive::node::Node::new(ctx, "test_publish_node", None, Default::default()).unwrap();

    let publisher = safe_drive::publisher::Publisher::<common::num::sample_msg__msg__Num>::new(
        node,
        "test_publish",
        unsafe {
            common::num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num(
            ) as *const ()
        },
        Default::default(),
    )?;

    let msg = common::num::sample_msg__msg__Num { num: 100 };
    publisher.send(msg)?;

    Ok(())
}
