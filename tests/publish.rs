pub mod common;

use safe_drive::{self, context::Context};
use std::error::Error;

#[test]
fn test_publish() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new()?;
    let node = ctx
        .create_node("test_publish_node", None, Default::default())
        .unwrap();

    let publisher = node.create_publisher::<common::num::sample_msg__msg__Num>(
        "test_publish",
        unsafe {
            common::num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num()
        },
        Default::default(),
    )?;

    let msg = common::num::sample_msg__msg__Num { num: 100 };
    publisher.send(msg)?;

    Ok(())
}
