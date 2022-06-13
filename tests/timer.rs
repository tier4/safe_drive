use safe_drive::context::Context;
use std::{error::Error, time::Duration};

#[test]
fn test_timer() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new()?;
    let mut selector = ctx.create_selector()?;

    selector.add_timer(
        Duration::from_millis(100),
        Box::new(|| println!("timer: 100[ms]")),
    );

    selector.add_timer(
        Duration::from_millis(200),
        Box::new(|| println!("timer: 200[ms]")),
    );

    for _ in 0..2 {
        selector.wait()?;
    }

    Ok(())
}
