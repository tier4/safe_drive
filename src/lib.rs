pub mod context;
pub mod error;
mod init_options;
mod rcl;

#[cfg(test)]
mod tests {
    use std::error::Error;

    #[test]
    fn context() -> Result<(), Box<dyn Error>> {
        use crate::*;
        context::Context::new()?;
        Ok(())
    }
}
