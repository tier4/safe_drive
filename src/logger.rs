//! Logger of ROS2.
//!
//! # Examples
//!
//! ## Basics
//!
//! ```
//! use safe_drive::{logger::Logger, pr_debug, pr_error, pr_fatal, pr_info, pr_warn};
//!
//! let logger = Logger::new("my_logger");
//! let some_value = 100;
//!
//! pr_debug!(logger, "debug: {some_value}");
//! pr_info!(logger, "information: {some_value}");
//! pr_warn!(logger, "warning: {some_value}");
//! pr_error!(logger, "error: {some_value}");
//! pr_fatal!(logger, "fatal: {some_value}");
//! ```
//!
//! ## Callback Functions of Single Threaded Execution
//!
//! ```
//! use std::{rc::Rc, time::Duration};
//! use safe_drive::{context::Context, logger::Logger, pr_error, pr_info};
//!
//! let ctx = Context::new().unwrap();
//! let mut selector = ctx.create_selector().unwrap();
//!
//! // Use Rc to share the logger by multiple callback functions.
//! let logger = Logger::new("my_logger");
//! let logger = Rc::new(logger);
//! let logger1 = logger.clone();
//!
//! selector.add_wall_timer(
//!     Duration::from_millis(100),
//!     Box::new(move || pr_info!(logger1, "some information")),
//! );
//!
//! selector.add_wall_timer(
//!     Duration::from_millis(150),
//!     Box::new(move || pr_error!(logger, "some error")),
//! );
//! ```
//!
//! ## Multi Threaded
//!
//! ```
//! use safe_drive::{logger::Logger, pr_info, pr_warn};
//! use std::sync::Arc;
//!
//! let logger = Logger::new("my_logger");
//!
//! // Use Arc to share a logger by multiple threads.
//! let logger = Arc::new(logger);
//! let logger1 = logger.clone();
//!
//! let th1 = std::thread::spawn(move || pr_info!(logger1, "some information"));
//! let th2 = std::thread::spawn(move || pr_warn!(logger, "some warning"));
//!
//! th1.join().unwrap();
//! th2.join().unwrap();
//! ```

use crate::{
    error::{DynError, RCLResult},
    helper::InitOnce,
    rcl,
};
use num_derive::{FromPrimitive, ToPrimitive};
use std::ffi::CString;

static INITIALIZER: InitOnce = InitOnce::new();

/// Get the function name called this macro.
#[macro_export]
macro_rules! function {
    () => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);
        &name[..name.len() - 3]
    }};
}

/// Print information.
#[macro_export]
macro_rules! pr_info {
    ($logger:expr, $($arg:tt)*) => {{
        let res = format!($($arg)*);
        let _ = $logger.write_info(&res, safe_drive::function!(), file!(), line!() as u64);
    }}
}

macro_rules! pr_info_in {
    ($logger:expr, $($arg:tt)*) => {{
        let res = std::format!($($arg)*);
        let _ = $logger.write_info(&res, crate::function!(), std::file!(), std::line!() as u64);
    }}
}
pub(crate) use pr_info_in;

/// Print warning.
#[macro_export]
macro_rules! pr_warn {
    ($logger:expr, $($arg:tt)*) => {{
        let res = format!($($arg)*);
        let _ = $logger.write_warn(&res, safe_drive::function!(), file!(), line!() as u64);
    }}
}

/// Print error.
#[macro_export]
macro_rules! pr_error {
    ($logger:expr, $($arg:tt)*) => {{
        let res = format!($($arg)*);
        let _ = $logger.write_error(&res, safe_drive::function!(), file!(), line!() as u64);
    }}
}

macro_rules! pr_error_in {
    ($logger:expr, $($arg:tt)*) => {{
        let res = std::format!($($arg)*);
        let _ = $logger.write_error(&res, crate::function!(), std::file!(), std::line!() as u64);
    }}
}
pub(crate) use pr_error_in;

/// Print fatal.
#[macro_export]
macro_rules! pr_fatal {
    ($logger:expr, $($arg:tt)*) => {{
        let res = format!($($arg)*);
        let _ = $logger.write_fatal(&res, safe_drive::function!(), file!(), line!() as u64);
    }}
}

/// Print debug.
/// Debug messages is not printed by default.
/// To enable debug print, type as follows.
///
/// ```text
/// ros2 run logging_demo logging_demo_main --ros-args --log-level debug
/// ```
#[macro_export]
macro_rules! pr_debug {
    ($logger:expr, $($arg:tt)*) => {{
        let res = format!($($arg)*);
        let _ = $logger.write_debug(&res, safe_drive::function!(), file!(), line!() as u64);
    }}
}

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPrimitive, ToPrimitive)]
enum Severity {
    Debug = rcl::RCUTILS_LOG_SEVERITY_RCUTILS_LOG_SEVERITY_DEBUG,
    Info = rcl::RCUTILS_LOG_SEVERITY_RCUTILS_LOG_SEVERITY_INFO,
    Warn = rcl::RCUTILS_LOG_SEVERITY_RCUTILS_LOG_SEVERITY_WARN,
    Error = rcl::RCUTILS_LOG_SEVERITY_RCUTILS_LOG_SEVERITY_ERROR,
    Fatal = rcl::RCUTILS_LOG_SEVERITY_RCUTILS_LOG_SEVERITY_FATAL,
}

/// Logger of ROS2.
/// The methods of Logger are called by pr_* macros.
/// Use these macros instead of the methods.
#[derive(Debug)]
pub struct Logger {
    name: CString,
}

impl Logger {
    /// Create a new logger.
    pub fn new(name: &str) -> Self {
        Logger {
            name: CString::new(name).unwrap(),
        }
    }

    fn write(
        &self,
        msg: &str,
        severity: Severity,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        init_once()?; // first of all, initialize the logging system

        if !self.is_enable_for(severity) {
            let msg = format!(
                "log severity is not enabled on this system: severity = {:?}",
                severity
            );
            return Err(msg.into());
        }

        let function_name = CString::new(function_name)?;
        let file_name = CString::new(file_name)?;
        let msg = CString::new(msg)?;

        let logging_location = rcl::rcutils_log_location_t {
            function_name: function_name.as_ptr(),
            file_name: file_name.as_ptr(),
            line_number,
        };

        let guard = rcl::MT_UNSAFE_LOG_FN.lock();
        guard.rcutils_log(
            &logging_location,
            severity as i32,
            self.name.as_ptr(),
            msg.as_ptr(),
        );

        Ok(())
    }

    /// Print information.
    /// Use `pr_info!` macro instead of this.
    pub fn write_info(
        &self,
        msg: &str,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        self.write(msg, Severity::Info, function_name, file_name, line_number)
    }

    /// Print warning.
    /// Use `pr_warn!` macro instead of this.
    pub fn write_warn(
        &self,
        msg: &str,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        self.write(msg, Severity::Warn, function_name, file_name, line_number)
    }

    /// Print error.
    /// Use `pr_error!` macro instead of this.
    pub fn write_error(
        &self,
        msg: &str,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        self.write(msg, Severity::Error, function_name, file_name, line_number)
    }

    /// Print fatal.
    /// Use `pr_fatal!` macro instead of this.
    pub fn write_fatal(
        &self,
        msg: &str,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        self.write(msg, Severity::Fatal, function_name, file_name, line_number)
    }

    /// Print debug.
    /// Use `pr_debug!` macro instead of this.
    pub fn write_debug(
        &self,
        msg: &str,
        function_name: &str,
        file_name: &str,
        line_number: u64,
    ) -> Result<(), DynError> {
        self.write(msg, Severity::Debug, function_name, file_name, line_number)
    }

    fn is_enable_for(&self, severity: Severity) -> bool {
        let guard = rcl::MT_UNSAFE_LOG_FN.lock();
        guard.rcutils_logging_logger_is_enabled_for(self.name.as_ptr(), severity as i32)
    }
}

fn init_once() -> RCLResult<()> {
    INITIALIZER.init(
        || {
            // initialize
            let guard = rcl::MT_UNSAFE_LOG_FN.lock();
            guard.rcutils_logging_initialize()?;
            Ok(())
        },
        Ok(()),
    )
}

#[cfg(test)]
mod test {
    use super::{Logger, Severity};

    #[test]
    fn test_logger() {
        let logger = Logger::new("test_logger");
        logger
            .write(
                "info message",
                Severity::Info,
                function!(),
                file!(),
                line!() as u64,
            )
            .unwrap();

        logger
            .write(
                "warn message",
                Severity::Warn,
                function!(),
                file!(),
                line!() as u64,
            )
            .unwrap();

        logger
            .write(
                "error message",
                Severity::Error,
                function!(),
                file!(),
                line!() as u64,
            )
            .unwrap();

        logger
            .write(
                "fatal message",
                Severity::Fatal,
                function!(),
                file!(),
                line!() as u64,
            )
            .unwrap();
    }
}
