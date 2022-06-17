use safe_drive::{logger::Logger, *};

#[test]
fn test_logger_macro() {
    let logger = Logger::new("test_logger_macro");
    pr_debug!(&logger, "debug message: {}", 10);
    pr_info!(&logger, "info message: {}", 10);
    pr_warn!(&logger, "warn message: {} {}", 20, 30);
    pr_error!(&logger, "info message: {} {} {}", 40, 50, 60);
    pr_fatal!(&logger, "info message: {} {} {} {}", 70, 80, 90, 100);
}
