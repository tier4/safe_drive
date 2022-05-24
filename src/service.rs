use crate::{error::RCLError, rcl, time::rcl_time_to_system_time};
use std::time::SystemTime;

pub mod client;
pub mod server;

#[derive(Debug)]
pub struct Header {
    header: rcl::rmw_service_info_t,
}

impl Header {
    pub fn get_source_timestamp(&self) -> SystemTime {
        rcl_time_to_system_time(self.header.source_timestamp)
    }

    pub fn get_received_timestamp(&self) -> SystemTime {
        rcl_time_to_system_time(self.header.received_timestamp)
    }

    pub fn get_sequence(self) -> i64 {
        self.header.request_id.sequence_number
    }

    pub fn get_writer_guid(self) -> [i8; 16] {
        self.header.request_id.writer_guid
    }
}
