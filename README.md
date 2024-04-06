# safe_drive: Formally Specified Rust Bindings for ROS2

`safe_drive` is a Rust bindings for ROS2.
This library provides formal specifications and tested the specifications by using a model checker.
Therefore, you can clearly understand how the scheduler work and the safeness of it.

## Specifications

Some algorithms we adopted are formally specified and tested the safeness by using TLA+.
Original ROS2's executor (rclcpp) suffers from starvation.
In contrast, the starvation freedom of our executor has been validated by not only dynamic analysis but also
formal verification.

See [specifications](https://github.com/tier4/safe_drive/tree/main/specifications).

We specified and tested as follows.

- Single Threaded Callback Execution
  - Deadlock freedom
  - Starvation freedom
- Scheduling Core Algorithm
  - Validate the insertion algorithm
  - Termination
- Initialize Once
  - Deadlock freedom
  - Termination
  - Initialization is performed just once

## Documents

- [https://tier4.github.io/safe_drive/](https://tier4.github.io/safe_drive/)
- [https://docs.rs/safe_drive/latest/safe_drive/](https://docs.rs/safe_drive/latest/safe_drive/)

## Supporting ROS2

- [x] Humble
- [ ] Galactic (EOL)

## Supporting DDS

- [x] CycloneDDS
- [x] FastDDS

## Progress

- [x] Zero copy
- [x] Custom memory allocator
- [x] Topic (Pub/Sub)
- [x] Service (Client/Server)
- [x] Asynchronous programming (async/await)
- [x] Callback based programming
- [x] Logging
- [x] Signal handling
- [x] Parameter
- [x] Timer
- [ ] Action (service + topic)
- [x] Rust code generation from .msg and .srv files
  - [safe_drive_msg](https://github.com/tier4/safe_drive_msg)
- [x] Formal Specification
  - [x] Single threaded callback based executer
  - [x] Scheduling Core Algorithm
  - [x] Initializer performed just once
