# safe_drive: Formally Specified Rust Bindings for ROS2

`safe_drive` is a Rust bindings for ROS2.
This library provides formal specifications and tested the specifications by using a model checker.
Therefore, you can clearly understand how the scheduler work and the safeness of it.

## Specifications

Some algorithms we adopted are formally specified and tested the safeness by using TLA+.
Original ROS2's executor (rclcpp) is suffering from starvation.
In contrast, the starvation freedom of our executor has been validated by not only dynamic analysis but also
formal verification.

See [specifications](./specifications/).

We specified and tested as follows.

- Async/await Scheduler
  - Deadlock freedom
  - Starvation freedom
- Single Threaded Callback Execution
  - Deadlock freedom
  - Starvation freedom
- Initialize Once
  - Deadlock freedom
  - Termination
  - Initialization is performed just once

## Examples

See [tests](./tests/).

## Progress

- [x] Topic (Pub/Sub)
- [x] Service (Client/Server)
- [x] Asynchronous programming (async/await)
- [x] Callback based programming
- [x] Logging
- [x] Signal handling
- [ ] Parameter
- [x] Timer
- [ ] Action (service + topic)
- [x] Rust code generation from .msg and .srv files
  - [ros2msg_to_rs](https://github.com/tier4/ros2msg_to_rs)
- [x] Formal Specification
  - [x] Single threaded callback based executer
  - [x] Async/await scheduler
  - [x] Initializer performed just once
