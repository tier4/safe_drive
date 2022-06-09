# safe_drive: Formally Specified Rust Bindings for ROS2

`safe_drive` is a Rust bindings for ROS2.
This library provides formal specifications and tested the specifications by using a model checker.
Therefore, you can clearly understand how the scheduler work and the safeness of it.

## Examples

See [tests](./tests/).

## Specifications

See [specifications](./specifications/).

## Progress

- [x] Topic (Pub/Sub)
- [x] Service (Client/Server)
- [x] Asynchronous programming (async/await)
- [x] Callback based programming
- [x] Logging
- [ ] Parameter
- [ ] Timer
- [ ] Action (service + topic)
- [ ] Rust code generation from .msg and .srv files
- [ ] Formal Specification
  - [ ] Callback based executer
  - [x] Basic scheduler
  - [ ] Prioritized scheduler
  - [x] Initializer performed just once
