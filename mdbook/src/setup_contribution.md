# Setting-up for contribution

## Basic setting-up

See [Setting-up](./setup.md) for basic setting-up.

## Setting-up development tools

To build `safe_drive`,
you need install `bindgen-cli` and `ros2msg_to_rs` as follows.

```text
$ cargo install bindgen-cli
$ cargo install --git https://github.com/tier4/ros2msg_to_rs.git
```

`bindgen_cli` is a transpiler from C to Rust,
and `ros2msg_to_rs` is also a transpiler from .msg and .srv to Rust.

If you want to contribute to documents you are reading now,
please install `mdbook` and `mdbook-mermaind` as follows.

```text
$ cargo install mdbook
$ cargo install mdbook-mermaid
```
