# Setting-up for Contribution

## Basic Setting-up

See [Setting-up](./setup.md) for basic setting-up.

## Setting-up Development Environment

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

Finally, download `safe_drive` as follows.

```text
$ git clone https://github.com/tier4/safe_drive
$ cd safe_drive
```

Following chapters introduce how to hack `safe_drive` in this directory.

## Use Docker

We provide Docker files in [docker](https://github.com/tier4/safe_drive/tree/main/docker).
You can use this to hack `safe_drive` as follows, alternatively.

```text
$ git clone https://github.com/tier4/safe_drive.git
$ cd safe_drive/docker
$ docker compose build
$ docker compose up -d
$ docker exec -it docker-safe_drive-1 /bin/zsh
```
