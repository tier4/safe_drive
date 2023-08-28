# Setting-up

## Install Dependencies

```text
$ sudo apt install curl gnupg2 lsb-release python3-pip git
```

## Install Rust

```text
$ sudo curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
$ source $HOME/.cargo/env
```

Choose `Default` when installing Rust.

## Install ROS2

```text
$ curl -s https://raw.githubusercontent.com/ros/rosdistro/master/ros.asc | sudo apt-key add -
$ sudo sh -c 'echo "deb [arch=$(dpkg --print-architecture)] http://packages.ros.org/ros2/ubuntu $(lsb_release -cs) main" > /etc/apt/sources.list.d/ros2-latest.list'
$ sudo curl -sSL https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -o /usr/share/keyrings/ros-archive-keyring.gpg
```

```text
$ sudo apt update
$ sudo apt install ros-iron-desktop python3-colcon-common-extensions
```

```text
$ . /opt/ros/iron/setup.bash
```

## Install Colcon-cargo

```text
$ pip install git+https://github.com/tier4/colcon-cargo.git
$ pip install git+https://github.com/colcon/colcon-ros-cargo.git
```

## Install Cargo-ament

```text
$ git clone https://github.com/tier4/cargo-ament-build.git
$ cd cargo-ament-build
$ cargo install --path .
```
