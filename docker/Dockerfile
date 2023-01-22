# FROM nvidia/cuda:11.7.0-runtime-ubuntu20.04
FROM ubuntu:22.04

ENV TZ=Asia/Tokyo
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt-get -y update && \
    apt-get -y upgrade && \
    apt-get -y install build-essential zsh git curl libncurses5-dev gnupg clang

RUN apt-get -y install software-properties-common && \
    add-apt-repository universe

RUN apt-get -y update && \
    apt-get -y install lsb-core lsb-release && \
    curl -sSL https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -o /usr/share/keyrings/ros-archive-keyring.gpg

RUN echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/ros-archive-keyring.gpg] http://packages.ros.org/ros2/ubuntu jammy main" | \
    tee /etc/apt/sources.list.d/ros2.list > /dev/null

RUN apt-get -y update && \
    apt-get -y install ros-humble-desktop python3-colcon-common-extensions python3-rosdep libclang-dev python3-pip python3-vcstool ros-humble-rmw-cyclonedds-cpp

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN . /root/.cargo/env && \
    cargo install bindgen-cli && \
    cargo install mdbook && \
    cargo install mdbook-mermaid && \
    cargo install --git https://github.com/tier4/ros2msg_to_rs.git

RUN pip install git+https://github.com/tier4/colcon-cargo.git && \
    pip install git+https://github.com/colcon/colcon-ros-cargo.git

COPY zshenv /root/.zshenv
COPY zshrc /root/.zshrc

ENTRYPOINT ["zsh"]
