FROM nvidia/cuda:11.6.2-runtime-ubuntu20.04

ENV TZ=Asia/Tokyo
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt-get -y update && \
    apt-get -y upgrade && \
    apt-get -y install build-essential zsh git curl libncurses5-dev gnupg clang default-jre

RUN apt-get -y install software-properties-common && \
    add-apt-repository universe

RUN apt-get -y update && \
    apt-get -y install lsb-core lsb-release && \
    curl -sSL https://raw.githubusercontent.com/ros/rosdistro/master/ros.key -o /usr/share/keyrings/ros-archive-keyring.gpg

RUN echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/ros-archive-keyring.gpg] http://packages.ros.org/ros2/ubuntu focal main" | \
    tee /etc/apt/sources.list.d/ros2.list > /dev/null

RUN apt-get -y update && \
    apt-get -y install ros-galactic-desktop python3-colcon-common-extensions python3-rosdep

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN apt-get -y install language-pack-ja

COPY zshenv /root/.zshenv
COPY zshrc /root/.zshrc

ENTRYPOINT ["zsh"]
