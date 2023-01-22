# Editor Setting-up

`safe_drive` has features like `humble` or `galactic`, which indicates ROS2 version.
We recommend pass one of a feature to enable editor's support.

If you use ROS2 humble and Visual Studio Code,
please add `humble` in `rust-analyzer -> cargo -> features` as follows.

```json
{
    "rust-analyzer.cargo.features": [
        "humble"
    ]
}
```

Client applications not necessary to specify a feature of ROS2 version,
because [build.rs](https://github.com/tier4/safe_drive/blob/main/build.rs) detects
ROS2 version from `ROS_DISTRO` environment variable.
