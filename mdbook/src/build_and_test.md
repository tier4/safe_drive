# Build and Test

Build and test can be done by using `make` as follows.

Build:

```text
$ make
```

Test:

```text
$ make test
```

`make test` executes test codes in [tests](https://github.com/tier4/safe_drive/tree/main/tests),
and codes in documentation comment.

`cargo test` may not work because it requires some environment variables
and some code generation.
Please see [Makefile](https://github.com/tier4/safe_drive/blob/main/Makefile).

Cleaning-up can be done as follows.

```text
$ make clean
```
