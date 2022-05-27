# Specification and Model Checking

## Setting-up

We use [TLA+](https://lamport.azurewebsites.net/tla/tla.html) to specify and check whether our algorithms are safe.

In order to check the specifications, we use [TLA+'s community modules](https://github.com/tlaplus/CommunityModules).
To use the modules, please install Java 9 or later.
Pass required modules to Java by using `-cp` option when you try these files.
See [tlaplus_community_jar](https://github.com/ytakano/tlaplus_community_jar) for more information.

## Specifications

- [Basic Scheduler](./scheduler/)
- TODO: Prioritized Scheduler
- TODO: Callback Based Execution
- [Initialize Once](./init_once/)
