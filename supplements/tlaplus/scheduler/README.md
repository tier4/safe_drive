# Basic Scheduler

`safe_drive` provides a basic scheduler for asynchronous programming in Rust; async/await. [scheduler.tla](./scheduler.tla) is the specification of the scheduler.

## Premises

- Worker threads make use of the work-stealing strategy.
- Subscribers can take messages periodically.
- Timers will be triggered periodically.

If subscribers or timers are ready,
the events are inserted into `wait-set`.
The scheduler pick a event and wake-up the task which are waiting it.

There are three states for a task. The scheduler changes the state
and execute it.

- run_queue : runnable but not running
- running : now running
- waiting : waiting an event

## What do we check?

- Deadlock freedom
- Starvation freedom

The starvation freedom can be checked by using the temporal logic.
We use the expression as follows to check the starvation freedom.

```tla+
starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)
```

This is equivalent with

<img src="https://render.githubusercontent.com/render/math?math=\forall \mathrm{event} \in \mathrm{AllTask}(\mathrm{event} \in \mathrm{wait_set} \Rightarrow \diamond(\mathrm{event} \in \mathrm{running}))">.


# Prioritized Scheduler

TODO