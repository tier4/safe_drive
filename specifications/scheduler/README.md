# Basic Scheduler

`safe_drive` provides a basic scheduler for asynchronous programming in Rust; async/await. [scheduler.tla](./scheduler.tla) is the specification of the scheduler.

## Premises

- Worker threads make use of the work-stealing strategy, which is used by `async_std` and `Tokio`.
- Servers, clients, and subscribers can take messages periodically.

If servers, clients, or subscribers are ready,
the events are inserted into `wait_set`.
The scheduler pick the events up and wake-up the tasks waiting the events.

There are three states for a task. The scheduler changes the state
and execute it.

- `run_queue` : runnable but not running
- `running` : now running
- `waiting` : waiting an event

## What do we check?

- Deadlock freedom
- Starvation freedom

The starvation freedom can be checked by using the temporal logic.
We use the expression as follows to check the starvation freedom.

```tla+
starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)
```

This is equivalent to

$$
\forall \mathrm{event} \in \mathrm{AllTask}(\mathrm{event} \in \mathrm{wait\verb|_|set} \Rightarrow \lozenge(\mathrm{event} \in \mathrm{running})).
$$

## Processes

- `shceduler` : the scheduler of `safe_drive`
- `trigger_*` : event trigger of servers, clients, and subscribers
- `worker` : worker threads provided by asynchronous libraries like `async_std` or `Tokio`
