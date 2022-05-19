---- MODULE scheduler ----
EXTENDS TLC, Sequences, Integers, SequencesExt

CONSTANTS Subscribers, Timers, Workers

(* --algorithm scheduler
variables
    wait_set = {};
    run_queue = <<>>;
    running = {};
    waiting = Subscribers \union Timers;

\* sleep random time
procedure sleep_random() begin
    start_sleep:
        while TRUE do
            either
                goto end_sleep;
            or
                skip;
            end either;
        end while;
    end_sleep:
        return;
end procedure;

fair+ process scheduler = "scheduler"
begin
    start_sched:
        while TRUE do
            pick_task:
                \* pick runnable tasks and change the states to run_queue from waiting
                with tasks = waiting \intersect wait_set do
                    with timers = tasks \intersect Timers,
                         subscriber = tasks \intersect Subscribers do
                        \* push to run_queue
                        run_queue := run_queue \o SetToSeq(timers) \o SetToSeq(subscriber);

                        waiting := waiting \ (timers \ subscriber); \* change state
                    end with;
                end with;
        end while;
end process;

fair process trigger_subscriber \in Subscribers
begin
    start_subscriber:
        while TRUE do
            wait_set := wait_set \union {self};
            call sleep_random();
        end while;
end process;

fair process trigger_timer \in Timers
begin
    start_timer:
        while TRUE do
            wait_set := wait_set \union {self};
            call sleep_random();
        end while;
end process;

\* worker thread
fair+ process worker \in Workers
variables
    task;
begin
    \* work-stealing
    start_worker:
        while TRUE do
            await run_queue /= <<>>;
            task := Head(run_queue);
            run_queue := Tail(run_queue);
            running := running \union {task};

            \* do some task
            call sleep_random();

            finish_task:
                running := running \ {task};
                waiting := waiting \union {task}
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2eee11fb" /\ chksum(tla) = "19f0418")
CONSTANT defaultInitValue
VARIABLES wait_set, run_queue, running, waiting, pc, stack, task

vars == << wait_set, run_queue, running, waiting, pc, stack, task >>

ProcSet == {"scheduler"} \cup (Subscribers) \cup (Timers) \cup (Workers)

Init == (* Global variables *)
        /\ wait_set = {}
        /\ run_queue = <<>>
        /\ running = {}
        /\ waiting = (Subscribers \union Timers)
        (* Process worker *)
        /\ task = [self \in Workers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "scheduler" -> "start_sched"
                                        [] self \in Subscribers -> "start_subscriber"
                                        [] self \in Timers -> "start_timer"
                                        [] self \in Workers -> "start_worker"]

start_sleep(self) == /\ pc[self] = "start_sleep"
                     /\ \/ /\ pc' = [pc EXCEPT ![self] = "end_sleep"]
                        \/ /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "start_sleep"]
                     /\ UNCHANGED << wait_set, run_queue, running, waiting, 
                                     stack, task >>

end_sleep(self) == /\ pc[self] = "end_sleep"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << wait_set, run_queue, running, waiting, task >>

sleep_random(self) == start_sleep(self) \/ end_sleep(self)

start_sched == /\ pc["scheduler"] = "start_sched"
               /\ pc' = [pc EXCEPT !["scheduler"] = "pick_task"]
               /\ UNCHANGED << wait_set, run_queue, running, waiting, stack, 
                               task >>

pick_task == /\ pc["scheduler"] = "pick_task"
             /\ LET tasks == waiting \intersect wait_set IN
                  LET timers == tasks \intersect Timers IN
                    LET subscriber == tasks \intersect Subscribers IN
                      /\ run_queue' = run_queue \o SetToSeq(timers) \o SetToSeq(subscriber)
                      /\ waiting' = waiting \ (timers \ subscriber)
             /\ pc' = [pc EXCEPT !["scheduler"] = "start_sched"]
             /\ UNCHANGED << wait_set, running, stack, task >>

scheduler == start_sched \/ pick_task

start_subscriber(self) == /\ pc[self] = "start_subscriber"
                          /\ wait_set' = (wait_set \union {self})
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sleep_random",
                                                                   pc        |->  "start_subscriber" ] >>
                                                               \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "start_sleep"]
                          /\ UNCHANGED << run_queue, running, waiting, task >>

trigger_subscriber(self) == start_subscriber(self)

start_timer(self) == /\ pc[self] = "start_timer"
                     /\ wait_set' = (wait_set \union {self})
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sleep_random",
                                                              pc        |->  "start_timer" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "start_sleep"]
                     /\ UNCHANGED << run_queue, running, waiting, task >>

trigger_timer(self) == start_timer(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ run_queue /= <<>>
                      /\ task' = [task EXCEPT ![self] = Head(run_queue)]
                      /\ run_queue' = Tail(run_queue)
                      /\ running' = (running \union {task'[self]})
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sleep_random",
                                                               pc        |->  "finish_task" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "start_sleep"]
                      /\ UNCHANGED << wait_set, waiting >>

finish_task(self) == /\ pc[self] = "finish_task"
                     /\ running' = running \ {task[self]}
                     /\ waiting' = (waiting \union {task[self]})
                     /\ pc' = [pc EXCEPT ![self] = "start_worker"]
                     /\ UNCHANGED << wait_set, run_queue, stack, task >>

worker(self) == start_worker(self) \/ finish_task(self)

Next == scheduler
           \/ (\E self \in ProcSet: sleep_random(self))
           \/ (\E self \in Subscribers: trigger_subscriber(self))
           \/ (\E self \in Timers: trigger_timer(self))
           \/ (\E self \in Workers: worker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(scheduler)
        /\ \A self \in Subscribers : WF_vars(trigger_subscriber(self)) /\ WF_vars(sleep_random(self))
        /\ \A self \in Timers : WF_vars(trigger_timer(self)) /\ WF_vars(sleep_random(self))
        /\ \A self \in Workers : SF_vars(worker(self)) /\ SF_vars(sleep_random(self))

\* END TRANSLATION
====
