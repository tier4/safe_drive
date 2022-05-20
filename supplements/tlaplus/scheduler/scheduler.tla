---- MODULE scheduler ----
EXTENDS TLC, Sequences, Integers, SequencesExt, FiniteSets

CONSTANTS Subscribers, Timers, Workers, LoopTimer, LoopSubscriber

AllTask == Subscribers \union Subscribers

(* --algorithm scheduler
variables
    \* events
    wait_set = {};

    \* states of tasks
    run_queue = <<>>;
    running = {};
    waiting = AllTask;

    finish_subscriber = FALSE;
    finish_timer = FALSE;
    is_finish_sched = FALSE;

define
    is_finish_event == finish_subscriber /\ finish_timer
    starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)
end define

fair+ process scheduler = "scheduler"
begin
    start_sched:
        while TRUE do
                await wait_set /= {} \/ is_finish_event;

                if wait_set /= {} then
                    \* pick runnable tasks and change the states to run_queue from waiting
                    with tasks = waiting \intersect wait_set,
                        timers = tasks \intersect Timers,
                        subscribers = tasks \intersect Subscribers do
                            \* push to run_queue
                            run_queue := run_queue \o SetToSeq(timers) \o SetToSeq(subscribers);

                            \* change state
                            waiting := (waiting \ timers) \ subscribers;
                    end with;
                else
                    goto end_sched;
                end if;
        end while;
    end_sched:
        is_finish_sched := TRUE;
end process;

fair+ process trigger_subscriber \in Subscribers
variables
    cnt = 0;
begin
    start_subscriber:
        while cnt < LoopSubscriber do
            wait_set := wait_set \union {self};
            cnt := cnt + 1;
        end while;
    end_subscriber:
        finish_subscriber := TRUE;
end process;

fair+ process trigger_timer \in Timers
variables
    cnt = 0;
begin
    start_timer:
        while cnt < LoopTimer do
            wait_set := wait_set \union {self};
            cnt := cnt + 1;
        end while;
    end_timer:
        finish_timer := TRUE;
end process;

\* worker thread
fair+ process worker \in Workers
variables
    task;
begin
    \* work-stealing
    start_worker:
        while TRUE do
            await run_queue /= <<>> \/ is_finish_sched;

            if run_queue = <<>> then
                goto end_worker;
            else
                task := Head(run_queue);
                run_queue := Tail(run_queue);
                running := running \union {task};
            end if;

            finish_task:
                running := running \ {task};
                waiting := waiting \union {task};
        end while;
    end_worker:
        skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "993d6fff" /\ chksum(tla) = "e3181fcf")
\* Process variable cnt of process trigger_subscriber at line 54 col 5 changed to cnt_
CONSTANT defaultInitValue
VARIABLES wait_set, run_queue, running, waiting, finish_subscriber, 
          finish_timer, is_finish_sched, pc

(* define statement *)
is_finish_event == finish_subscriber /\ finish_timer
starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)

VARIABLES cnt_, cnt, task

vars == << wait_set, run_queue, running, waiting, finish_subscriber, 
           finish_timer, is_finish_sched, pc, cnt_, cnt, task >>

ProcSet == {"scheduler"} \cup (Subscribers) \cup (Timers) \cup (Workers)

Init == (* Global variables *)
        /\ wait_set = {}
        /\ run_queue = <<>>
        /\ running = {}
        /\ waiting = AllTask
        /\ finish_subscriber = FALSE
        /\ finish_timer = FALSE
        /\ is_finish_sched = FALSE
        (* Process trigger_subscriber *)
        /\ cnt_ = [self \in Subscribers |-> 0]
        (* Process trigger_timer *)
        /\ cnt = [self \in Timers |-> 0]
        (* Process worker *)
        /\ task = [self \in Workers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = "scheduler" -> "start_sched"
                                        [] self \in Subscribers -> "start_subscriber"
                                        [] self \in Timers -> "start_timer"
                                        [] self \in Workers -> "start_worker"]

start_sched == /\ pc["scheduler"] = "start_sched"
               /\ wait_set /= {} \/ is_finish_event
               /\ IF wait_set /= {}
                     THEN /\ LET tasks == waiting \intersect wait_set IN
                               LET timers == tasks \intersect Timers IN
                                 LET subscribers == tasks \intersect Subscribers IN
                                   /\ run_queue' = run_queue \o SetToSeq(timers) \o SetToSeq(subscribers)
                                   /\ waiting' = (waiting \ timers) \ subscribers
                          /\ pc' = [pc EXCEPT !["scheduler"] = "start_sched"]
                     ELSE /\ pc' = [pc EXCEPT !["scheduler"] = "end_sched"]
                          /\ UNCHANGED << run_queue, waiting >>
               /\ UNCHANGED << wait_set, running, finish_subscriber, 
                               finish_timer, is_finish_sched, cnt_, cnt, task >>

end_sched == /\ pc["scheduler"] = "end_sched"
             /\ is_finish_sched' = TRUE
             /\ pc' = [pc EXCEPT !["scheduler"] = "Done"]
             /\ UNCHANGED << wait_set, run_queue, running, waiting, 
                             finish_subscriber, finish_timer, cnt_, cnt, task >>

scheduler == start_sched \/ end_sched

start_subscriber(self) == /\ pc[self] = "start_subscriber"
                          /\ IF cnt_[self] < LoopSubscriber
                                THEN /\ wait_set' = (wait_set \union {self})
                                     /\ cnt_' = [cnt_ EXCEPT ![self] = cnt_[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "start_subscriber"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "end_subscriber"]
                                     /\ UNCHANGED << wait_set, cnt_ >>
                          /\ UNCHANGED << run_queue, running, waiting, 
                                          finish_subscriber, finish_timer, 
                                          is_finish_sched, cnt, task >>

end_subscriber(self) == /\ pc[self] = "end_subscriber"
                        /\ finish_subscriber' = TRUE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << wait_set, run_queue, running, waiting, 
                                        finish_timer, is_finish_sched, cnt_, 
                                        cnt, task >>

trigger_subscriber(self) == start_subscriber(self) \/ end_subscriber(self)

start_timer(self) == /\ pc[self] = "start_timer"
                     /\ IF cnt[self] < LoopTimer
                           THEN /\ wait_set' = (wait_set \union {self})
                                /\ cnt' = [cnt EXCEPT ![self] = cnt[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "start_timer"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "end_timer"]
                                /\ UNCHANGED << wait_set, cnt >>
                     /\ UNCHANGED << run_queue, running, waiting, 
                                     finish_subscriber, finish_timer, 
                                     is_finish_sched, cnt_, task >>

end_timer(self) == /\ pc[self] = "end_timer"
                   /\ finish_timer' = TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << wait_set, run_queue, running, waiting, 
                                   finish_subscriber, is_finish_sched, cnt_, 
                                   cnt, task >>

trigger_timer(self) == start_timer(self) \/ end_timer(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ run_queue /= <<>> \/ is_finish_sched
                      /\ IF run_queue = <<>>
                            THEN /\ pc' = [pc EXCEPT ![self] = "end_worker"]
                                 /\ UNCHANGED << run_queue, running, task >>
                            ELSE /\ task' = [task EXCEPT ![self] = Head(run_queue)]
                                 /\ run_queue' = Tail(run_queue)
                                 /\ running' = (running \union {task'[self]})
                                 /\ pc' = [pc EXCEPT ![self] = "finish_task"]
                      /\ UNCHANGED << wait_set, waiting, finish_subscriber, 
                                      finish_timer, is_finish_sched, cnt_, cnt >>

finish_task(self) == /\ pc[self] = "finish_task"
                     /\ running' = running \ {task[self]}
                     /\ waiting' = (waiting \union {task[self]})
                     /\ pc' = [pc EXCEPT ![self] = "start_worker"]
                     /\ UNCHANGED << wait_set, run_queue, finish_subscriber, 
                                     finish_timer, is_finish_sched, cnt_, cnt, 
                                     task >>

end_worker(self) == /\ pc[self] = "end_worker"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << wait_set, run_queue, running, waiting, 
                                    finish_subscriber, finish_timer, 
                                    is_finish_sched, cnt_, cnt, task >>

worker(self) == start_worker(self) \/ finish_task(self) \/ end_worker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == scheduler
           \/ (\E self \in Subscribers: trigger_subscriber(self))
           \/ (\E self \in Timers: trigger_timer(self))
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(scheduler)
        /\ \A self \in Subscribers : SF_vars(trigger_subscriber(self))
        /\ \A self \in Timers : SF_vars(trigger_timer(self))
        /\ \A self \in Workers : SF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====

