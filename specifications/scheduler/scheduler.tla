---- MODULE scheduler ----
EXTENDS TLC, Sequences, SequencesExt, FiniteSets

CONSTANTS Subscribers, Servers, Clients, Workers

AllTask == Subscribers \union Subscribers

(* --algorithm scheduler
variables
    \* events
    wait_set = {};

    \* states of tasks
    run_queue = <<>>;
    running = {};
    waiting = AllTask;

define
    starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)
end define

fair+ process scheduler = "scheduler"
begin
    start_sched:
        while TRUE do
                await wait_set /= {};

                \* pick runnable tasks and change the states to run_queue from waiting
                with tasks = waiting \intersect wait_set,
                     servers = tasks \intersect Servers,
                     clients = tasks \intersect Clients,
                     subscribers = tasks \intersect Subscribers do
                        \* push to run_queue
                        run_queue := run_queue \o SetToSeq(subscribers) \o SetToSeq(servers) \o SetToSeq(clients);

                        \* change state
                        waiting := ((waiting \ subscribers) \ servers) \ clients;
                end with;
        end while;
end process;

fair process trigger_subscriber \in Subscribers
begin
    start_subscriber:
        while TRUE do
            wait_set := wait_set \union {self};
        end while;
end process;

fair process trigger_server \in Servers
begin
    start_server:
        while TRUE do
            wait_set := wait_set \union {self};
        end while;
end process;

fair process trigger_client \in Clients
begin
    start_client:
        while TRUE do
            wait_set := wait_set \union {self};
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

            finish_task:
                running := running \ {task};
                waiting := waiting \union {task};
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f261a5cb" /\ chksum(tla) = "14a8e3c0")
CONSTANT defaultInitValue
VARIABLES wait_set, run_queue, running, waiting, pc

(* define statement *)
starvation_free == \A event \in AllTask: event \in wait_set ~> <>(event \in running)

VARIABLE task

vars == << wait_set, run_queue, running, waiting, pc, task >>

ProcSet == {"scheduler"} \cup (Subscribers) \cup (Servers) \cup (Clients) \cup (Workers)

Init == (* Global variables *)
        /\ wait_set = {}
        /\ run_queue = <<>>
        /\ running = {}
        /\ waiting = AllTask
        (* Process worker *)
        /\ task = [self \in Workers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = "scheduler" -> "start_sched"
                                        [] self \in Subscribers -> "start_subscriber"
                                        [] self \in Servers -> "start_server"
                                        [] self \in Clients -> "start_client"
                                        [] self \in Workers -> "start_worker"]

start_sched == /\ pc["scheduler"] = "start_sched"
               /\ wait_set /= {}
               /\ LET tasks == waiting \intersect wait_set IN
                    LET servers == tasks \intersect Servers IN
                      LET clients == tasks \intersect Clients IN
                        LET subscribers == tasks \intersect Subscribers IN
                          /\ run_queue' = run_queue \o SetToSeq(subscribers) \o SetToSeq(servers) \o SetToSeq(clients)
                          /\ waiting' = ((waiting \ subscribers) \ servers) \ clients
               /\ pc' = [pc EXCEPT !["scheduler"] = "start_sched"]
               /\ UNCHANGED << wait_set, running, task >>

scheduler == start_sched

start_subscriber(self) == /\ pc[self] = "start_subscriber"
                          /\ wait_set' = (wait_set \union {self})
                          /\ pc' = [pc EXCEPT ![self] = "start_subscriber"]
                          /\ UNCHANGED << run_queue, running, waiting, task >>

trigger_subscriber(self) == start_subscriber(self)

start_server(self) == /\ pc[self] = "start_server"
                      /\ wait_set' = (wait_set \union {self})
                      /\ pc' = [pc EXCEPT ![self] = "start_server"]
                      /\ UNCHANGED << run_queue, running, waiting, task >>

trigger_server(self) == start_server(self)

start_client(self) == /\ pc[self] = "start_client"
                      /\ wait_set' = (wait_set \union {self})
                      /\ pc' = [pc EXCEPT ![self] = "start_client"]
                      /\ UNCHANGED << run_queue, running, waiting, task >>

trigger_client(self) == start_client(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ run_queue /= <<>>
                      /\ task' = [task EXCEPT ![self] = Head(run_queue)]
                      /\ run_queue' = Tail(run_queue)
                      /\ running' = (running \union {task'[self]})
                      /\ pc' = [pc EXCEPT ![self] = "finish_task"]
                      /\ UNCHANGED << wait_set, waiting >>

finish_task(self) == /\ pc[self] = "finish_task"
                     /\ running' = running \ {task[self]}
                     /\ waiting' = (waiting \union {task[self]})
                     /\ pc' = [pc EXCEPT ![self] = "start_worker"]
                     /\ UNCHANGED << wait_set, run_queue, task >>

worker(self) == start_worker(self) \/ finish_task(self)

Next == scheduler
           \/ (\E self \in Subscribers: trigger_subscriber(self))
           \/ (\E self \in Servers: trigger_server(self))
           \/ (\E self \in Clients: trigger_client(self))
           \/ (\E self \in Workers: worker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(scheduler)
        /\ \A self \in Subscribers : WF_vars(trigger_subscriber(self))
        /\ \A self \in Servers : WF_vars(trigger_server(self))
        /\ \A self \in Clients : WF_vars(trigger_client(self))
        /\ \A self \in Workers : SF_vars(worker(self))

\* END TRANSLATION
====

