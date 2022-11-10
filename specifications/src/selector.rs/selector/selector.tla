---- MODULE selector ----
EXTENDS TLC, Sequences, SequencesExt, FiniteSets, Integers

CONSTANTS Timers, DeltaRange, Servers, Clients, Subscribers

Tasks == Subscribers \union Servers \union Clients

(* --algorithm selector
variables
    \* list for timer
    \* example: <<[delta |-> 3, name |-> "timer1"], [delta |-> 2, name |-> "timer2"]>>
    delta_list = SetToSeq({[delta |-> random_num(0, DeltaRange), name |-> x]: x \in Timers});

    \* events
    wait_set = {};

    \* tasks
    running = {};
    waiting = Tasks;

define
    random_num(min, max) == CHOOSE i \in min..max: TRUE
    pick_task(set) == CHOOSE x \in set: TRUE

    starvation_free == \A x \in (Timers \union Tasks):
        LET delta_set == {y.name: y \in ToSet(delta_list)} IN
        (((x \in delta_set) \/ (x \in wait_set)) ~> <>(x \in running))
    running_xor_waiting == \A x \in Tasks:
        (x \in running /\ x \notin waiting) \/ (x \notin running /\ x \in waiting)
    running_then_not_delta_list == \A x \in Timers:
        LET delta_set == {y.name: y \in ToSet(delta_list)} IN
        x \in running => x \notin delta_set
    type_check ==
        LET delta_set == {y.name: y \in ToSet(delta_list)} IN
        /\ waiting \subseteq Tasks
        /\ running \subseteq (Tasks \union Timers)
        /\ delta_set \subseteq Timers
end define

\* To emulate incrementing clock, decrement the delta of the head of the delta_list.
macro increment_clock()
begin
    if delta_list /= <<>> /\ delta_list[1].delta > 0 then
        delta_list[1].delta := delta_list[1].delta - 1;
    end if;
end macro;

\* execute a callback function
procedure callback(name)
begin
    BeginCallback:
        increment_clock();
        running := running \union { name };
        waiting := waiting \ { name };

    EndCallback:
        running := running \ { name };
        if name \in Tasks then
            waiting := waiting \union  { name }
        end if;
        return;
end procedure;

\* reenable timer with at random delay
procedure reload_timer(name)
variables
    idx;
    delta;
begin
    BeginReloadTimer:
        increment_clock();

        \* choose insertion point
        idx := random_num(1, Len(delta_list) + 1);
        if idx <= Len(delta_list) then
            \* insert to middle
            delta := random_num(0, delta_list[idx].delta);

            reload_insert1:
                \* update delta and insert
                delta_list[idx].delta := delta_list[idx].delta - delta;

            reload_insert2:
                delta_list := InsertAt(delta_list, idx, [delta |-> delta, name |-> name]);
        else
            \* insert to the end
            delta := random_num(0, DeltaRange);

            reload_insert_end:
                delta_list := Append(delta_list, [delta |-> delta, name |-> name]);
            skip;
        end if;

    EndReloadTimer:
        return;
end procedure;

\* execute a task
\*
\* safe_drive::selector::notify
procedure notify(runnable)
variables
    task;
begin
    BeginNotify:
        while runnable /= {} do
            task := pick_task(runnable);
            runnable := runnable \ {task};
            call callback(task);
        end while;

    EndNotify:
        return;
end procedure;

\* wait with timeout.
\*
\* safe_drive::selector::notify_timer
procedure notify_timer()
variables
    head;
    to_be_reloaded = <<>>;
begin
    BeginNotifyTimer:
        while delta_list /= <<>> /\ delta_list[1].delta = 0 do
            \* pop front
            head := Head(delta_list);
            delta_list := Tail(delta_list);

            \* call the callback function
            call callback(head.name);

            \* reenable timer later
            save_timer:
                to_be_reloaded := Append(to_be_reloaded, head.name);
        end while;

    ReladTimer:
        \* reenable timer
        while to_be_reloaded /= <<>> do
            call reload_timer(to_be_reloaded[1]);

            reload2:
                to_be_reloaded := Tail(to_be_reloaded);
        end while;

    EndNotifyTimer:
        return;
end procedure;

\* Emulate ROS2's rcl_wait()
procedure rcl_wait()
begin
    BeginRclWait:
        while delta_list /= <<>> /\ delta_list[1].delta > 0 /\ wait_set = {} do
            increment_clock();
        end while;

    EndRclWait:
        return;
end procedure;

\* safe_drive::selector::wait_timer
procedure wait_timer()
begin
    BeginWaitTimer:
        call rcl_wait();

    EndWaitTimer:
        return;
end procedure;

\* safe_drive::selector::wait
procedure wait()
begin
    BeginWait:
        call wait_timer();

    NotifyTimer:
        call notify_timer();

    Notify:
        \* pick wait_set tasks up
        with tmp_wait_set = wait_set do
            wait_set := {};
            call notify(tmp_wait_set);
        end with;

    EndWait:
        return;
end procedure;

fair process trigger_event \in Tasks
begin
    fire_event:
        while TRUE do
            wait_set := wait_set \union {self};
        end while;
end process;

fair+ process executor = "executor"
variables
    head;
    to_be_reloaded = <<>>;
begin
    BeginExecutor:
        while TRUE do
            call wait();
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "615b0ea5" /\ chksum(tla) = "7cf79cd9")
\* Process variable head of process executor at line 203 col 5 changed to head_
\* Process variable to_be_reloaded of process executor at line 204 col 5 changed to to_be_reloaded_
\* Parameter name of procedure callback at line 49 col 20 changed to name_
CONSTANT defaultInitValue
VARIABLES delta_list, wait_set, running, waiting, pc, stack

(* define statement *)
random_num(min, max) == CHOOSE i \in min..max: TRUE
pick_task(set) == CHOOSE x \in set: TRUE

starvation_free == \A x \in (Timers \union Tasks):
    LET delta_set == {y.name: y \in ToSet(delta_list)} IN
    (((x \in delta_set) \/ (x \in wait_set)) ~> <>(x \in running))
running_xor_waiting == \A x \in Tasks:
    (x \in running /\ x \notin waiting) \/ (x \notin running /\ x \in waiting)
running_then_not_delta_list == \A x \in Timers:
    LET delta_set == {y.name: y \in ToSet(delta_list)} IN
    x \in running => x \notin delta_set
type_check ==
    LET delta_set == {y.name: y \in ToSet(delta_list)} IN
    /\ waiting \subseteq Tasks
    /\ running \subseteq (Tasks \union Timers)
    /\ delta_set \subseteq Timers

VARIABLES name_, name, idx, delta, runnable, task, head, to_be_reloaded, 
          head_, to_be_reloaded_

vars == << delta_list, wait_set, running, waiting, pc, stack, name_, name, 
           idx, delta, runnable, task, head, to_be_reloaded, head_, 
           to_be_reloaded_ >>

ProcSet == (Tasks) \cup {"executor"}

Init == (* Global variables *)
        /\ delta_list = SetToSeq({[delta |-> random_num(0, DeltaRange), name |-> x]: x \in Timers})
        /\ wait_set = {}
        /\ running = {}
        /\ waiting = Tasks
        (* Procedure callback *)
        /\ name_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure reload_timer *)
        /\ name = [ self \in ProcSet |-> defaultInitValue]
        /\ idx = [ self \in ProcSet |-> defaultInitValue]
        /\ delta = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure notify *)
        /\ runnable = [ self \in ProcSet |-> defaultInitValue]
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure notify_timer *)
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        /\ to_be_reloaded = [ self \in ProcSet |-> <<>>]
        (* Process executor *)
        /\ head_ = defaultInitValue
        /\ to_be_reloaded_ = <<>>
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Tasks -> "fire_event"
                                        [] self = "executor" -> "BeginExecutor"]

BeginCallback(self) == /\ pc[self] = "BeginCallback"
                       /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0
                             THEN /\ delta_list' = [delta_list EXCEPT ![1].delta = delta_list[1].delta - 1]
                             ELSE /\ TRUE
                                  /\ UNCHANGED delta_list
                       /\ running' = (running \union { name_[self] })
                       /\ waiting' = waiting \ { name_[self] }
                       /\ pc' = [pc EXCEPT ![self] = "EndCallback"]
                       /\ UNCHANGED << wait_set, stack, name_, name, idx, 
                                       delta, runnable, task, head, 
                                       to_be_reloaded, head_, to_be_reloaded_ >>

EndCallback(self) == /\ pc[self] = "EndCallback"
                     /\ running' = running \ { name_[self] }
                     /\ IF name_[self] \in Tasks
                           THEN /\ waiting' = (waiting \union  { name_[self] })
                           ELSE /\ TRUE
                                /\ UNCHANGED waiting
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ name_' = [name_ EXCEPT ![self] = Head(stack[self]).name_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << delta_list, wait_set, name, idx, delta, 
                                     runnable, task, head, to_be_reloaded, 
                                     head_, to_be_reloaded_ >>

callback(self) == BeginCallback(self) \/ EndCallback(self)

BeginReloadTimer(self) == /\ pc[self] = "BeginReloadTimer"
                          /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0
                                THEN /\ delta_list' = [delta_list EXCEPT ![1].delta = delta_list[1].delta - 1]
                                ELSE /\ TRUE
                                     /\ UNCHANGED delta_list
                          /\ idx' = [idx EXCEPT ![self] = random_num(1, Len(delta_list') + 1)]
                          /\ IF idx'[self] <= Len(delta_list')
                                THEN /\ delta' = [delta EXCEPT ![self] = random_num(0, delta_list'[idx'[self]].delta)]
                                     /\ pc' = [pc EXCEPT ![self] = "reload_insert1"]
                                ELSE /\ delta' = [delta EXCEPT ![self] = random_num(0, DeltaRange)]
                                     /\ pc' = [pc EXCEPT ![self] = "reload_insert_end"]
                          /\ UNCHANGED << wait_set, running, waiting, stack, 
                                          name_, name, runnable, task, head, 
                                          to_be_reloaded, head_, 
                                          to_be_reloaded_ >>

reload_insert1(self) == /\ pc[self] = "reload_insert1"
                        /\ delta_list' = [delta_list EXCEPT ![idx[self]].delta = delta_list[idx[self]].delta - delta[self]]
                        /\ pc' = [pc EXCEPT ![self] = "reload_insert2"]
                        /\ UNCHANGED << wait_set, running, waiting, stack, 
                                        name_, name, idx, delta, runnable, 
                                        task, head, to_be_reloaded, head_, 
                                        to_be_reloaded_ >>

reload_insert2(self) == /\ pc[self] = "reload_insert2"
                        /\ delta_list' = InsertAt(delta_list, idx[self], [delta |-> delta[self], name |-> name[self]])
                        /\ pc' = [pc EXCEPT ![self] = "EndReloadTimer"]
                        /\ UNCHANGED << wait_set, running, waiting, stack, 
                                        name_, name, idx, delta, runnable, 
                                        task, head, to_be_reloaded, head_, 
                                        to_be_reloaded_ >>

reload_insert_end(self) == /\ pc[self] = "reload_insert_end"
                           /\ delta_list' = Append(delta_list, [delta |-> delta[self], name |-> name[self]])
                           /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "EndReloadTimer"]
                           /\ UNCHANGED << wait_set, running, waiting, stack, 
                                           name_, name, idx, delta, runnable, 
                                           task, head, to_be_reloaded, head_, 
                                           to_be_reloaded_ >>

EndReloadTimer(self) == /\ pc[self] = "EndReloadTimer"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ idx' = [idx EXCEPT ![self] = Head(stack[self]).idx]
                        /\ delta' = [delta EXCEPT ![self] = Head(stack[self]).delta]
                        /\ name' = [name EXCEPT ![self] = Head(stack[self]).name]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                        name_, runnable, task, head, 
                                        to_be_reloaded, head_, to_be_reloaded_ >>

reload_timer(self) == BeginReloadTimer(self) \/ reload_insert1(self)
                         \/ reload_insert2(self) \/ reload_insert_end(self)
                         \/ EndReloadTimer(self)

BeginNotify(self) == /\ pc[self] = "BeginNotify"
                     /\ IF runnable[self] /= {}
                           THEN /\ task' = [task EXCEPT ![self] = pick_task(runnable[self])]
                                /\ runnable' = [runnable EXCEPT ![self] = runnable[self] \ {task'[self]}]
                                /\ /\ name_' = [name_ EXCEPT ![self] = task'[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "callback",
                                                                            pc        |->  "BeginNotify",
                                                                            name_     |->  name_[self] ] >>
                                                                        \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "BeginCallback"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "EndNotify"]
                                /\ UNCHANGED << stack, name_, runnable, task >>
                     /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                     name, idx, delta, head, to_be_reloaded, 
                                     head_, to_be_reloaded_ >>

EndNotify(self) == /\ pc[self] = "EndNotify"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                   /\ runnable' = [runnable EXCEPT ![self] = Head(stack[self]).runnable]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                   name_, name, idx, delta, head, 
                                   to_be_reloaded, head_, to_be_reloaded_ >>

notify(self) == BeginNotify(self) \/ EndNotify(self)

BeginNotifyTimer(self) == /\ pc[self] = "BeginNotifyTimer"
                          /\ IF delta_list /= <<>> /\ delta_list[1].delta = 0
                                THEN /\ head' = [head EXCEPT ![self] = Head(delta_list)]
                                     /\ delta_list' = Tail(delta_list)
                                     /\ /\ name_' = [name_ EXCEPT ![self] = head'[self].name]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "callback",
                                                                                 pc        |->  "save_timer",
                                                                                 name_     |->  name_[self] ] >>
                                                                             \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "BeginCallback"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "ReladTimer"]
                                     /\ UNCHANGED << delta_list, stack, name_, 
                                                     head >>
                          /\ UNCHANGED << wait_set, running, waiting, name, 
                                          idx, delta, runnable, task, 
                                          to_be_reloaded, head_, 
                                          to_be_reloaded_ >>

save_timer(self) == /\ pc[self] = "save_timer"
                    /\ to_be_reloaded' = [to_be_reloaded EXCEPT ![self] = Append(to_be_reloaded[self], head[self].name)]
                    /\ pc' = [pc EXCEPT ![self] = "BeginNotifyTimer"]
                    /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                    stack, name_, name, idx, delta, runnable, 
                                    task, head, head_, to_be_reloaded_ >>

ReladTimer(self) == /\ pc[self] = "ReladTimer"
                    /\ IF to_be_reloaded[self] /= <<>>
                          THEN /\ /\ name' = [name EXCEPT ![self] = to_be_reloaded[self][1]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "reload_timer",
                                                                           pc        |->  "reload2",
                                                                           idx       |->  idx[self],
                                                                           delta     |->  delta[self],
                                                                           name      |->  name[self] ] >>
                                                                       \o stack[self]]
                               /\ idx' = [idx EXCEPT ![self] = defaultInitValue]
                               /\ delta' = [delta EXCEPT ![self] = defaultInitValue]
                               /\ pc' = [pc EXCEPT ![self] = "BeginReloadTimer"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "EndNotifyTimer"]
                               /\ UNCHANGED << stack, name, idx, delta >>
                    /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                    name_, runnable, task, head, 
                                    to_be_reloaded, head_, to_be_reloaded_ >>

reload2(self) == /\ pc[self] = "reload2"
                 /\ to_be_reloaded' = [to_be_reloaded EXCEPT ![self] = Tail(to_be_reloaded[self])]
                 /\ pc' = [pc EXCEPT ![self] = "ReladTimer"]
                 /\ UNCHANGED << delta_list, wait_set, running, waiting, stack, 
                                 name_, name, idx, delta, runnable, task, head, 
                                 head_, to_be_reloaded_ >>

EndNotifyTimer(self) == /\ pc[self] = "EndNotifyTimer"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                        /\ to_be_reloaded' = [to_be_reloaded EXCEPT ![self] = Head(stack[self]).to_be_reloaded]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                        name_, name, idx, delta, runnable, 
                                        task, head_, to_be_reloaded_ >>

notify_timer(self) == BeginNotifyTimer(self) \/ save_timer(self)
                         \/ ReladTimer(self) \/ reload2(self)
                         \/ EndNotifyTimer(self)

BeginRclWait(self) == /\ pc[self] = "BeginRclWait"
                      /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0 /\ wait_set = {}
                            THEN /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0
                                       THEN /\ delta_list' = [delta_list EXCEPT ![1].delta = delta_list[1].delta - 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED delta_list
                                 /\ pc' = [pc EXCEPT ![self] = "BeginRclWait"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "EndRclWait"]
                                 /\ UNCHANGED delta_list
                      /\ UNCHANGED << wait_set, running, waiting, stack, name_, 
                                      name, idx, delta, runnable, task, head, 
                                      to_be_reloaded, head_, to_be_reloaded_ >>

EndRclWait(self) == /\ pc[self] = "EndRclWait"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                    name_, name, idx, delta, runnable, task, 
                                    head, to_be_reloaded, head_, 
                                    to_be_reloaded_ >>

rcl_wait(self) == BeginRclWait(self) \/ EndRclWait(self)

BeginWaitTimer(self) == /\ pc[self] = "BeginWaitTimer"
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "rcl_wait",
                                                                 pc        |->  "EndWaitTimer" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "BeginRclWait"]
                        /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                        name_, name, idx, delta, runnable, 
                                        task, head, to_be_reloaded, head_, 
                                        to_be_reloaded_ >>

EndWaitTimer(self) == /\ pc[self] = "EndWaitTimer"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                      name_, name, idx, delta, runnable, task, 
                                      head, to_be_reloaded, head_, 
                                      to_be_reloaded_ >>

wait_timer(self) == BeginWaitTimer(self) \/ EndWaitTimer(self)

BeginWait(self) == /\ pc[self] = "BeginWait"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait_timer",
                                                            pc        |->  "NotifyTimer" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "BeginWaitTimer"]
                   /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                   name_, name, idx, delta, runnable, task, 
                                   head, to_be_reloaded, head_, 
                                   to_be_reloaded_ >>

NotifyTimer(self) == /\ pc[self] = "NotifyTimer"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "notify_timer",
                                                              pc        |->  "Notify",
                                                              head      |->  head[self],
                                                              to_be_reloaded |->  to_be_reloaded[self] ] >>
                                                          \o stack[self]]
                     /\ head' = [head EXCEPT ![self] = defaultInitValue]
                     /\ to_be_reloaded' = [to_be_reloaded EXCEPT ![self] = <<>>]
                     /\ pc' = [pc EXCEPT ![self] = "BeginNotifyTimer"]
                     /\ UNCHANGED << delta_list, wait_set, running, waiting, 
                                     name_, name, idx, delta, runnable, task, 
                                     head_, to_be_reloaded_ >>

Notify(self) == /\ pc[self] = "Notify"
                /\ LET tmp_wait_set == wait_set IN
                     /\ wait_set' = {}
                     /\ /\ runnable' = [runnable EXCEPT ![self] = tmp_wait_set]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "notify",
                                                                 pc        |->  "EndWait",
                                                                 task      |->  task[self],
                                                                 runnable  |->  runnable[self] ] >>
                                                             \o stack[self]]
                     /\ task' = [task EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "BeginNotify"]
                /\ UNCHANGED << delta_list, running, waiting, name_, name, idx, 
                                delta, head, to_be_reloaded, head_, 
                                to_be_reloaded_ >>

EndWait(self) == /\ pc[self] = "EndWait"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << delta_list, wait_set, running, waiting, name_, 
                                 name, idx, delta, runnable, task, head, 
                                 to_be_reloaded, head_, to_be_reloaded_ >>

wait(self) == BeginWait(self) \/ NotifyTimer(self) \/ Notify(self)
                 \/ EndWait(self)

fire_event(self) == /\ pc[self] = "fire_event"
                    /\ wait_set' = (wait_set \union {self})
                    /\ pc' = [pc EXCEPT ![self] = "fire_event"]
                    /\ UNCHANGED << delta_list, running, waiting, stack, name_, 
                                    name, idx, delta, runnable, task, head, 
                                    to_be_reloaded, head_, to_be_reloaded_ >>

trigger_event(self) == fire_event(self)

BeginExecutor == /\ pc["executor"] = "BeginExecutor"
                 /\ stack' = [stack EXCEPT !["executor"] = << [ procedure |->  "wait",
                                                                pc        |->  "BeginExecutor" ] >>
                                                            \o stack["executor"]]
                 /\ pc' = [pc EXCEPT !["executor"] = "BeginWait"]
                 /\ UNCHANGED << delta_list, wait_set, running, waiting, name_, 
                                 name, idx, delta, runnable, task, head, 
                                 to_be_reloaded, head_, to_be_reloaded_ >>

executor == BeginExecutor

Next == executor
           \/ (\E self \in ProcSet:  \/ callback(self) \/ reload_timer(self)
                                     \/ notify(self) \/ notify_timer(self)
                                     \/ rcl_wait(self) \/ wait_timer(self)
                                     \/ wait(self))
           \/ (\E self \in Tasks: trigger_event(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Tasks : WF_vars(trigger_event(self))
        /\ /\ SF_vars(executor)
           /\ SF_vars(wait("executor"))
           /\ SF_vars(callback("executor"))
           /\ SF_vars(reload_timer("executor"))
           /\ SF_vars(notify("executor"))
           /\ SF_vars(notify_timer("executor"))
           /\ SF_vars(rcl_wait("executor"))
           /\ SF_vars(wait_timer("executor"))

\* END TRANSLATION
====

