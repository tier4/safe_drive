---- MODULE callback ----
EXTENDS TLC, Sequences, SequencesExt, FiniteSets, Integers

CONSTANTS Timers, DeltaRange, Servers, Clients, Subscribers

Tasks == Subscribers \union Servers \union Clients

(* --algorithm callback
variables
    \* list for timer
    \* example: <<[delta |-> 3, name |-> "timer1"], [delta |-> 2, name |-> "timer2"]>>
    delta_list = SetToSeq({[delta |-> random_num(0, DeltaRange), name |-> x]: x \in Timers});

    \* events
    runnable = {};

    \* tasks
    running = {};
    waiting = Tasks;

define
    random_num(min, max) == CHOOSE i \in min..max: TRUE
    starvation_free == \A x \in (Timers \union Tasks):
        (((x \in {y.name: y \in ToSet(delta_list)}) \/ (x \in runnable)) ~> <>(x \in running))
    pick_task(set) == CHOOSE x \in set: TRUE
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
    start_callback:
        increment_clock();
        running := running \union { name };

    end_callback:
        running := running \ { name };
        return;
end procedure;

\* reenable timer with at random delay
procedure reload_timer(name)
variables
    idx;
    delta;
begin
    start_reload_timer:
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

    end_reload_timer:
        return;
end procedure;

\* execute a task
procedure execute_task(wait_set)
variables
    task;
begin
    start_task:
        while wait_set /= {} do
            task := pick_task(wait_set);
            wait_set := wait_set \ {task};
            call callback(task);

            finish_a_task:
                waiting := waiting \union {task};
        end while;

        return;
end procedure;

fair process trigger_event \in Tasks
begin
    fire_event:
        while TRUE do
            if self \in waiting then
                runnable := runnable \union {self};
                waiting := waiting \ {self};
            end if;
        end while;
end process;

fair+ process executor = "executor"
variables
    head;
    to_be_reloaded = <<>>;
begin
    start_executor:
        while TRUE do
            increment_clock();

            execute:
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

            reload:
                \* reenable timer
                while to_be_reloaded /= <<>> do
                    call reload_timer(to_be_reloaded[1]);

                    reload2:
                        to_be_reloaded := Tail(to_be_reloaded);
                end while;

            execute_tasks:
                \* pick runnable tasks up
                with tmp_runnable = runnable do
                    runnable := {};
                    call execute_task(tmp_runnable);
                end with;

        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3e628361" /\ chksum(tla) = "d2603b82")
\* Parameter name of procedure callback at line 37 col 20 changed to name_
CONSTANT defaultInitValue
VARIABLES delta_list, runnable, running, waiting, pc, stack

(* define statement *)
random_num(min, max) == CHOOSE i \in min..max: TRUE
starvation_free == \A x \in (Timers \union Tasks):
    (((x \in {y.name: y \in ToSet(delta_list)}) \/ (x \in runnable)) ~> <>(x \in running))
pick_task(set) == CHOOSE x \in set: TRUE

VARIABLES name_, name, idx, delta, wait_set, task, head, to_be_reloaded

vars == << delta_list, runnable, running, waiting, pc, stack, name_, name, 
           idx, delta, wait_set, task, head, to_be_reloaded >>

ProcSet == (Tasks) \cup {"executor"}

Init == (* Global variables *)
        /\ delta_list = SetToSeq({[delta |-> random_num(0, DeltaRange), name |-> x]: x \in Timers})
        /\ runnable = {}
        /\ running = {}
        /\ waiting = Tasks
        (* Procedure callback *)
        /\ name_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure reload_timer *)
        /\ name = [ self \in ProcSet |-> defaultInitValue]
        /\ idx = [ self \in ProcSet |-> defaultInitValue]
        /\ delta = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure execute_task *)
        /\ wait_set = [ self \in ProcSet |-> defaultInitValue]
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        (* Process executor *)
        /\ head = defaultInitValue
        /\ to_be_reloaded = <<>>
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Tasks -> "fire_event"
                                        [] self = "executor" -> "start_executor"]

start_callback(self) == /\ pc[self] = "start_callback"
                        /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0
                              THEN /\ delta_list' = [delta_list EXCEPT ![1].delta = delta_list[1].delta - 1]
                              ELSE /\ TRUE
                                   /\ UNCHANGED delta_list
                        /\ running' = (running \union { name_[self] })
                        /\ pc' = [pc EXCEPT ![self] = "end_callback"]
                        /\ UNCHANGED << runnable, waiting, stack, name_, name, 
                                        idx, delta, wait_set, task, head, 
                                        to_be_reloaded >>

end_callback(self) == /\ pc[self] = "end_callback"
                      /\ running' = running \ { name_[self] }
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ name_' = [name_ EXCEPT ![self] = Head(stack[self]).name_]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << delta_list, runnable, waiting, name, idx, 
                                      delta, wait_set, task, head, 
                                      to_be_reloaded >>

callback(self) == start_callback(self) \/ end_callback(self)

start_reload_timer(self) == /\ pc[self] = "start_reload_timer"
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
                            /\ UNCHANGED << runnable, running, waiting, stack, 
                                            name_, name, wait_set, task, head, 
                                            to_be_reloaded >>

reload_insert1(self) == /\ pc[self] = "reload_insert1"
                        /\ delta_list' = [delta_list EXCEPT ![idx[self]].delta = delta_list[idx[self]].delta - delta[self]]
                        /\ pc' = [pc EXCEPT ![self] = "reload_insert2"]
                        /\ UNCHANGED << runnable, running, waiting, stack, 
                                        name_, name, idx, delta, wait_set, 
                                        task, head, to_be_reloaded >>

reload_insert2(self) == /\ pc[self] = "reload_insert2"
                        /\ delta_list' = InsertAt(delta_list, idx[self], [delta |-> delta[self], name |-> name[self]])
                        /\ pc' = [pc EXCEPT ![self] = "end_reload_timer"]
                        /\ UNCHANGED << runnable, running, waiting, stack, 
                                        name_, name, idx, delta, wait_set, 
                                        task, head, to_be_reloaded >>

reload_insert_end(self) == /\ pc[self] = "reload_insert_end"
                           /\ delta_list' = Append(delta_list, [delta |-> delta[self], name |-> name[self]])
                           /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "end_reload_timer"]
                           /\ UNCHANGED << runnable, running, waiting, stack, 
                                           name_, name, idx, delta, wait_set, 
                                           task, head, to_be_reloaded >>

end_reload_timer(self) == /\ pc[self] = "end_reload_timer"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ idx' = [idx EXCEPT ![self] = Head(stack[self]).idx]
                          /\ delta' = [delta EXCEPT ![self] = Head(stack[self]).delta]
                          /\ name' = [name EXCEPT ![self] = Head(stack[self]).name]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << delta_list, runnable, running, 
                                          waiting, name_, wait_set, task, head, 
                                          to_be_reloaded >>

reload_timer(self) == start_reload_timer(self) \/ reload_insert1(self)
                         \/ reload_insert2(self) \/ reload_insert_end(self)
                         \/ end_reload_timer(self)

start_task(self) == /\ pc[self] = "start_task"
                    /\ IF wait_set[self] /= {}
                          THEN /\ task' = [task EXCEPT ![self] = pick_task(wait_set[self])]
                               /\ wait_set' = [wait_set EXCEPT ![self] = wait_set[self] \ {task'[self]}]
                               /\ /\ name_' = [name_ EXCEPT ![self] = task'[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "callback",
                                                                           pc        |->  "finish_a_task",
                                                                           name_     |->  name_[self] ] >>
                                                                       \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "start_callback"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                               /\ wait_set' = [wait_set EXCEPT ![self] = Head(stack[self]).wait_set]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ name_' = name_
                    /\ UNCHANGED << delta_list, runnable, running, waiting, 
                                    name, idx, delta, head, to_be_reloaded >>

finish_a_task(self) == /\ pc[self] = "finish_a_task"
                       /\ waiting' = (waiting \union {task[self]})
                       /\ pc' = [pc EXCEPT ![self] = "start_task"]
                       /\ UNCHANGED << delta_list, runnable, running, stack, 
                                       name_, name, idx, delta, wait_set, task, 
                                       head, to_be_reloaded >>

execute_task(self) == start_task(self) \/ finish_a_task(self)

fire_event(self) == /\ pc[self] = "fire_event"
                    /\ IF self \in waiting
                          THEN /\ runnable' = (runnable \union {self})
                               /\ waiting' = waiting \ {self}
                          ELSE /\ TRUE
                               /\ UNCHANGED << runnable, waiting >>
                    /\ pc' = [pc EXCEPT ![self] = "fire_event"]
                    /\ UNCHANGED << delta_list, running, stack, name_, name, 
                                    idx, delta, wait_set, task, head, 
                                    to_be_reloaded >>

trigger_event(self) == fire_event(self)

start_executor == /\ pc["executor"] = "start_executor"
                  /\ IF delta_list /= <<>> /\ delta_list[1].delta > 0
                        THEN /\ delta_list' = [delta_list EXCEPT ![1].delta = delta_list[1].delta - 1]
                        ELSE /\ TRUE
                             /\ UNCHANGED delta_list
                  /\ pc' = [pc EXCEPT !["executor"] = "execute"]
                  /\ UNCHANGED << runnable, running, waiting, stack, name_, 
                                  name, idx, delta, wait_set, task, head, 
                                  to_be_reloaded >>

execute == /\ pc["executor"] = "execute"
           /\ IF delta_list /= <<>> /\ delta_list[1].delta = 0
                 THEN /\ head' = Head(delta_list)
                      /\ delta_list' = Tail(delta_list)
                      /\ /\ name_' = [name_ EXCEPT !["executor"] = head'.name]
                         /\ stack' = [stack EXCEPT !["executor"] = << [ procedure |->  "callback",
                                                                        pc        |->  "save_timer",
                                                                        name_     |->  name_["executor"] ] >>
                                                                    \o stack["executor"]]
                      /\ pc' = [pc EXCEPT !["executor"] = "start_callback"]
                 ELSE /\ pc' = [pc EXCEPT !["executor"] = "reload"]
                      /\ UNCHANGED << delta_list, stack, name_, head >>
           /\ UNCHANGED << runnable, running, waiting, name, idx, delta, 
                           wait_set, task, to_be_reloaded >>

save_timer == /\ pc["executor"] = "save_timer"
              /\ to_be_reloaded' = Append(to_be_reloaded, head.name)
              /\ pc' = [pc EXCEPT !["executor"] = "execute"]
              /\ UNCHANGED << delta_list, runnable, running, waiting, stack, 
                              name_, name, idx, delta, wait_set, task, head >>

reload == /\ pc["executor"] = "reload"
          /\ IF to_be_reloaded /= <<>>
                THEN /\ /\ name' = [name EXCEPT !["executor"] = to_be_reloaded[1]]
                        /\ stack' = [stack EXCEPT !["executor"] = << [ procedure |->  "reload_timer",
                                                                       pc        |->  "reload2",
                                                                       idx       |->  idx["executor"],
                                                                       delta     |->  delta["executor"],
                                                                       name      |->  name["executor"] ] >>
                                                                   \o stack["executor"]]
                     /\ idx' = [idx EXCEPT !["executor"] = defaultInitValue]
                     /\ delta' = [delta EXCEPT !["executor"] = defaultInitValue]
                     /\ pc' = [pc EXCEPT !["executor"] = "start_reload_timer"]
                ELSE /\ pc' = [pc EXCEPT !["executor"] = "execute_tasks"]
                     /\ UNCHANGED << stack, name, idx, delta >>
          /\ UNCHANGED << delta_list, runnable, running, waiting, name_, 
                          wait_set, task, head, to_be_reloaded >>

reload2 == /\ pc["executor"] = "reload2"
           /\ to_be_reloaded' = Tail(to_be_reloaded)
           /\ pc' = [pc EXCEPT !["executor"] = "reload"]
           /\ UNCHANGED << delta_list, runnable, running, waiting, stack, 
                           name_, name, idx, delta, wait_set, task, head >>

execute_tasks == /\ pc["executor"] = "execute_tasks"
                 /\ LET tmp_runnable == runnable IN
                      /\ runnable' = {}
                      /\ /\ stack' = [stack EXCEPT !["executor"] = << [ procedure |->  "execute_task",
                                                                        pc        |->  "start_executor",
                                                                        task      |->  task["executor"],
                                                                        wait_set  |->  wait_set["executor"] ] >>
                                                                    \o stack["executor"]]
                         /\ wait_set' = [wait_set EXCEPT !["executor"] = tmp_runnable]
                      /\ task' = [task EXCEPT !["executor"] = defaultInitValue]
                      /\ pc' = [pc EXCEPT !["executor"] = "start_task"]
                 /\ UNCHANGED << delta_list, running, waiting, name_, name, 
                                 idx, delta, head, to_be_reloaded >>

executor == start_executor \/ execute \/ save_timer \/ reload \/ reload2
               \/ execute_tasks

Next == executor
           \/ (\E self \in ProcSet:  \/ callback(self) \/ reload_timer(self)
                                     \/ execute_task(self))
           \/ (\E self \in Tasks: trigger_event(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Tasks : WF_vars(trigger_event(self))
        /\ /\ SF_vars(executor)
           /\ SF_vars(callback("executor"))
           /\ SF_vars(reload_timer("executor"))
           /\ SF_vars(execute_task("executor"))

\* END TRANSLATION
====

