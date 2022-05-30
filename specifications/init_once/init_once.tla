---- MODULE init_once ----
EXTENDS TLC, FiniteSets, Integers

CONSTANTS Processes

(* --algorithm init_once
variables
    lock = FALSE;
    is_init = FALSE;

    pids = {};

define
    just_once == <>(Cardinality(pids) = 1) /\ [](Cardinality(pids) <= 1)
end define

\* initializer
fair+ process pid \in Processes
begin
    start_init_once:
        while ~is_init do
            load_lock_relaxed:
                if ~lock then
                    compare_exchange:
                        if ~lock then
                            lock := TRUE;
                            pids := pids \union {self};

                            initialize:
                                skip;

                            store_is_init:
                                is_init := TRUE;
                        end if;
                end if;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f8df04e6" /\ chksum(tla) = "153edf40")
VARIABLES lock, is_init, pids, pc

(* define statement *)
just_once == <>(Cardinality(pids) = 1) /\ [](Cardinality(pids) <= 1)


vars == << lock, is_init, pids, pc >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ lock = FALSE
        /\ is_init = FALSE
        /\ pids = {}
        /\ pc = [self \in ProcSet |-> "start_init_once"]

start_init_once(self) == /\ pc[self] = "start_init_once"
                         /\ IF ~is_init
                               THEN /\ pc' = [pc EXCEPT ![self] = "load_lock_relaxed"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << lock, is_init, pids >>

load_lock_relaxed(self) == /\ pc[self] = "load_lock_relaxed"
                           /\ IF ~lock
                                 THEN /\ pc' = [pc EXCEPT ![self] = "compare_exchange"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "start_init_once"]
                           /\ UNCHANGED << lock, is_init, pids >>

compare_exchange(self) == /\ pc[self] = "compare_exchange"
                          /\ IF ~lock
                                THEN /\ lock' = TRUE
                                     /\ pids' = (pids \union {self})
                                     /\ pc' = [pc EXCEPT ![self] = "initialize"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "start_init_once"]
                                     /\ UNCHANGED << lock, pids >>
                          /\ UNCHANGED is_init

initialize(self) == /\ pc[self] = "initialize"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "store_is_init"]
                    /\ UNCHANGED << lock, is_init, pids >>

store_is_init(self) == /\ pc[self] = "store_is_init"
                       /\ is_init' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "start_init_once"]
                       /\ UNCHANGED << lock, pids >>

pid(self) == start_init_once(self) \/ load_lock_relaxed(self)
                \/ compare_exchange(self) \/ initialize(self)
                \/ store_is_init(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : SF_vars(pid(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
