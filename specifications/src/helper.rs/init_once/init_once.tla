---- MODULE init_once ----
EXTENDS TLC, FiniteSets, Integers

CONSTANTS Processes

(* --algorithm init_once
variables
    lock = FALSE;
    is_init = FALSE;

    pids = {};

define
    just_once == <>[](Cardinality(pids) = 1) /\ [](Cardinality(pids) <= 1)
end define

\* initializer
fair+ process pid \in Processes
begin
    BeginInitOnce:
        while ~is_init do
            LoadLockRelaxed:
                if ~lock then
                    CompareExchange:
                        if ~lock then
                            lock := TRUE;
                            pids := pids \union {self};

                            Initialize:
                                skip;

                            StoreIsInit:
                                is_init := TRUE;
                        end if;
                end if;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "171ee2b4" /\ chksum(tla) = "1cd14bb5")
VARIABLES lock, is_init, pids, pc

(* define statement *)
just_once == <>[](Cardinality(pids) = 1) /\ [](Cardinality(pids) <= 1)


vars == << lock, is_init, pids, pc >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ lock = FALSE
        /\ is_init = FALSE
        /\ pids = {}
        /\ pc = [self \in ProcSet |-> "BeginInitOnce"]

BeginInitOnce(self) == /\ pc[self] = "BeginInitOnce"
                       /\ IF ~is_init
                             THEN /\ pc' = [pc EXCEPT ![self] = "LoadLockRelaxed"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << lock, is_init, pids >>

LoadLockRelaxed(self) == /\ pc[self] = "LoadLockRelaxed"
                         /\ IF ~lock
                               THEN /\ pc' = [pc EXCEPT ![self] = "CompareExchange"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "BeginInitOnce"]
                         /\ UNCHANGED << lock, is_init, pids >>

CompareExchange(self) == /\ pc[self] = "CompareExchange"
                         /\ IF ~lock
                               THEN /\ lock' = TRUE
                                    /\ pids' = (pids \union {self})
                                    /\ pc' = [pc EXCEPT ![self] = "Initialize"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "BeginInitOnce"]
                                    /\ UNCHANGED << lock, pids >>
                         /\ UNCHANGED is_init

Initialize(self) == /\ pc[self] = "Initialize"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "StoreIsInit"]
                    /\ UNCHANGED << lock, is_init, pids >>

StoreIsInit(self) == /\ pc[self] = "StoreIsInit"
                     /\ is_init' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "BeginInitOnce"]
                     /\ UNCHANGED << lock, pids >>

pid(self) == BeginInitOnce(self) \/ LoadLockRelaxed(self)
                \/ CompareExchange(self) \/ Initialize(self)
                \/ StoreIsInit(self)

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
