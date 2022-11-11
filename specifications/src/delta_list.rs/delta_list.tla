---- MODULE delta_list ----
EXTENDS TLC, FiniteSets, Sequences, Integers

(* --algorithm delta_list
variables
    delta_list = nil,

    result_insert_delta = nil,

    result_seq_to_delta = <<>>,
    result_delta_list_to_seq = <<>>;

define
    nil == << "DelaList::Nil", <<>> >>
    cons(delta, data, next) == << "DelaList::Cons", <<delta, data, next>> >>

    eventually_equal == <>(result_seq_to_delta = result_delta_list_to_seq)

    rand == CHOOSE i \in 0..100: TRUE
    durations == << rand, rand, rand >>
end define

procedure test()
variables
    d = durations,
    sorted = SortSeq(d, <);
begin
    BeginTest:
        while d /= <<>> do
            call insert(Head(d), Head(d));
            GetTail:
                d := Tail(d);
        end while;

    GetDelta:
        call seq_to_delta(sorted);

    GetSeqOfDeltaList:
        call delta_list_to_seq();

    EndTest:
        return;
end procedure;

procedure seq_to_delta(s)
variables
    prev = 0,
    current = 0,
    result = <<>>;
begin
    BeginSeqToDelta:
        while s /= <<>> do
            current := Head(s);
            result := result \o <<prev - current>>;
            prev := current;
            s := Tail(s);
        end while;

    EndSeqToDelta:
        result_seq_to_delta := result;
        return;
end procedure;

procedure delta_list_to_seq()
variables
    list = delta_list,
    result = <<>>;
begin
    DeltaListToSeq:
        while list[1] /= "DelaList::Nil" do
            result := result \o <<list[2][1]>>;
            list := list[2][3];
        end while;

    EndDeltaListToSeq:
        result_delta_list_to_seq := result;
        return;
end procedure;

\* crate::delta_list::DeltaList::insert
procedure insert(delta, data) begin
    BeginInsert:
        call insert_delta(delta_list, delta, data);
    EndInsert:
        delta_list := result_insert_delta;
        return;
end procedure;

\* crate::delta_list::insert_delta
procedure insert_delta(list, delta, data)
variables
    front = <<>>,
    d_mut = 0;
begin
    BeginInsertDelta:
        if list[1] = "DelaList::Nil" then
            list := cons(delta, data, nil);
        elsif list[1] = "DelaList::Cons" then
            front := list[2];
            d_mut := front[1];

            if delta < d_mut then
                with next = cons(d_mut - delta, front[2], front[3]) do
                    list := cons(delta, data, next);
                end with;
            else
                CallRecursive:
                    call insert_delta(front[3], delta - d_mut, data);

                UpdateList:
                    list := cons(d_mut, front[2], result_insert_delta);
            end if;
        end if;

    EndInsertDelta:
        result_insert_delta := list;
        return;
end procedure;

begin
    BeginAlgorithm:
        call test();

    EndAlgorithm:
        \* assert(FALSE)
        skip
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "972a10cb" /\ chksum(tla) = "57346188")
\* Procedure variable result of procedure seq_to_delta at line 49 col 5 changed to result_
\* Procedure variable list of procedure delta_list_to_seq at line 66 col 5 changed to list_
\* Parameter delta of procedure insert at line 81 col 18 changed to delta_
\* Parameter data of procedure insert at line 81 col 25 changed to data_
CONSTANT defaultInitValue
VARIABLES delta_list, result_insert_delta, result_seq_to_delta, 
          result_delta_list_to_seq, pc, stack

(* define statement *)
nil == << "DelaList::Nil", <<>> >>
cons(delta, data, next) == << "DelaList::Cons", <<delta, data, next>> >>

eventually_equal == <>(result_seq_to_delta = result_delta_list_to_seq)

rand == CHOOSE i \in 0..100: TRUE
durations == << rand, rand, rand >>

VARIABLES d, sorted, s, prev, current, result_, list_, result, delta_, data_, 
          list, delta, data, front, d_mut

vars == << delta_list, result_insert_delta, result_seq_to_delta, 
           result_delta_list_to_seq, pc, stack, d, sorted, s, prev, current, 
           result_, list_, result, delta_, data_, list, delta, data, front, 
           d_mut >>

Init == (* Global variables *)
        /\ delta_list = nil
        /\ result_insert_delta = nil
        /\ result_seq_to_delta = <<>>
        /\ result_delta_list_to_seq = <<>>
        (* Procedure test *)
        /\ d = durations
        /\ sorted = SortSeq(d, <)
        (* Procedure seq_to_delta *)
        /\ s = defaultInitValue
        /\ prev = 0
        /\ current = 0
        /\ result_ = <<>>
        (* Procedure delta_list_to_seq *)
        /\ list_ = delta_list
        /\ result = <<>>
        (* Procedure insert *)
        /\ delta_ = defaultInitValue
        /\ data_ = defaultInitValue
        (* Procedure insert_delta *)
        /\ list = defaultInitValue
        /\ delta = defaultInitValue
        /\ data = defaultInitValue
        /\ front = <<>>
        /\ d_mut = 0
        /\ stack = << >>
        /\ pc = "BeginAlgorithm"

BeginTest == /\ pc = "BeginTest"
             /\ IF d /= <<>>
                   THEN /\ /\ data_' = Head(d)
                           /\ delta_' = Head(d)
                           /\ stack' = << [ procedure |->  "insert",
                                            pc        |->  "GetTail",
                                            delta_    |->  delta_,
                                            data_     |->  data_ ] >>
                                        \o stack
                        /\ pc' = "BeginInsert"
                   ELSE /\ pc' = "GetDelta"
                        /\ UNCHANGED << stack, delta_, data_ >>
             /\ UNCHANGED << delta_list, result_insert_delta, 
                             result_seq_to_delta, result_delta_list_to_seq, d, 
                             sorted, s, prev, current, result_, list_, result, 
                             list, delta, data, front, d_mut >>

GetTail == /\ pc = "GetTail"
           /\ d' = Tail(d)
           /\ pc' = "BeginTest"
           /\ UNCHANGED << delta_list, result_insert_delta, 
                           result_seq_to_delta, result_delta_list_to_seq, 
                           stack, sorted, s, prev, current, result_, list_, 
                           result, delta_, data_, list, delta, data, front, 
                           d_mut >>

GetDelta == /\ pc = "GetDelta"
            /\ /\ s' = sorted
               /\ stack' = << [ procedure |->  "seq_to_delta",
                                pc        |->  "GetSeqOfDeltaList",
                                prev      |->  prev,
                                current   |->  current,
                                result_   |->  result_,
                                s         |->  s ] >>
                            \o stack
            /\ prev' = 0
            /\ current' = 0
            /\ result_' = <<>>
            /\ pc' = "BeginSeqToDelta"
            /\ UNCHANGED << delta_list, result_insert_delta, 
                            result_seq_to_delta, result_delta_list_to_seq, d, 
                            sorted, list_, result, delta_, data_, list, delta, 
                            data, front, d_mut >>

GetSeqOfDeltaList == /\ pc = "GetSeqOfDeltaList"
                     /\ stack' = << [ procedure |->  "delta_list_to_seq",
                                      pc        |->  "EndTest",
                                      list_     |->  list_,
                                      result    |->  result ] >>
                                  \o stack
                     /\ list_' = delta_list
                     /\ result' = <<>>
                     /\ pc' = "DeltaListToSeq"
                     /\ UNCHANGED << delta_list, result_insert_delta, 
                                     result_seq_to_delta, 
                                     result_delta_list_to_seq, d, sorted, s, 
                                     prev, current, result_, delta_, data_, 
                                     list, delta, data, front, d_mut >>

EndTest == /\ pc = "EndTest"
           /\ pc' = Head(stack).pc
           /\ d' = Head(stack).d
           /\ sorted' = Head(stack).sorted
           /\ stack' = Tail(stack)
           /\ UNCHANGED << delta_list, result_insert_delta, 
                           result_seq_to_delta, result_delta_list_to_seq, s, 
                           prev, current, result_, list_, result, delta_, 
                           data_, list, delta, data, front, d_mut >>

test == BeginTest \/ GetTail \/ GetDelta \/ GetSeqOfDeltaList \/ EndTest

BeginSeqToDelta == /\ pc = "BeginSeqToDelta"
                   /\ IF s /= <<>>
                         THEN /\ current' = Head(s)
                              /\ result_' = result_ \o <<prev - current'>>
                              /\ prev' = current'
                              /\ s' = Tail(s)
                              /\ pc' = "BeginSeqToDelta"
                         ELSE /\ pc' = "EndSeqToDelta"
                              /\ UNCHANGED << s, prev, current, result_ >>
                   /\ UNCHANGED << delta_list, result_insert_delta, 
                                   result_seq_to_delta, 
                                   result_delta_list_to_seq, stack, d, sorted, 
                                   list_, result, delta_, data_, list, delta, 
                                   data, front, d_mut >>

EndSeqToDelta == /\ pc = "EndSeqToDelta"
                 /\ result_seq_to_delta' = result_
                 /\ pc' = Head(stack).pc
                 /\ prev' = Head(stack).prev
                 /\ current' = Head(stack).current
                 /\ result_' = Head(stack).result_
                 /\ s' = Head(stack).s
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << delta_list, result_insert_delta, 
                                 result_delta_list_to_seq, d, sorted, list_, 
                                 result, delta_, data_, list, delta, data, 
                                 front, d_mut >>

seq_to_delta == BeginSeqToDelta \/ EndSeqToDelta

DeltaListToSeq == /\ pc = "DeltaListToSeq"
                  /\ IF list_[1] /= "DelaList::Nil"
                        THEN /\ result' = result \o <<list_[2][1]>>
                             /\ list_' = list_[2][3]
                             /\ pc' = "DeltaListToSeq"
                        ELSE /\ pc' = "EndDeltaListToSeq"
                             /\ UNCHANGED << list_, result >>
                  /\ UNCHANGED << delta_list, result_insert_delta, 
                                  result_seq_to_delta, 
                                  result_delta_list_to_seq, stack, d, sorted, 
                                  s, prev, current, result_, delta_, data_, 
                                  list, delta, data, front, d_mut >>

EndDeltaListToSeq == /\ pc = "EndDeltaListToSeq"
                     /\ result_delta_list_to_seq' = result
                     /\ pc' = Head(stack).pc
                     /\ list_' = Head(stack).list_
                     /\ result' = Head(stack).result
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED << delta_list, result_insert_delta, 
                                     result_seq_to_delta, d, sorted, s, prev, 
                                     current, result_, delta_, data_, list, 
                                     delta, data, front, d_mut >>

delta_list_to_seq == DeltaListToSeq \/ EndDeltaListToSeq

BeginInsert == /\ pc = "BeginInsert"
               /\ /\ data' = data_
                  /\ delta' = delta_
                  /\ list' = delta_list
                  /\ stack' = << [ procedure |->  "insert_delta",
                                   pc        |->  "EndInsert",
                                   front     |->  front,
                                   d_mut     |->  d_mut,
                                   list      |->  list,
                                   delta     |->  delta,
                                   data      |->  data ] >>
                               \o stack
               /\ front' = <<>>
               /\ d_mut' = 0
               /\ pc' = "BeginInsertDelta"
               /\ UNCHANGED << delta_list, result_insert_delta, 
                               result_seq_to_delta, result_delta_list_to_seq, 
                               d, sorted, s, prev, current, result_, list_, 
                               result, delta_, data_ >>

EndInsert == /\ pc = "EndInsert"
             /\ delta_list' = result_insert_delta
             /\ pc' = Head(stack).pc
             /\ delta_' = Head(stack).delta_
             /\ data_' = Head(stack).data_
             /\ stack' = Tail(stack)
             /\ UNCHANGED << result_insert_delta, result_seq_to_delta, 
                             result_delta_list_to_seq, d, sorted, s, prev, 
                             current, result_, list_, result, list, delta, 
                             data, front, d_mut >>

insert == BeginInsert \/ EndInsert

BeginInsertDelta == /\ pc = "BeginInsertDelta"
                    /\ IF list[1] = "DelaList::Nil"
                          THEN /\ list' = cons(delta, data, nil)
                               /\ pc' = "EndInsertDelta"
                               /\ UNCHANGED << front, d_mut >>
                          ELSE /\ IF list[1] = "DelaList::Cons"
                                     THEN /\ front' = list[2]
                                          /\ d_mut' = front'[1]
                                          /\ IF delta < d_mut'
                                                THEN /\ LET next == cons(d_mut' - delta, front'[2], front'[3]) IN
                                                          list' = cons(delta, data, next)
                                                     /\ pc' = "EndInsertDelta"
                                                ELSE /\ pc' = "CallRecursive"
                                                     /\ list' = list
                                     ELSE /\ pc' = "EndInsertDelta"
                                          /\ UNCHANGED << list, front, d_mut >>
                    /\ UNCHANGED << delta_list, result_insert_delta, 
                                    result_seq_to_delta, 
                                    result_delta_list_to_seq, stack, d, sorted, 
                                    s, prev, current, result_, list_, result, 
                                    delta_, data_, delta, data >>

CallRecursive == /\ pc = "CallRecursive"
                 /\ /\ data' = data
                    /\ delta' = delta - d_mut
                    /\ list' = front[3]
                    /\ stack' = << [ procedure |->  "insert_delta",
                                     pc        |->  "UpdateList",
                                     front     |->  front,
                                     d_mut     |->  d_mut,
                                     list      |->  list,
                                     delta     |->  delta,
                                     data      |->  data ] >>
                                 \o stack
                 /\ front' = <<>>
                 /\ d_mut' = 0
                 /\ pc' = "BeginInsertDelta"
                 /\ UNCHANGED << delta_list, result_insert_delta, 
                                 result_seq_to_delta, result_delta_list_to_seq, 
                                 d, sorted, s, prev, current, result_, list_, 
                                 result, delta_, data_ >>

UpdateList == /\ pc = "UpdateList"
              /\ list' = cons(d_mut, front[2], result_insert_delta)
              /\ pc' = "EndInsertDelta"
              /\ UNCHANGED << delta_list, result_insert_delta, 
                              result_seq_to_delta, result_delta_list_to_seq, 
                              stack, d, sorted, s, prev, current, result_, 
                              list_, result, delta_, data_, delta, data, front, 
                              d_mut >>

EndInsertDelta == /\ pc = "EndInsertDelta"
                  /\ result_insert_delta' = list
                  /\ pc' = Head(stack).pc
                  /\ front' = Head(stack).front
                  /\ d_mut' = Head(stack).d_mut
                  /\ list' = Head(stack).list
                  /\ delta' = Head(stack).delta
                  /\ data' = Head(stack).data
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << delta_list, result_seq_to_delta, 
                                  result_delta_list_to_seq, d, sorted, s, prev, 
                                  current, result_, list_, result, delta_, 
                                  data_ >>

insert_delta == BeginInsertDelta \/ CallRecursive \/ UpdateList
                   \/ EndInsertDelta

BeginAlgorithm == /\ pc = "BeginAlgorithm"
                  /\ stack' = << [ procedure |->  "test",
                                   pc        |->  "EndAlgorithm",
                                   d         |->  d,
                                   sorted    |->  sorted ] >>
                               \o stack
                  /\ d' = durations
                  /\ sorted' = SortSeq(d', <)
                  /\ pc' = "BeginTest"
                  /\ UNCHANGED << delta_list, result_insert_delta, 
                                  result_seq_to_delta, 
                                  result_delta_list_to_seq, s, prev, current, 
                                  result_, list_, result, delta_, data_, list, 
                                  delta, data, front, d_mut >>

EndAlgorithm == /\ pc = "EndAlgorithm"
                /\ TRUE
                /\ pc' = "Done"
                /\ UNCHANGED << delta_list, result_insert_delta, 
                                result_seq_to_delta, result_delta_list_to_seq, 
                                stack, d, sorted, s, prev, current, result_, 
                                list_, result, delta_, data_, list, delta, 
                                data, front, d_mut >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == test \/ seq_to_delta \/ delta_list_to_seq \/ insert \/ insert_delta
           \/ BeginAlgorithm \/ EndAlgorithm
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
