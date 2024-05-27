---- MODULE scci_p1 ----
EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

\* model values
\* ---------------
CONSTANTS NULL

\* constants
\* ---------------
MESSAGES == {"m1", "m2", "m3"}

\* types
\* ---------------
LogType == [diff: BOOLEAN, ctime: Nat, msg: MESSAGES]
DataType == [mtime: Nat]

\* utilities
SeqOf(set, count) == [1..count -> set]

(*--algorithm scci_p1
    variables 
        data = [mtime |-> 0],
        \* Use set to simulate out-of-order messages (e.g. retry)
        \* For simplicity, we assume that kafka is partitioned by key already
        msg_queue = {},
        msg_to_send = <<"m1", "m2", "m3">>,

        \* ghost variables
        \* ---------------
        consumed_msg = <<>>,
        \* set of LogType
        compare_and_update_log = {};

    define
        \* safety
        \* ---------------
        \* Older data can never overwrite newer data
        Integrity == \A log \in compare_and_update_log : ~log.diff \/ (log.ctime <= data.mtime)

        \* liveness
        \* ---------------
        \* Assuming API call & producing msg are atomic, when API is called, eventually C&U will run
        Progress == <>(\A msg \in MESSAGES : (\E log \in compare_and_update_log : log.msg = msg))
        \* If Compare shows diff, data is eventually updated to newer
        Validity == <>(\A log \in compare_and_update_log : log.diff => (log.ctime <= data.mtime))

    end define;

    fair process producer = "producer"
    begin
        ActionProducerPreCheck:
            if Len(msg_to_send) = 0 then
                goto ActionProducerDone;
            end if;
        
        ActionProducerLoop:
            \* TODO: add failure case
            msg_queue := msg_queue \union {Head(msg_to_send)};
            msg_to_send := Tail(msg_to_send);
        
        ActionProducerNextStep:
            goto ActionProducerPreCheck;
        
        ActionProducerDone:
            skip;
    end process;

    fair process consumer = "consumer"
    variable
        clock = 1,
        cur_msg = "no message",
        log = [diff |-> FALSE, ctime |-> 0, msg |-> "no message"]; \* LogType
    begin
        ActionConsumerWait:
            await Cardinality(msg_queue) > 0;

        \* TODO: add failure case
        ActionConsumeMsg:
            cur_msg := CHOOSE m \in msg_queue: TRUE;
            log := [diff |-> FALSE, ctime |-> clock, msg |-> cur_msg];
            clock := clock + 1;
        
        ActionCompare:
            \* TODO: add fail case
            either
                log.diff := FALSE;
            or
                log.diff := TRUE;
            end either;
            clock := clock + 1;
        
        ActionUpdate:
            \* TODO: add fail case
            \* TODO: add DB process
            if log.diff then
                data.mtime := clock;
            end if;
            clock := clock + 1;
        
        ActionMsgDone:
            consumed_msg := Append(consumed_msg, cur_msg);
            msg_queue := msg_queue \ {cur_msg};
            clock := clock + 1;
            compare_and_update_log := compare_and_update_log \union {log};
        
        ActionConsumerNextStep:
            goto ActionConsumerWait;
    end process; 

    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e3c256f8" /\ chksum(tla) = "25e1e58d")
VARIABLES data, msg_queue, msg_to_send, consumed_msg, compare_and_update_log, 
          pc

(* define statement *)
Integrity == \A log \in compare_and_update_log : ~log.diff \/ (log.ctime <= data.mtime)




Progress == <>(\A msg \in MESSAGES : (\E log \in compare_and_update_log : log.msg = msg))

Validity == <>(\A log \in compare_and_update_log : log.diff => (log.ctime <= data.mtime))

VARIABLES clock, cur_msg, log

vars == << data, msg_queue, msg_to_send, consumed_msg, compare_and_update_log, 
           pc, clock, cur_msg, log >>

ProcSet == {"producer"} \cup {"consumer"}

Init == (* Global variables *)
        /\ data = [mtime |-> 0]
        /\ msg_queue = {}
        /\ msg_to_send = <<"m1", "m2", "m3">>
        /\ consumed_msg = <<>>
        /\ compare_and_update_log = {}
        (* Process consumer *)
        /\ clock = 1
        /\ cur_msg = "no message"
        /\ log = [diff |-> FALSE, ctime |-> 0, msg |-> "no message"]
        /\ pc = [self \in ProcSet |-> CASE self = "producer" -> "ActionProducerPreCheck"
                                        [] self = "consumer" -> "ActionConsumerWait"]

ActionProducerPreCheck == /\ pc["producer"] = "ActionProducerPreCheck"
                          /\ IF Len(msg_to_send) = 0
                                THEN /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerDone"]
                                ELSE /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerLoop"]
                          /\ UNCHANGED << data, msg_queue, msg_to_send, 
                                          consumed_msg, compare_and_update_log, 
                                          clock, cur_msg, log >>

ActionProducerLoop == /\ pc["producer"] = "ActionProducerLoop"
                      /\ msg_queue' = (msg_queue \union {Head(msg_to_send)})
                      /\ msg_to_send' = Tail(msg_to_send)
                      /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerNextStep"]
                      /\ UNCHANGED << data, consumed_msg, 
                                      compare_and_update_log, clock, cur_msg, 
                                      log >>

ActionProducerNextStep == /\ pc["producer"] = "ActionProducerNextStep"
                          /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerPreCheck"]
                          /\ UNCHANGED << data, msg_queue, msg_to_send, 
                                          consumed_msg, compare_and_update_log, 
                                          clock, cur_msg, log >>

ActionProducerDone == /\ pc["producer"] = "ActionProducerDone"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT !["producer"] = "Done"]
                      /\ UNCHANGED << data, msg_queue, msg_to_send, 
                                      consumed_msg, compare_and_update_log, 
                                      clock, cur_msg, log >>

producer == ActionProducerPreCheck \/ ActionProducerLoop
               \/ ActionProducerNextStep \/ ActionProducerDone

ActionConsumerWait == /\ pc["consumer"] = "ActionConsumerWait"
                      /\ Cardinality(msg_queue) > 0
                      /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumeMsg"]
                      /\ UNCHANGED << data, msg_queue, msg_to_send, 
                                      consumed_msg, compare_and_update_log, 
                                      clock, cur_msg, log >>

ActionConsumeMsg == /\ pc["consumer"] = "ActionConsumeMsg"
                    /\ cur_msg' = (CHOOSE m \in msg_queue: TRUE)
                    /\ log' = [diff |-> FALSE, ctime |-> clock, msg |-> cur_msg']
                    /\ clock' = clock + 1
                    /\ pc' = [pc EXCEPT !["consumer"] = "ActionCompare"]
                    /\ UNCHANGED << data, msg_queue, msg_to_send, consumed_msg, 
                                    compare_and_update_log >>

ActionCompare == /\ pc["consumer"] = "ActionCompare"
                 /\ \/ /\ log' = [log EXCEPT !.diff = FALSE]
                    \/ /\ log' = [log EXCEPT !.diff = TRUE]
                 /\ clock' = clock + 1
                 /\ pc' = [pc EXCEPT !["consumer"] = "ActionUpdate"]
                 /\ UNCHANGED << data, msg_queue, msg_to_send, consumed_msg, 
                                 compare_and_update_log, cur_msg >>

ActionUpdate == /\ pc["consumer"] = "ActionUpdate"
                /\ IF log.diff
                      THEN /\ data' = [data EXCEPT !.mtime = clock]
                      ELSE /\ TRUE
                           /\ data' = data
                /\ clock' = clock + 1
                /\ pc' = [pc EXCEPT !["consumer"] = "ActionMsgDone"]
                /\ UNCHANGED << msg_queue, msg_to_send, consumed_msg, 
                                compare_and_update_log, cur_msg, log >>

ActionMsgDone == /\ pc["consumer"] = "ActionMsgDone"
                 /\ consumed_msg' = Append(consumed_msg, cur_msg)
                 /\ msg_queue' = msg_queue \ {cur_msg}
                 /\ clock' = clock + 1
                 /\ compare_and_update_log' = (compare_and_update_log \union {log})
                 /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerNextStep"]
                 /\ UNCHANGED << data, msg_to_send, cur_msg, log >>

ActionConsumerNextStep == /\ pc["consumer"] = "ActionConsumerNextStep"
                          /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerWait"]
                          /\ UNCHANGED << data, msg_queue, msg_to_send, 
                                          consumed_msg, compare_and_update_log, 
                                          clock, cur_msg, log >>

consumer == ActionConsumerWait \/ ActionConsumeMsg \/ ActionCompare
               \/ ActionUpdate \/ ActionMsgDone \/ ActionConsumerNextStep

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == producer \/ consumer
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(producer)
        /\ WF_vars(consumer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
