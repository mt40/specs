---- MODULE scci_p1 ----
EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

\* model values
\* ---------------
CONSTANTS NULL

\* constants
\* ---------------
MESSAGE_TYPE == {"m1", "m2", "m3"}
MESSAGES_TO_SEND_COUNT == 3

\* types
\* ---------------
LogType == [diff: BOOLEAN, ctime: Nat, msg: MESSAGE_TYPE]
DataType == [mtime: Nat]

\* utilities
SeqOf(set, count) == [1..count -> set]

(*--algorithm scci_p1
    variables
        \* Pick from possible messages.
        \* Simulate duplicate messages.
        all_messages \in SeqOf(MESSAGE_TYPE, MESSAGES_TO_SEND_COUNT),
        \* our database
        data = [mtime |-> 0],
        \* Use set to simulate out-of-order messages (e.g. retry)
        \* For simplicity, we assume that kafka is partitioned by key already
        msg_queue = {},
        msg_to_send = all_messages,

        \* ghost variables
        \* ---------------
        produced_msg = {},
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
        Progress == <>(\A msg \in produced_msg : (\E log \in compare_and_update_log : log.msg = msg))
        \* If Compare shows diff, data is eventually updated to newer
        Validity == <>(\A log \in compare_and_update_log : log.diff => (log.ctime <= data.mtime))

    end define;

    procedure fail_by_budget(budget=0)
        variables
            internal_budget = budget;
        begin
        MayFail:
            either
                if internal_budget > 0 then
                    internal_budget := internal_budget - 1;
                    goto MayFail;
                else
                    return;
                end if;
            or
                return;
            end either;
    end procedure;

    fair process producer = "producer"
    variables
        failure_budget = 3;
    begin
        ActionProducerPreCheck:
            if Len(msg_to_send) = 0 then
                goto ActionProducerDone;
            end if;
        
        ActionProducerMayFail:
            call fail_by_budget(failure_budget);

        ActionProducerLoop:
            msg_queue := msg_queue \union {Head(msg_to_send)};
            produced_msg := produced_msg \union {Head(msg_to_send)};
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
        
        ActionConsumeMsgMayFail:
            call fail_by_budget(failure_budget);

        ActionConsumeMsg:
            cur_msg := CHOOSE m \in msg_queue: TRUE;
            log := [diff |-> FALSE, ctime |-> clock, msg |-> cur_msg];
            clock := clock + 1;
        
        ActionCompareMayFail:
            call fail_by_budget(failure_budget);

        ActionCompare:
            either
                log.diff := FALSE;
            or
                log.diff := TRUE;
            end either;
            clock := clock + 1;
        
        ActionUpdateMayFail:
            call fail_by_budget(failure_budget);
        
        ActionUpdate:
            if log.diff then
                data.mtime := clock;
            end if;
            clock := clock + 1;
        
        ActionMsgACKMayFail:
            call fail_by_budget(failure_budget);
        
        ActionMsgACK:
            consumed_msg := Append(consumed_msg, cur_msg);
            msg_queue := msg_queue \ {cur_msg};
            clock := clock + 1;
            compare_and_update_log := compare_and_update_log \union {log};
        
        ActionConsumerNextStep:
            goto ActionConsumerWait;
    end process; 

    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5ffe163b" /\ chksum(tla) = "789a10f4")
VARIABLES all_messages, data, msg_queue, msg_to_send, produced_msg, 
          consumed_msg, compare_and_update_log, pc, stack

(* define statement *)
Integrity == \A log \in compare_and_update_log : ~log.diff \/ (log.ctime <= data.mtime)




Progress == <>(\A msg \in produced_msg : (\E log \in compare_and_update_log : log.msg = msg))

Validity == <>(\A log \in compare_and_update_log : log.diff => (log.ctime <= data.mtime))

VARIABLES budget, internal_budget, failure_budget, clock, cur_msg, log

vars == << all_messages, data, msg_queue, msg_to_send, produced_msg, 
           consumed_msg, compare_and_update_log, pc, stack, budget, 
           internal_budget, failure_budget, clock, cur_msg, log >>

ProcSet == {"producer"} \cup {"consumer"}

Init == (* Global variables *)
        /\ all_messages \in SeqOf(MESSAGE_TYPE, MESSAGES_TO_SEND_COUNT)
        /\ data = [mtime |-> 0]
        /\ msg_queue = {}
        /\ msg_to_send = all_messages
        /\ produced_msg = {}
        /\ consumed_msg = <<>>
        /\ compare_and_update_log = {}
        (* Procedure fail_by_budget *)
        /\ budget = [ self \in ProcSet |-> 0]
        /\ internal_budget = [ self \in ProcSet |-> budget[self]]
        (* Process producer *)
        /\ failure_budget = 3
        (* Process consumer *)
        /\ clock = 1
        /\ cur_msg = "no message"
        /\ log = [diff |-> FALSE, ctime |-> 0, msg |-> "no message"]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "producer" -> "ActionProducerPreCheck"
                                        [] self = "consumer" -> "ActionConsumerWait"]

MayFail(self) == /\ pc[self] = "MayFail"
                 /\ \/ /\ IF internal_budget[self] > 0
                             THEN /\ internal_budget' = [internal_budget EXCEPT ![self] = internal_budget[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "MayFail"]
                                  /\ UNCHANGED << stack, budget >>
                             ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ internal_budget' = [internal_budget EXCEPT ![self] = Head(stack[self]).internal_budget]
                                  /\ budget' = [budget EXCEPT ![self] = Head(stack[self]).budget]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    \/ /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ internal_budget' = [internal_budget EXCEPT ![self] = Head(stack[self]).internal_budget]
                       /\ budget' = [budget EXCEPT ![self] = Head(stack[self]).budget]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << all_messages, data, msg_queue, msg_to_send, 
                                 produced_msg, consumed_msg, 
                                 compare_and_update_log, failure_budget, clock, 
                                 cur_msg, log >>

fail_by_budget(self) == MayFail(self)

ActionProducerPreCheck == /\ pc["producer"] = "ActionProducerPreCheck"
                          /\ IF Len(msg_to_send) = 0
                                THEN /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerDone"]
                                ELSE /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerMayFail"]
                          /\ UNCHANGED << all_messages, data, msg_queue, 
                                          msg_to_send, produced_msg, 
                                          consumed_msg, compare_and_update_log, 
                                          stack, budget, internal_budget, 
                                          failure_budget, clock, cur_msg, log >>

ActionProducerMayFail == /\ pc["producer"] = "ActionProducerMayFail"
                         /\ /\ budget' = [budget EXCEPT !["producer"] = failure_budget]
                            /\ stack' = [stack EXCEPT !["producer"] = << [ procedure |->  "fail_by_budget",
                                                                           pc        |->  "ActionProducerLoop",
                                                                           internal_budget |->  internal_budget["producer"],
                                                                           budget    |->  budget["producer"] ] >>
                                                                       \o stack["producer"]]
                         /\ internal_budget' = [internal_budget EXCEPT !["producer"] = budget'["producer"]]
                         /\ pc' = [pc EXCEPT !["producer"] = "MayFail"]
                         /\ UNCHANGED << all_messages, data, msg_queue, 
                                         msg_to_send, produced_msg, 
                                         consumed_msg, compare_and_update_log, 
                                         failure_budget, clock, cur_msg, log >>

ActionProducerLoop == /\ pc["producer"] = "ActionProducerLoop"
                      /\ msg_queue' = (msg_queue \union {Head(msg_to_send)})
                      /\ produced_msg' = (produced_msg \union {Head(msg_to_send)})
                      /\ msg_to_send' = Tail(msg_to_send)
                      /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerNextStep"]
                      /\ UNCHANGED << all_messages, data, consumed_msg, 
                                      compare_and_update_log, stack, budget, 
                                      internal_budget, failure_budget, clock, 
                                      cur_msg, log >>

ActionProducerNextStep == /\ pc["producer"] = "ActionProducerNextStep"
                          /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerPreCheck"]
                          /\ UNCHANGED << all_messages, data, msg_queue, 
                                          msg_to_send, produced_msg, 
                                          consumed_msg, compare_and_update_log, 
                                          stack, budget, internal_budget, 
                                          failure_budget, clock, cur_msg, log >>

ActionProducerDone == /\ pc["producer"] = "ActionProducerDone"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT !["producer"] = "Done"]
                      /\ UNCHANGED << all_messages, data, msg_queue, 
                                      msg_to_send, produced_msg, consumed_msg, 
                                      compare_and_update_log, stack, budget, 
                                      internal_budget, failure_budget, clock, 
                                      cur_msg, log >>

producer == ActionProducerPreCheck \/ ActionProducerMayFail
               \/ ActionProducerLoop \/ ActionProducerNextStep
               \/ ActionProducerDone

ActionConsumerWait == /\ pc["consumer"] = "ActionConsumerWait"
                      /\ Cardinality(msg_queue) > 0
                      /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumeMsgMayFail"]
                      /\ UNCHANGED << all_messages, data, msg_queue, 
                                      msg_to_send, produced_msg, consumed_msg, 
                                      compare_and_update_log, stack, budget, 
                                      internal_budget, failure_budget, clock, 
                                      cur_msg, log >>

ActionConsumeMsgMayFail == /\ pc["consumer"] = "ActionConsumeMsgMayFail"
                           /\ /\ budget' = [budget EXCEPT !["consumer"] = failure_budget]
                              /\ stack' = [stack EXCEPT !["consumer"] = << [ procedure |->  "fail_by_budget",
                                                                             pc        |->  "ActionConsumeMsg",
                                                                             internal_budget |->  internal_budget["consumer"],
                                                                             budget    |->  budget["consumer"] ] >>
                                                                         \o stack["consumer"]]
                           /\ internal_budget' = [internal_budget EXCEPT !["consumer"] = budget'["consumer"]]
                           /\ pc' = [pc EXCEPT !["consumer"] = "MayFail"]
                           /\ UNCHANGED << all_messages, data, msg_queue, 
                                           msg_to_send, produced_msg, 
                                           consumed_msg, 
                                           compare_and_update_log, 
                                           failure_budget, clock, cur_msg, log >>

ActionConsumeMsg == /\ pc["consumer"] = "ActionConsumeMsg"
                    /\ cur_msg' = (CHOOSE m \in msg_queue: TRUE)
                    /\ log' = [diff |-> FALSE, ctime |-> clock, msg |-> cur_msg']
                    /\ clock' = clock + 1
                    /\ pc' = [pc EXCEPT !["consumer"] = "ActionCompareMayFail"]
                    /\ UNCHANGED << all_messages, data, msg_queue, msg_to_send, 
                                    produced_msg, consumed_msg, 
                                    compare_and_update_log, stack, budget, 
                                    internal_budget, failure_budget >>

ActionCompareMayFail == /\ pc["consumer"] = "ActionCompareMayFail"
                        /\ /\ budget' = [budget EXCEPT !["consumer"] = failure_budget]
                           /\ stack' = [stack EXCEPT !["consumer"] = << [ procedure |->  "fail_by_budget",
                                                                          pc        |->  "ActionCompare",
                                                                          internal_budget |->  internal_budget["consumer"],
                                                                          budget    |->  budget["consumer"] ] >>
                                                                      \o stack["consumer"]]
                        /\ internal_budget' = [internal_budget EXCEPT !["consumer"] = budget'["consumer"]]
                        /\ pc' = [pc EXCEPT !["consumer"] = "MayFail"]
                        /\ UNCHANGED << all_messages, data, msg_queue, 
                                        msg_to_send, produced_msg, 
                                        consumed_msg, compare_and_update_log, 
                                        failure_budget, clock, cur_msg, log >>

ActionCompare == /\ pc["consumer"] = "ActionCompare"
                 /\ \/ /\ log' = [log EXCEPT !.diff = FALSE]
                    \/ /\ log' = [log EXCEPT !.diff = TRUE]
                 /\ clock' = clock + 1
                 /\ pc' = [pc EXCEPT !["consumer"] = "ActionUpdateMayFail"]
                 /\ UNCHANGED << all_messages, data, msg_queue, msg_to_send, 
                                 produced_msg, consumed_msg, 
                                 compare_and_update_log, stack, budget, 
                                 internal_budget, failure_budget, cur_msg >>

ActionUpdateMayFail == /\ pc["consumer"] = "ActionUpdateMayFail"
                       /\ /\ budget' = [budget EXCEPT !["consumer"] = failure_budget]
                          /\ stack' = [stack EXCEPT !["consumer"] = << [ procedure |->  "fail_by_budget",
                                                                         pc        |->  "ActionUpdate",
                                                                         internal_budget |->  internal_budget["consumer"],
                                                                         budget    |->  budget["consumer"] ] >>
                                                                     \o stack["consumer"]]
                       /\ internal_budget' = [internal_budget EXCEPT !["consumer"] = budget'["consumer"]]
                       /\ pc' = [pc EXCEPT !["consumer"] = "MayFail"]
                       /\ UNCHANGED << all_messages, data, msg_queue, 
                                       msg_to_send, produced_msg, consumed_msg, 
                                       compare_and_update_log, failure_budget, 
                                       clock, cur_msg, log >>

ActionUpdate == /\ pc["consumer"] = "ActionUpdate"
                /\ IF log.diff
                      THEN /\ data' = [data EXCEPT !.mtime = clock]
                      ELSE /\ TRUE
                           /\ data' = data
                /\ clock' = clock + 1
                /\ pc' = [pc EXCEPT !["consumer"] = "ActionMsgACKMayFail"]
                /\ UNCHANGED << all_messages, msg_queue, msg_to_send, 
                                produced_msg, consumed_msg, 
                                compare_and_update_log, stack, budget, 
                                internal_budget, failure_budget, cur_msg, log >>

ActionMsgACKMayFail == /\ pc["consumer"] = "ActionMsgACKMayFail"
                       /\ /\ budget' = [budget EXCEPT !["consumer"] = failure_budget]
                          /\ stack' = [stack EXCEPT !["consumer"] = << [ procedure |->  "fail_by_budget",
                                                                         pc        |->  "ActionMsgACK",
                                                                         internal_budget |->  internal_budget["consumer"],
                                                                         budget    |->  budget["consumer"] ] >>
                                                                     \o stack["consumer"]]
                       /\ internal_budget' = [internal_budget EXCEPT !["consumer"] = budget'["consumer"]]
                       /\ pc' = [pc EXCEPT !["consumer"] = "MayFail"]
                       /\ UNCHANGED << all_messages, data, msg_queue, 
                                       msg_to_send, produced_msg, consumed_msg, 
                                       compare_and_update_log, failure_budget, 
                                       clock, cur_msg, log >>

ActionMsgACK == /\ pc["consumer"] = "ActionMsgACK"
                /\ consumed_msg' = Append(consumed_msg, cur_msg)
                /\ msg_queue' = msg_queue \ {cur_msg}
                /\ clock' = clock + 1
                /\ compare_and_update_log' = (compare_and_update_log \union {log})
                /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerNextStep"]
                /\ UNCHANGED << all_messages, data, msg_to_send, produced_msg, 
                                stack, budget, internal_budget, failure_budget, 
                                cur_msg, log >>

ActionConsumerNextStep == /\ pc["consumer"] = "ActionConsumerNextStep"
                          /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerWait"]
                          /\ UNCHANGED << all_messages, data, msg_queue, 
                                          msg_to_send, produced_msg, 
                                          consumed_msg, compare_and_update_log, 
                                          stack, budget, internal_budget, 
                                          failure_budget, clock, cur_msg, log >>

consumer == ActionConsumerWait \/ ActionConsumeMsgMayFail
               \/ ActionConsumeMsg \/ ActionCompareMayFail \/ ActionCompare
               \/ ActionUpdateMayFail \/ ActionUpdate
               \/ ActionMsgACKMayFail \/ ActionMsgACK
               \/ ActionConsumerNextStep

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == producer \/ consumer
           \/ (\E self \in ProcSet: fail_by_budget(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(producer) /\ WF_vars(fail_by_budget("producer"))
        /\ WF_vars(consumer) /\ WF_vars(fail_by_budget("consumer"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
