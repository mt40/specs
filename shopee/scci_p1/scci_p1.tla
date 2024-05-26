---- MODULE scci_p1 ----
EXTENDS TLC, Naturals, Integers, Sequences

\* model values
\* ---------------
CONSTANTS NULL

\* constants
\* ---------------
MESSAGES == {"m1", "m2"}

\* types
\* ---------------
LogType == [diff: BOOLEAN, ctime: Nat, msg: MESSAGES]
DataType == [mtime: Nat]

(*--algorithm scci_p1
    variables 
        \* assume that MQ is ordered, required suitable
        \* kafka config
        msg_queue = <<>>,
        data = [mtime: Nat],

        \* ghost variables
        \* ---------------
        \* set of consumed messages
        consumed_msg = {},
        \* set of LogType
        compare_and_update_log = {};

    define
        \* safety
        \* ---------------
        NoMessageLoss == \A msg \in MESSAGES : (msg \in msg_queue) ~> (msg \in consumed_msg)
        \* If the system is available, it responds with data not older than 1h
        BoundedStaleness == TRUE \* todo
        \* If the system was down for 3d and then recover, and consumer speed is
        \* faster than producer, BoundedStaleness is eventually TRUE
        Recovery == TRUE \* todo
        \* Older data can never overwrite newer data
        Integrity == \A log \in compare_and_update_log : log.ctime <= data.mtime

        \* liveness
        \* ---------------
        \* Assuming API call & producing msg are atomic, when API is called, eventually C&U will run
        Progress == \A msg \in MESSAGES : (msg \in msg_queue) ~> (\E log \in compare_and_update_log : log.msg = msg)
        \* If Compare shows diff, data is eventually updated to newer
        Validity == \A log \in compare_and_update_log : log.diff ~> (log.ctime <= data.mtime)

    end define;

        
    fair process producer = "producer"
    variables
        msg_to_send \in [m \in 1..Cardinality(MESSAGES) -> MESSAGES];
    begin
        ActionProducerLoop:
            either
                skip;
            or
                ActionProduceMsg:
                    msg_queue := msg_queue \union {Head(msg_to_send)};
                    msg_to_send := Tail(msg_to_send);
            end either;
        
        ActionProducerNextStep:
            goto ActionProducerLoop;
    end process;

    fair process consumer = "consumer"
    variable
        clock = 1,
        log = [diff |-> FALSE, ctime |-> 0, msg |-> NULL]; \* LogType
    begin
        ActionConsumerLoop:
            await Len(all_msg) > 0;
        
            either
                clock := clock + 1;
                skip;
            or
                ActionConsumeMsg:
                    log := [diff |-> FALSE, ctime |-> clock, msg |-> Head(msg_queue)];
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
                    msg_queue := Tail(msg_queue);
                    clock := clock + 1;
            end either;
        
        
        ActionConsumerNextStep:
            goto ActionConsumerLoop;
    end process;

    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b5a89ee0" /\ chksum(tla) = "78c15256")
VARIABLES msg_queue, data, consumed_msg, compare_and_update_log, pc

(* define statement *)
NoMessageLoss == \A msg \in MESSAGES : (msg \in msg_queue) ~> (msg \in consumed_msg)

BoundedStaleness == TRUE


Recovery == TRUE

Integrity == \A log \in compare_and_update_log : log.ctime <= data.mtime




Progress == \A msg \in MESSAGES : (msg \in msg_queue) ~> (\E log \in compare_and_update_log : log.msg = msg)

Validity == \A log \in compare_and_update_log : log.diff ~> (log.ctime <= data.mtime)

VARIABLES msg_to_send, clock, log

vars == << msg_queue, data, consumed_msg, compare_and_update_log, pc, 
           msg_to_send, clock, log >>

ProcSet == {"producer"} \cup {"consumer"}

Init == (* Global variables *)
        /\ msg_queue = <<>>
        /\ data = [mtime: Nat]
        /\ consumed_msg = {}
        /\ compare_and_update_log = {}
        (* Process producer *)
        /\ msg_to_send \in [m \in 1..Cardinality(MESSAGES) -> MESSAGES]
        (* Process consumer *)
        /\ clock = 1
        /\ log = [diff |-> FALSE, ctime |-> 0, msg |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = "producer" -> "ActionProducerLoop"
                                        [] self = "consumer" -> "ActionConsumerLoop"]

ActionProducerLoop == /\ pc["producer"] = "ActionProducerLoop"
                      /\ \/ /\ TRUE
                            /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerNextStep"]
                         \/ /\ pc' = [pc EXCEPT !["producer"] = "ActionProduceMsg"]
                      /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                      compare_and_update_log, msg_to_send, 
                                      clock, log >>

ActionProduceMsg == /\ pc["producer"] = "ActionProduceMsg"
                    /\ msg_queue' = (msg_queue \union {Head(msg_to_send)})
                    /\ msg_to_send' = Tail(msg_to_send)
                    /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerNextStep"]
                    /\ UNCHANGED << data, consumed_msg, compare_and_update_log, 
                                    clock, log >>

ActionProducerNextStep == /\ pc["producer"] = "ActionProducerNextStep"
                          /\ pc' = [pc EXCEPT !["producer"] = "ActionProducerLoop"]
                          /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                          compare_and_update_log, msg_to_send, 
                                          clock, log >>

producer == ActionProducerLoop \/ ActionProduceMsg
               \/ ActionProducerNextStep

ActionConsumerLoop == /\ pc["consumer"] = "ActionConsumerLoop"
                      /\ Len(all_msg) > 0
                      /\ \/ /\ clock' = clock + 1
                            /\ TRUE
                            /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerNextStep"]
                         \/ /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumeMsg"]
                            /\ clock' = clock
                      /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                      compare_and_update_log, msg_to_send, log >>

ActionConsumeMsg == /\ pc["consumer"] = "ActionConsumeMsg"
                    /\ log' = [diff |-> FALSE, ctime |-> clock, msg |-> Head(msg_queue)]
                    /\ clock' = clock + 1
                    /\ pc' = [pc EXCEPT !["consumer"] = "ActionCompare"]
                    /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                    compare_and_update_log, msg_to_send >>

ActionCompare == /\ pc["consumer"] = "ActionCompare"
                 /\ \/ /\ log' = [log EXCEPT !.diff = FALSE]
                    \/ /\ log' = [log EXCEPT !.diff = TRUE]
                 /\ clock' = clock + 1
                 /\ pc' = [pc EXCEPT !["consumer"] = "ActionUpdate"]
                 /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                 compare_and_update_log, msg_to_send >>

ActionUpdate == /\ pc["consumer"] = "ActionUpdate"
                /\ IF log.diff
                      THEN /\ data' = [data EXCEPT !.mtime = clock]
                      ELSE /\ TRUE
                           /\ data' = data
                /\ clock' = clock + 1
                /\ pc' = [pc EXCEPT !["consumer"] = "ActionMsgDone"]
                /\ UNCHANGED << msg_queue, consumed_msg, 
                                compare_and_update_log, msg_to_send, log >>

ActionMsgDone == /\ pc["consumer"] = "ActionMsgDone"
                 /\ msg_queue' = Tail(msg_queue)
                 /\ clock' = clock + 1
                 /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerNextStep"]
                 /\ UNCHANGED << data, consumed_msg, compare_and_update_log, 
                                 msg_to_send, log >>

ActionConsumerNextStep == /\ pc["consumer"] = "ActionConsumerNextStep"
                          /\ pc' = [pc EXCEPT !["consumer"] = "ActionConsumerLoop"]
                          /\ UNCHANGED << msg_queue, data, consumed_msg, 
                                          compare_and_update_log, msg_to_send, 
                                          clock, log >>

consumer == ActionConsumerLoop \/ ActionConsumeMsg \/ ActionCompare
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
