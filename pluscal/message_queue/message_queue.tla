---- MODULE message_queue ----
EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue
variables
    queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

procedure add_to_queue(val="") begin
    Add:
        await Len(queue) < MaxQueueSize;
        queue := Append(queue, val);
        return;
end procedure;

    
process writer = "writer"
begin Write:
    while TRUE do
        call  add_to_queue("msg");
    end while;
end process;

process reader \in {"reader1", "reader2"}
variables
    current_msg = "none";
begin Read:
    while TRUE do
        await queue # <<>>;
        current_msg := Head(queue);
        queue := Tail(queue);

        \* simulate read failure
        either
            skip;
        or
            NotifyFailure:
                current_msg := "none";
                call add_to_queue(self);
        end either;

    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7cd74e9d" /\ chksum(tla) = "64391f26")
VARIABLES queue, pc, stack

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLES val, current_msg

vars == << queue, pc, stack, val, current_msg >>

ProcSet == {"writer"} \cup ({"reader1", "reader2"})

Init == (* Global variables *)
        /\ queue = <<>>
        (* Procedure add_to_queue *)
        /\ val = [ self \in ProcSet |-> ""]
        (* Process reader *)
        /\ current_msg = [self \in {"reader1", "reader2"} |-> "none"]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in {"reader1", "reader2"} -> "Read"]

Add(self) == /\ pc[self] = "Add"
             /\ Len(queue) < MaxQueueSize
             /\ queue' = Append(queue, val[self])
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED current_msg

add_to_queue(self) == Add(self)

Write == /\ pc["writer"] = "Write"
         /\ /\ stack' = [stack EXCEPT !["writer"] = << [ procedure |->  "add_to_queue",
                                                         pc        |->  "Write",
                                                         val       |->  val["writer"] ] >>
                                                     \o stack["writer"]]
            /\ val' = [val EXCEPT !["writer"] = "msg"]
         /\ pc' = [pc EXCEPT !["writer"] = "Add"]
         /\ UNCHANGED << queue, current_msg >>

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ queue # <<>>
              /\ current_msg' = [current_msg EXCEPT ![self] = Head(queue)]
              /\ queue' = Tail(queue)
              /\ \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Read"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "NotifyFailure"]
              /\ UNCHANGED << stack, val >>

NotifyFailure(self) == /\ pc[self] = "NotifyFailure"
                       /\ current_msg' = [current_msg EXCEPT ![self] = "none"]
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "add_to_queue",
                                                                   pc        |->  "Read",
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = self]
                       /\ pc' = [pc EXCEPT ![self] = "Add"]
                       /\ queue' = queue

reader(self) == Read(self) \/ NotifyFailure(self)

Next == writer
           \/ (\E self \in ProcSet: add_to_queue(self))
           \/ (\E self \in {"reader1", "reader2"}: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
