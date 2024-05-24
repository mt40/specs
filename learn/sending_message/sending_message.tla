---- MODULE sending_message ----
EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

(*--algorithm sending_message
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};

begin
    while Len(received) # 3 do
        \* send
        if Len(to_send) > 0 then
            in_transit := in_transit \union {Head(to_send)};
            to_send := Tail(to_send);
        end if;

        \* receive
        either
            skip;
        or
            \* receive msg in random order
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
            end with;
        end either;
    end while;

    assert received = <<1, 2, 3>>;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b0f3ceb6" /\ chksum(tla) = "fec2cb63")
VARIABLES to_send, received, in_transit, pc

(* define statement *)
Add(a, b) == a + b


vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) # 3
               THEN /\ IF Len(to_send) > 0
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ TRUE
                          /\ pc' = "Lbl_1"
                       \/ /\ pc' = "Lbl_2"
               ELSE /\ Assert(received = <<1, 2, 3>>, 
                              "Failure of assertion at line 34, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
