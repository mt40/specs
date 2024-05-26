---- MODULE scci_p1 ----
EXTENDS TLC, Naturals, Integers, Sequences

(*--algorithm scci_p1
    variables 
        ints = <<>>, max = -999, i = 1,
        \* ghost variables
        compare_and_update_log = ;

    define
        \* safety
        \* ======
        NoMessageLoss = \A msg \in all_msg : (msg \in produced_msg) ~> (msg \in consumed_msg)
        \* If the system is available, it responds with data not older than 1h
        BoundedStaleness = TRUE \* todo
        \* If the system was down for 3d and then recover, and consumer speed is
        \* faster than producer, BoundedStaleness is eventually TRUE
        Recovery = TRUE \* todo
        \* Older data can never overwrite newer data
        Integrity = \A log \in compare_and_update_log : log.ctime <= data.mtime

        \* liveness
        \* ========
        \* Assuming API call & producing msg are atomic, when API is called, eventually C&U will run
        Progress = \A msg \in all_msg : (msg \in produced_msg) ~> (\E log \in compare_and_update_log : log.msg = msg)
        \* If Compare shows diff, data is eventually updated to newer
        Validity = \A log \in compare_and_update_log : log.diff ~> (log.ctime <= data.mtime)

    end define;

    begin

    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bcdac820" /\ chksum(tla) = "847f1fa0")
VARIABLES ints, max, i, pc

vars == << ints, max, i, pc >>

Init == (* Global variables *)
        /\ ints = <<>>
        /\ max = -999
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A n \in 1..Len(ints) : ints[n] > -999, 
                   "Failure of assertion at line 10, column 9.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << ints, max, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF (i =< Len(ints))
               THEN /\ IF (ints[i] > max)
                          THEN /\ max' = ints[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(       (
                                  (\A n \in 1..Len(ints) : max >= ints[n])
                                  /\ (\E n \in 1..Len(ints) : max = ints[n])
                              ), 
                              "Failure of assertion at line 19, column 9.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << max, i >>
         /\ ints' = ints

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
