---- MODULE scci_p1 ----
EXTENDS TLC, Naturals, Integers, Sequences

(*--algorithm scci_p1
    variables 
        ints = <<>>, max = -999, i = 1;

    begin
        
        assert \A n \in 1..Len(ints) : ints[n] > -999;

        while (i =< Len(ints)) do
            if (ints[i] > max) then
                max := ints[i];
            end if;
            i := i + 1;
        end while;

        assert (
            (\A n \in 1..Len(ints) : max >= ints[n])
            /\ (\E n \in 1..Len(ints) : max = ints[n])
        );

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
