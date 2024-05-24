---- MODULE functions ----
EXTENDS TLC

(*--algorithm functions
variables
    Flags = {"f1", "f2"},
    flags \in [Flags -> BOOLEAN];
begin
    
    with f \in Flags do
        flags[f] := TRUE;
    end with;

    print flags;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2483bb3b" /\ chksum(tla) = "41b01527")
VARIABLES Flags, flags, pc

vars == << Flags, flags, pc >>

Init == (* Global variables *)
        /\ Flags = {"f1", "f2"}
        /\ flags \in [Flags -> BOOLEAN]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \E f \in Flags:
              flags' = [flags EXCEPT ![f] = TRUE]
         /\ PrintT(flags')
         /\ pc' = "Done"
         /\ Flags' = Flags

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
