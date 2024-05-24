---- MODULE dekker ----
EXTENDS TLC
CONSTANT Servers

(*--algorithm dekker

variables
    flag = [s \in Servers |-> FALSE];

define
    \* safety
    MutualExclusion == \A s1, s2 \in Servers : s1 # s2 => ~(pc[s1] = "CS" /\ pc[s2] = "CS")

    \* liveness
    Progress == \E s \in Servers : <>(pc[s] = "CS")
    \* deadlock is already checked by default by TLC
end define;

fair process server \in Servers
begin
    P1: flag[self] := TRUE;

    \* wait for a turn by keep turn on/off to avoid deadlock
    P2:
        while \E s \in (Servers \ {self}) : flag[s] do
            P2_1: flag[self] := FALSE;
            P2_2: flag[self] := TRUE;
        end while;

    \* simulate Critical Section
    CS: skip;

    P3: flag[self] := FALSE;
    P4: goto P1;

end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "67bd4ce4" /\ chksum(tla) = "f3b314d0")
VARIABLES flag, pc

(* define statement *)
MutualExclusion == \A s1, s2 \in Servers : s1 # s2 => ~(pc[s1] = "CS" /\ pc[s2] = "CS")


Progress == \E s \in Servers : <>(pc[s] = "CS")


vars == << flag, pc >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ flag = [s \in Servers |-> FALSE]
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]

P2(self) == /\ pc[self] = "P2"
            /\ IF \E s \in (Servers \ {self}) : flag[s]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ flag' = flag

P2_1(self) == /\ pc[self] = "P2_1"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "P2_2"]

P2_2(self) == /\ pc[self] = "P2_2"
              /\ flag' = [flag EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "P2"]

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ flag' = flag

P3(self) == /\ pc[self] = "P3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P4"]

P4(self) == /\ pc[self] = "P4"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ flag' = flag

server(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_2(self)
                   \/ CS(self) \/ P3(self) \/ P4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Servers: server(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
