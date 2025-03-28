---- MODULE dekker ----
EXTENDS TLC, Integers, FiniteSets, Sequences
Servers == 1..2
(*--algorithm dekker

variables
    \*Servers = <<1, 2>>, \* only works with 2 servers
    flag = [s \in Servers |-> FALSE], \* indicate the server that is running
    next_server \in Servers;

define
    \* safety
    MutualExclusion == \A s1, s2 \in Servers : s1 # s2 => ~(pc[s1] = "CS" /\ pc[s2] = "CS")

    \* liveness
    Progress == \E s \in {1} : <>(pc[s] = "CS")
    \* deadlock is already checked by default by TLC
end define;

procedure server()
    begin
    P1: flag[self] := TRUE;

    \* scenario that violates Progress:
    \*     1. crash process reaches P2_1_1 and then crashes
    \*     2. fair process reaches P2_1
    \*     3. fair process check P2_1 if condition and fails, go back to while loop of P2
    \*     4. fair process repeats step 2 & 3 forever
    P2:
        while \E s \in (Servers \ {self}) : flag[s] do
            P2_1:
                if next_server # self then
                    P2_1_1: flag[self] := FALSE;
                    P2_1_2: await next_server = self;
                    P2_1_3: flag[self] := TRUE;
                end if;
        end while;

    \* simulate Critical Section
    CS: skip;

    P3: next_server := 3 - next_server;
    P4: flag[self] := FALSE;
    P5: goto P1;
end procedure;

fair process fair_server \in {1}
begin
    Fair:
        call server();
end process;

process crashable_server \in {2}
begin
    Crashable:
        call server();

end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "21bbb53" /\ chksum(tla) = "d967e409")
VARIABLES flag, next_server, pc, stack

(* define statement *)
MutualExclusion == \A s1, s2 \in Servers : s1 # s2 => ~(pc[s1] = "CS" /\ pc[s2] = "CS")


Progress == \E s \in {1} : <>(pc[s] = "CS")


vars == << flag, next_server, pc, stack >>

ProcSet == ({1}) \cup ({2})

Init == (* Global variables *)
        /\ flag = [s \in Servers |-> FALSE]
        /\ next_server \in Servers
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {1} -> "Fair"
                                        [] self \in {2} -> "Crashable"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << next_server, stack >>

P2(self) == /\ pc[self] = "P2"
            /\ IF \E s \in (Servers \ {self}) : flag[s]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, next_server, stack >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_server # self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next_server, stack >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED << next_server, stack >>

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_server = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, next_server, stack >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ UNCHANGED << next_server, stack >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_server, stack >>

P3(self) == /\ pc[self] = "P3"
            /\ next_server' = 3 - next_server
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ UNCHANGED << flag, stack >>

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << next_server, stack >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, next_server, stack >>

server(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

Fair(self) == /\ pc[self] = "Fair"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "server",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << flag, next_server >>

fair_server(self) == Fair(self)

Crashable(self) == /\ pc[self] = "Crashable"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "server",
                                                            pc        |->  "Done" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "P1"]
                   /\ UNCHANGED << flag, next_server >>

crashable_server(self) == Crashable(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: server(self))
           \/ (\E self \in {1}: fair_server(self))
           \/ (\E self \in {2}: crashable_server(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1} : WF_vars(fair_server(self)) /\ WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
