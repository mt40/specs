------------------------------ MODULE fischer ------------------------------

EXTENDS Integers

CONSTANTS Process, Delta, Epsilon, Special, Inf
ASSUME  /\ (Delta \in Int) /\ (Epsilon \in Int)
        /\ 0 < Delta
        /\ Delta =< Epsilon
       
VARIABLES lock, pc, ubTimer, lbTimer, now

vars    == <<lock, pc, ubTimer, lbTimer, now>>

At(p, loc) == pc[p] = loc
GoTo(p, loc) == pc' = [pc EXCEPT ![p] = loc]
GoFromTo(p, loc1, loc2) == At(p, loc1) /\ GoTo(p, loc2)
SetTimer(p, timer, val) == timer' = [timer EXCEPT ![p] = val]

NCS(p)      ==  /\ GoFromTo(p, "ncs", "a")
                /\ UNCHANGED<<lock, now, lbTimer, ubTimer>>
StmtA(p)    ==  /\ lock = Special
                /\ GoFromTo(p, "a", "b")
                /\ SetTimer(p, ubTimer, Delta)
                /\ UNCHANGED<<lock, now, lbTimer>>
StmtB(p)    ==  /\ lock' = p
                /\ GoFromTo(p, "b", "c")
                /\ SetTimer(p, ubTimer, Inf)
                /\ SetTimer(p, lbTimer, Epsilon)
StmtC(p)    ==  /\ lbTimer[p] = 0
                /\ IF lock # p THEN GoFromTo(p, "c", "a") ELSE GoFromTo(p, "c", "cs")
                /\ UNCHANGED<<now, lock, ubTimer>>
CS(p)       ==  /\ GoFromTo(p, "cs", "d")
                /\ UNCHANGED<<now, lock, ubTimer>>
StmtD(p)    ==  /\GoFromTo(p, "d", "a")
                /\ lock' = Special
                /\ UNCHANGED<<now, lbTimer, ubTimer>>
                
Tick        ==  /\ now' = now + 1
                /\ ubTimer' = [p \in Process |-> IF ubTimer[p] = Inf THEN Inf ELSE ubTimer[p] - 1]
                /\ lbTimer' = [p \in Process |-> IF lbTimer[p] = 0 THEN 0 ELSE lbTimer[p] - 1]
                /\ UNCHANGED<<lock, pc>>
PNext(p)    == NCS(p) \/ StmtA(p) \/ StmtB(p) \/ StmtC(p) \/ CS(p) \/ StmtD(p)
Init        ==  /\ pc = [p \in Process |-> "ncs"]
                /\ now = 0
                /\ lock = Special
                /\ lbTimer = [p \in Process |-> 0]
                /\ ubTimer = [p \in Process |-> Inf]
Next        == Tick \/ (\A p \in Process : PNext(p))

AllBehaviors    == Init /\ [][Next]_vars
Liveness        ==  /\ \A p \in Process : WF_vars(StmtA(p) \/ StmtC(p) \/ StmtD(p))
                    /\ \A i \in Int : <>(now > i)

MutualExclusion == \A i, j \in Process : (i # j) => (pc[i] # "cs") \/ (pc[j] # "cs")
Progress        == (\E i \in Process : pc[i] \in {"a", "b", "c"}) ~> (\E j \in Process : pc[j] = "cs")


=============================================================================
\* Modification History
\* Last modified Sat Sep 09 22:38:57 ICT 2023 by minhthai.pham
\* Created Sat Sep 09 21:13:26 ICT 2023 by minhthai.pham
