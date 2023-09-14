This is an untimed version of the Fischer's Algorithm for Mutual Exclusion.
When you run the model, you will see that MutualExclusion temporal prop is
violated. This is because this algorithm only works when there is time
constraint.

------------------------------ MODULE fischer ------------------------------

EXTENDS Integers

CONSTANTS Process, Special
       
VARIABLES lock, pc

vars    == <<lock, pc>>

At(p, loc) == pc[p] = loc
GoTo(p, loc) == pc' = [pc EXCEPT ![p] = loc]
GoFromTo(p, loc1, loc2) == At(p, loc1) /\ GoTo(p, loc2)

NCS(p)      ==  /\ GoFromTo(p, "ncs", "a")
                /\ UNCHANGED<<lock>>
StmtA(p)    ==  /\ lock = Special
                /\ GoFromTo(p, "a", "b")
                /\ UNCHANGED<<lock>>
StmtB(p)    ==  /\ lock' = p
                /\ GoFromTo(p, "b", "c")
StmtC(p)    ==  /\ IF lock # p THEN GoFromTo(p, "c", "a") ELSE GoFromTo(p, "c", "cs")
                /\ UNCHANGED<<lock>>
CS(p)       ==  /\ GoFromTo(p, "cs", "d")
                /\ UNCHANGED<<lock>>
StmtD(p)    ==  /\ GoFromTo(p, "d", "a")
                /\ lock' = Special
                
PNext(p)    == NCS(p) \/ StmtA(p) \/ StmtB(p) \/ CS(p) \/ StmtD(p) \/ StmtC(p)
Init        ==  /\ pc = [p \in Process |-> "ncs"]
                /\ lock = Special
Next        == \E p \in Process : PNext(p)


NoConcurrentCS(i, j) == (i # j) => (pc[i] # "cs") \/ (pc[j] # "cs")
MutualExclusion == \A i, j \in Process : []NoConcurrentCS(i, j)


=============================================================================
\* Modification History
\* Last modified Sun Sep 10 10:22:30 ICT 2023 by minhthai.pham
\* Created Sat Sep 09 21:13:26 ICT 2023 by minhthai.pham
