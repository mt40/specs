Mutual Exclusion solution when we have a special atomic action 'TS' (Test & Set).

---------------------------- MODULE test_and_set ----------------------------

EXTENDS Integers
CONSTANTS Process
VARIABLES hasLock, lock, pc

At(p, loc)              == pc[p] = loc
GoTo(p, loc)            == pc' = [pc EXCEPT ![p] = loc]
GoFromTo(p, loc1, loc2) == At(p, loc1) /\ GoTo(p, loc2)

TS(p, x, y) == (x' = [x EXCEPT ![p] = y]) /\ (y' = FALSE)

Wait(p) ==
    \/ (hasLock[p] = FALSE /\ TS(p, hasLock, lock) /\ UNCHANGED<<pc>>)
    \/ (hasLock[p] = TRUE /\ GoFromTo(p, "wait", "cs") /\ UNCHANGED<<hasLock, lock>>)
CS(p) ==
    /\ GoFromTo(p, "cs", "reset")
    /\ UNCHANGED<<hasLock, lock>>
Reset(p) ==
    /\ lock' = TRUE
    /\ hasLock' = [hasLock EXCEPT ![p] = FALSE]
    /\ GoFromTo(p, "reset", "wait")

Init ==
    /\ pc = [p \in Process |-> "wait"]
    /\ hasLock = [p \in Process |-> FALSE]
    /\ lock = TRUE
PNext(p)    == Wait(p) \/ CS(p) \/ Reset(p)
Next        == \E p \in Process: PNext(p)

NoConcurrentCS(i, j)    == (i # j) => (pc[i] # "cs") \/ (pc[j] # "cs")
MutualExclusion         == \A i, j \in Process : []NoConcurrentCS(i, j)

vars            == <<hasLock, lock, pc>>
Fairness        == \A p \in Process : WF_vars(Wait(p) \/ CS(p) \/ Reset(p))
CSEventually    == (\E i \in Process : pc[i] \in {"wait"}) ~> (\E j \in Process : pc[j] = "cs")
Progress        == Fairness => CSEventually

=============================================================================
\* Modification History
\* Last modified Thu Sep 14 17:33:50 ICT 2023 by minhthai.pham
\* Created Thu Sep 14 17:28:49 ICT 2023 by minhthai.pham
