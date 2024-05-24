[v] it is possible that only Tick will run in formula Next,
  hence eventually violating our invariant NoFrequencyViolation
[ ] todo: it is possible that all processes have hasLock=TRUE
  caused by lock is set to TRUE when a process is in CS
[ ] todo: now will increase forever, is this ok?

-------------------- MODULE test_and_set_with_frequency --------------------

EXTENDS Integers
CONSTANTS
    NormalProcesses,
    Freq \* number of seconds between 2 consecutive CS accesses
VARIABLES
    hasLock,
    lock, \* TRUE = lock is available, FALSE = lock is taken
    pc,
    now,
    lbTimer \* lowerbound timer: time to wait before allowed to access CS

\* utils
ResetLbTimer == lbTimer' = Freq

\*states of normal process
At(p, loc)              == pc[p] = loc
GoTo(p, loc)            == pc' = [pc EXCEPT ![p] = loc]
GoFromTo(p, loc1, loc2) == At(p, loc1) /\ GoTo(p, loc2)

TS(p) == (hasLock' = [hasLock EXCEPT ![p] = lock]) /\ (lock' = FALSE)

Wait(p) ==
    \/ (hasLock[p] = FALSE /\ TS(p) /\ UNCHANGED<<pc, now, lbTimer>>)
    \/ (hasLock[p] = TRUE /\ GoFromTo(p, "wait", "cs") /\ UNCHANGED<<hasLock, lock, now, lbTimer>>)
CS(p) ==
    /\ GoFromTo(p, "cs", "reset")
    /\ UNCHANGED<<hasLock, lock, now, lbTimer>>
Reset(p) ==
    /\ hasLock' = [hasLock EXCEPT ![p] = FALSE]
    /\ GoFromTo(p, "reset", "wait")
    /\ UNCHANGED<<lock, now, lbTimer>>

\*states of coordinator process
Expire ==
    /\ lbTimer = 0
    /\ lbTimer' = Freq
    /\ lock' = TRUE
    /\ UNCHANGED<<hasLock, pc, now>>

\*observer's clock
Tick ==
    /\ lbTimer >= 1
    /\ now' = now + 1
    /\ lbTimer' = IF lbTimer = 0 THEN 0 ELSE lbTimer - 1
    /\ UNCHANGED<<hasLock, lock, pc>>

\*temporal properties
Init ==
    /\ pc = [p \in NormalProcesses |-> "wait"]
    /\ hasLock = [p \in NormalProcesses |-> FALSE]
    /\ lock = TRUE
    /\ now = 0
    /\ lbTimer = Freq
PNext(p)    == Wait(p) \/ CS(p) \/ Reset(p)
Next        == Expire \/ Tick \/ (\E p \in NormalProcesses: PNext(p))


noConcurrentCS(i, j)    == (i # j) => (pc[i] # "cs") \/ (pc[j] # "cs")
MutualExclusion         == \A i, j \in NormalProcesses : []noConcurrentCS(i, j)

vars            == <<hasLock, lock, pc, now, lbTimer>>
fairness        == \A p \in NormalProcesses : WF_vars(Wait(p) \/ CS(p) \/ Reset(p))
csEventually    ==
                    (\E i \in NormalProcesses : pc[i] \in {"wait"})
                    ~> (\E j \in NormalProcesses : pc[j] = "cs")
NoDeadLock      == fairness => csEventually

NoFrequencyViolation == (lbTimer = 0) ~> (\E p \in NormalProcesses: pc[p] = "cs")

=============================================================================
\* Modification History
\* Last modified Sun Sep 24 09:17:08 ICT 2023 by minhthai.pham
\* Created Wed Sep 20 12:44:46 ICT 2023 by minhthai.pham
