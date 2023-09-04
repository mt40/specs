---- MODULE active_cache ----

EXTENDS Integers

CONSTANTS
    FREQ, \*frequency
    P \*set of processes

VARIABLES
    hasLock,
    lock,
    clock, \*refers to time of the cache service (e.g. Redis)
    pState

\*invariants

ProcessStateTypeOk == pState \in [P -> {"checking", "cs", "waiting", "releasing_lock"}]

\*no process need the lock
LockNotUsed == lock = 1
\*only 1 process can have the lock
LockInUse == /\ lock = 0
MutualExclusive == LockNotUsed \/ LockInUse

\*time between 2 critical section accesses must be FREQ
Frequency == \/ (LockInUse /\ (clock = FREQ))
             \/ (LockNotUsed /\ (clock /= FREQ))

====
