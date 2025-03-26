// -*- mode: Bluespec; -*-

module two_layered_cache {
    //**********************************************************
    // TYPE DEFINITIONS
    //**********************************************************
    type CacheLayer = Set[int] // use Set so it is easy to extend to multiple keys if needed
    type ClientPID = int

    type HistoryEntry = Read(int) | Write(int)

    //**********************************************************
    // CONSTANTS
    //**********************************************************
    pure val DefaultExpireDuration = 3
    pure val ClientProcesses: Set[ClientPID] = 1.to(10)
    pure val MaxVal = 1000000
    pure val Expired = -99
    pure val NotFound = -98

    //**********************************************************
    // STATE MACHINE
    // State-dependent definitions and actions
    //**********************************************************

    var l1: CacheLayer
    var l2: CacheLayer
    var num: int

    // Global log of system events. Use to specify correctness
    // properties below.
    var history: List[HistoryEntry]

    //**********************************************************
    // FUNCTIONAL LAYER
    // Values and functions that are state-independent
    //**********************************************************

    pure def isWrite(entry: HistoryEntry): bool = {
        match entry {
            | Write(_) => true
            | _ => false
        }
    }

    pure def isRead(entry: HistoryEntry): bool = {
        match entry {
            | Read(_) => true
            | _ => false
        }
    }

    pure def value(entry: HistoryEntry): int = {
        match entry {
            | Read(v) => v
            | Write(v) => v
        }
    }

    // Get the first element of a given non-empty Set
    pure def getHeadOfSet(s: Set[int]): int = {
        s.fold(0, (a, b) => b)
    }

    //**********************************************************
    // HELPERS
    // Operators for convenience
    //**********************************************************

    action writeL1(v: int): bool = all {
        l1' = l1.union(Set(v))
    }

    action writeL2(v: int): bool = all {
        l2' = l2.union(Set(v))
    }

    //**********************************************************
    // ACTIONS
    //**********************************************************

    action writeCache(pid: ClientPID, v: int): bool = all {
        writeL1(v),
        writeL2(v),
        history' = history.append(Write(v))
    }

    action handleNotFound(): bool = all {
        l1' = l1,
        l2' = l2,
        history' = history.append(Read(NotFound))
    }

    action handleL1Found(): bool = {
        val value = getHeadOfSet(l1)
        all {
            l1' = l1,
            l2' = l2,
            history' = history.append(Read(value))
        }
    }

    action handleL2Found(): bool = {
        val value = getHeadOfSet(l2)
        all {
            writeL1(value),
            l2' = l2,
            history' = history.append(Read(value))
        }
    }

    action handleFound(): bool = {
        if (l1.size() > 0) {
            handleL1Found
        } else {
            handleL2Found
        }
    }

    // If val doesn't exist in L1, read from L2.
    // If val exists in L2, write back to L1 then return.
    // Otherwise, not found (false).
    action readCache(pid: ClientPID): bool = {
        if (l1.size() > 0 or l2.size() > 0) {
            handleFound
        } else {
            handleNotFound
        }
    }

    action clientProc = all {
        nondet pid = ClientProcesses.oneOf()
        
        any {
            all {
                num' = num + 1,
                writeCache(pid, num)
            },
            all {
                num' = num,
                readCache(pid),
            }
        },
    }

    action init = all {
        num' = 0,
        l1' = Set(),
        l2' = Set(),
        history' = [],
    }

    action stutter = all {
        num' = num,
        l1' = l1,
        l2' = l2,
        history' = history,
    }

    action step = any {
        clientProc,
        stutter,
    }

    //**********************************************************
    // CORRECTNESS
    // 1. Safety Properties / Invariants
    //**********************************************************

    // Read the latest write
    val readAfterWrite: bool = {
        val idx = history.indices()
        idx.forall(i => {
            idx.forall(j => {
                i < j
                and history[i].isWrite()
                and history[j].isRead()
                implies history[i].value() <= history[j].value()
            })
        })
    }

    // Later write must contain a greater value
    val writeAfterWrite: bool = {
        val idx = history.indices()
        idx.forall(i => {
            idx.forall(j => {
                i < j
                and history[i].isWrite()
                and history[j].isWrite()
                implies history[i].value() < history[j].value()
            })
        })
    }

    val strongConsistency: bool = {
        readAfterWrite
        and writeAfterWrite
    }

    // All layers contain the same latest written value
    val agreement: bool = {
        val a = getHeadOfSet(l1)
        val b = getHeadOfSet(l2)
        a == b
    }

    val safety: bool = {
        strongConsistency
        and agreement
    }

    //**********************************************************
    // CORRECTNESS
    // 2. Liveness Properties / Temporal
    //**********************************************************


    //**********************************************************
    // QUICK TESTS
    //**********************************************************
    // run initAndStepTest = init.then(step)
}