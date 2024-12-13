module twolayeredcache {
    //**********************************************************
    // TYPE DEFINITIONS
    //**********************************************************
    type CacheLayer = Set[int]
    type ClientPID = int

    // tpe: "read" or "write"
    type HistoryEntry = { tpe: str, value: int}

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

    action writeLayer(layer: CacheLayer, v: int): bool = all {
        layer' = layer.union(Set(v))
    }

    //**********************************************************
    // HELPERS
    // Functions for convenience
    //**********************************************************

    //**********************************************************
    // ACTIONS
    //**********************************************************

    action writeCache(pid: ClientPID, v: int): bool = all {
        writeLayer(l1, v),
        writeLayer(l2, v),
        history' = history.append({
            tpe: "write",
            value: v,
        }),
    }

    action handleNotFound: bool = all {
        l1' = l1,
        l2' = l2,
        history' = history.append({
            tpe: "read",
            value: NotFound,
        }),
    }

    action handleL1Found(v: int): bool = all {
        l1' = l1,
        l2' = l2,
        history' = history.append({
            tpe: "read",
            value: v,
        }),
    }

    action handleL2Found(v: int): bool = all {
        writeLayer(l1, v),
        l2' = l2,
        history' = history.append({
            tpe: "read",
            value: v,
        }),
    }

    action handleFound(v: int): bool = {
        if(l1.contains(v)) {
            handleL1Found(v)
        } else {
            handleL2Found(v)
        }
    }

    // If this val doesn't exist in L1, read from L2.
    // If val exists in L2, write back to L1 then return.
    // Otherwise, not found (false).
    action readCache(pid: ClientPID, v: int): bool = {
        if (not(l1.contains(v)) and not(l2.contains(v))) {
            handleNotFound
        } else {
            handleFound(v)
        }
    }

    action clientProc = all {
        num' = num + 1,
        nondet pid = ClientProcesses.oneOf()
        nondet readVal = 1.to(num).oneOf()
        any {
            writeCache(pid, num),
            readCache(pid, readVal),
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
                and history[i].tpe == "write"
                and history[j].tpe == "read"
                implies history[i].value <= history[j].value
            })
        })
    }

    // Later write must contain a greater value
    val writeAfterWrite: bool = {
        val idx = history.indices()
        idx.forall(i => {
            idx.forall(j => {
                i < j
                and history[i].tpe == "write"
                and history[j].tpe == "write"
                implies history[i].value < history[j].value
            })
        })
    }

    val strongConsistency: bool = {
        readAfterWrite
        and writeAfterWrite
    }

    val safety: bool = {
        strongConsistency
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