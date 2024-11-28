module twolayeredcache {
    //**********************************************************
    // TYPE DEFINITIONS
    //**********************************************************
    type CacheLayerValue = {value: str, expire: int}
    type CacheLayer = str -> CacheLayerValue
    type CacheRequest = {pid: ClientPID, tpe: str, key: str, value: str}
    type CacheResponse = {tpe: str, key: str, value: CacheLayerValue, readTime: int}
    type CacheReadResult = {value: CacheLayerValue, readLayer1: bool}
    type ClientPID = int

    // tpe: "read" or "write"
    type HistoryEntry = { tpe: str, key: str, value: str, valueExpire: int, time: int }

    //**********************************************************
    // CONSTANTS
    //**********************************************************
    pure val DefaultExpireDuration = 3
    pure val ClientProcesses: Set[ClientPID] = 1.to(10)

    //**********************************************************
    // FUNCTIONAL LAYER
    // Values and functions that are state-independent
    //**********************************************************
    pure val NotFound: CacheLayerValue = {value: "not_found", expire: 0}
    
    //**********************************************************
    // STATE MACHINE
    // State-dependent definitions and actions
    //**********************************************************
    
    // layer1 is in-memory cache inside each Client Process
    var layer1: ClientPID -> CacheLayer
    var layer2: CacheLayer

    // There is no guarantee in order of requests and responses
    var requests: Set[CacheRequest]
    var responses: Set[CacheResponse]

    // Global log of system interactions. Use to specify correctness
    // properties below.
    var history: List[HistoryEntry]
    var historyClock: int

    //**********************************************************
    // HELPERS
    // Functions for convenience
    //**********************************************************
    def keyExists(key: str, layer: CacheLayer, localTime: int): bool = and {
        layer.keys().contains(key),
        val v = layer.get(key)
        v.expire > localTime
    }

    //**********************************************************
    // ACTIONS
    // 1. Client process
    //**********************************************************

    action sendRequest(pid: ClientPID): bool = all {
        nondet tpe = Set("R", "W").oneOf()
        nondet key = Set("a", "b", "c").oneOf()
        nondet value = Set("john", "tom", "carl", "alice", "rick").oneOf()

        pure val req = if (tpe == "R") {
            {pid: pid, tpe: tpe, key: key, value: ""}
        } else {
            {pid: pid, tpe: tpe, key: key, value: value}
        }

        requests' = requests.union(Set(req)),
        responses' = responses,
        history' = history,
    }

    action clientProc = all {
        nondet pid = ClientProcesses.oneOf()
        any {
            sendRequest(pid),
        },
        layer1' = layer1,
        layer2' = layer2,
        historyClock' = historyClock + 1,
    }

    //**********************************************************
    // ACTIONS
    // 1. Server process
    //**********************************************************

    // If this key doesn't exist in L1, read from L2.
    // If key exists in L2, write back to L1 then return.
    // Otherwise, not found.
    def doRead(req: CacheRequest): CacheReadResult = {
        val layer1OfPID = layer1.get(req.pid)
        if (keyExists(req.key, layer1OfPID, historyClock)){
                {value: layer1OfPID.get(req.key), readLayer1: true}
        } else {
            if (keyExists(req.key, layer2, historyClock)) {
                {value: layer2.get(req.key), readLayer1: false}
            } else {
                {value: NotFound, readLayer1: false}
            }
        }
    }

    action handleRead(req: CacheRequest): bool = all {
        val resp = doRead(req)
        all {
            any {
                all {
                    resp.readLayer1,
                    layer1' = layer1,
                    layer2' = layer2,
                },
                all {
                    not(resp.readLayer1),
                    layer1' = layer1.setBy(req.pid, layer => layer.put(req.key, resp.value)),
                    layer2' = layer2,
                }
            },
            responses' = responses.union(Set({
                tpe: "read", key: req.key, value: resp.value, readTime: historyClock
            })),
            history' = history.append({
                tpe: "read", 
                key: req.key, 
                value: resp.value.value,
                valueExpire: resp.value.expire,
                time: historyClock,
            }),
        }
    }

    action handleWrite(req: CacheRequest): bool = all {
        layer2' = layer2.put(req.key, {value: req.value, expire: historyClock + DefaultExpireDuration}),

        layer1' = layer1.setBy(req.pid, layer => layer.put(req.key, {
            value: req.value,
            expire: historyClock + DefaultExpireDuration,
        })),

        history' = history.append({
            tpe: "write", 
            key: req.key,
            value: req.value,
            valueExpire: 0,
            time: historyClock,
        }),
        responses' = responses,
    }

    action serverProc = all {
        requests.size() > 0,
        nondet req = oneOf(requests)
        all {
            if (req.tpe == "R") {
                handleRead(req)
            } else {
                handleWrite(req)
            },
            requests' = requests.exclude(Set(req)),
        },
        historyClock' = historyClock + 1,
    }

    // INIT:
    action init = {
        all {
            requests' = Set(),
            responses' = Set(),
            
            historyClock' = 1,
            history' = [],

            layer1' = ClientProcesses.mapBy(pid => Map("a" -> {value: "1", expire: 1 + DefaultExpireDuration})),
            layer2' = Map("a" -> {value: "1", expire: 1 + DefaultExpireDuration}),
        }
    }

    // STEPS:
    action step = any {
        clientProc,
        serverProc,
    }

    //**********************************************************
    // CORRECTNESS
    // 1. Safety Properties / Invariants
    //**********************************************************

    // Any read returns the latest written value. Formally:
    //
    // for any i, j in history:
    //      if i < j and i is a write(k, v) and j is a read(k, v)
    //          then i.time < j.time
    //
    val strongConsistency: bool = {
        val idx = history.indices()
        idx.forall(i => {
            idx.forall(j => {
                i < j
                and history[i].tpe == "write"
                and history[j].tpe == "read"
                and history[i].key == history[j].key
                and history[i].value == history[j].value

                implies history[i].time < history[j].time
            })
        })
    }

    // Any read returns non-expired value
    val validity: bool = {
        val idx = history.indices()
        idx.forall(i => {
            history[i].tpe == "read"
            and history[i].value != NotFound.value

            implies history[i].time < history[i].valueExpire
        })
    }

    val safety: bool = {
        strongConsistency
        and validity
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