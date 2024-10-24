module twolayeredcache {
    // TYPE DEFINITIONS
    type CacheRequest = {tpe: str, key: str, value: str}
    type CacheResponse = {tpe: str, key: str, value: str}
    type CacheLayer = str -> str
    // tpe: "read" or "write"
    type HistoryEntry = { tpe: str, key: str, value: str, time: int }

    // FUNCTIONAL LAYER:
    // Values and functions that are state-independent
    pure val NotFound: str = "not_found"
    pure def newRequest(): CacheRequest = {
        val tpe = Set("R", "W").chooseSome()
        val key = Set("a", "b", "c").chooseSome()
        val value = Set("john", "tom", "carl", "alice", "rick").chooseSome()
        {tpe: tpe, key: key, value: value}
    }

    pure def forallListItem(l: List[a], pred: a => bool): bool =
        l.foldl(true, (result, elem) => result and pred(elem))
    
    // STATE MACHINE:
    // State-dependent definitions and actions
    var layer1: CacheLayer
    var layer2: CacheLayer

    var requests: List[CacheRequest]
    var responses: List[CacheResponse]

    var history: List[HistoryEntry]
    var traceTime: int

    // HELPERS:
    // Functions for convenience
    def require(cond: bool): bool = cond

    // ACTIONS:
    action receiveResponse = all {
        responses.length() > 0,
        val resp = responses.head()
        all {
            responses' = responses.tail(),
            history' = history.append({
                tpe: "read", 
                key: resp.key, 
                value: resp.value, 
                time: traceTime,
            }),
        },
        requests' = requests,
    }

    action sendRequest = all {
        val req = newRequest
        requests' = requests.append(req),

        responses' = responses,
        history' = history,
    }

    action serverProc = all {
        any {
            receiveResponse,
            sendRequest,
        },
        layer1' = layer1,
        layer2' = layer2,
        traceTime' = traceTime,
    }

    action handleRead(req: CacheRequest): bool = all {
        // if this key doesn't exist
        if (not(layer1.keys().contains(req.key))) {
            all {
                responses' = responses.append({tpe: req.tpe, key: req.key, value: NotFound}),
            }
        } else {
            val v = layer1.get(req.key)
            all {
                responses' = responses.append({tpe: req.tpe, key: req.key, value: v}),
            }
        },

        layer1' = layer1,
        layer2' = layer2,
        history' = history,
        traceTime' = traceTime + 1,
    }

    action handleWrite(req: CacheRequest): bool = all {
        layer2' = layer2.put(req.key, req.value),
        layer1' = layer1.put(req.key, req.value),

        history' = history.append({
            tpe: "write", 
            key: req.key,
            value: req.value,
            time: traceTime,
        }),
        responses' = responses,
        traceTime' = traceTime + 1,
    }

    action layer1Proc = all {
        requests.length() > 0,
        {
            val req = requests.head()
            if (req.tpe == "R") {
                handleRead(req)
            } else {
                handleWrite(req)
            }
        },
        requests' = requests.tail(),
    }

    // INIT:
    action init = all {
        layer1' = Map("a" -> "1"),
        layer2' = Map("a" -> "1"),
        requests' = [],
        responses' = [],
        traceTime' = 1,
        history' = [],
    }

    // STEPS:
    action step = any {
        serverProc,
        layer1Proc,
    }

    // CORRECTNESS:

    // 1. Safety Properties / Invariants


    // for any i, j in history:
    //      if i < j and i is a write(k, v) and j is a read(k, v)
    //          then i.time < j.time
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

    // 2. Liveness Properties / Temporal


    // TESTS:
    // run initAndStepTest = init.then(step)
}