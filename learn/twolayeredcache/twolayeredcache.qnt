module twolayeredcache {
    // TYPE DEFINITIONS
    type CacheRequest = {tpe: str, key: str, value: str}
    type CacheResponse = {tpe: str, key: str, value: str}
    type CacheLayer = str -> str
    type WriteTraceEntry = { key: str, value: str, time: int }
    type ReadTraceEntry = { key: str, value: str, time: int }

    // FUNCTIONAL LAYER:
    // Values and functions that are state-independent
    pure val NotFound: str = "not_found"
    pure val requestSet: Set[CacheRequest] = Set(
        {tpe: "R", key: "a", value: ""},
        {tpe: "R", key: "b", value: ""},
        {tpe: "R", key: "c", value: ""},
        {tpe: "W", key: "a", value: "aaa"},
        {tpe: "W", key: "b", value: "bbb"},
        {tpe: "W", key: "c", value: "ccc"}
    )
    pure def forallListItem(l: List[a], pred: a => bool): bool =
        l.foldl(true, (result, elem) => result and pred(elem))
    
    // STATE MACHINE:
    // State-dependent definitions and actions
    var layer1: CacheLayer
    var requests: List[CacheRequest]
    var responses: List[CacheResponse]
    var writeTrace: List[WriteTraceEntry]
    var readTrace: List[ReadTraceEntry]
    var traceTime: int

    // HELPERS:
    // Functions for convenience
    def require(cond: bool): bool = cond

    // ACTIONS:
    action receiveResponse = all {
        responses.length() > 0,
        {
            val resp = responses.head()
            responses' = responses.tail()
        },
        layer1' = layer1,
        requests' = requests,
        readTrace' = readTrace,
        writeTrace' = writeTrace,
        traceTime' = traceTime,
    }

    action sendRequest = all {
        nondet req = requestSet.oneOf()
        requests' = requests.append(req),
        layer1' = layer1,
        responses' = responses,
        readTrace' = readTrace,
        writeTrace' = writeTrace,
        traceTime' = traceTime,
    }

    action serverProc = any {
        receiveResponse,
        sendRequest,
    }

    action handleRead(req: CacheRequest): bool = {
        if (not(layer1.keys().contains(req.key))) {
            all {
                responses' = responses.append({tpe: req.tpe, key: req.key, value: NotFound}),
                readTrace' = readTrace.append({key: req.key, value: NotFound, time: traceTime}),
                layer1' = layer1,
                traceTime' = traceTime + 1,
                writeTrace' = writeTrace,
            }
        } else {
            val v = layer1.get(req.key)
            all {
                responses' = responses.append({tpe: req.tpe, key: req.key, value: v}),
                readTrace' = readTrace.append({key: req.key, value: v, time: traceTime}),
                layer1' = layer1,
                traceTime' = traceTime + 1,
                writeTrace' = writeTrace,
            }
        }
    }

    action handleWrite(req: CacheRequest): bool = all {
        layer1' = layer1.put(req.key, req.value),
        writeTrace' = writeTrace.append({key: req.key, value: req.value, time: traceTime}),
        responses' = responses,
        traceTime' = traceTime + 1,
        readTrace' = readTrace,
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
        requests' = [],
        responses' = [],
        writeTrace' = [],
        readTrace' = [],
        traceTime' = 1,
    }

    // STEPS:
    action step = any {
        serverProc,
        layer1Proc,
    }

    // CORRECTNESS:

    // 1. Safety Properties / Invariants

    // either:
    // - write_trace is empty
    // - for all read=(K, V, time):
    //      let S is sequence of write=(K,*,t'), t' < t, then:
    //          S is empty
    //          \/ S[last] = (K, V, t')
    val strongConsistency: bool = or {
        writeTrace == [],
        readTrace == [],
        forallListItem(readTrace, r => {
            val writes = writeTrace.select(w => w.key == r.key and w.time < r.time)
            
            writes == [] 
            or writes[writes.length() - 1].value == r.value
        })
    }

    // 2. Liveness Properties / Temporal


    // TESTS:
    run initAndStepTest = init.then(step)
}