module twolayeredcache {
    // TYPE DEFINITIONS
    type CacheRequest = {tpe: str, key: str, value: str}
    type CacheResponse = {tpe: str, key: str, value: str}
    type CacheLayer = str -> str
    type WriteTraceEntry = { key: str, value: str, time: int }
    type ReadTraceEntry = { key: str, value: str, time: int }

    // FUNCTIONAL LAYER:
    // Values and functions that are state-independent
    pure val requestSet: Set[CacheRequest] = Set(
        {tpe: "R", key: "a", value: ""},
        {tpe: "W", key: "a", value: "1"}
    )
    
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
        // layer1WriteLog' = layer1WriteLog,
    }

    action sendRequest = all {
        nondet req = requestSet.oneOf()
        requests' = requests.append(req),
        layer1' = layer1,
        responses' = responses,
        // layer1WriteLog' = layer1WriteLog,
        readTrace' = readTrace,
        writeTrace' = writeTrace,
        traceTime' = traceTime,
    }

    action serverProc = any {
        receiveResponse,
        sendRequest,
    }

    action handleRead(req: CacheRequest): bool = {
        val v = layer1.get(req.key)
        all {
            responses' = responses.append({tpe: req.tpe, key: req.key, value: v}),
            layer1' = layer1,
            readTrace' = readTrace.append({key: req.key, value: v, time: traceTime}),
            traceTime' = traceTime + 1,
            writeTrace' = writeTrace,
        }
    }

    action handleWrite(req: CacheRequest): bool = all {
        layer1' = layer1.set(req.key, req.value),
        responses' = responses,
        writeTrace' = writeTrace.append({key: req.key, value: req.value, time: traceTime}),
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
        // for simplicity, ignore not-found case
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
    // - write_trace has last write=(key, val, time)
    //   /\ (
    //      read_trace is empty
    //      \/ read_trace has last read=(key, val, t') and t' >= t
    //      \/ read_trace has last read=(key', val', t') and t' < t, key' & val' are anything
    //   )
    val strongConsistency: bool = or {
        writeTrace == [],
        readTrace == [],
        val lastWrite = writeTrace[writeTrace.length()-1]
        val lastRead = readTrace[readTrace.length()-1]
        or {
            lastRead.time < lastWrite.time,
            and {
                lastWrite.key == lastRead.key,
                lastWrite.value == lastRead.value,
            },
        },
    }

    // 2. Liveness Properties / Temporal


    // TESTS:
    run initAndStepTest = init.then(step)
}