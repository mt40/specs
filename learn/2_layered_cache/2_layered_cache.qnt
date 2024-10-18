module twolayeredcache {
    // TYPE DEFINITIONS
    type CacheVal = str
    type CacheRequest = (str, str, CacheVal)

    // FUNCTIONAL LAYER:
    // Values and functions that are state-independent
    pure val querySet: Set[CacheRequest] = Set(
        ("read", "a", ""),
        ("write", "a", "1")
    )
    
    // STATE MACHINE:
    // State-dependent definitions and actions
    var layer1: str -> str
    var layer1WriteLog: List[str]
    // var layer2: str -> str
    var requests: List[CacheRequest]
    var responses: List[CacheVal]

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
        layer1WriteLog' = layer1WriteLog,
    }

    action sendRequest = all {
        nondet req = querySet.oneOf()
        requests' = requests.append(req),
        layer1' = layer1,
        responses' = responses,
        layer1WriteLog' = layer1WriteLog,
    }

    action serverProc = any {
        receiveResponse,
        sendRequest,
    }

    action handleRead(req: CacheRequest): bool = all {
        val v = layer1.get(req._2)
        responses' = responses.append(v),
        layer1' = layer1,
        layer1WriteLog' = layer1WriteLog,
    }

    action handleWrite(req: CacheRequest): bool = all {
        layer1' = layer1.set(req._2, req._3),
        layer1WriteLog' = layer1WriteLog.append(req._3),
        responses' = responses,
    }

    action layer1Proc = all {
        requests.length() > 0,
        {
            val req = requests.head()
            if (req._1 == "read") {
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
        layer1WriteLog' = [],
        requests' = [],
        responses' = [],
    }

    // STEPS:
    action step = any {
        serverProc,
        layer1Proc,
    }

    // CORRECTNESS:
    // 1. Safety Properties / Invariants
    // todo: do this properly by using composite trace
    val strongConsistency: bool = all {
        if(responses.length() > 0 and layer1WriteLog.length() > 0) {
            val latestReadResp = responses[responses.length() - 1]
            val latestWriteVal = layer1WriteLog[layer1WriteLog.length() - 1]
            latestReadResp == latestWriteVal
        } else {
            true
        }
    }

    val strongConsistency2: bool = or {
        writeTrace == [],
        and {
            writeTrace == [.., ("a", x, t)],
            or {
                readTrace == [.., ("a", _, t' < t)],
                readTrace == [.., ("a", x, t' >= t)],
            }
        }
    }

    // 2. Liveness Properties / Temporal


    // TESTS:
    run initAndStepTest = init.then(step)
}