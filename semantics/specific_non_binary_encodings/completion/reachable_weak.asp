weak_attacks(C, Id) :- conf(C), inConf(C, Id), inConf(C, Id1), Id != Id1, not pref(Id, Id1).
reachable(Id) :- cause(C), inCause(C,Id).
reachable(Id1) :- inConf(C, Id), weak_attacks(C, Id), reachable(Id), inConf(C, Id1).