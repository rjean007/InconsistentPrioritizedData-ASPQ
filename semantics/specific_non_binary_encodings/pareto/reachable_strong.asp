reachable(Id) :- cause(C), inCause(C,Id).
reachable(Beta) :- conf(C), attacks(C,Alpha), reachable(Alpha), inConf(C,Beta).
