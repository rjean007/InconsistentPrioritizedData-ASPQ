reachable(Id) :- cause(C), inCause(C,Id).
reachable(Beta) :- conf(C), inConf(C,Alpha), reachable(Alpha), inConf(C,Beta), not pref(Alpha,Beta).

{inRepair(Id)}:-reachable(Id).

solved(C):-inConf(C,Id1), not inRepair(Id1).
:- conf(C), not solved(C).

violatedCause(C) :- inCause(C,Id), not inRepair(Id).
satisfied :- cause(C), not violatedCause(C).

valid(A) :- reachable(A), inRepair(A).
valid(A) :- reachable(A), not inRepair(A), conf(X), inConf(X, A), not pref(A,B), inConf(X, B), inRepair(B).
:- reachable(A), not valid(A).

#show .