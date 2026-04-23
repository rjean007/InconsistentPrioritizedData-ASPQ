
{inRepair(Id)}:-reachable(Id).

solved(C):-inConf(C,Id1), not inRepair(Id1).
:- conf(C), not solved(C).

violatedCause(C) :- inCause(C,Id), not inRepair(Id).
satisfied :- cause(C), not violatedCause(C).

valid(A) :- reachable(A), inRepair(A).
invalid_att(X, A) :- reachable(A), attacks(X, A), inConf(X, B), not inRepair(B), not A = B.
valid(A) :- reachable(A), conf(X), not inRepair(A), attacks(X, A), not invalid_att(X, A).
:- reachable(A), not valid(A).

#show .