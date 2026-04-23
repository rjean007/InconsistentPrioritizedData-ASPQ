{inRepair(Id)}:-reachable(Id).

solved(C):-inConf(C,Id1), not inRepair(Id1).
:- conf(C), not solved(C).

violatedCause(C) :- inCause(C,Id), not inRepair(Id).
satisfied :- cause(C), not violatedCause(C).

pref_comp(A, B) :- reachable(A), reachable(B), pref(A, B).
1{pref_comp(A, B); pref_comp(B, A)}1 :- reachable(A), reachable(B), inConf(X, A), inConf(X, B), not pref(A, B), not pref(B, A), not A = B.
trans_cl_comp(A, B) :- pref_comp(A, B).
trans_cl_comp(A, B) :- trans_cl_comp(A, Y), pref_comp(Y, B).
:- trans_cl_comp(A, A).

valid(A) :- reachable(A), inRepair(A).
invalid_att(X, A) :- reachable(A), not inRepair(A), inConf(X, A), not A = B, inConf(X, B), not inRepair(B).
invalid_att(X, A) :- reachable(A), not inRepair(A), inConf(X, A), inConf(X, B), not A = B, pref_comp(A, B).
valid(A) :- reachable(A), not inRepair(A), inConf(X, A), not invalid_att(X, A).
:- reachable(A), not valid(A).

#show .