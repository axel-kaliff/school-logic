verify(InputFileName):-
  see(InputFileName), read(Prems), read(Goal), read(Proof),
  seen,
  valid_proof(Goal, Proof),
  iterate(Prems, Proof, Proof).

  valid_goal(Goal, Proof) :-
    get_last(Proof, Row),
    get_value(Row, Value),
    Goal = Value, !.


%% is this necessary to the lab?
valid_premise(_, []) :- fail.
valid_premise(Value, [Value | _]).
valid_premise(Value, [_ | Tail]) :- valid_premise(Value, Tail).





get_first([Head | _], Head).


get_last([Head | []], Head).
get_last([_| Tail], Head) :- get_last(Tail, Head).


get_value([_, Head, _], Head).
get_nr([Nr, _, _], Nr).


box_in_scope(_, [], _) :- fail.
box_in_scope([Nr, Value, _], [[[Nr, Value, _] | BoxTail] | _], [[Nr, Value, _] | BoxTail]).
box_in_scope([Nr, Value, _], [_ | Tail], Box) :-
  box_in_scope([Nr, Value, _], Tail, Box).

peek(_, [], _) :- fail.
peek(Nr, [[Nr, Value, _] | _], Value).
peek(Nr, [_ | Tail], Row) :- peek(Nr, Tail, Row).

valid_proof(_, _, [], _) :- !.

valid_proof(Prems, Proof, [[[Row, Value, assumption] | BoxTail] | Tail], Scope) :-
    valid_proof(Prems, Proof, BoxTail, [[Row, Value, assumption] | Scope]),
    valid_proof(Prems, Proof, Tail, [[[Row, Value, assumption] | BoxTail] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], Scope) :-
  valid_premise(Value, Prems),
  valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | Scope]).

valid_proof(Prems, Proof, [[Row, Value, impel(X, Y)] | Tail], Scope) :-
  peek(X, Scope, Copy1),
  peek(y, Scope, imp(Copy1, Value)),
  valid_preef(Prems, Proof, Tail, [[Row, Value, impel(X, Y)] | Scope]).





valid_proof(Prems, Proof, [[Row, imp(A, B), impint(X, Y)] | Tail], Scope) :-
  box_in_scope([X, A, _], Scope, Box),
  get_first(Box, [X, A, _]),
  get_last(Box, [Y, B, _]),
  valid_proof(Prems, Proof, Tail, [[Row, imp(A, B), impint(X, Y)] | Scope]).



valid_proof(Prems, Proof, [[Row, and(A,B), andint(X,Y)] | Tail], Scope) :-
  peek(X, Scope, A),
  peek(Y, Scope, B),
  valid_proof(Prems, Proof, Tail, [[Row, and(A, B), andint(X, Y)] | Scope]).




