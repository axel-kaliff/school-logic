verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof, Proof, []), !.


get_value([_, Head, _], Head).
get_nr([Nr, _, _], Nr).



first_in_scope([Head | _], Head).


last_in_scope([Head | []], Head).
last_in_scope([_| Tail], Head) :- last_in_scope(Tail, Head).



%% checks that the goal of the proof is the last line
valid_goal(Goal, Proof) :-
    last_in_scope(Proof, Row),
    get_value(Row, Value),
    Goal = Value, !.

%% checks if premise is given
valid_premise(_, []):- fail.
valid_premise(Value, [Value | _]).
valid_premise(Value, [_ | Tail]) :- valid_premise(Value, Tail).


%% pattern match for a list (e.g. box) within the scope, if so it unifies with free variabel
box_from_row(_, [], _) :- fail.
box_from_row([Nr, Value, _],         [ [ [Nr, Value, _] | BoxTail ] | _],          [[Nr, Value, _] | BoxTail]).
box_from_row([Nr, Value, _], [ _ | Tail], Box) :- 
    box_from_row([Nr, Value, _], Tail, Box).



exists_above(_, [], _) :- fail.
exists_above(Nr, [[Nr, Value, _] | _], Value).
exists_above(Nr, [_ | Tail], Row) :- exists_above(Nr, Tail, Row).    

%% Basecase
%% Returns true if scope is empty
valid_proof(_, _, [], _) :- !.

% imp int
valid_proof(Prems, Proof, [[Row, imp(A,B), impint(X,Y)] | Tail], Scope) :-
    box_from_row([X, A, _], Scope, Box),
    %%unnecessary since this is checked in box_from_row
    %%first_in_scope(Box, [X, A, _]),
    last_in_scope(Box, [Y, B, _]),
    valid_proof(Prems, Proof, Tail, [[Row, imp(A,B), impint(X,Y)] | Scope]).

    %% imp el
valid_proof(Prems, Proof, [[Row, Value, impel(X,Y)] | Tail], Scope) :-
    exists_above(X, Scope, Copy1),
    exists_above(Y, Scope, imp(Copy1, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X,Y)] | Scope]).   



%% Case where it matches for the characteristic signature of 
%% a box. It will be a list in place of a proof-row inside the proof-list.
%% Also, the rule of the row will be an assumption
valid_proof(Prems, Proof, [[[Row, Value, assumption] | BoxTail] | Tail], Scope) :-
    valid_proof(Prems, Proof, BoxTail, [[Row, Value, assumption] | Scope]),
    valid_proof(Prems, Proof, Tail, [[[Row, Value, assumption] | BoxTail] | Scope]).


%% calls predicate valid_premise to see if the supposed premise was given 
valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], Scope) :-
    valid_premise(Value, Prems),
    valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | Scope]).


%% or int 1
valid_proof(Prems, Proof, [[Row, or(A,B), orint1(X)] | Tail], Scope) :-
    exists_above(X, Scope, A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | Scope]).


%% or int 2
valid_proof(Prems, Proof, [[Row, or(A,B), orint2(X)] | Tail], Scope) :-
    exists_above(X, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | Scope]).

%% or el
valid_proof(Prems, Proof, [[Row, Value, orel(R, A, B, X, Y)] | Tail], Scope) :- 
    exists_above(R, Scope, or(P,Q)),
    box_from_row([A, P, _], Scope, FirstBox),
    box_from_row([X, Q, _], Scope, SecondBox),
    first_in_scope(FirstBox, [A, P, _]),
    first_in_scope(SecondBox, [X, Q, _]),
    last_in_scope(FirstBox, [B, Value, _]),
    last_in_scope(SecondBox, [Y, Value, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, orel(R, R, B, X, Y)] | Scope]).



%% copy
valid_proof(Prems, Proof, [[Row, Value, copy(X)] | Tail], Scope) :-
    exists_above(X, Scope, Value),
    valid_proof(Prems, Proof, Tail, [[Row, Value, copy(X)] | Scope]).


%% and int
valid_proof(Prems, Proof, [[Row, and(A,B), andint(X,Y)] | Tail], Scope) :-
    exists_above(X, Scope, A),
    exists_above(Y, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, and(A,B), andint(X,Y)] | Scope]).

%% and el 1
valid_proof(Prems, Proof, [[Row, Value, andel1(X)] | Tail], Scope) :-
    exists_above(X, Scope, and(Value, _)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel1(X)] | Scope]).

%% and el 2
valid_proof(Prems, Proof, [[Row, Value, andel2(X)] | Tail], Scope) :-
    exists_above(X, Scope, and(_, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel2(X)] | Scope]).

%% neg int
valid_proof(Prems, Proof, [[Row, neg(A), negint(X,Y)] | Tail], Scope) :-
    box_from_row([X, A, _], Scope, Box),
    first_in_scope(Box, [X, A, _]),
    last_in_scope(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, neg(A), negint(X,Y)] | Scope]).

%% neg el
valid_proof(Prems, Proof, [[Row, cont, negel(X,Y)] | Tail], Scope) :-
    exists_above(X, Scope, A),
    exists_above(Y, Scope, neg(A)),
    valid_proof(Prems, Proof, Tail, [[Row, cont, negel(X,Y)] | Scope]).


%% neg neg int
valid_proof(Prems, Proof, [[Row, Value, negnegint(X)] | Tail], Scope) :-
    exists_above(X, Scope, Copy), neg(neg(Copy)) = Value,
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegint(X)] | Scope]).


%% neg neg el
valid_proof(Prems, Proof, [[Row, Value, negnegel(X)] | Tail], Scope) :-
    exists_above(X, Scope, neg(neg(Value))), 
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegel(X)] | Scope]).


%% cont el
valid_proof(Prems, Proof, [[Row, Value, contel(X)] | Tail], Scope) :-
    exists_above(X, Scope, cont),
    valid_proof(Prems, Proof, Tail, [[Row, Value, contel(X)] | Scope]).



%% MT
valid_proof(Prems, Proof, [[Row, neg(Value), mt(X,Y)] | Tail], Scope) :-
    exists_above(X, Scope, imp(Value,B)),
    exists_above(Y, Scope, neg(B)),
    valid_proof(Prems, Proof, Tail, [[Row, neg(Value), mt(X,Y)] | Scope]).

%% PBC
valid_proof(Prems, Proof, [[Row, Value, pbc(X, Y)] | Tail], Scope) :-
    box_from_row([X, neg(Value), _], Scope, Box),
    first_in_scope(Box, [X, neg(Value), _]),
    last_in_scope(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, pbc(X,Y)] | Scope]). 

%% LEM
valid_proof(Prems, Proof, [[Row, or(A, B), lem] | Tail], Scope) :-
    A = neg(B) ; B = neg(A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), lem] | Scope]).