% For SICStus, uncomment line below: (needed for member/2)
use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid. %
% (T,L), S |- F
%
%
% :- discontiguous(check/5).

% Literals
check(_, L, S, [], F)      :-
  member([S | [Labels]], L),
  member(F,Labels).

check(T, L, S, [], neg(F)) :-
  \+ check(T,L,S,[],F).



% And
% checks that F and G both are true in S
check(T, L, S, [], and(F,G)) :-
  check(T,L,S,[],F),
  check(T,L,S,[],G).


% Or
% checks that either F or G is true in S
check(T,L,S,[],or(F,G)) :-
  check(T,L,S,[],F);
  check(T,L,S,[],G).



% AX Alla S'
check(T,L,S,[],ax(F)) :-
  member([S | [Adjacents]], T),

  % checking ax predicate on adjacents

  
  ax(T,L,Adjacents,[],F).

ax(T,L,[FirstAdjacent,NextAdjacent|AdjacentTail],[],F) :-

% check adjacents one by one
  check(T,L,FirstAdjacent,[],F),
  ax(T,L,[NextAdjacent|AdjacentTail],[],F).

%last adjacent
ax(T,L,[LastAdjacent|[]],[],F) :-
  check(T,L,LastAdjacent,[],F).





% EX Minst en S'
check(T, L, S, [], ex(F)) :-
  member([S | [Adjacents]],T),
  member(L0,Adjacents),
  check(T,L,L0,[],F).



% AG
check(T,L,S,Visited,ag(F)) :-
  \+ member(S, Visited),
  member([S,Adjacents],T),
  check(T,L,S,[],F),
  ag(T,L,Adjacents,[S|Visited],F).

ag(T,L,[FirstAdjacent,NextAdjacent|AdjacentTail],Visited,F) :-
  check(T,L,FirstAdjacent,Visited,ag(F)),
  ag(T,L,[NextAdjacent|AdjacentTail],Visited,F).

ag(T,L,[FirstAdjacent|[]],Visited,F) :-
  check(T,L,FirstAdjacent,Visited,ag(F)).

check(_,_,S,Visited,ag(_)) :-
  member(S,Visited).



%EF
check(T,L,S,U,ef(F)) :-
  \+ member(S,U),
  check(T,L,S,[],F).

check(T,L,S,U,ef(F)) :-
  \+ member(S,U),
  member([S,Adjacents],T),
  member(L0,Adjacents),
  check(T,L,L0,[S|U],ef(F)).



% AF
check(T,L,S,Visited,af(F)) :-
  \+ member(S,Visited),
  check(T,L,S,[],F).

check(T,L,S,Visited,af(F)) :-
  \+ member(S,Visited),
  member([S,Adjacents],T),
  af(T,L,Adjacents,[S|Visited],F).

af(T,L,[FirstAdjacent,NextAdjacent|AdjacentTail],Visited,F) :-
  check(T,L,FirstAdjacent,Visited,af(F)),
  af(T,L,[NextAdjacent|AdjacentTail],Visited,F).

af(T,L,[FirstAdjacent|[]],Visited,F) :-
  check(T,L,FirstAdjacent,Visited,af(F)).



% EG
% sann om S är medlem i U
check(_,_,S,U, eg(_)) :-
  member(S,U).

% 
check(T,L,S,U,eg(F)) :-
% om den inte är member i U
  \+ member(S,U),

  %kolla om F stämmer i S
  check(T,L,S,[],F),

  %hämta Adjacents lista från T genom member
  member([S | [Adjacents]],T),


  member(ArbitraryAdjacent,Adjacents),

  %forstätt med S i U (fortsätter även om F har varit sann tidigare)
  check(T,L,ArbitraryAdjacent,[S|U],eg(F)).


