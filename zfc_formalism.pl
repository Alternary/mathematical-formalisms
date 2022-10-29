/*string("'").
string("*").
string("¤").
string("!").
string(">").
string("§").
string("#").
string(X) :- string_concat(A,B,X), string(A), string(B).*/


%I need to make a tree datatype for each term
isCounter([counter,A]) :- isCounter_(A).
isCounter_("'").
isCounter_(X) :- isCounter_(A), string_concat(A,"'",X).
isArity([arity,A]) :- isArity_(A).
isArity_("*").
isArity_(X) :- string_concat(A,"*",X), isArity_(A).
isAtomic_proposition([atomic_proposition,"¤",A]) :- isCounter(A).
isIndividual([individual,"¤¤",A]) :- isCounter(A).
isFunction([function,"¤¤¤",A,B]) :- isCounter(A), isArity(B).
isPredicate([predicate,"¤¤¤¤",A,B]) :- isCounter(A), isArity(B).

%here I have function,"¤¤¤", which means "¤¤¤" is redundant but I guess I'll keep it just in case I need it later

%isFunction([function,"¤¤¤",[counter,"'''''"],[arity,"****"]]).
%isTerm([term,[function,"¤¤¤",[counter,"'''''"],[arity,"*"]],[individual,"¤¤",[counter,"''"]]]).     %of one input
%isInput([input,[[individual,"¤¤",[counter,"''"]],[individual,"¤¤",[counter,"''"]]]]).
%isTerm([term,[function,"¤¤¤",[counter,"'''''"],[arity,"**"]],[input,[[individual,"¤¤",[counter,"''"]],[individual,"¤¤",[counter,"''"]]]]]).     %of many inputs

%should I instead of lists use tuples? well I like the "[" symbol as opposed to ordinary parentheses which are used elsewhere as well

isTerm(A) :- isIndividual(A).
isTerm([term,[function,"¤¤¤",A,[arity,"*"]],B]) :- isCounter(A), isTerm(B).
isTerm([term,[function,"¤¤¤",A,[arity,F]],[input,[C,D]]]) :-
  string_concat(E,"*",F), [arity,E] = B,
  isCounter(A), isArity(B), isInput(C), isTerm(D), isTerm([term,[function,"¤¤¤",A,B],C]).
isInput(A) :- isTerm(A).
isInput([input,[A,B]]) :- isInput(A), isTerm(B). %so [[[x,y],z],w] is the form of an input

isWff(A) :- isAtomic_proposition(A).
isWff([wff,[predicate,"¤¤¤¤",A,[arity,"*"]],B]) :- isCounter(A), isTerm(B).
isWff([wff,[predicate,"¤¤¤¤",A,[arity,F]],[input,[C,D]]]) :-
  string_concat(E,"*",F), [arity,E] = B,
  isCounter(A), isArity(B), isInput(C), isTerm(D), isTerm([term,[function,"¤¤¤",A,B],C]).
isWff([wff,"!",A]) :- isWff(A).
isWff([wff,">",A,B]) :- isWff(A), isWff(B).
isWff([wff,"§",A,B]) :- isIndividual(A), isWff(B).

%isProviso([proviso,[individual,"¤¤",[counter,"'"]],"#",[individual,"¤¤",[counter,"''"]]]).
isProviso([proviso,A,"#",[individual,"¤¤",[counter,E]]]) :-
  string_concat(C,D,E), [counter,D] = B, [individual,"¤¤",[counter,C]] = A, isIndividual(A), isCounter(B).
isProviso([proviso,[individual,"¤¤",[counter,E]],"#",A]) :-
  string_concat(C,D,E), [counter,D] = B, [individual,"¤¤",[counter,C]] = A, isIndividual(A), isCounter(B).
isProviso([proviso,A,"#",B]) :- isIndividual(A), isAtomic_proposition(B).
isProviso([proviso,A,"#",[input,[B,C]]]) :-
  isIndividual(A), isInput(B), isTerm(C), isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]). %defining input proviso
isProviso([proviso,A,"#",[term,B,C]]) :-
  isIndividual(A), isFunction(B), isInput(C), isProviso([proviso,A,"#",C]). %here we define cases for functions and predicates directly as they are used
isProviso([proviso,A,"#",[wff,B,C]]) :-
  isIndividual(A), isPredicate(B), isInput(C), isProviso([proviso,A,"#",C]).
isProviso([proviso,A,"#",[wff,"!",B]]) :-
  isIndividual(A), isWff(B), isProviso([proviso,A,"#",B]).
isProviso([proviso,A,"#",[wff,">",B,C]]) :-
  isIndividual(A), isWff(B), isWff(C), isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]).
isProviso([proviso,A,"#",[wff,"§",B,C]]) :-
  isIndividual(A), isIndividual(B), isWff(C), isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]).
%isProviso_group(A) :- isProviso(A).
%isProviso_group([proviso_group,A,"#",B]) :- isProviso_group(A), isProviso_group(B). %these became just so unwieldy

isTheorem1([wff,">",[wff,">",[wff,">",[wff,">",[wff,">",A,B],[wff,">",[wff,"!",C],[wff,"!",D]]],C],E],[wff,">",[wff,">",E,A],[wff,">",D,A]]]) :-
  isWff(A), isWff(B), isWff(C), isWff(D), isWff(E).
%isTheorem2(B) :- isWff(A), isWff(B), isTheorem16(A), isTheorem17([wff,">",A,B]).
%manually input into modus ponens the input theorems, which is how it should go anyway, really, the result of modus ponens shouldn't go straight back to the pool, it should be saved as an instance, so that we don't start going through modus ponens aimlessly, obviously
isTheorem2_2(A,B) :- isWff(A), isWff(B), isTheorem(A), isTheorem([wff,">",A,B]). %omg it hecking works
%isTheorem2_3(A,C,B) :- isWff(A), isWff(B), isTheorem(A), isTheorem(C), [wff,">",A,B] = C. % here we input the two theorems and out comes b
%isTheorem2_4(A,C,B) :- [wff,">",A,B] = C, isWff(A), isWff(B), isTheorem(A), isTheorem(C). % here we input the two theorems and out comes b
isTheorem2_5(A,C,B) :- [wff,">",A,B] = C, isWff(A), isWff(B). %here we just derive a conclusion from two hypotheses
isTheorem2(A,C,B) :- [wff,">",A,B] = C, isWff(A), isWff(B), isTheorem(A), isTheorem(C). % here we input the two theorems and out comes b

isTheorem3([wff,">",[wff,"§",A,[wff,">",B,C]],[wff,">",[wff,"§",A,B],[wff,"§",A,C]]]) :- isIndividual(A), isWff(B), isWff(C).
isTheorem4([wff,">",B,[wff,"§",A,B]]) :- isIndividual(A), isWff(B), isProviso([proviso,A,"#",B]).
%isTheorem5([wff,"§",A,B]) :- isIndividual(A), isWff(B), isTheorem(B).
%isTheorem5_2(A,B,C) :- [wff,"§",A,B] = C, isIndividual(A), isWff(B), isTheorem(B). %we also have to specify the individual we wanna use
isTheorem5(A,B,C) :- [wff,"§",A,B] = C, isIndividual(A), isWff(B), isTheorem(B). %we also have to specify the individual we wanna use
isTheorem5_3(A,B,C) :- [wff,"§",A,B] = C, isIndividual(A), isWff(B). %here we just dirve a conclusion from a hypothesis

isTheorem6([wff,"!",[wff,"§",A,[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,[A,B]]]]]]) :-
  individual(A), term(B).
isTheorem7([wff,">",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,A,B]],[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,A,C]],[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,B,C]]]]) :-
  isIndividual(A), isTerm(B).

isTheorem8([wff,">",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,A,B]],[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,C]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,C]]]]) :-
  isIndividual(A), isTerm(B).
isTheorem9([wff,">",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,A,B]],[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,A]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,B]]]]) :-
  isIndividual(A), isTerm(B).
isTheorem10([wff,">",[wff,"§",A,[wff,"!",[wff,">",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,C]]],[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,C]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]]]]]]],[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,B,C]]]) :-
  isIndividual(A), isTerm(B), isTerm(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]).
isTheorem11([wff,"!",[wff,"§",A,[wff,"!",[wff,">",[wff,"!",[wff,"§",B,[wff,"!",[wff,"§",C,[wff,">",D,[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,C,B]]]]]]],[wff,"§",C,[wff,"!",[wff,">",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,A]],[wff,"!",[wff,"§",A,[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,"!",[wff,"§",B,D]]]]]]]],[wff,"!",[wff,">",[wff,"!",[wff,"§",A,[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,"!",[wff,"§",B,D]]]]]]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,A]]]]]]]]]]]) :-
  isIndividual(A), isIndividual(B), isIndividual(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]), isProviso([proviso,B,"#",C]).
isTheorem12([wff,"!",[wff,"§",A,[wff,"!",[wff,"§",B,[wff,">",[wff,"§",A,[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,C]]]],[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,A]]]]]]]) :-
  isIndividual(A), isIndividual(B), isIndividual(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]), isProviso([proviso,B,"#",C]).
isTheorem13([wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,"!",[wff,"§",A,[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,A,B]],[wff,"!",[wff,"§",C,[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,A]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,B]]]]]]]]]]]]) :-
  isIndividual(A), isTerm(B), isIndividual(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]), isProviso([proviso,C,"#",B]).
isTheorem14([wff,"!",[wff,"§",A,[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,A]],[wff,"!",[wff,"§",B,[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,A]],[wff,"!",[wff,"§",C,[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,C]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,A]]]]]]]]]]]]]]]]) :-
  isIndividual(A), isIndividual(B), isIndividual(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,A,"#",C]), isProviso([proviso,B,"#",C]).

isTheorem15([wff,"!",[wff,"§",A,[wff,"!",[wff,"§",B,[wff,"§",C,[wff,">",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,C]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,D]]]]],[wff,"!",[wff,"§",D,[wff,"!",[wff,"§",B,[wff,"!",[wff,">",[wff,">",[wff,"!",[wff,"§",D,[wff,"!",[wff,"!",[wff,">",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,C]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,D]]]]],[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,D]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,D,A]]]]]]]]]]],[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,B,D]]],[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"'"],[arity,"**"]],[input,B,D]],[wff,"!",[wff,"§",D,[wff,"!",[wff,"!",[wff,">",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,C]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,C,D]]]]],[wff,"!",[wff,"!",[wff,">",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,B,D]],[wff,"!",[wff,[predicate,"¤¤¤¤",[counter,"''"],[arity,"**"]],[input,D,A]]]]]]]]]]]]]]]]]]]]]]]]]) :-
  isIndividual(A), isIndividual(B), isIndividual(C), isIndividual(C),
  isProviso([proviso,A,"#",B]), isProviso([proviso,B,"#",C]), isProviso([proviso,A,"#",C]),
  isProviso([proviso,A,"#",D]), isProviso([proviso,B,"#",D]), isProviso([proviso,C,"#",D]).

isTheorem(X) :- isTheorem1(X).
%isTheorem(X) :- isTheorem2(X).
isTheorem(X) :- isTheorem3(X).
isTheorem(X) :- isTheorem4(X).
%isTheorem(X) :- isTheorem5(X).
isTheorem(X) :- isTheorem6(X).
isTheorem(X) :- isTheorem7(X).
isTheorem(X) :- isTheorem8(X).
isTheorem(X) :- isTheorem9(X).
isTheorem(X) :- isTheorem10(X).
isTheorem(X) :- isTheorem11(X).
isTheorem(X) :- isTheorem12(X).
isTheorem(X) :- isTheorem13(X).
isTheorem(X) :- isTheorem14(X).
isTheorem(X) :- isTheorem15(X).


isTheorem(X) :- isTheorem_1(X).
isTheorem(X) :- isTheorem_2(X).
isTheorem(X) :- isTheorem_3(X).

%[wff,">",[atomic_proposition,"¤",[counter,"'"]],[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'"]]]]
%proving A>A
%isTheorem2([wff,">",[atomic_proposition,"¤",[counter,"'"]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'"]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'"]],[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'"]]]]],B).

isTheorem_1([wff,">",A,[wff,">",B,A]]) :- isWff(A), isWff(B).
isTheorem_2([wff,">",[wff,">",A,[wff,">",B,C]],[wff,">",[wff,">",A,B],[wff,">",A,C]]]) :- isWff(A), isWff(B), isWff(C).
isTheorem_3([wff,">",[wff,">",[wff,"!",A],[wff,"!",B]],[wff,">",B,A]]) :- isWff(A), isWff(B).




%making the basic propositional calculus postulates
%theorem16(X) :- atomics_to_string([">",A,">",B,A],X), wff(A), wff(B).


%prolog trace.

%metamath derivations from the meredith axiom
%https://us.metamath.org/mpeuni/merlem1.html
%https://us.metamath.org/mpeuni/meredith.html for general info
%here they are translated
/*

[wff,">",[wff,">",[wff,">",[wff,">",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'''"]]],[wff,"!",[atomic_proposition,"¤",[counter,"''''"]]]]],[wff,"!",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]]]]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'''"]]],[wff,"!",[atomic_proposition,"¤",[counter,"''''"]]]]],[atomic_proposition,"¤",[counter,"'''"]]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'''"]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]]]]

[wff,">",[wff,">",[wff,">",[wff,">",[wff,">",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'''"]]],[wff,"!",[atomic_proposition,"¤",[counter,"''''"]]]]],[wff,"!",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]]]]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'''"]]],[wff,"!",[atomic_proposition,"¤",[counter,"''''"]]]]],[atomic_proposition,"¤",[counter,"'''"]]],[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'''"]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]]]],[wff,">",[wff,">",[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'''"]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,">",[atomic_proposition,"¤",[counter,"''''"]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]]]]

[wff,">",[wff,">",[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'''"]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,">",[atomic_proposition,"¤",[counter,"''''"]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]]]

[wff,">",[wff,">",[wff,">",[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"'''"]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]],[wff,">",[wff,"!",[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,"!",[atomic_proposition,"¤",[counter,"'"]]]]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[wff,">",[atomic_proposition,"¤",[counter,"''''"]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]]],[wff,">",[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"''''"]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[atomic_proposition,"¤",[counter,"'''"]]],[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'''"]]]]]

[wff,">",[wff,">",[wff,">",[atomic_proposition,"¤",[counter,"''''"]],[wff,">",[wff,"!",[atomic_proposition,"¤",[counter,"'"]]],[atomic_proposition,"¤",[counter,"''"]]]],[atomic_proposition,"¤",[counter,"'''"]]],[wff,">",[atomic_proposition,"¤",[counter,"'"]],[atomic_proposition,"¤",[counter,"'''"]]]]

*/




/*
%this is the textual version, which is good to have too

counter("'").
counter(X) :- string_concat(A,"'",X), counter(A).
arity("*").
arity(X) :- string_concat(A,"*",X), arity(A).
atomic_proposition(X) :- string_concat("¤",A,X), counter(A).
individual(X) :- string_concat("¤¤",A,X), counter(A).
function(X) :- atomics_to_string(["¤¤¤",A,B],X), counter(A), arity(B).
predicate(X) :- atomics_to_string(["¤¤¤¤",A,B],X), counter(A), arity(B).

term(A) :- individual(A).
term(X) :- counter(A), term(B), atomics_to_string(["¤¤¤",A,"*",B],X).
term(X) :- atomics_to_string(["¤¤¤",A,"*",B],X), counter(A), term(B).
term(Y) :- atomics_to_string(["¤¤¤",A,B,"*",C,D],Y), term(X), atomics_to_string(["¤¤¤",A,B,C],X), counter(A), arity(B), input(C), term(D).
input(A) :- term(A).
input(X) :- string_concat(A,B,X), input(A), input(B).

wff(A) :- atomic_proposition(A).
wff(X) :- atomics_to_string(["¤¤¤¤",A,"*",B],X), counter(A), term(B).
wff(Y) :- atomics_to_string(["¤¤¤¤",A,B,"*",C,D],Y), term(X), atomics_to_string(["¤¤¤¤",A,B,C],X), counter(A), term(B), input(C), term(D).
wff(X) :- string_concat("!",A,X), wff(A).
wff(X) :- atomics_to_string([">",A,B],X), wff(A), wff(B).
wff(X) :- atomics_to_string(["§",A,B],X), individual(A), wff(B).

proviso(X) :- atomics_to_string([A,"#",A,B],X), individual(A), counter(B).
proviso(X) :- atomics_to_string([A,B,"#",A],X), individual(A), counter(B).
proviso(X) :- atomics_to_string([A,"#",B],X), individual(A), atomic_proposition(B).
proviso(X) :- atomics_to_string([A,"#",B],X), individual(A), function(B).
proviso(X) :- atomics_to_string([A,"#",B],X), individual(A), predicate(B).
proviso(X) :- string_concat(A,"#!",X), individual(A).
proviso(X) :- string_concat(A,"#>",X), individual(A).
proviso(X) :- string_concat(A,"#§",X), individual(A).
proviso(Z) :- atomics_to_string([A,"#",B,C],Z), proviso(Y), atomics_to_string([A,"#",C],Y), proviso(X), atomics_to_string([A,"#",B],X), individual(A), string(B), string(C).
proviso_group(A) :- proviso(A).
proviso_group(X) :- atomics_to_string([A,"#",B],X), proviso(A), proviso(B).

theorem1(X) :- atomics_to_string([">>>>>",A,B,">!",C,"!",D,C,E,">>",E,A,">",D,A],X), wff(A), wff(B), wff(C), wff(D), wff(E).
theorem2(B) :- theorem(X), atomics_to_string([">",A,B],X), theorem(A), wff(A), wff(B).

theorem3(X) :- atomics_to_string([">§",A,">",B,C,">§",A,B,"§",A,C],X), individual(A), wff(B), wff(C).
theorem4(Y) :- atomics_to_string([">",B,"§",A,B],Y), proviso(X), atomics_to_string([A,"#",B],X), individual(A), wff(B).
theorem5(X) :- atomics_to_string(["§",A,B],X), theorem(B), individual(A), wff(B).

theorem6(X) :- atomics_to_string(["!§",A,"!¤¤¤¤'**",A,B],X), individual(A), term(B).
theorem7(X) :- atomics_to_string([">¤¤¤¤'**",A,B,">¤¤¤¤'**",A,C,"¤¤¤¤'**",B,C],X), individual(A), term(B).

theorem8(X) :- atomics_to_string([">¤¤¤¤'**",A,B,">¤¤¤¤''**",A,C,"¤¤¤¤''**",B,C],X), individual(A), term(B).
theorem9(X) :- atomics_to_string([">¤¤¤¤'**",A,B,">¤¤¤¤''**",C,A,"¤¤¤¤''**",C,B],X), individual(A), term(B).
theorem10(Y) :- atomics_to_string([">§",A,"!>>¤¤¤¤''**",A,B,"¤¤¤¤''**",A,C,"!>¤¤¤¤''**",A,C,"¤¤¤¤''**",A,B,"¤¤¤¤'**",B,C],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C],X), individual(A), term(B), term(C).
theorem11(Y) :- atomics_to_string(["!§",A,"!>!§",B,"!§",C,">",D,"¤¤¤¤'**",C,B,"§",C,"!>>¤¤¤¤''**",C,A,"!§",A,"!!>¤¤¤¤''**",A,B,"!§",B,D,"!>!§",A,"!!>¤¤¤¤''**",A,B,"!§",B,D,"¤¤¤¤''**",C,A],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C,"#",B,"#",C],X), individual(A), individual(B), individual(C).
theorem12(Y) :- atomics_to_string(["!§",A,"!§",B,">§",A,">¤¤¤¤''**",A,B,"¤¤¤¤''**",A,C,"¤¤¤¤''**",B,A],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C,"#",B,"#",C],X), individual(A), individual(B), individual(C).
theorem13(Y) :- atomics_to_string([">¤¤¤¤''**",A,B,"!§",A,"!!>¤¤¤¤''**",A,B,"!§",C,">¤¤¤¤''**",C,A,"!¤¤¤¤''**",C,B],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C,"#",C,"#",B],X), individual(A), term(B), individual(C).
theorem14(Y) :- atomics_to_string(["!§",A,"!!>¤¤¤¤''**",B,A,"!§",B,">¤¤¤¤''**",B,A,"!§",C,"!!>¤¤¤¤''**",B,C,"!¤¤¤¤''**",C,A],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C,"#",B,"#",C],X), individual(A), individual(B), individual(C).

theorem15(Y) :- atomics_to_string(["!§",A,"!§",B,"§",C,">!>¤¤¤¤''**",B,C,"!¤¤¤¤''**",C,D,"!§",D,"!§",B,"!>>!§",D,"!!>!>¤¤¤¤''**",B,C,"!¤¤¤¤''**",C,D,"!!>¤¤¤¤''**",B,D,"!¤¤¤¤''**",D,A,"¤¤¤¤'**",B,D,"!>¤¤¤¤'**",B,D,"!§",D,"!!>!>¤¤¤¤''**",B,C,"!¤¤¤¤''**",C,D,"!!>¤¤¤¤''**",B,D,"!¤¤¤¤''**",D,A],Y), proviso_group(X), atomics_to_string([A,"#",B,"#",A,"#",C,"#",A,"#",D,"#",B,"#",C,"#",B,"#",D,"#",C,"#",D],X), individual(A), individual(B), individual(C), individual(D).


%making the basic propositional calculus postulates
theorem16(X) :- atomics_to_string([">",A,">",B,A],X), wff(A), wff(B).


*/


/*
⸢′⸣ is a string.
⸢☼⸣ is a string.
⸢◆⸣ is a string.
⸢¬⸣ is a string.
⸢→⸣ is a string.
⸢∀⸣ is a string.
⸢▒⸣ is a string.
If A is a string and B is a string, then ⸢AB⸣ is a string.

⸢′⸣ is a counter.
If A is a counter, then ⸢A′⸣ is a counter.
⸢☼⸣ is an arity.
If A is an arity, then ⸢A☼⸣ is an arity.
If A is a counter, then ⸢◆A⸣ is an atomic proposition.
If A is a counter, then ⸢◆◆A⸣ is an individual.
If A is a counter and B is an arity, then ⸢◆◆◆AB⸣ is a function.
If A is a counter and B is an arity, then ⸢◆◆◆◆AB⸣ is a predicate.

If A is an individual, then A is a term.
If A is a counter and B is a term, then ⸢◆◆◆A☼B⸣ is a term.
If A is a counter and B is an arity and C is an input and D is a term and ⸢◆◆◆ABC⸣ is a term, then ⸢◆◆◆AB☼CD⸣ is a term.
If A is a term, then A is an input.
If A is an input and B is an input, then ⸢AB⸣ is an input.

If A is an atomic proposition, then A is a wff.
If A is a counter and B is a term, then ⸢◆◆◆◆A☼B⸣ is a wff.
If A is a counter and B is an arity and C is an input and D is a term and ⸢◆◆◆◆ABC⸣ is a wff, then ⸢◆◆◆◆AB☼CD⸣ is a wff.
If A is a wff, then ⸢¬A⸣ is a wff.
If A is a wff and B is a wff, then ⸢→AB⸣ is a wff.
If A is an individual and B is a wff, then ⸢∀AB⸣ is a wff.

If A is an individual and B is a counter, then ⸢A▒AB⸣ is a proviso.
If A is an individual and B is a counter, then ⸢AB▒A⸣ is a proviso.
If A is an individual and B is an atomic proposition, then ⸢A▒B⸣ is a proviso.
If A is an individual and B is a function, then ⸢A▒B⸣ is a proviso.
If A is an individual and B is a predicate, then ⸢A▒B⸣ is a proviso.
If A is an individual, then ⸢A▒¬⸣ is a proviso.
If A is an individual, then ⸢A▒→⸣ is a proviso.
If A is an individual, then ⸢A▒∀⸣ is a proviso.
If A is an individual and B is a string and C is a string and ⸢A▒B⸣ is a proviso and ⸢A▒C⸣ is a proviso, then ⸢A▒BC⸣ is a proviso.
If A is a proviso, then A is a proviso group.
If A is a proviso group and B is a proviso group, then ⸢A▒B⸣ is a proviso group.

If A is a wff and B is a wff and C is a wff and D is a wff and E is a wff, then ⸢→→→→→AB→¬C¬DCE→→EA→DA⸣ is a theorem.
If A is a wff and B is a wff and A is a theorem and ⸢→AB⸣ is a theorem, then B is a theorem.

If A is an individual and B is a wff and C is a wff, then ⸢→∀A→BC→∀AB∀AC⸣ is a theorem.
If A is an individual and B is a wff and ⸢A▒B⸣ is a proviso, then ⸢→B∀AB⸣ is a theorem.
If A is an individual and B is a wff and B is a theorem, then ⸢∀AB⸣ is a theorem.

If A is an individual and B is a term, then ⸢¬∀A¬◆◆◆◆′☼☼AB⸣ is a theorem.
If A is a term and B is a term and C is a term, then ⸢→◆◆◆◆′☼☼AB→◆◆◆◆′☼☼AC◆◆◆◆′☼☼BC⸣ is a theorem.

If A is a term and B is a term and C is a term, then ⸢→◆◆◆◆′☼☼AB→◆◆◆◆′′☼☼AC◆◆◆◆′′☼☼BC⸣ is a theorem.
If A is a term and B is a term and C is a term, then ⸢→◆◆◆◆′☼☼AB→◆◆◆◆′′☼☼CA◆◆◆◆′′☼☼CB⸣ is a theorem.
If A is an individual and B is a term and C is a term and ⸢A▒B▒A▒C⸣ is a proviso group, then ⸢→∀A¬→→◆◆◆◆′′☼☼AB◆◆◆◆′′☼☼AC¬→◆◆◆◆′′☼☼AC◆◆◆◆′′☼☼AB◆◆◆◆′☼☼BC⸣ is a theorem.
If A is an individual and B is an individual and C is an individual and ⸢A▒B▒A▒C▒B▒C⸣ is a proviso group, then ⸢¬∀A¬→¬∀B¬∀C→D◆◆◆◆′☼☼CB∀C¬→→◆◆◆◆′′☼☼CA¬∀A¬¬→◆◆◆◆′′☼☼AB¬∀BD¬→¬∀A¬¬→◆◆◆◆′′☼☼AB¬∀BD◆◆◆◆′′☼☼CA⸣ is a theorem.
If A is an individual and B is an individual and C is an individual and ⸢A▒B▒A▒C▒B▒C⸣ is a proviso group, then ⸢¬∀A¬∀B→∀A→◆◆◆◆′′☼☼AB◆◆◆◆′′☼☼AC◆◆◆◆′′☼☼BA⸣ is a theorem.
If A is an individual and B is a term and C is an individual and ⸢A▒B▒A▒C▒C▒B⸣ is a proviso group, then ⸢→◆◆◆◆′′☼☼AB¬∀A¬¬→◆◆◆◆′′☼☼AB¬∀C→◆◆◆◆′′☼☼CA¬◆◆◆◆′′☼☼CB⸣ is a theorem.
If A is an individual and B is an individual and C is an individual and ⸢A▒B▒A▒C▒B▒C⸣ is a proviso group, then ⸢¬∀A¬¬→◆◆◆◆′′☼☼BA¬∀B→◆◆◆◆′′☼☼BA¬∀C¬¬→◆◆◆◆′′☼☼BC¬◆◆◆◆′′☼☼CA⸣ is a theorem.

If A is an individual and B is an individual and C is an individual and D is an individual and ⸢A▒B▒A▒C▒A▒D▒B▒C▒B▒D▒C▒D⸣ is a proviso group, then ⸢¬∀A¬∀B∀C→¬→◆◆◆◆′′☼☼BC¬◆◆◆◆′′☼☼CD¬∀D¬∀B¬→→¬∀D¬¬→¬→◆◆◆◆′′☼☼BC¬◆◆◆◆′′☼☼CD¬¬→◆◆◆◆′′☼☼BD¬◆◆◆◆′′☼☼DA◆◆◆◆′☼☼BD¬→◆◆◆◆′☼☼BD¬∀D¬¬→¬→◆◆◆◆′′☼☼BC¬◆◆◆◆′′☼☼CD¬¬→◆◆◆◆′′☼☼BD¬◆◆◆◆′′☼☼DA⸣ is a theorem.
*/
