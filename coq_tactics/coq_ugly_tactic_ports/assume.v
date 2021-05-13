(*
Author: Lulof Pirée (1363638)
Creation date: 13 May 2021

Ltac2 prototype of the "Assume" tactic.
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.


Ltac2 Type exn ::= [ AssumeError(string) ].

Ltac2 raise_assume_error (s:string) := 
    Control.zero (AssumeError s).


Definition type_of {T : Type} (x : T) := T.

Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).

Ltac2 assume_goal_premise_with_type_checking (h) (t:constr) :=
    match! goal with
    | [|- ?premise -> ?conclusion] => 
        match check_constr_type_equal t premise with
        | true => Std.intros false h (* "intros h" always use the name "h"*)
        | false => raise_assume_error "Premise does not match goal."
        end
    | [|- _] => raise_assume_error "Cannot assume premise: 
                               top goal is not an implication."
    end.



Ltac2 Notation "Assume" h(intropatterns) ":" t(constr) :=
    assume_goal_premise_with_type_checking h t.

(*
--------------------------------------------------------------------------------
    TESTCASES
*)
Ltac2 Type exn ::= [ TestFailedError(string) ].
Ltac2 assert_raises_error f :=
    match Control.case f with
    | Val _ => Control.throw (TestFailedError "Should raise an error")
    | Err exn => print (concat 
        (of_string "Test passed, got error:") 
        (of_exn exn))
    end.

(* Test 0: 
    Basic case of implication goal.
    User chooses default name for hypothesis.
*)
Goal forall n : nat, (n = 1) -> (n = 1).
    intros n.
    Assume h : (n = 1).
Abort.

(* Test 1: 
    Basic case of implication goal.
    User chooses custom name for hypothesis.
*)
Goal forall n : nat, (n = 1) -> (n = 1).
    intros n.
    Assume my_hypothesis : (n = 1).
Abort.



