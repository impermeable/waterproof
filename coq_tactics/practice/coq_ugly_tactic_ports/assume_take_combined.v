(*
Author: Lulof Pirée (1363638)
    & Cosmin Manea
Creation date: 12 May 2021

Version of "Take" tactic that accepts any number of arguments.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.


Ltac2 Type exn ::= [ TakeError(string) ].

Ltac2 raise_take_error (s:string) := 
    Control.zero (TakeError s).

(*  
    Arguments:
        * s: an intropatterns
        * t: a Type
    Does:
    * perform ∀-elim by introducing s as a variable of type t.
        Raises an exception if the type 
        does not match the bound variable in the ∀-goal,
        or if the goal is not a ∀-quantifier.
*)
Ltac2 elim_forall_with_type_matching s t := 
    lazy_match! goal with
    | [ |- forall _ : ?u, _] => 
        match Constr.equal u t with
            | true => Std.intros false s
            | false => raise_take_error (
            "The type of the variable must match the type of the 'forall' goal's bound variable.")
        end
    | [|- _] => raise_take_error("'Take' can only be applied to 'forall' goals")
    end.

Ltac2 Type exn ::= [ AssumeError(string) ].
Ltac2 raise_assume_error (s:string) := 
    Control.zero (AssumeError s).

Definition type_of {T : Type} (x : T) := T.

(*  Arguments:
        * a, b: any constr
    Returns:
        * a bool:
            - true if a and b are judgementally equal
                (i.e. are of the same type after normalization)
            - false otherwise.
*)  
Ltac2 check_constr_type_equal (a: constr) (b: constr) :=
    Constr.equal (eval cbv in (type_of $a)) (eval cbv in (type_of $b)).

(*  Arguments:
    * h: an intropatterns
    * t: a Type, the type of the premise of the implication in the goal.
    Does:
    * perform ⇒-elim on the goal by introducing s as a variable of type t.
        Raises an exception if the top logical connective of the goal
        is not ⇒, or if the premise does not match t.
*)
Ltac2 assume_goal_premise_with_type_checking (h) (t:constr) :=
    lazy_match! goal with
    | [|- ?premise -> ?conclusion] => 
        match check_constr_type_equal t premise with
        | true => Std.intros false h (* "intros h" always use the name "h"*)
        | false => raise_assume_error "Premise does not match goal."
        end
    | [|- _] => raise_assume_error "Cannot assume premise: 
                                top goal is not an implication."
    end.
    
Ltac2 Type exn ::= [ CannotHappenError(string) ].

(*  Arguments:
        * x: a list of intropatterns
        * t: a Type
        * is_premise: bool
            - false -> x contains a list of variable names
                        to elim a ∀-quantifier.
            - true -> x contains a list of premise-hypothesis-names
                        to elim a ⇒-goal.
    Does:
        * call intro_with_type_matching v t for each v ∈ x.
*)
Ltac2 rec intro_list_with_typematching x (t:constr) is_premise:=
    match x with
    | head::tail => 
        match is_premise with
        | true => assume_goal_premise_with_type_checking head t
        | false => elim_forall_with_type_matching head t
        end; intro_list_with_typematching tail t is_premise
    | [] => ()
    end.

(*  Arguments:
        * x: a list of (v, t) pairs
        * is_premise: bool
            - false -> all v's are a list of variable names
                        to elim a ∀-quantifier.
            - true -> all v's are a list of premise-hypothesis-names
                        to elim a ⇒-goal.
    Does:
    * call intro_list_with_typematching(v, t, is_premise) for each (v, t) ∈ x
*)
Ltac2 rec intros_with_type_check_multiarg x (is_premise:bool):=
    match x with
    | head::tail =>
        match head with
        | (v, t) => intro_list_with_typematching v t is_premise
        | _ => Control.zero (CannotHappenError "Cannot happen")
        end; intros_with_type_check_multiarg tail is_premise
    | [] => ()
    end.


Ltac2 Notation "Take" 
    x(list1(seq(list1(intropatterns, ","), ":", constr), ",")) := 
    intros_with_type_check_multiarg x false.


Ltac2 Notation "Assume" 
    x(list1(seq(list1(intropatterns, ","), ":", constr), ",")) := 
    intros_with_type_check_multiarg x true.

(*
--------------------------------------------------------------------------------
    TESTCASES
    for Take
*)

Ltac2 Type exn ::= [ TestFailedError(string) ].

Ltac2 assert_raises_error f :=
    match Control.case f with
    | Val _ => Control.throw (TestFailedError "Should raise an error")
    | Err exn => print (concat 
        (of_string "Test passed, got error:") 
        (of_exn exn))
    end.

(* Test 0: This should work fine *)
Goal forall n : nat, n <= 2*n.
    Take n : nat.
Abort.

(* Test 1: Also this should work fine *)
Goal forall n : nat, n <= 2*n.
    Take x : nat.
Abort.

(* Test 2: This should raise an error, because the type does not match*)
Goal forall n : nat, n <= 2*n.
    assert_raises_error (fun () => Take n : bool).
Abort.

(* Test 3: This should raise an error, because "Take" solves forall-quatifiers *)
Goal exists n : nat, n <= 2*n.
    assert_raises_error (fun() => Take n : nat).
Abort.

(* Test 4: Multi argument testcase *)
Goal forall n : nat, forall m : nat, n + m <= 2*n + m.
    Take n : nat, m : nat.
Abort.

(* Test 5: Two sets of multiple variables of the same type. *)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take n, m, k : nat, b1, b2: bool.
Abort.
            
(* Test 6: Two sets of multiple variables of the same type.
   But with different names *)
   Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
   Take a, b, c : nat, d, e: bool.
Abort.

(* Test 7: not allowed to introduce so many bools *)
   Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
   assert_raises_error (fun () => Take a, b, c, d, e: bool).
Abort.

(* Test 8: look how crazy many vars we can introduce*)
   Goal forall (a b c d e f g: nat) (b1 b2: bool), 
        Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
   Take a, b, c, d, e, f, g : nat, b1, b2: bool.
Abort.

(* Test 9: This should give a helpful error.
    (Note that two variables have the same name "a"!)
    
    Currently it raises "Internal (err:(a is already used.))"
    which seems clear enough :)
    *)
Goal forall (a b c d e f g: nat) (b1 b2: bool), 
        Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    assert_raises_error (fun() => Take a, b, c, d, e, f, g : nat, a, h: bool).
Abort.

(* Test 10: Two sets of multiple variables of the same type.
   But in a *different order* with different names.*)
(* DOES NOT WORK (yet)*)
(* Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take y, u: bool, a, b, c : nat.
Abort.
             *)


(*
--------------------------------------------------------------------------------
    TESTCASES
    for Assume
*)

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

(* Test 2:
    Not an implication goal, should raise an error.
*)
Goal forall n : nat, (n = 1) /\ (n = 1).
    intros n.
    assert_raises_error (fun () => Assume my_hypothesis : (n = 1)).
Abort.

(* Test 3: 
    Two premises.
    THIS DOES NOT WORK AS INTENDED.
*)
Goal forall n : nat, ((n = 1) /\ (n = 2)) -> (n = 1).
    intros n.
    Assume h1 : (n = 1).
Abort.






