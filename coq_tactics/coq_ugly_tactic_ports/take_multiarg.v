(*
Author: Lulof Pirée (1363638)
Creation date: 12 May 2021

Version of "Take" tactic that accepts any number of arguments.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.


Ltac2 Type exn ::= [ TakeError(string) ].

Ltac2 raise_take_error (s:string) := 
    Control.zero (TakeError s).

(*  Arguments:
    * s: an intropatterns
    * t: a Type
Does:
    * perform ∀-elim by introducing s as a variable of type t.
        Raises an exception if the type 
        does not match the bound variable in the ∀-goal,
        or if the goal is not a ∀-quantifier.
*)
Ltac2 intro_with_type_matching s t := 
    match! goal with
    | [ |- forall _ : ?u, _] => 
        match Constr.equal u t with
            | true => Std.intros false s
            | false => raise_take_error (
            "The type of the variable must match the type of the 'forall' goal's bound variable.")
        end
    | [|- _] => raise_take_error("'Take' can only be applied to 'forall' goals")
    end.
    
Ltac2 Type exn ::= [ CannotHappenError(string) ].

(*  Arguments:
        * x: a list of intropatterns
        * t: a Type
    Does:
        * call intro_with_type_matching v t for each v ∈ x.
*)
Ltac2 rec intro_list_with_typematching x (t:constr) :=
    match x with
    | head::tail => intro_with_type_matching head t; 
                    intro_list_with_typematching tail t
    | [] => ()
    end.

(*  Arguments:
        * x: a list of (v, t) pairs
    Does:
    * call intro_list_with_typematching(v, t) for each (v, t) ∈ x
*)
Ltac2 rec take_multiarg x :=
    match x with
    | head::tail =>
        match head with
        | (v, t) => intro_list_with_typematching v t
        | _ => Control.zero (CannotHappenError "Cannot happen")
        end; take_multiarg tail
    | [] => ()
    end.


Ltac2 Notation "Take" x(list1(seq(list1(intropatterns, ","), ":", constr), ",")) := 
    take_multiarg x.

(* Testcases *)

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

(* Test 9: This should give a helpful error, but it does not:
    "Uncaught Ltac2 exception:
    Match_failure"
    (Note that two variables have the same name "a"!)*)
Goal forall (a b c d e f g: nat) (b1 b2: bool), 
        Nat.odd (a + b + c + d + e + f + g) = andb b1 b2.
    Take a, b, c, d, e, f, g : nat, a, h: bool.
Abort.

(* Test 9: Two sets of multiple variables of the same type.
   But in a *different order* with different names.*)
(* DOES NOT WORK (yet)*)
Goal forall (n m k: nat)  (b1 b2: bool), Nat.odd (n + m + k) = andb b1 b2.
    Take y, u: bool, a, b, c : nat.
Abort.
            



