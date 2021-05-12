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
    



Ltac2 Notation "Take" s(intropatterns) ":" t(constr) := intro_with_type_matching s t.

Ltac2 Type exn ::= [ CannotHappenError(string) ].

Ltac2 rec take_multiarg x :=
    match x with
    | head::tail =>
        match head with
        | (s, t) => intro_with_type_matching s t
        | _ => Control.zero (CannotHappenError "Cannot happen")
        end; take_multiarg tail
    | [] => ()
    end.

Ltac2 rec intro_list_with_typematching (x) (t:constr) :=
    match x with
    | head::tail => intro_with_type_matching head t; 
                    intro_list_with_typematching tail t
    | [] => ()
    end.
Ltac2 Notation "Take" x(list1(seq(intropatterns, ":", constr), ",")) := 
    take_multiarg x.

(* Testcases *)

Ltac2 Type exn ::= [ TestFailedError(string) ].

Ltac2 assert_raises_error f :=
    match Control.case f with
    | Val _ => Control.throw (TestFailedError "Should raise an error")
    | Err exn => print (of_string "Test passed")
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

Search (nat  -> bool).

(* Test 5: Two sets of multiple variables of the same type. *)
Goal forall n: nat, forall m : nat, forall k: nat, 
     forall b1:bool, forall b2:bool, Nat.odd (n + m + k) = andb b1 b2.
    Take n, m, k : nat, b1, b2: bool.
Abort.
            
            



