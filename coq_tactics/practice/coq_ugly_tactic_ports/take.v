(*
Author: Lulof Pirée (1363638)
    & Cosmin Manea
Creation date: 7 May 2021

First attempt at rewriting the "Take" tactic in Ltac2.
Mostly for practice, does not focus on maintainability.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.


Ltac2 Type exn ::= [ TakeError(string) ].

Ltac2 raise_take_error (s:string) := 
    Control.throw (TakeError s).

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

(* This should work fine *)
Goal forall n : nat, n <= 2*n.
    Take n : nat.
Abort.

(* Also this should work fine *)
Goal forall n : nat, n <= 2*n.
    Take x : nat.
Abort.

(* This should raise an error, because the type does not match*)
Goal forall n : nat, n <= 2*n.
    Take n : bool.
Abort.

(* This should raise an error, because "Take" solves forall-quatifiers *)
Goal exists n : nat, n <= 2*n.
    Take n : nat.
Abort.
        
            
            
            



