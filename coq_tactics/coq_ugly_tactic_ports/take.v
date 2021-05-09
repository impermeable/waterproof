(*
Author: Lulof Pirée (1363638)
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

Ltac2 intro_with_type_matching s (t:constr) := 
    lazy_match! goal with
    | [ |- forall _ : ?u, _] => 
        lazy_match! u with
            | &t => print (of_constr t); print (of_constr u); Std.intros false s
            | _ => raise_take_error (
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


    (* induction n.
    (* Base case, 0 <= 2*0 *)
        apply le_n.
    (* Inductive step *)
        assert (n_le_Sn: n <= S n).
            apply le_S.
            apply le_n.
        apply n_le_Sn. *)
        
            
            
            



