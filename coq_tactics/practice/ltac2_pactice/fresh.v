(*
Authors: 
    * Lulof Pirée (1363638)
Creation date: 28 May 2021

Experiments with the Ltac2 "Fresh" command.
See <https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Fresh.v>
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
(* From Ltac2 Require Import Fresh. *)

Ltac2 Eval Fresh.Free.of_ids.
Ltac2 Eval Fresh.in_goal (match Ident.of_string "h" with
|Some y => y
| None => @none
end).
Ltac2 Eval Fresh.in_goal (match Ident.of_string "h" with
|Some y => y
| None => @none
end).
Ltac2 Eval Fresh.fresh (Fresh.Free.of_constr constr:(1)) @h.


Goal forall n:nat, n > 0 /\ n < 2 -> n = 1.
Proof.
    intros n.
    intros h.

    print (of_ident (Fresh.in_goal @h)).

    destruct h as [h h0].

    print (of_ident (Fresh.in_goal @h)).
Abort.