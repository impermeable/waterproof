(*
Author: Lulof Pirée (1363638)
Creation date: 14 May 2021

Example of using "match!" with a "context " keyword.
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Definition type_of {T : Type} (x : T) := T.

Lemma test: forall n: nat, (n < 4 /\ n > 2) /\ (n > 1) -> n = 3.
Proof.
    intros n.
    intros [h1 h2].
    match! eval cbv in (type_of h1) with
    | context [(_ /\ _)]  => destruct h1 as [h3 h4]
    | _ => ()
    end.