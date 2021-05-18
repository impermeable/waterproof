(* From Ltac2 Require Import Ltac2.
From Ltac2 Require Option. *)


Lemma all_x_is_itself2 : forall x: nat, x = x.
Proof.
    intros x.
    is_evar x.

