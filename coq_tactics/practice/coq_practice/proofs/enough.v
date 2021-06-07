(** * enough.v
Authors: 
    - Lulof Pirée (1363638)
Creation date: 6 June 2021

Experimenting with the [enough] tactic of Coq.
*)
Require Import Arith.
Require Import Bool.

Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Lemma example_1: forall x:nat, x > 1 /\ x < 3 -> even x.
Proof.
    intros x h.
    enough (x = 2).
        rewrite H. (* Change the goal to "even 2"*)
        apply evenS. (* Change the goal to "even 0"*)
        apply even0.

    (* Remains to show: (x = 2) *)
    destruct h as [h1 h3].
    apply gt_le_S in h1. (* h1 becomes (2 <= x) *)
    apply Nat.lt_le_pred in h3. 
    simpl in h3. (* h3 becomes (x <= 2) *)

    (* Destruct goal in (x <= 2) and (2 <= x) *)
    apply Nat.le_antisymm.
    exact h3.
    exact h1.
Qed.

Lemma example_2: forall x:nat, x > 1 /\ x < 3 -> even x.
Proof.
    intros x h.
    enough (hyp:(x = 2)) by (
        rewrite hyp;apply evenS;apply even0).

    (* Remains to show: (x = 2) *)
    destruct h as [h1 h3].
    apply gt_le_S in h1. (* h1 becomes (2 <= x) *)
    apply Nat.lt_le_pred in h3. 
    simpl in h3. (* h3 becomes (x <= 2) *)

    (* Destruct goal in (x <= 2) and (2 <= x) *)
    apply Nat.le_antisymm.
    exact h3.
    exact h1.
Qed.


