From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Std.
Require Import ArithRing.
Require Import Nat.


Ltac2 Notation "my_refl" := reflexivity.

Lemma one_is_one : 1 = 1.
Proof.
    my_refl.
Qed.

(* Ltac2 Notation "ring" := ArithRing.ring. *)

Definition double_successor x := S (S x).

(* Ltac2 Notation "quadruple_successor" x(constr) :=
    double_successor (double_successor x). *)

Ltac2 my_intro_function this :=
    Control.enter(
        fun () => Std.intros true this).
Ltac2 Notation "my_intro" x(intropatterns) := my_intro_function x.

Lemma all_x_is_itself : forall x: nat, x = x.
Proof.
    my_intro x.
    reflexivity.
Qed.


Ltac2 Notation "intro_cb" "{" x(intropatterns) "}" := my_intro_function x.

Lemma all_x_is_itself2 : forall x: nat, x = x.
Proof.
    intro_cb {x}.
    reflexivity.
Qed.

Ltac2 destruct_into_2 hyp :=
    Control.enter (fun () => Std.destruct false hyp).
Ltac2 Notation "break_in_two" H(constr) := 
    destruct_into_2 hyp.

Lemma one_is_one_and_not_zero : 1 = 1 /\ 1 <> 0.