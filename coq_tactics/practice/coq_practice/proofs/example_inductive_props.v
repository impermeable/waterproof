Require Import Arith.

Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Print even.

Compute even 0.

Lemma even_mult : forall x, even x -> exists y, x = 2 * y.
Proof.
intros x H.
(* Apply induction on the inductive proposition! *)
induction H.

(* Base case: even0. So assume x = 0.0 = 2 * y? *)
exists 0.
reflexivity.

(* Induction step: evenS. So assume any "x" and "even x". 
  IHeven : exists y : nat, x = 2 * y
  Goal: exists y : nat, S (S x) = 2 * y  *)

(* Pick some y with x = 2*y *)
destruct IHeven as [y Heq].
(* replace "S (S x))" -> "S ( S 2*y)" *)
rewrite Heq.
(* Goal is now "exists y0 : nat, S (S (2 * y)) = 2 * y0".
  Now just pick S(y) as y0 and show that works. *)
exists (S y).
ring.
Qed.



