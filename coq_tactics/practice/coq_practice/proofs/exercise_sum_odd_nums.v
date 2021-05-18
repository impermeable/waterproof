(* Exercise to prove properties of the "sum_odd_n" function. *)

Require Import Arith.

(* Compute the sum of the first n odd natural numbers. *)
Fixpoint sum_odd_n (n:nat) : nat :=
  match n with
    0 => 0
  | S p => 1 + 2 * p + sum_odd_n p
  end.



Lemma sum_odd_lemma: forall n : nat, sum_odd_n n = n*n.
Proof.
induction n.
(* Base case *)
simpl.
reflexivity.
(* Inductive case:
  IH:  sum_odd_n n = n * n
  Goal: sum_odd_n (S n) = S n * S n *)
assert (prod_succ: forall x: nat, (S x) * (S x) = x*x + 2 * x + 1).
  intros x.
  ring.
rewrite prod_succ.
simpl.
rewrite IHn.
ring.
Qed.
