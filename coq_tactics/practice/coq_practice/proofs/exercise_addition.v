(* Exercises to prove properties of the "add" function. *)

Require Import Arith.

(* 
              { m               if n == 0
    n + m =   {
              { (n-1) + (m + 1) otherwise
*)
Fixpoint add (n m: nat) : nat :=
  match n with
    0 => m
  | S p => add p (S m)
  end.


Lemma helper: forall n, S n = n + 1.
Proof.
intros.
ring.
Qed.


Lemma exercise_1: forall n m, add n (S m) = S (add n m).
Proof.
intros.
induction n.
(* Case n = 0. Then add(n, m) = m.
  As a result, S(m) = add(0, (S(m)) = S(add(n, m)) = S(m) *)
simpl.
reflexivity.
(*Inductive step.
  IHn : add n (S m) = S (add n m)
  Goal: add (S n) (S m) = S (add (S n) m)
*)
assert (succ_add_is_plus_1: forall x y, S (add x y) = add x y + 1).
  intros.
  apply helper.


simpl.
assert (this: forall x y, (add x (S (S y) ) ) = add x y + 2).
intros.
induction x.
simpl.
ring.
simpl.






(* Case S(n) with IHn : add n (S m) = S (add n m) *)
assert (this: forall x y, add (S x) y = (add x y) + 1 ).
intros.
simpl.
induction x.
simpl.
ring.
simpl.
rewrite IHx.
apply helper (S y).
Search (S _ = _).
