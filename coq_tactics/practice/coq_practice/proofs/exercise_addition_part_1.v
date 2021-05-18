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
(* THIS IS IMPORTANT:
  I first only wrote "intros.". Then it fixes m.
  Then the IH becomes "add n (S m) = S (add n m)"
  with m and n fixed. This is not sufficient to solve the inductive step!
  Explicitly only introducing "n" leaves the universal quantification over m. *)
intros n.
induction n as [ | n'].
(* Case n = 0. Then add(n, m) = m.
  As a result, S(m) = add(0, (S(m)) = S(add(n, m)) = S(m) *)
simpl.
reflexivity.
(*Inductive step.
  IHn : add n (S m) = S (add n m)
  Goal: add (S n) (S m) = S (add (S n) m)
*)
intros.
(* Follow the definition of the recursion one step. *)
simpl.
(* This already shows both sides are equal. *)
apply IHn'.
Qed.

