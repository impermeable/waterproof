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

Lemma exercise_2: forall n m, add (S n) m = S (add n m).
Proof.
intros n.
induction n.
(* Base case: n = 0 *)
simpl.
reflexivity.
(* Inductive case.
    IHn: "forall m : nat, add (S n) m = S (add n m)"
    Goal: "forall m : nat, add (S (S n)) m = S (add (S n) m)" *)
intros m.
simpl.
apply exercise_1.
Qed.

Lemma exercise_3: forall n m, add n m = n + m.
Proof.
intros n.
induction n.
(* Base case: n = 0 *)
simpl.
reflexivity.
(* Inductive case.
    IHn: "IHn : forall m : nat, add n m = n + m"
    Goal: "forall m : nat, add (S n) m = S n + m" *)
intros m.
rewrite exercise_2.
rewrite IHn.
reflexivity.
Qed.









