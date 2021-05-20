(* Example proof using the 'rewrite' tactic *)

Require Import Arith.

(* forall n m p : nat, n * (m + p) = n * m + n * p    *)
Check Nat.mul_add_distr_l.

Lemma example: forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
intros x y.
(* Rewrite (x + y) * (x + y) as (x * y)*x + (x * y)*y. 
  Coq figured out that n := (x+y), m := x, p := y. 
  Don't ask me how. Something with pattern matching.*)
rewrite Nat.mul_add_distr_l.
(* Can we also do other way around? Let's search! *)
SearchRewrite ((_ + _) * _).
(* We can now apply Nat.mul_add_distr_r without substitution,
  but it is unclear whether Coq will choose p:=x or p:=y. *)
rewrite Nat.mul_add_distr_r with (p:=x).
rewrite Nat.mul_add_distr_r with (p:=y).

(* now we got:
  x * x + y * x + (x * y + y * y)
  How to get rid of those silly brackets? *)
SearchRewrite (_ + (_ + _)).
rewrite Nat.add_assoc.

(* Now we want to use the theorem from right to left.
  i.e. we got the RHS of the equality theorem, and we want the LHS *)
rewrite <- Nat.add_assoc with (n := x * x).

(* Need to replace (y * x + x * y) by 2*x*y.
  First get the order straight.*)
SearchPattern (?x * ?y = ?y * ?x).
rewrite Nat.mul_comm with (n:=y) (m:=x).
SearchRewrite (S _ * _).
(* at 1 = apply only once.  This just says that x*y = 1*x*y   *)
rewrite <- (Nat.mul_1_l (x * y)) at 1.
(*  1*x*y + x*y = S(1)*x*y = 2*x*y  *)
rewrite <- Nat.mul_succ_l.
SearchRewrite (_ * (_ * _)).
rewrite Nat.mul_assoc.
(* Ok we are done. We got an expression of the shape A = A. *)
reflexivity.
Qed.



