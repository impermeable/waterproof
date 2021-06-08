(*
Authors: 
    - Lulof Pirée (1363638)
Creation date: 08 June 2021

Various versions of [Rewrite using ...] tactic. 
This tactic is used to rewrite the goal or hypotheses.
--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Add LoadPath "./coq_tactics/new_wplib/" as wplib.
Load rewrite_using.
Load test_auxiliary.

Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite using ...] 
    Variant without the [in] clause.
*)

(** * Test 1
    Base case: valid rewrite statement.
*)
Lemma test_rewrite_using_1: forall x y: nat, 5 * (x + y) = 5 * x + 5 * y.
Proof.
    intros x y.
    Rewrite using Nat.mul_add_distr_l.
    reflexivity.
Qed.

(** * Test 2
    Base case: valid rewrite statement.
*)
Lemma test_rewrite_using_2: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    Rewrite using Nat.add_assoc.
    reflexivity.
Qed.

(** * Test 3
    Error case: unapplicable rewrite statement.
*)
Lemma test_rewrite_using_3: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    (* No multiplication is involved in the goal... *)
    let result () := (Rewrite using Nat.mul_add_distr_l) in
    assert_raises_error result.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [Rewrite using ... in ...] 
    Variant with the [in] clause.
*)
Lemma test_rewrite_using_in_1: forall x y: nat, 5 * (x + y) = 10 -> 2 = (x + y).
Proof.
    intros x y.
    intros h.
    Rewrite using Nat.mul_add_distr_l in h.
    assert_hyp_has_type @h (5 * x + 5 * y).
Qed.

(* TODO: remove below. Just WIP inspiration for testcases. *)

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