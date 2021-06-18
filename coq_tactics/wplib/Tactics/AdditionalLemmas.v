(** # **Additional lemmas**

This file contains lemmas written to support the tactic library.
We will add these lemmas to a database called ```additional```*)
Require Import Coq.Logic.PropExtensionality.
Require Import wplib.Definitions.SetDefinitions.
Require Import wplib.Notations.Notations.
Lemma base_same : forall C : Type,
  forall P : C -> Prop,
  forall x y : sig P, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros C P x y H.
apply eq_sig_hprop.
intros.
apply proof_irrelevance.
apply H.
Qed.

Lemma same_base : forall C : Type,
  forall P : C -> Prop,
    forall x y : sig P, x = y -> proj1_sig x = proj1_sig y.
Proof.
intros C P x y H.
rewrite H.
trivial.
Qed.


Hint Resolve base_same : additional.
Hint Resolve same_base : additional.
Require Import Reals.
Require Import Reals.ROrderedType.

Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
intros. destruct (Reqb_eq x y). apply (H1 H).
Qed.

Lemma true_Req : forall x y : R, Reqb x y = true -> x = y.
Proof.
intros. destruct (Reqb_eq x y). apply (H0 H).
Qed.

Lemma Req_false : forall x y : R, x <> y -> Reqb x y = false.
Proof.
intros. unfold Reqb. destruct Req_dec. contradiction. trivial.
Qed.

Lemma false_Req : forall x y : R, Reqb x y = false -> x <> y.
Proof.
intros. destruct (Req_dec x y). rewrite (Req_true x y e) in H. 
assert (H1 : true <> false). auto with *. contradiction.
apply n.
Qed.

Require Import Coq.micromega.Lra.
Hint Resolve (eq_sym) : reals.
Hint Resolve false_Req : reals.
Hint Resolve true_Req : reals.
(** ** Subsets*)
Require Import wplib.Definitions.SetDefinitions.
Lemma subset_elements_satisfy_predicate :
  forall V : subsets_R,
    forall x : V,
      is_in V x.
Proof.
intro V.
induction x.
assumption.
Qed.
Hint Resolve subset_elements_satisfy_predicate : additional.

Lemma elements_satisfy_other_pred :
  ∀ (A : subsets_R) (pred : ℝ → Prop),
    (∀ a : A, pred a) ⇒
      ∀ b : ℝ, is_in A b ⇒ pred b.
  
    
Proof.
intros A pred A_satisfies b b_in_A.
set (c := (mk_element_R (is_in A) b b_in_A)).
assert (pred_c : (pred c)) by eauto using A_satisfies with *.
eauto with *.
Qed.
(** 
### Intervals*)
Require Import wplib.Notations.Notations.
Definition int_cc_prop {x y : R} :
  forall r : [x, y], x <= r <= y
  := subset_elements_satisfy_predicate [x,y].
Definition int_co_prop {x y : R} :
  forall r : [x, y), x <= r < y
  := subset_elements_satisfy_predicate [x,y).
Definition int_oc_prop {x y : R}:
  forall r : (x, y], x < r <= y
  := subset_elements_satisfy_predicate (x,y].
Definition int_oo_prop {x y : R}:
  forall r : (x, y), x < r < y
  := subset_elements_satisfy_predicate (x,y).
Definition int_cc_prop1 {x y : R} : forall r : [x,y], x <= r.
  intro r. 
  apply (subset_elements_satisfy_predicate [x,y]).
Qed.
Definition int_cc_prop2 {x y : R} : forall r : [x, y], r <= y.
  intro r.
  apply (subset_elements_satisfy_predicate [x,y]).
Qed.
Definition int_co_prop1 {x y : R} : forall r : [x,y), x <= r.
  intro r.
  apply (subset_elements_satisfy_predicate [x,y)).
Qed.
Definition int_co_prop2 {x y : R} : forall r : [x,y), r < y.
  intro r.
  apply (subset_elements_satisfy_predicate [x,y)).
Qed.
Definition int_oc_prop1 {x y : R} : forall r : (x,y], x < r.
  intro r.
  apply (subset_elements_satisfy_predicate (x,y]).
Qed.
Definition int_oc_prop2 {x y : R} : forall r : (x,y], r <= y.
  intro r.
  apply (subset_elements_satisfy_predicate (x,y]).
Qed.
Definition int_oo_prop1 {x y : R} : forall r : (x,y), x < r.
  intro r.
  apply (subset_elements_satisfy_predicate (x,y)).
Qed.
Definition int_oo_prop2 {x y : R} : forall r : (x,y), r < y.
  intro r.
  apply (subset_elements_satisfy_predicate (x,y)).
Qed.
Hint Resolve int_cc_prop : additional.
Hint Resolve int_co_prop : additional.
Hint Resolve int_oc_prop : additional.
Hint Resolve int_oo_prop : additional.

Hint Resolve int_cc_prop1 : additional.
Hint Resolve int_cc_prop2 : additional.
Hint Resolve int_co_prop1 : additional.
Hint Resolve int_co_prop2 : additional.
Hint Resolve int_oc_prop1 : additional.
Hint Resolve int_oc_prop2 : additional.
Hint Resolve int_oo_prop1 : additional.
Hint Resolve int_oo_prop2 : additional.
(** ## Absolute values and inverses*)
Lemma div_sign_flip : forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 > 1 / r2 -> 1 / r1 < r2.
Proof.
intros.
unfold Rdiv in *.
rewrite Rmult_1_l in *.
rewrite <- (Rinv_involutive r2).
apply (Rinv_lt_contravar (/ r2) r1).
apply Rmult_lt_0_compat. apply Rinv_0_lt_compat. apply H0. apply H.
apply H1. apply Rgt_not_eq. apply H0.
Qed.

Lemma div_pos : forall r1 r2 : R, r1 > 0 ->1 / r1 > 0.
Proof.
intros. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_0_lt_compat. apply H.
Qed.

Lemma Rabs_zero : forall r : R, Rabs (r - 0) = Rabs r.
Proof.
intros. rewrite Rminus_0_r. trivial.
Qed.

Lemma inv_remove : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 1 / r1 < 1 / r2 -> r1 > r2.
Proof.
intros.
unfold Rdiv in *. rewrite Rmult_1_l in *.
rewrite <- (Rinv_involutive r1), <- (Rinv_involutive r2).
apply (Rinv_lt_contravar (/ r1) (/ r2)). apply Rmult_lt_0_compat. apply Rinv_0_lt_compat. apply H.
apply Rinv_0_lt_compat. apply H0. rewrite Rmult_1_l in *. apply H1.
all: apply Rgt_not_eq; assumption.
Qed.

Lemma Rle_abs_min : forall x : R, -x <= Rabs x.
Proof.
intros. rewrite <- (Rabs_Ropp (x)). apply Rle_abs.
Qed.

Lemma Rge_min_abs : forall x : R, x >= -Rabs x.
Proof.
intros. rewrite <- (Ropp_involutive x). apply Ropp_le_ge_contravar.
rewrite (Rabs_Ropp (- x)). apply Rle_abs.
Qed.

Lemma Rmax_abs : forall a b : R, Rmax (Rabs a) (Rabs b) >= 0.
Proof.
intros.
apply (Rge_trans _ (Rabs a) _).
apply Rle_ge.
apply Rmax_l.
apply (Rle_ge 0 (Rabs a)).
apply Rabs_pos.
Qed.


Hint Resolve div_sign_flip : reals.
Hint Resolve div_pos : reals.
Hint Resolve inv_remove : reals.
Hint Resolve Rabs_left : reals.
Hint Resolve Rabs_right : reals.
Hint Resolve Rabs_left1 : reals.
Hint Resolve Rabs_pos_lt : reals.
Hint Resolve Rabs_zero : reals.
Hint Resolve Rle_abs : reals.
Hint Resolve Rabs_pos : reals.
Hint Resolve Rle_abs_min : reals.
Hint Resolve Rge_min_abs : reals.
Hint Resolve Rmax_abs : reals.


Hint Extern 1 => rewrite Rabs_zero : reals.
(** ## Subsequences*)
