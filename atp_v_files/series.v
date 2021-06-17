(** # Series*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Tactics.Databases.
Require Import wplib.Notations.Notations.
Require Import wplib.Lib.sequences.

Hint Resolve Rabs_Rabsolu.
Hint Resolve Rabs_minus_sym.
Hint Resolve Rmult_lt_0_compat : real.
Hint Resolve Rinv_lt_contravar : real.
Lemma sigma_split_v2 :
  ∀ (a : ℕ → ℝ) (k l N : ℕ),
    (k < l)%nat ⇒ (l ≤ N)%nat 
      ⇒ sigma a k N = sigma a k (l - 1)%nat + sigma a l N.
Proof.
Take a : (ℕ → ℝ). Take k : ℕ.
Take l : ℕ. Take N : ℕ.
Assume k_lt_N. Assume l_le_N.
It holds that (l = S (l - 1)%nat ) (H1).
rewrite H1 at 2.
apply sigma_split with (low := k) (k := (l-1)%nat) (high := N).
This follows immediately. This follows immediately.
Qed.
Notation partial_sums := sum_f_R0.

Lemma partial_sums_pos_incr :
  ∀ (a : ℕ → ℝ), (∀ n : ℕ, a n ≥ 0)⇒
    Un_growing (partial_sums a).
Proof.
Take a : (ℕ → ℝ).
Assume terms_pos : (∀ n : ℕ, a n ≥ 0).
Expand the definition of Un_growing.
We need to show that
  (for all n : ℕ,
   partial_sums a n ≤ partial_sums a (S n)).
Take n : ℕ.
Rewrite using (partial_sums a (S n) = partial_sums a n + a (S n)).
It holds that (a (S n) ≥ 0) (H1).
It follows that (partial_sums a n
≤ partial_sums a n + a (S n)).
Qed.
Definition series_cv_to (a : ℕ → ℝ) (l : ℝ) :=
  Un_cv (partial_sums a) l.
Definition series_cv (a : ℕ → ℝ) :=
  ∃ l : ℝ, series_cv_to a l.
Definition series_cv_abs (a : ℕ → ℝ) :=
  series_cv (fun n ↦ Rabs( a n )).
Definition series_cv_abs_to (a : ℕ → ℝ) (l : ℝ) :=
  series_cv_to (fun n ↦ Rabs(a n)) l.
Theorem mouse_tail :
  ∀ (a : ℕ → ℝ) (k l : ℕ) (L : ℝ),
    (k < l)%nat ⇒
      ((Un_cv (fun N ↦ sigma a l N) L)
        ⇔ 
      (Un_cv (fun N ↦ sigma a k N) ((sigma a k (l-1)) + L))).
Proof.
Take a : (ℕ → ℝ). Take k : ℕ.
Take l : ℕ. Take L : ℝ. Assume k_lt_l.
split.
Assume sigma_l_cv.
We claim that
  (Un_cv (fun N ↦ sigma a k (l-1)%nat) (sigma a k (l-1)%nat)) (H1).
  Apply lim_const_seq.
By CV_plus it holds that 
  (Un_cv (fun N ↦ sigma a k (l-1)%nat 
                  + 
                  sigma a l N)
         (sigma a k (l-1)%nat + L) ) (H2).
We claim that
  (∃ M : ℕ, 
    ∀ n : ℕ, (n ≥ M)%nat ⇒
      sigma a k n = sigma a k (l - 1)%nat + sigma a l n ) (H3).
Choose M := l%nat.
Take n : ℕ. Assume n_ge_l. Apply sigma_split_v2. assumption. assumption.
apply conv_evt_eq_seq
  with (a := fun N ↦ sigma a k (l-1) + sigma a l N)
       (b := fun N ↦ sigma a k N).
Choose M such that H5 according to H3.
Choose k0 := M.
Take n : ℕ. Assume n_ge_M : (n ≥ M)%nat.
It holds that (sigma a k n = sigma a k (l-1) + sigma a l n) (H6).
It holds that (sigma a k (l-1) + sigma a l n = sigma a k n).
Apply H2.
Assume sigma_k_cv.
We claim that
  (Un_cv (fun N ↦ sigma a k (l-1)) (sigma a k (l-1))) (H7).
  Apply lim_const_seq.
By CV_minus it holds that
  (Un_cv (fun N ↦ sigma a k N - (sigma a k (l-1)))
         (sigma a k (l-1) + L - (sigma a k (l-1)))) (H8).
We claim that
  (∃ M : ℕ, 
    ∀ n : ℕ, (n ≥ M)%nat ⇒
      sigma a k n - sigma a k (l - 1)%nat = sigma a l n ) (H9).
Choose M := l.
Take n : ℕ. Assume n_ge_l : (n ≥ l)%nat. 
By sigma_split_v2 it holds that 
  (sigma a k n = sigma a k (l - 1)%nat + sigma a l n) (H10).
We need to show that (sigma a k n - sigma a k (l-1) = sigma a l n).
It follows that (sigma a k n - sigma a k (l - 1) =
sigma a l n).

Rewrite using (L = sigma a k (l-1) + L - sigma a k (l-1)).
apply conv_evt_eq_seq
  with (a := fun n ↦ sigma a k n - sigma a k (l-1))
       (b := fun n ↦ sigma a l n).
Choose M such that H11 according to H9.
Choose k0 := M.
Apply H11.
Apply H8.
Qed.
 
