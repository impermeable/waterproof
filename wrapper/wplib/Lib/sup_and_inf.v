(*# Suprema and infima*) (*Add LoadPath "./".
Add LoadPath "../../".*)

Add LoadPath "./wrapper/".

Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.

Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra. Definition is_sup := is_lub. (*### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*) Lemma sup_is_upp_bd :
  forall A : R -> Prop,
    forall M : R,
      is_sup A M -> is_upper_bound A M. Proof.
Take A : (R -> Prop). Take M : R. Assume M_is_sup_A. 
Because M_is_sup_A both M_is_upp_bd_A and any_upp_bd_A_le_M. (*We now just*) apply M_is_upp_bd_A (*to show that $M$ is an upper bound for A*) . Qed. (*### Any upper bound is greater than or equal to the supremum*) Lemma any_upp_bd_ge_sup :
  forall A : R -> Prop,
    forall M L : R,
      is_sup A M -> (is_upper_bound A L -> M <= L). Proof.
Take A : (R -> Prop). Take M : R. Take L : R. 
Assume A_is_sup_M. Assume L_is_upp_bd_A. Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M. (*We need to show that $M \leq L$.*) This follows immediately. Qed. (*## Infima*) Definition is_lower_bound :=
  fun (A : R -> Prop) m 
    => forall a : R, A a -> m <= a. Definition is_inf :=
  fun (A : R -> Prop) m 
    => (is_lower_bound A m) /\ (forall l : R, is_lower_bound A l -> l <= m). (*## An infimum is a lower bound*) Lemma inf_is_low_bd :
  forall A : R -> Prop,
    forall m : R,
      is_inf A m -> is_lower_bound A m. Proof.
Take A : (R -> Prop).
Take m : R.
Assume m_is_inf_A.
Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m. (*We now just *) apply m_is_low_bd (*to show that $m$ is a lower bound of $A$*) . Qed. (*## Any lower bound is less than or equal to the infimum*) Lemma any_low_bd_ge_inf :
  forall A : R -> Prop,
    forall m l : R,
      is_inf A m -> is_lower_bound A l -> l <= m. Proof.
Take A : (R -> Prop).
Take m : R. Take l : R. Assume m_is_inf_A (*: $m = \inf A$*) . Assume l_is_low_bd_A (*: $l$ is a lower bound for $A$*) . Because m_is_inf_A both m_low_bd and any_low_bd_le_m. (*We need to show that $l \leq m$.*) This follows immediately. Qed. (*### $\varepsilon$-characterizations*) Lemma exists_almost_maximizer :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, A a ∧ L < a. Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_is_sup_A. Take L : ℝ. Assume L_lt_M.
We argue by contradiction. 
We claim that 
  (∀ x : ℝ, A x ⇒ x ≤ L) (H1).
  Take x : ℝ. Assume x_in_A. 
  It holds that (¬(L < x)) (H2).
  We need to show that (x ≤ L). This follows immediately.
It holds that (is_upper_bound A L) (H3).
By any_upp_bd_ge_sup it holds that (M ≤ L) (H4).
It holds that (¬(M ≤ L)) (H5).
contradiction.
Qed. Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, A a ∧ M - ε < a. Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_is_sup_A. Take ε : ℝ. Assume ε_gt_0.
It holds that (M - ε < M) (H1). 
apply exists_almost_maximizer with (L := M- ε) (M := M); assumption.
Qed. Lemma max_or_strict :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, A a ⇒ a < M). Proof.
Take A : (ℝ → Prop). Take M : ℝ. 
Assume M_is_sup_A. We argue by contradiction. 
By not_or_and it holds that ((¬ (A M)) ∧ 
  ¬(∀ a : ℝ, A a ⇒ a < M) ) (H1).
Because H1 both H2 and H3. (*We only show the proposition on the *) right (*hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*) . Take a : ℝ. Assume a_in_A.
By sup_is_upp_bd it holds that (is_upper_bound A M) (M_upp_bd).
It holds that (a ≤ M) (a_le_M).
We claim that (¬(a = M)) (a_is_not_M).
We argue by contradiction.
Assume a_eq_M.
We claim that (A M) (M_in_A).
Rewrite using (M=a).
assumption. contradiction. This follows immediately.
Qed. (*## Suprema and sequences*) Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε. Proof.
Take a : (ℕ → ℝ). Take pr : (has_ub a). 
Expand the definition of lub.
Define sup_with_proof := (ub_to_lub a pr).
Choose l such that l_is_sup according to sup_with_proof.
Take ε : ℝ. Assume ε_gt_0.
By exists_almost_maximizer_ε it holds that (∃ y : ℝ, (EUn a) y ∧ y > l - ε) (H1).
Choose y such that H2 according to H1.
Because H2 both y_in_range and y_gt_l_min_ε.
Expand the definition of EUn in y_in_range.
Choose i such that ai_is_y according to y_in_range.
Choose k := i.
Rewrite using (a i = y).
Apply y_gt_l_min_ε.
Qed. Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1). Proof.
Take a : (ℕ → ℝ). Take pr : (has_ub a). Take m : ℕ.
Apply seq_ex_almost_maximizer_ε. (*We need to show that $1/(m+1) > 0$.*)  Rewrite using (1 / (INR m + 1) = / (INR m + 1)).  (*We need to show that $(m+1) > 0$. *) This follows immediately. Qed. Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1). Proof.
Take a : (ℕ → ℝ). Take pr : (has_ub a). Take m : ℕ. Take N : ℕ.
We claim that (∃ i : ℕ, a (N + i)%nat > sequence_ub a pr N - 1 / (INR m + 1)) (H1).
Apply seq_ex_almost_maximizer_m.
Choose i such that i_good according to H1.
Choose k := (N+i)%nat.
This follows immediately.
Qed. 