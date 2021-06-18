(** # Suprema and infima*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.

Require Import wplib.Tactics.Tactics.
Require Import wplib.Notations.Notations.
Require Import wplib.Tactics.TacticsContra.

Open Scope analysis_scope.
(** ## Upper bounds

A number $M : ℝ$ is called an **upper bound** of a subset $A : ℝ \to \mathsf{Prop}$ of the real numbers, if for all $a : ℝ$, if $a ∈ A$ then $a ≤ M$.

```
Definition is_upper_bound (A : ℝ → Prop) (M : ℝ) :=
  ∀ a : A, a ∈ A ⇒ a ≤ M.
```

We say that a subset $A : ℝ \to \mathsf{Prop}$ is bounded above if there exists an $M : ℝ$ such that $M$ is an upper bound of $A$.

```
Definition is_bounded_above (A : ℝ → Prop) :=
  ∃ M : ℝ, is_upper_bound A M.
```

## The supremum

A real number $L : ℝ$ is called the **supremum** of a subset $A : ℝ \to \mathsf{Prop}$ if it is the smallest upper bound.
```
Definition is_sup (A : ℝ → Prop) (L : ℝ) :=
  (is_upper_bound A L) ∧ (∀ M : ℝ, is_upper_bound A M ⇒ (L ≤ M) ).
```

## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.

```
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : ℝ → Prop) (m : ℝ) :=
  ∀ a : ℝ, a ∈ A ⇒ m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bdd_below (A : ℝ → Prop) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : ℝ → Prop) m 
    => (is_lower_bound A m) ∧ (∀ l : R, is_lower_bound A l ⇒ l ≤ m).
(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, we first introduce the reflection of subsets of $\mathbb{R}$ in the origin. Given a subset $A : ℝ → \mathsf{Prop}$, we consider the set $-A$ (which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : ℝ → Prop)  :=
  fun (x : ℝ) ↦ (A (-x)).
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_upp_bd : (is_upper_bound A M).
We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ -M ≤ a).
Take a : ℝ. Assume min_a_in_A : (-a ∈ A).
By M_upp_bd it holds that (-a ≤ M) (H1).
It holds that (-M ≤ a).
Qed.
Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
Take A : (ℝ → Prop). Take m : ℝ.
Assume m_low_bd : (is_lower_bound A m).
We need to show that (∀ a : ℝ, (-a ∈ A) ⇒ a ≤ -m).
Take a : ℝ. Assume min_a_in_A : (-a ∈ A).
By m_low_bd it holds that (m ≤ -a) (H1).
It holds that (a ≤ -m).
Qed.
Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : ℝ → Prop) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
Take A : (ℝ → Prop). Take m : ℝ.
Assume m_low_bd : (is_lower_bound (set_opp A) m).
We need to show that
  (∀ a : ℝ, a ∈ A ⇒ a ≤ -m).
Take a : ℝ. Assume a_in_A : (a ∈ A).
Write m_low_bd as
  (∀ a : ℝ, (-a) ∈ A ⇒ m ≤ a).
We claim that (--a ∈ A) (minmin_a_in_A).
  Write goal using (--a = a) as
    (a ∈ A).
  It holds that (a ∈ A).
By m_low_bd it holds that (m ≤ -a) (m_le_min_a).
It holds that (a ≤ -m).
Qed.
Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_upp_bd : (is_upper_bound (set_opp A) M).
We need to show that
  (∀ a : ℝ, a ∈ A ⇒ -M ≤ a).
Take a : ℝ. Assume a_in_A : (a ∈ A).
We claim that (--a ∈ A) (minmin_a_in_A).
  Write goal using (--a = a) as
    (a ∈ A).
  It holds that (a ∈ A).
By M_upp_bd it holds that (-a ≤ M) (mina_le_M).
It holds that (-M ≤ a).
Qed.
Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : ℝ → Prop),
    is_bdd_below A ⇒ is_bdd_above (set_opp A).
Proof.
Take A : (ℝ → Prop). Assume A_bdd_below : (is_bdd_below A).
We need to show that
  (∃ M : ℝ, is_upper_bound (set_opp A) M).
Write A_bdd_below as
  (∃ m : ℝ, is_lower_bound A m).
Choose m such that m_low_bd according to A_bdd_below.
Choose M := (-m).
We need to show that (is_upper_bound (set_opp A) (-m)).
By low_bd_set_to_upp_bd_set_opp it holds that
  (is_upper_bound (set_opp A) (-m)) (H_con).
It holds that (is_upper_bound (set_opp A) (-m)).
Qed.
Lemma sup_set_opp_is_inf_set :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_is_sup : (is_sup (set_opp A) M).
Expand the definition of is_inf.
We need to show that
  (is_lower_bound A (-M) ∧
   ∀ l : ℝ, is_lower_bound A l ⇒ 
     l ≤ -M).
split.
Expand the definition of is_sup in M_is_sup.
By M_is_sup it holds that (is_upper_bound (set_opp A) M) (M_upp_bd).
By upp_bd_set_opp_to_low_bd_set it holds that
  (is_lower_bound A (-M)) (H1).
It holds that (is_lower_bound A (-M)).
We need to show that
  (∀ l : ℝ, is_lower_bound A l ⇒
    l ≤ -M).
Take l : ℝ. 
Assume l_low_bd : (is_lower_bound A l).
Expand the definition of is_sup in M_is_sup.
By M_is_sup it holds that (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b) (H1).
By low_bd_set_to_upp_bd_set_opp 
  it holds that
  (is_upper_bound (set_opp A) (-l)) (H2).
By H1 it holds that (M ≤ -l) (H3).
It holds that (l ≤ -M).
Qed.
Lemma exists_inf :
  ∀ A : (ℝ →  Prop), is_bdd_below A ⇒
    ((∃ x : ℝ, x ∈ A) ⇒ { m : ℝ | is_inf A m }).
Proof.
Take A : (ℝ → Prop). Assume A_bdd_below : (is_bdd_below A).
Assume ex_x : (∃ x : ℝ, x ∈ A).
Define B := (set_opp A).
By bdd_below_to_bdd_above_set_opp 
  it holds that (is_bdd_above B) (B_bdd_above).
We claim that (∃ y : ℝ, y ∈ B) (ex_y_in_B).
  Choose x such that x_in_A according to ex_x.
  Choose y:= (-x).
  We need to show that ((-(-x)) ∈ A).
  Write goal using (--x = x) as
    (x ∈ A).
  It holds that (x ∈ A).
By completeness it holds that
  ({L | is_sup B L}) (exists_sup).
Choose L such that L_is_sup according to exists_sup.
Choose m := (-L).
By sup_set_opp_is_inf_set 
  it holds that (is_inf A (-L)) (minL_is_inf_A).
It holds that (is_inf A m).
Qed.
(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : ℝ → Prop,
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
Take A : (ℝ → Prop). Take M : ℝ. Assume M_is_sup_A : (is_sup A M).
Write M_is_sup_A as (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b) ).
It follows that (is_upper_bound A M). Qed.
(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : ℝ → Prop,
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
Take A : (ℝ → Prop). Take M : ℝ. Take L : ℝ. 
Assume A_is_sup_M : (is_sup A M).
Assume L_is_upp_bd_A.
Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M.
(** We need to show that $M \leq L$.*)
This follows immediately. Qed.
(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : ℝ → Prop,
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
Take A : (R -> Prop).
Take m : R.
Assume m_is_inf_A.
Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m.
(** We now just *)
apply m_is_low_bd
(** to show that $m$ is a lower bound of $A$*)
. Qed.
(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_ge_inf :
  forall A : R -> Prop,
    forall m l : R,
      is_inf A m -> is_lower_bound A l -> l <= m.
Proof.
Take A : (R -> Prop).
Take m : R. Take l : R.
Assume m_is_inf_A
(** : $m = \inf A$*)
.
Assume l_is_low_bd_A
(** : $l$ is a lower bound for $A$*)
.
Because m_is_inf_A both m_low_bd and any_low_bd_le_m.
(** We need to show that $l \leq m$.*)
This follows immediately. Qed.
(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : ℝ, A a ∧ L < a.
Proof.
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
Qed.
Lemma exists_almost_maximizer_ε :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : ℝ, A a ∧ M - ε < a.
Proof.
Take A : (ℝ → Prop). Take M : ℝ.
Assume M_is_sup_A. Take ε : ℝ. Assume ε_gt_0.
It holds that (M - ε < M) (H1). 
apply exists_almost_maximizer with (L := M- ε) (M := M); assumption.
Qed.
Lemma max_or_strict :
  ∀ (A : ℝ → Prop) (M : ℝ),
    is_sup A M ⇒ 
      (A M) ∨ (∀ a : ℝ, A a ⇒ a < M).
Proof.
Take A : (ℝ → Prop). Take M : ℝ. 
Assume M_is_sup_A. We argue by contradiction. 
By not_or_and it holds that ((¬ (A M)) ∧ 
  ¬(∀ a : ℝ, A a ⇒ a < M) ) (H1).
Because H1 both H2 and H3.
(** We only show the proposition on the *)
right
(** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
.
Take a : ℝ. Assume a_in_A.
By sup_is_upp_bd it holds that (is_upper_bound A M) (M_upp_bd).
It holds that (a ≤ M) (a_le_M).
We claim that (¬(a = M)) (a_is_not_M).
We argue by contradiction.
Assume a_eq_M.
We claim that (A M) (M_in_A).
Rewrite using (M=a).
assumption. contradiction. This follows immediately.
Qed.
(** ## Suprema and sequences*)
Lemma seq_ex_almost_maximizer_ε :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (ε : ℝ), 
    ε > 0 ⇒ ∃ k : ℕ, a k > lub a pr - ε.
Proof.
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
We need to show that (a i > l - ε).
Rewrite using (a i = y).
Apply y_gt_l_min_ε.
Qed.
Lemma seq_ex_almost_maximizer_m :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ), 
    ∃ k : ℕ, a k > lub a pr - 1 / (INR(m) + 1).
Proof.
Take a : (ℕ → ℝ). Take pr : (has_ub a). Take m : ℕ.
Apply seq_ex_almost_maximizer_ε.
(** We need to show that $1/(m+1) > 0$.*)
 Rewrite using (1 / (INR m + 1) = / (INR m + 1)). 
(** We need to show that $(m+1) > 0$. *)
This follows immediately. Qed.
Lemma exists_almost_lim_sup_aux :
  ∀ (a : ℕ → ℝ) (pr : has_ub a) (m : ℕ) (N : ℕ),
    ∃ k : ℕ, (k ≥ N)%nat ∧ a k > sequence_ub a pr N - 1 / (INR(m) + 1).
Proof.
Take a : (ℕ → ℝ). Take pr : (has_ub a). Take m : ℕ. Take N : ℕ.
We claim that (∃ i : ℕ, a (N + i)%nat > sequence_ub a pr N - 1 / (INR m + 1)) (H1).
Apply seq_ex_almost_maximizer_m.
Choose i such that i_good according to H1.
Choose k := (N+i)%nat.
This follows immediately.
Qed.
