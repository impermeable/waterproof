(** # Suprema and infima*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.

Require Import wplib.Definitions.SetDefinitions.
Require Import wplib.Notations.Notations.
Require Import wplib.Tactics.AdditionalLemmas.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.

Open Scope analysis_scope.
(** ## Upper bounds

A number $M : ℝ$ is called an **upper bound** of a subset $A : ℝ \to \mathsf{Prop}$ of the real numbers, if for all $a : ℝ$, if $a ∈ A$ then $a ≤ M$.*)
Definition is_upper_bound (A : subsets_R) (M : ℝ) :=
  ∀ a : A, a ≤ M.
(** We say that a subset $A : ℝ \to \mathsf{Prop}$ is bounded above if there exists an $M : ℝ$ such that $M$ is an upper bound of $A$.
*)
Definition is_bounded_above (A : subsets_R) :=
  ∃ M : ℝ, is_upper_bound A M.
(** ## The supremum

A real number $L : ℝ$ is called the **supremum** of a subset $A : ℝ \to \mathsf{Prop}$ if it is the smallest upper bound.
*)
Definition is_sup (A : subsets_R) (L : ℝ) :=
  (is_upper_bound A L) ∧ (∀ M : ℝ, is_upper_bound A M ⇒ (L ≤ M) ).
(** 
We have to use `SetDefinitions.is_in` since `is_in` is already defined somewhere, but where?*)
Notation is_in := SetDefinitions.is_in.

Lemma equivalence_upper_bounds :
  ∀ (A : subsets_R) (L : ℝ),
    is_upper_bound A L ⇔
    Raxioms.is_upper_bound (is_in A) L.
Proof.
Take A : subsets_R.
Take L : ℝ.
We show both directions.
Assume L_upp_bd : (is_upper_bound A L).
Expand the definition of Raxioms.is_upper_bound.
Expand the definition of is_upper_bound in L_upp_bd.
Take x : ℝ.
Assume w : (is_in A x).
Define b := (mk_element_R (is_in A) x w).
By L_upp_bd it holds that (b ≤ L) (H).
Apply H.

Assume L_is_upp_bd : (Raxioms.is_upper_bound (is_in A) L).
Expand the definition of is_upper_bound.
Expand the definition of Raxioms.is_upper_bound in L_is_upp_bd.
Take a : A.
By subset_elements_satisfy_predicate it holds that
  (is_in A a) (H1).
By L_is_upp_bd it holds that (a ≤ L).
Qed.
Lemma equivalence_sup_lub :
  ∀ (A : subsets_R) (M : ℝ),
  is_lub (is_in A) M
  ⇔ is_sup A M.
Proof.
Take A : subsets_R.
Take M : ℝ.
We show both directions.

Assume M_is_sup_A : (Notations.is_sup (is_in A) M).
Expand the definition of is_sup.
Expand the definition of Notations.is_sup in M_is_sup_A.
We show both statements.
  Expand the definition of is_upper_bound.
  Take a : A. It holds that (a ≤ M).
  Take M0 : ℝ.
  Assume M_is_ub_A : (is_upper_bound A M0).
  destruct M_is_sup_A as [M_is_R_ub_A M_is_R_lub_A].
  destruct (equivalence_upper_bounds A M0). apply (M_is_R_lub_A M0 (H M_is_ub_A)).

Assume M_is_sup_A : (is_sup A M).
Expand the definition of Notations.is_sup.
Expand the definition of is_sup in M_is_sup_A.
We show both statements.
  Expand the definition of Raxioms.is_upper_bound.
  destruct M_is_sup_A. Expand the definition of is_upper_bound in H.
  Take x : ℝ. Assume x_in_A : (is_in A x). 
  Define b := (mk_element_R (is_in A) x x_in_A).
  By H it holds that (b ≤ M) (H1).
  Apply H1.
  
  Take b : ℝ.
  Assume M_is_R_lub_A : (Raxioms.is_upper_bound (is_in A) b).
  destruct M_is_sup_A as [M_is_ub_A M_is_lub_A].
  Apply (M_is_lub_A b).
  destruct (equivalence_upper_bounds A b). apply (H0 M_is_R_lub_A).
Qed.
(** ## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.*)
Lemma R_complete : ∀ (A : subsets_R) (x : A),
  is_bounded_above A ⇒ mk_subset_R (fun M : ℝ => is_sup A M).
Proof.
Take A : subsets_R.
Take x : A.
Assume A_bdd_above : (is_bounded_above A).
We claim that (sig (is_lub (is_in A))) (H).
  Apply completeness.
  unfold is_bounded_above in A_bdd_above.
  unfold is_upper_bound in A_bdd_above.
  unfold is_bdd_above.
  Choose M such that A_bdd_by_M according to A_bdd_above.
  Choose m := M.
  We need to show that
    (∀ a : ℝ, is_in A a ⇒ a ≤ M).
  Take a : ℝ.
  Assume w : (is_in A a).
  Define b := (mk_element_R (is_in A) a w).
  pose proof (A_bdd_by_M b).
  assumption.
  Choose y := x.
  induction y.
  assumption.
  Choose M such that M_upp_bd according to H.
  
  destruct (equivalence_sup_lub A M) as [M_is_sup_A H2]. specialize (M_is_sup_A M_upp_bd).
  exists M. exact M_is_sup_A.
Qed.
(** 

```
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : subsets_R) (m : ℝ) :=
  ∀ a : A, m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bounded_below (A : subsets_R) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : subsets_R) m 
    => (is_lower_bound A m) ∧ (∀ l : R, is_lower_bound A l ⇒ l ≤ m).
(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, we first introduce the reflection of subsets of $\mathbb{R}$ in the origin. Given a subset $A : ℝ → \mathsf{Prop}$, we consider the set $-A$ (which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : subsets_R)  :=
  mk_subset_R (fun (x : ℝ) ↦ (is_in A (-x))).
Definition original_elem {A : subsets_R} : (set_opp A) -> A.
Proof.
Take opp_a : (set_opp A).
It holds that (is_in (set_opp A) (opp_a)) (H1).
It holds that (is_in A (-opp_a)) (H2).
exact (mk_element_R (is_in A) (-opp_a) H2).
Defined.
Lemma neg_opp_is_original_elem {A : subsets_R} : 
  forall opp_a : (set_opp A), -opp_a = original_elem opp_a.
Proof.
  Take opp_a : (set_opp A). 
  It holds that (-opp_a =  original_elem opp_a).
Qed.
(* TODO: add this to additional lemmas.. *)
(*Hint Resolve neg_opp_is_original_elem : additional.*)
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : subsets_R) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
Take A : subsets_R. Take M : ℝ.
Assume M_upp_bd : (is_upper_bound A M).
We need to show that (∀ a : (set_opp A),-M ≤ a).
Take opp_a : (set_opp A).
Define a := (original_elem opp_a).
It holds that (is_in A a) (H1).
By M_upp_bd it holds that (a ≤ M) (H2).
It holds that (-opp_a = a) (H3).
It holds that (-M ≤ opp_a).
Qed.
Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : subsets_R) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
Take A : subsets_R. Take m : ℝ.
Assume m_low_bd : (is_lower_bound A m).
We need to show that (∀ opp_a : (set_opp A), opp_a ≤ -m).
Take opp_a : (set_opp A).
Define a := (original_elem opp_a).
By m_low_bd it holds that (m ≤ a) (H1).
It holds that (-opp_a = a) (H2).
It holds that (opp_a ≤ -m).
Qed.
Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : subsets_R) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
Take A : (subsets_R). Take m : ℝ.
Assume m_low_bd : (is_lower_bound (set_opp A) m).
We need to show that
  (∀ a : A, a ≤ -m).
Take a : A.
Write m_low_bd as
  (∀ b : (set_opp A), m ≤ b).
We claim that (is_in A (--a)) (minmin_a_in_A).
  Write goal using (--a = a) as
    (is_in A a).
  It holds that (is_in A a).
It holds that (is_in (set_opp A) (-a)) (min_a_in_set_opp_A).
(*By m_low_bd it holds that (m ≤ -a) (m_le_min_a).*)
Define c := (mk_element_R _ (-a) min_a_in_set_opp_A).
We claim that (m ≤ c) (m_le_c).
Apply m_low_bd.
It holds that (m ≤ -a) (m_le_min_a).
It holds that (a ≤ -m).
Qed.
Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : subsets_R) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
Take A : (subsets_R). Take M : ℝ.
Assume M_upp_bd : (is_upper_bound (set_opp A) M).
We need to show that
  (∀ a : A, -M ≤ a).
Take a : A.
We claim that (is_in A (--a)) (minmin_a_in_A).
  Write goal using (--a = a) as
    (is_in A a).
  It holds that (is_in A a).
It holds that (is_in (set_opp A) (-a)) (min_a_in_set_opp_A).
Define c := (mk_element_R _ (-a) (min_a_in_set_opp_A)).
By M_upp_bd it holds that (c ≤ M) (mina_le_M).
It holds that (-a ≤ M) (min_a_le_M).
It holds that (-M ≤ a).
Qed.
Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : subsets_R),
    is_bounded_below A ⇒ is_bounded_above (set_opp A).
Proof.
Take A : (subsets_R). Assume A_bdd_below : (is_bounded_below A).
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
  ∀ (A : subsets_R) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
Take A : (subsets_R). Take M : ℝ.
Assume M_is_sup : (is_sup (set_opp A) M).
Expand the definition of is_inf.
We need to show that
  (is_lower_bound A (-M) ∧
   ∀ l : ℝ, is_lower_bound A l ⇒ 
     l ≤ -M).
split.
We claim that (is_upper_bound (set_opp A) M) (H0).
  Expand the definition of is_upper_bound.
  Take a : (set_opp A).
  Expand the definition of is_sup in M_is_sup.
  By M_is_sup it holds that (is_upper_bound (set_opp A) M) (M_upp_bd).
  It holds that (a ≤ M).
By upp_bd_set_opp_to_low_bd_set it holds that
  (is_lower_bound A (-M)) (H1).
It holds that (is_lower_bound A (-M)).
We need to show that
  (∀ l : ℝ, is_lower_bound A l ⇒
    l ≤ -M).
Take l : ℝ. 
Assume l_low_bd : (is_lower_bound A l).
Expand the definition of is_sup in M_is_sup.
By M_is_sup it holds that
  (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b) (H1).
By low_bd_set_to_upp_bd_set_opp 
  it holds that
  (is_upper_bound (set_opp A) (-l)) (H2).
By H1 it holds that (M ≤ -l) (H3).
It holds that (l ≤ -M).
Qed.
Lemma exists_inf :
  ∀ (A : (subsets_R)) (x : A), is_bounded_below A ⇒
    mk_subset_R (fun m : ℝ => is_inf A m).
Proof.
Take A : (subsets_R).
Take z : A.
Assume A_bdd_below : (is_bounded_below A).
(*Assume ex_x : (∃ x : ℝ, x ∈ A).*)
Define B := (set_opp A).
By bdd_below_to_bdd_above_set_opp 
  it holds that (is_bounded_above B) (B_bdd_above).
We claim that (is_in A (--z)) (min_min_z_in_A).
  Write goal using (--z = z) as (is_in A z).
  It holds that (is_in A z).
It holds that (is_in (set_opp A) (-z)) (min_z_in_B).
Define c := (mk_element_R _ (-z) (min_z_in_B)).
(*We claim that (∃ y : ℝ, y ∈ B) (ex_y_in_B).
  Choose x such that x_in_A according to ex_x.
  Choose y:= (-x).
  We need to show that ((-(-x)) ∈ A).
  Write goal using (--x = x) as
    (x ∈ A).
  It holds that (x ∈ A).*)
Define L := (R_complete B c B_bdd_above).

(*We claim that
  ({L | is_sup B L}) (exists_sup).

Choose L such that L_is_sup according to exists_sup.*)
Choose m := (-L).
We claim that (is_sup B L) (L_is_sup_B).
  destruct L.
  apply witness.
By sup_set_opp_is_inf_set 
  it holds that (is_inf A (-L)) (minL_is_inf_A).
It holds that (is_inf A m).
Qed.
(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : (subsets_R),
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
Take A : (subsets_R). Take M : ℝ. Assume M_is_sup_A : (is_sup A M).
Write M_is_sup_A as (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b) ).
It follows that (is_upper_bound A M). Qed.
(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : (subsets_R),
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
Take A : (subsets_R). Take M : ℝ. Take L : ℝ. 
Assume A_is_sup_M : (is_sup A M).
Assume L_is_upp_bd_A.
Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M.
(** We need to show that $M \leq L$.*)
It holds that (M ≤ L). Qed.
(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : (subsets_R),
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
Take A : (subsets_R).
Take m : R.
Assume m_is_inf_A.
Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m.
(** We now just *)
apply m_is_low_bd
(** to show that $m$ is a lower bound of $A$*)
. Qed.
(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_ge_inf :
  forall A : (subsets_R),
    forall m l : R,
      is_inf A m ⇒ is_lower_bound A l ⇒ l <= m.
Proof.
Take A : (subsets_R).
Take m : R. Take l : R.
Assume m_is_inf_A
(** : $m = \inf A$*)
.
Assume l_is_low_bd_A
(** : $l$ is a lower bound for $A$*)
.
Because m_is_inf_A both m_low_bd and any_low_bd_le_m.
(** We need to show that $l \leq m$.*)
It holds that (l ≤m). Qed.
(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : A, L < a.
Proof.
Take A : (subsets_R). Take M : ℝ.
Assume M_is_sup_A. Take L : ℝ. Assume L_lt_M.
We argue by contradiction. 
We claim that 
  (∀ x : A, x ≤ L) (H1).
  Take x : A.
  It holds that (¬(L < x)) (H2).
  We need to show that (x ≤ L).
  It holds that (x ≤ L).
It holds that (is_upper_bound A L) (H3).
By any_upp_bd_ge_sup it holds that (M ≤ L) (H4).
It holds that (¬(M ≤ L)) (H5).
contradiction.
Qed.
Lemma exists_almost_maximizer_ε :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, M - ε < a.
Proof.
Take A : (subsets_R). Take M : ℝ.
Assume M_is_sup_A. Take ε : ℝ. Assume ε_gt_0.
It holds that (M - ε < M) (H1). 
apply exists_almost_maximizer with (L := M- ε) (M := M); assumption.
Qed.
Lemma max_or_strict :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒ 
      (is_in A M) ∨ (∀ a : A, a < M).
Proof.
Take A : (subsets_R). Take M : ℝ. 
Assume M_is_sup_A. We argue by contradiction. 
By not_or_and it holds that ((¬ (is_in A M)) ∧ 
  ¬(∀ a : A, a < M) ) (H1).
Because H1 both H2 and H3.
(** We only show the proposition on the *)
right
(** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
.
Take a : A.
By sup_is_upp_bd it holds that (is_upper_bound A M) (M_upp_bd).
It holds that (a ≤ M) (a_le_M).
We claim that (¬(element _ a = M)) (a_is_not_M).
We argue by contradiction.
Assume a_eq_M.
We claim that (is_in A M) (M_in_A).
Rewrite using (M=a).
It holds that (is_in A a). contradiction. It holds that (a < M).
Qed.
(** * Lemmas for convenience*)
Lemma bounded_by_upper_bound_propform :
  ∀ (A : subsets_R) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ is_in A b ⇒ b ≤ M.
Proof.
Take A : subsets_R. Take M : ℝ. Take b : ℝ.
Assume M_upp_bd : (is_upper_bound A M).
Assume b_in_A : (is_in A b).
Define c := (mk_element_R (is_in A) b b_in_A).
Expand the definition of is_upper_bound in M_upp_bd.
By M_upp_bd it holds that (c ≤ M) (c_le_M).
It holds that (b ≤ M).
Qed.
Lemma bounded_by_lower_bound_propform :
  ∀ (A : subsets_R) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ is_in A b ⇒ m ≤ b.
Proof.
Take A : subsets_R. Take m : ℝ. Take b: ℝ.
Assume m_low_bd : (is_lower_bound A m).
Assume b_in_A : (is_in A b).
Define c := (mk_element_R (is_in A) b b_in_A).
Expand the definition of is_lower_bound in m_low_bd.
By m_low_bd it holds that (m ≤ c) (m_le_c).
It holds that (m ≤ b).
Qed.

Hint Resolve bounded_by_upper_bound_propform : additional.
Hint Resolve bounded_by_lower_bound_propform : additional.
(** ### **Hints***)
Hint Extern 1 => (unfold is_sup) : unfolds.
Hint Extern 1 => (unfold is_inf) : unfolds.
