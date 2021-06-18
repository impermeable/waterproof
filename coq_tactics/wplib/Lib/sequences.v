(** # Sequences*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Notations.Notations.

Hint Resolve Rabs_Rabsolu.
Hint Resolve Rabs_minus_sym.
Hint Resolve Rmult_lt_0_compat : real.
Hint Resolve Rinv_lt_contravar : real.

Open Scope extra.
(** ## What is a sequence?

A sequence of real numbers is a function from the natural numbers to the real numbers. So a function $a : \mathbb{N} → \mathbb{R}$ is a sequence.*)
(** ### Examples of sequences

Let us give a few examples of sequences of real numbers. The first example is the sequence $a : ℕ → ℝ$ defined by 

$$a := \mathsf{fun} \   n \mapsto \mathsf{INR}(n) + 2.$$

In Waterproof, we can write this as*)

Definition a : ℕ → ℝ := fun n ↦ INR(n) + 2.
(** We could also have written that $a: \mathbb{N} → ℝ$ is defined by $a_n := \mathsf{INR} (n) + 2$, and usually we just leave out the function $\mathsf{INR}$ and would write $a_n := n + 2$.*)
(** 
Another example is the sequence $b: ℕ → ℝ$ defined by $b_n := 3$. The sequence $b$ is just constant! Within Waterproof, we could define the sequence $b$ by
```
Definition b : ℕ → ℝ := 3.
```

However, let us also give an alternative way, which looks a  bit closer to the definition $b_n := 3$.*)

Definition b (n : ℕ) := 3.
(** ## Terminology about sequences

We call the function values $a(0)$, $a(1)$, $a(2)$, $\dots$ the **elements** of the sequence. Instead of $a(n)$, in mathematics we often write $a_n$. Moreover, instead of writing *let $a : \mathbb{N} \to \mathbb{R}$ be a sequence*, one often writes *let $(a_n)_{n \in \mathbb{N}}$ be a sequence*, or even shorter *let $(a_n)$ be a sequence*. 

The reason for the name *sequence* becomes clearer by writing the elements in a row, i.e. in a sequence,
$$
a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, \dots
$$

However convenient and intuitive this notation is, it can also become confusing if you forget that a sequence of real numbers is *really* a function from the natural numbers to the real numbers.*)
(** ## Asymptotic behavior of sequences

Analysis all revolves around questions such as: what happens if a parameter gets very small? What happens if a parameter gets very large?

For sequences, the interesting question is: what can we say about the elements $a_n$ when $n$ gets very large? Think for instance about the sequence $a_n := 1/n$. Then we might want to say: when $n$ gets very large, the element $a_n$ is very close to zero.

The only thing is, that we need to make the previous sentence much more precise if we want to work with it in mathematics. For all $\epsilon : ℝ$, if $ε > 0$, then there is a certain threshold $N : ℕ$ such that for all $n: ℕ$, if $n \geq N$ then $a_n$ is within distance $\epsilon$ from $0$.`*)
(** The definition of `cv_to` is completely equivalent to the definition of `Un_cv` in the standard library. *)
Lemma convergence_equivalence : converges_to = Un_cv.
Proof.
  trivial.
Qed.
(** ## Preparation for a simple limit*)
Lemma archimed_mod :
  ∀ x : ℝ, ∃ n : ℕ, INR(n) > x.
Proof.
Take x : ℝ.
Either (x <= 0) or (0 < x).
Choose n := 1%nat.
It holds that (INR 1 > INR 0) (H1).
Rewrite using (0 = INR(0)) in r.
It follows that (INR 1 > x).

By archimed it holds that (IZR( up x) > x ∧ IZR( up x ) - x ≤ 1) (H2).
It holds that (IZR( up x ) > x) (H3).
It holds that (0 < IZR( up x )) (H4).
By lt_0_IZR it holds that (0 < up x)%Z (H5).
It holds that (0 <= up x)%Z (H6).
By IZN it holds that (∃ k : ℕ, up x = Z.of_nat k) (H7).
Choose k such that up_x_is_k according to H7.
Choose n := k.
We need to show that (INR k > x).
By INR_IZR_INZ it holds that (INR k = IZR (Z.of_nat k)) (H8).
Rewrite using (INR k = IZR (Z.of_nat k)).
Rewrite using (Z.of_nat k = up x).
This follows by assumption.
Qed.
(** Next, we introduce eventually equal sequences, and show that they converge to the same limit.*)
Definition evt_eq_sequences (a b : ℕ → ℝ) := (∃ k : ℕ,
      ∀ n : ℕ, (n ≥ k)%nat ⇒ a n = b n).

Lemma conv_evt_eq_seq :
  ∀ (a b : ℕ → ℝ) (l : ℝ), evt_eq_sequences a b ⇒ a ⟶ l ⇒ b ⟶ l.
Proof.
Take a, b : (ℕ → ℝ) and l : ℝ.
Assume a_b_similar and a_to_l.

To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜(b n) - l ｜ <ε).

Take ε : ℝ; such that ε_gt_0 : (ε > 0).
Choose n1 such that a_close_to_l according to (a_to_l ε ε_gt_0).
Choose k such that an_is_bn_for_n_ge_k according to a_b_similar.
Choose N := (Nat.max n1 k).

Take n : ℕ; such that n_ge_N : (n ≥ N)%nat.
It holds that (a n = b n) (an_eq_bn). 
It holds that (|(a n) - l | < ε) (an_close_to_l).

Rewrite (｜(b n) - l ｜) = (｜(a n) - l｜) < ε.
Qed.
(** From This, it is fairly easy to prove that sequences that are exactly the same also converge to the same limit.
We do this by first using the lemma, and then proving that the sequences are indeed eventually equal.*)
Lemma eq_seq_conv_to_same_lim :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n = b n) ⇒ a ⟶ l ⇒ b ⟶ l.
Proof.
Take a, b : (ℕ → ℝ) and l : R.
Assume seq_eq: (∀ n : ℕ, a n = b n).
Apply conv_evt_eq_seq.
(** By our lemma, it suffices to prove that (evt_eq_sequences a b) *)

We need to show that (∃ k : ℕ, ∀ n : ℕ, 
  (n ≥ k)%nat ⇒ a n = b n).
Choose k := O.
Take n : ℕ; such that n_gt_k : (n ≥ k)%nat.
Then (a n = b n) holds by assumption.
Qed.
(** ## A simple limit

The simplest sequence we can think of is the constant sequence, e.g. $1, 1, 1, 1, 1, ...$.
We can generalise this to any real number $c$, and define the constant sequence $s_n = c, ∀ n : \mathbb{N}$.
Since we can choose $n$ as large as possible, without changing the value of $s_n$, this sequences clearly converges to its constant value $c$, i.e. $\lim_{n \to \infty} s_n = c$.*)
Definition constant_sequence (c : ℝ) := fun (n : ℕ) ↦ c.
Lemma lim_const_seq :
  ∀ (c : ℝ), constant_sequence c ⟶ c.
Proof.
Take c : ℝ. 
Define s := (constant_sequence c).
To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜(s n) - c｜ < ε).

Take ε : ℝ; such that ε_gt_0 : (ε > 0).
Choose N := O.
Take n : ℕ; such that n_ge_N : (n ≥ N)%nat.
It holds that (s n = c) (H).
It holds that (｜c - c｜ = 0) (H1).
Rewrite (｜s n - c｜) = (｜c - c｜) < ε.
Qed.
(** #### **Another simple limit**

Next, we consider another rather simple sequence, namely $1, \frac{1}{2}, \frac{1}{3}, \frac{1}{4}, ...$.
We can denote the sequence as follows:
$$
  d_n = \frac{1}{n+1}.
$$
This is a bit more involved than the constant sequence, since the value of our sequence now depends on $n$.
Still, it is easy to see that when $n$ increases, the value of $d_n$ converges to $0$.*)
Definition d := fun (n : ℕ) ↦ 1 / (n + 1).

Lemma lim_d_0 : Un_cv d 0.
Proof.
Expand the definition of d. 
Expand the definition of Un_cv.
Take ε : ℝ. Assume ε_gt_0 : (ε > 0).
Choose n1 such that H_large according to
  (archimed_mod (/ε)).
Choose N := n1. 
Take n : ℕ. Assume n_ge_n1 : (n ≥ n1)%nat.
Expand the definition of R_dist.
Apply Rabs_def1.
Rewrite using (1 / (INR n + 1) - 0 = 1 / (INR n + 1)).
We need to show that (1 / (INR n+1) < ε ).
Rewrite using (ε = / / ε).
We need to show that (1 / (INR n+1) < / / ε ).
Rewrite using (1/(INR n+1) = /(INR n+1)).
We need to show that (/ (INR n+1) < / / ε ).
Apply (Rinv_lt_contravar :
  for all r1 r2 : R, 0 < r1 * r2 -> r1 < r2 -> / r2 < / r1).
We need to show that (0 < / ε * (INR n + 1)).
This follows immediately.

It holds that (/ ε < INR n1) (H2).
By le_INR it holds that (INR n1 ≤ INR n ) (H3).
It holds that (INR n < INR n + 1) (H4).
We need to show that (/ ε < INR n + 1 ).
This follows immediately.
Rewrite using (1/(INR n + 1) - 0 = / (INR n + 1)).
It holds that (INR n + 1 > 0) (H5).
It holds that (/(INR n + 1) > 0) (H6).
This follows immediately.
Qed.
Lemma min_1_over_n_plus_1_to_0 :
  Un_cv (fun (n : ℕ) ↦ - (1 / (INR(n) + 1))) 0.
Proof.
By lim_d_0 it holds that (Un_cv d 0) (H1).
By (CV_opp) it holds that (Un_cv (opp_seq d) (-0)) (H2).
Rewrite using (-0 = 0) in H2.
Expand the definition of opp_seq in H2.
Expand the definition of d in H2.
assumption.
Qed.
(** ## The squeeze theorem*)
Theorem squeeze_theorem :
  ∀ (a : ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℝ) (l : ℝ),
    (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) ⇒
      a ⟶ l ⇒ c ⟶ l ⇒ b ⟶ l.
Proof.
Take a, b and c: (ℕ → ℝ). Take l : ℝ.
Assume b_squeezed : (∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n).
Assume a_cv_to_l : (a ⟶ l) and c_cv_to_l : (c ⟶ l).

To show: (∀ ε : ℝ, ε > 0 ⇒ ∃ N : ℕ, ∀ n : ℕ, (n ≥ N)%nat ⇒ ｜b n - l｜ < ε).
Take ε : ℝ; such that ε_gt_0 : (ε > 0). 
Choose Na such that a_close_to_l according to (a_cv_to_l ε ε_gt_0).
Choose Nc such that c_close_to_l according to (c_cv_to_l ε ε_gt_0).
Choose N := (Nat.max Na Nc).

Take n : ℕ; such that n_ge_N : (n ≥ N)%nat.

It holds that (n ≥ Na)%nat (n_ge_Na).
It holds that (R_dist (a n) l < ε) (d_an_l_lt_ε).
Expand the definition of R_dist in d_an_l_lt_ε.
Rewrite using (Rabs( a n - l  ) = Rabs( l - a n)) in d_an_l_lt_ε.
By Rabs_def2 it holds that (l - a n < ε ∧- ε < l - a n) (H2).
It holds that (- ε < l - a n) (H3).
It holds that (n ≥ Nc)%nat (n_ge_Nc).
It holds that (R_dist (c n) l < ε) (d_cn_l_lt_ε).
Expand the definition of R_dist in d_cn_l_lt_ε.
By Rabs_def2 it holds that (c n - l < ε ∧ - ε < c n - l) (H4).
It holds that (c n - l < ε) (H5).
Expand the definition of R_dist.
Apply Rabs_def1. 
By b_squeezed it holds that (a n ≤ b n ∧ b n ≤ c n) (H6).
By b_squeezed it holds that (a n ≤ b n) (H7). 
We need to show that ( b n - l < ε).
This follows immediately.
It holds that (a n ≤ b n ∧ b n ≤ c n) (H6).
By b_squeezed it holds that (b n ≤ c n) (H8).
We need to show that (- ε < b n - l).
This follows immediately.
Qed.
Lemma upp_bd_seq_is_upp_bd_lim :
  ∀ (a : ℕ → ℝ) (L M: ℝ),
    (∀ n : ℕ, a n ≤ M) ⇒ 
      (Un_cv a L) ⇒ L ≤ M.
Proof.
Take a : (ℕ → ℝ).
Take L : ℝ. Take M : ℝ.
Assume a_bdd_by_M : (∀ n : ℕ, a n ≤ M).
Assume a_cv_to_L : (Un_cv a L).
By Rle_or_lt it holds that (L ≤ M ∨ M < L) (H).
Because H either L_le_M or M_lt_L.
(** We first consider the case that $L \leq M$. *)
It follows that (L ≤ M).
(** 
Next, we consider the case $M < L$.*)
Define ε := (L-M).
Expand the definition of Un_cv in a_cv_to_L.
We claim that (∃ N : ℕ, ∀n : ℕ, (n ≥ N)%nat ⇒ R_dist (a n) L < ε) (H2).
  Apply a_cv_to_L. It holds that (L - M > 0) (H3). It follows that (ε > 0).
Choose N such that a_close_to_L according to H2.
It holds that (R_dist (a N) L < ε) (H4).
Expand the definition of R_dist in H4.
By Rabs_def2 it holds that (a N - L < ε ∧ (- ε < a N - L)) (H5).
It holds that (- ε < a N - L) (H6).
It holds that (a N ≤ M) (H7).
Rewrite using (ε = L - M) in H6.
It follows that (L ≤ M).
Qed.
Lemma low_bd_seq_is_low_bd_lim :
  ∀ (a : ℕ → ℝ) (L M: ℝ),
    (∀ n : ℕ, a n ≥ M) ⇒ 
      (Un_cv a L) ⇒ L ≥ M.
Proof.
Take a : (ℕ → ℝ).
Take L : ℝ. Take M : ℝ. 
Assume a_bdd_by_M : (∀ n : ℕ, a n ≥ M).
Define b := (opp_seq a).
Assume a_cv_to_L : (Un_cv a L).
By CV_opp it holds that (Un_cv b (-L)) (H).
We claim that (-L ≤ -M) (H1).
Apply (upp_bd_seq_is_upp_bd_lim b).
We need to show that (for all n : ℕ, b n ≤ - M).
  Take n : ℕ. Rewrite using (b = opp_seq a). Expand the definition of opp_seq. This follows immediately.
We need to show that (Un_cv b (-L)). This follows immediately.
It follows that (L ≥ M).
Qed.
(** ## Order and limits*)
Lemma seq_ordered_lim_ordered :
  ∀ (a b: ℕ → ℝ) (m l : ℝ),
    Un_cv a m ⇒ Un_cv b l ⇒
    (∀ n : ℕ, a n ≤ b n) ⇒ m ≤ l.
Proof.
Take a : (ℕ → ℝ). Take b : (ℕ → ℝ).
Take m : ℝ. Take l : ℝ.
Assume a_cv_to_m : (Un_cv a m).
Assume b_cv_to_l : (Un_cv b l).
Assume a_b_ordered : (∀ n : ℕ, a n ≤ b n).
By Rle_or_lt it holds that (m ≤ l ∨ l < m) (H1).
Because H1 either m_le_l or l_lt_m.
(** We first consider the case $m \leq l$.*)
It holds that (m ≤ l).
(** Next, we consider the case $l < m$.*)
Define ε := ((m - l)/2).
Expand the definition of Un_cv in b_cv_to_l.
Expand the definition of Un_cv in a_cv_to_m.
It holds that (m-l > 0) (H2).
It holds that ((m-l)/2 > 0) (H3).
It holds that (ε > 0) (H4).
It holds that (∃ N1 : ℕ, ∀ n : ℕ, (n ≥ N1)%nat ⇒ R_dist (b n) l < ε) (H5).
It holds that (∃ N2 : ℕ, ∀ n : ℕ, (n ≥ N2)%nat ⇒ R_dist (a n) m < ε) (H6).
Choose N1 such that H7 according to H5.
Choose N2 such that H8 according to H6.
Define N3 := (Nat.max N1 N2).
It holds that (Nat.max N1 N2 ≥ N1)%nat (H9).
It holds that (Nat.max N1 N2 ≥ N2)%nat (H10).
It holds that (N3 ≥ N1)%nat (H11).
It holds that (N3 ≥ N2)%nat (H12).
It holds that (R_dist (b N3) l < ε) (H13).
It holds that (R_dist (a N3) m < ε) (H14).
Expand the definition of R_dist in H13.
Expand the definition of R_dist in H14.
By Rabs_def2 it holds that (a N3 - m < ε ∧ - ε < a N3 - m) (H15).
By Rabs_def2 it holds that (b N3 - l < ε ∧ - ε < b N3 - l) (H16).
It holds that (a N3 - m < ε) (H17).
It holds that (- ε < b N3 - l) (H18).
Rewrite using (ε = (m - l)/2) in H17.
Rewrite using (ε = (m - l)/2) in H18.
It holds that (a N3 ≤ b N3) (H19).
It holds that (ε = (m - l)/2) (H20).
It follows that (m ≤ l).
Qed.
