(** # Subsequences*)
Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Tactics.Databases.
Require Import wplib.Notations.Notations.

Hint Resolve Rabs_Rabsolu.
(** ## Creating a subsequence of elements satisfying a certain property

The purpose of this section is to provide a somewhat general strategy to construct subsequences of elements satisfying a certain property. *)
(** ### From existence of a next element to a function producing this element

The next lemma is quite technical, and is usually not so visible in classical analysis. We rely here on a version of the axiom of choice.*)
Lemma existence_next_el_to_fun :
    ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ f : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ f m N)%nat ∧ P m (a (f m N)).
Proof.
Take a : (ℕ → ℝ). Take P : (ℕ → ℝ → Prop).
Assume ex_next.
We claim that (∀ (m : ℕ),  ∃ g : ℕ → ℕ, ∀ N : ℕ, (N ≤ g N)%nat ∧ (P m (a (g N)))) (H1).
  Take m : ℕ.
  apply choice with
    (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P m (a l))).
    Apply ex_next.
apply choice with
  (R := fun (m : ℕ) (h : ℕ → ℕ) ↦ ( ∀ N : ℕ, (N ≤ h N)%nat ∧ P m (a (h N)) )   ).
  Apply H1.
Qed.
(** The next definition captures what it means to be an index sequence.*)
Definition is_index_seq (n : ℕ → ℕ) :=
  ∀ k : ℕ, (n k < n (S k))%nat.
(** Given the function that produces 'good' elements, we can use it to construct a subsequence by induction.*)
Fixpoint create_seq 
  (f : ℕ → ℕ → ℕ) (l : ℕ) :=
  match l with
  | O => f O O
  | S k => f l (S (create_seq f k))
  end.
(** If the function that produces 'good' elements is such that the produced elements are far enough in the sequence, it is certain that the produced sequence is an index sequence.*)
Lemma created_seq_is_index_seq :
  ∀ (f : ℕ → ℕ → ℕ),
    (∀ (m N : ℕ), (f m N ≥ N)%nat ) ⇒
      is_index_seq (create_seq f).
Proof.
Take f : (ℕ → ℕ → ℕ).
Assume f_large : (∀ (m N : ℕ), (f m N ≥ N)%nat ).
Expand the definition of is_index_seq.
Take k : ℕ.
Rewrite using (create_seq f (S k) = f (S k) (S (create_seq f k))).
By f_large it holds that (f (S k) (S (create_seq f k)) ≥ S(create_seq f k))%nat (H1).
(** The conclusion *)
follows immediately. Qed.
(** 
The next lemma records that indeed the elements in the subsequence satisfy the desired property.*)
Lemma subseq_sat_rel :
  ∀ (a : ℕ → ℝ) (f : ℕ → ℕ → ℕ) (P : ℕ → ℝ → Prop),
    (∀ m N : ℕ, P m (a (f m N)) ) ⇒ 
      ∀ k : ℕ, P k (a (create_seq f k)).
Proof.
Take a : (ℕ → ℝ). Take f : (ℕ → ℕ → ℕ). Take P : (ℕ → ℝ → Prop).
Assume relation_satisfied : (∀ m N : ℕ, P m (a (f m N)) ).
induction k as [|k IH].
simpl. 
(** We need to show that $P(0, a (f(0,0)))$ holds. *)
Apply relation_satisfied.
(** For the induction step, we *)
simpl 
(** the expression*)
.
We need to show that (P (S k) (a (f (S k) (S (create_seq f k))))). Apply relation_satisfied.
Qed.
Lemma exists_good_subseq :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ (m : ℕ) (N : ℕ), ∃ k : ℕ, (N ≤ k)%nat ∧ (P m (a k))) ⇒
      ∃ n : ℕ → ℕ, is_index_seq n ∧ ∀ k : ℕ, P k (a (n k)).
Proof.
Take a : (ℕ → ℝ). Take P : (ℕ → ℝ → Prop).
Assume large_good_el_exist.
By existence_next_el_to_fun it holds that
  (∃ f : ℕ → ℕ → ℕ, ∀ (m : ℕ) (N : ℕ), (N ≤ f m N)%nat ∧ P m (a (f m N))) (H1).
Choose f such that f_choice_fun according to H1.
Choose n := (create_seq f).
We claim that (∀ (m : ℕ) (N : ℕ), (N ≤ f m N)%nat) (H2).
  Take m : ℕ. Take N : ℕ.
  By f_choice_fun it holds that ((N ≤ f m N)%nat ∧ P m (a (f m N))) (H3).
  This follows immediately.
By created_seq_is_index_seq it holds that (is_index_seq (create_seq f)) (H4).
We claim that (∀ (m : ℕ) (N : ℕ), P m (a (f m N))) (H5).
  Take m : ℕ. Take N : ℕ.
  By f_choice_fun it holds that ((N ≤ f m N)%nat ∧ P m (a (f m N))) (H3). 
  Because H3 both f_large and f_sat. trivial.
We claim that (∀ k : ℕ, P k (a (create_seq f k))) (H6).
  Apply subseq_sat_rel; assumption.
This follows immediately.
Qed.
Definition is_increasing (f : ℕ → ℕ) :=
  ∀ k : ℕ, (f k ≤ f (S k))%nat.
Lemma incr_loc_to_glob :
  ∀ f : ℕ → ℕ,
    is_increasing f
      ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (f k ≤ f l)%nat).
Proof.
Take f : (ℕ → ℕ). Expand the definition of is_increasing. Assume incr_loc : (∀ k : ℕ, (f k ≤ f (S k))%nat).

Take k : ℕ. induction l as [|l IH_l]. 
(** We first need to show that if $k \leq 0$ then $(f (k) \leq f(0))$.*)
Assume k_le_0. Rewrite using (k = 0)%nat. 
We need to show that (f 0 ≤ f 0)%nat.
This follows immediately.
(** Next, we need to show that if $k \leq S (l)$ then $f(k) \leq f(S (l))$.*)
Assume Sk_le_Sl.
destruct (lt_eq_lt_dec k (S l)) as [temp | k_gt_Sl].
  destruct temp as [k_lt_Sl | k_eq_Sl].
(** We first consider the case that $k < S(l)$.*)
It holds that (k ≤ l)%nat (k_le_l).
By IH_l it holds that (f k ≤ f l)%nat (fk_le_fl).
It holds that (f l ≤ f (S l))%nat (fl_le_f_Sl).
(** It *)
follows immediately
(** that $f(k) \leq f(S(l))$*)
.
(** 
We now consider the case $k = S(l)$. We need to show that $f(k) \leq f(S(l))$. *)
Rewrite using (k = S l).
(** It*)
follows immediately
(** that $f(S(l))\leq f(S(l))$*)
.
(** 
Finally we consider the case $k > S(l)$. However, this case is in contradiction with $k \leq S(l)$. *)
It holds that (¬(S l < k)%nat) (not_Sl_lt_k). contradiction.
Qed.
Lemma index_seq_strictly_incr :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (is_increasing (fun (k : ℕ) ↦ (n k - k)%nat)).
Proof.
Take n : (ℕ → ℕ). Assume n_is_index_seq.
Expand the definition of is_increasing.
Take k : ℕ. 
Expand the definition of is_index_seq in n_is_index_seq.
It holds that (n k < n (S k))%nat (H1).
(** It *)
follows immediately
(** that $n_k - k \leq n_{S(k)} - S(k)$*)
. Qed.
Lemma index_seq_grows_0 :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ ∀ k : ℕ, (n k ≥ k)%nat.
Proof.
Take n : (ℕ → ℕ). Assume n_is_index_seq.
induction k as [|k IH].
This follows immediately.
Expand the definition of is_index_seq in n_is_index_seq.
It holds that (n k < n (S k))%nat (H1).

(** We need to show that $n_{S(k)} \geq S(k)$. *)
This follows immediately. Qed.
Lemma index_seq_grows :
  ∀ n : ℕ → ℕ, is_index_seq n ⇒ (∀ k l : ℕ, (k ≤ l)%nat ⇒ (n k - k ≤ n l - l)%nat).
Proof.
Take n : (ℕ → ℕ). Assume n_is_index_seq.
Define f := (fun (k : ℕ) ↦ (n k - k)%nat).
By index_seq_strictly_incr it holds that (is_increasing f) (H1).
By incr_loc_to_glob it holds that (∀ k l : ℕ, (k ≤ l)%nat ⇒ (f k ≤ f l)%nat) (H2).
Take k : ℕ. Take l : ℕ. Assume k_le_l.
By H2 it holds that (f k ≤ f l)%nat (H3).
Expand the definition of f in H3.

(** The result follows by *)
assumption. Qed.


(** ## Constructing a subsequence with elements satisfying a particular property

Given a property $P : \mathbb{N} → \mathbb{R} → \mathrm{Prop}$, and given that it holds for infinitely many elements in the sequence, we want to find a subsequence with all elements satisfying the property. *)
(** ### Finding the smallest element satisfying the property

This seems to require some decidability on the property*)
Fixpoint first_satisfying_element_helper
  (rel : ℕ → ℕ → bool)
  (k : ℕ)
  (N : ℕ) :=
  match k with
  | O => N
  | S l => if (rel (N-k)%nat (N-k)%nat) 
                then k
                else (first_satisfying_element_helper rel l N)
  end.  
Definition first_satisfying_element
  (rel : ℕ → ℕ → bool)
  (l : ℕ)
  (N : ℕ)
  := first_satisfying_element_helper rel (N-l) N.  
(** ### From infinitely many elements to a function producing those elements*)
Lemma inf_el_to_fun :
  ∀ (a : ℕ → ℝ) (P : ℕ → ℝ → Prop),
    (∀ N : ℕ, ∃ k : ℕ, (N ≤ k)%nat ∧ (P N (a k))) ⇒
      ∃ f : ℕ → ℕ, ∀ l : ℕ, (l ≤ f l)%nat ∧ P l (a (f l)).
Proof.
Take a : (ℕ → ℝ). Take P : (ℕ → ℝ → Prop).
apply choice with 
  (R := fun (k : ℕ) (l : ℕ) ↦ ((k ≤ l)%nat ∧ P k (a l))).
Qed.
Fixpoint seq_of_max (f : ℕ → ℕ) (l : ℕ) :=
  match l with 
  | O => f O
  | S k => Nat.max (f l) (seq_of_max f k)
  end.
(** ### The sequence of maxima is increasing*)
Lemma seq_of_max_is_increasing :
  ∀ f : ℕ → ℕ, is_increasing (seq_of_max f).
Proof.
Take f : (ℕ → ℕ).
Expand the definition of is_increasing.
Take k : ℕ. simpl. This follows immediately.
Qed.
Lemma elements_le_seq_of_max_pre :
  ∀ (f : ℕ → ℕ) (n : ℕ),
    (f n ≤ seq_of_max f n)%nat.
Proof.
Take f : (ℕ → ℕ). 
(** We apply*)
induction 
(** on*)
 n as [|n IH_n].
(** We first consider the base case $n=0$.*)
Expand the definition of seq_of_max.
(** We need to show that $f( 0 ) \leq f( 0)$.*)
This follows immediately.
(** 
Next we consider the general case. We need to show that $f(S(n))\leq \mathsf{seqofmax}(f, S(n))$. *)
Expand the definition of seq_of_max. 
(** By the definition of $\mathsf{seqofmax}(f,S(n))$ as the maximum of $f(S(n))$ and another number, this*)
follows immediately. 
Qed.
Lemma elements_le_seq_of_max :
  ∀ (f : ℕ → ℕ) (n : ℕ) (k : ℕ),
    (k ≤ n)%nat ⇒ (f k ≤ seq_of_max f n)%nat.
Proof.
Take f : (ℕ → ℕ). Take n : ℕ. Take k : ℕ.
Assume k_le_n. By elements_le_seq_of_max_pre it holds that (f k ≤ seq_of_max f k)%nat (H1).
We claim that (seq_of_max f k ≤ seq_of_max f n)%nat (H2).
Apply incr_loc_to_glob. Apply seq_of_max_is_increasing. Apply k_le_n.
(** By transitivity, the conclusion *)
follows immediately.
Qed.
(** ### From a function producing the correct elements to an index sequence*)
Fixpoint build_seq 
  (f : ℕ → ℕ) 
  (k : ℕ) :=
  match k with 
  | O => f O
  | S m => f (S (seq_of_max f (build_seq f m)))
  end.
Lemma built_seq_is_index_seq :
  ∀ f : ℕ → ℕ,
    (∀ k : ℕ, (f k ≥ k)%nat) ⇒
      is_index_seq (build_seq f).
Proof.
Take f : (ℕ → ℕ).
Assume for_all_k_f_k_ge_k.
Expand the definition of is_index_seq.
Take l : ℕ.
Rewrite using (build_seq f (S l) = f( S(seq_of_max f (build_seq f l))))%nat.
We claim that (f( S(seq_of_max f (build_seq f l)))≥ S(seq_of_max f (build_seq f l)))%nat (H1).
  Apply for_all_k_f_k_ge_k.
It holds that (f( S(seq_of_max f (build_seq f l)))> seq_of_max f (build_seq f l))%nat (H2).
We claim that (seq_of_max f (build_seq f l) ≥ f(build_seq f l))%nat (H3).
  Apply elements_le_seq_of_max_pre.
By for_all_k_f_k_ge_k it holds that (f(build_seq f l) ≥ build_seq f l)%nat (H4).
This follows immediately.
Qed.
(** ### Subsequence satisfies relation*)
