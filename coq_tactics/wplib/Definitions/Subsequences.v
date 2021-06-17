(** ## Subsequences definitions*)
Require Import Reals.
Require Import wplib.Notations.Notations.
Require Import wplib.Lib.subsequences.
Require Import wplib.Tactics.Tactics.
Open Scope metric_scope.
Definition is_index_sequence  (n : ℕ → ℕ) := 
  ∀ k : ℕ,
    (n k < n (k + 1))%nat.
Variable M : Metric_Space.
Definition X := Base M.
Definition dist := dist M.

Notation "a ◦ n" := (fun (k : nat) => a (n k)) (right associativity, at level 20).
Notation "a ◦ n ◦ m" := (fun (k : nat) => a (n (m k))) (right associativity, at level 21).
Definition is_subsequence (b : ℕ → X) (a : ℕ → X) := 
  ∃ m : (ℕ → ℕ),
    is_index_sequence m ∧ ∀ k : ℕ,
      b k = (a ◦ m) k.
Definition is_accumulation_point (p : X) (a : ℕ → X) :=
  ∃ l : (ℕ → ℕ),
    is_index_sequence l ∧ (a ◦ l) ⟶ p.

Lemma index_sequence_property (n : ℕ → ℕ) :
  is_index_sequence n ⇒ 
    ∀ k : ℕ,
      (n k ≥ k)%nat.
Proof.
intros. unfold is_index_sequence in H. induction k.
specialize (H 0%nat). unfold ge. apply Nat.le_0_l.
specialize (H k). unfold ge. apply lt_le_S. rewrite Nat.add_1_r in H.
apply (Nat.le_lt_trans k (n k) _). apply IHk. apply H.
Qed.

Hint Resolve index_sequence_property : reals.
Hint Extern 1 => (unfold ge) : reals.

Lemma index_seq_equiv (n : ℕ → ℕ) : is_index_seq n ⇔ is_index_sequence n.
Proof. 
We show both directions.
intro.
unfold is_index_sequence. 
Take k : ℕ. 
unfold is_index_seq in H. 
It holds that ((k + 1)%nat = S k) (H1).
Write goal using ((k + 1)%nat = S k)
  as ((n k < n (S k))%nat). 
Apply H.

intro.
unfold is_index_seq. 
Take k : ℕ. 
unfold is_index_sequence in H. 
It holds that (S k = (k + 1)%nat) (H1).
Write goal using (S k = (k + 1)%nat)
  as ((n k < n (k + 1))%nat). 
Apply H.
Qed.
Lemma index_sequence_property2 (n : ℕ → ℕ) : 
  is_index_sequence n ⇒ 
    ∀ k1 k2 : ℕ, 
      (k1 ≥ k2)%nat ⇒ 
        (n k1 ≥ n k2)%nat.
Proof.
Assume H : (is_index_sequence n).
Take k1 and k2 : ℕ.
Assume k1_ge_k2 : (k1 ≥ k2)%nat.
We need to show that (n k1 ≥ n k2)%nat.

pose proof (incr_loc_to_glob n).
We claim that (is_increasing n) (n_is_increasing).
Expand the definition of is_increasing.
Take k : ℕ.
It holds that (n k ≤ n (k+1))%nat (temp).
It holds that (k+1 = S k)%nat (temp2).
Write goal using (S k = (k + 1)%nat) as ((n k ≤ n (k + 1))%nat).
Apply temp.
Apply H0. Apply n_is_increasing. Apply k1_ge_k2.
Qed.

Hint Resolve index_sequence_property2 : reals.
Lemma double_is_even : forall n : nat, Nat.even (2 * n) = true.
Proof.
Take n : nat.
Rewrite (Nat.even (2*n)) = (Nat.even (0 + 2 * n)).
rewrite Nat.even_add_mul_2. auto.
Qed.
Hint Resolve double_is_even : reals.
