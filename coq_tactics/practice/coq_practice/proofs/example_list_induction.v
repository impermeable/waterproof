Require Import Arith.
Require Import List.

Fixpoint insert (n: nat) (li: list nat) : list nat :=
  match li with
    nil => n::nil
  | a::tail => if n <=? a then n::li else a::insert n tail
  end.


Fixpoint count (n: nat) (li: list nat) : nat :=
  match li with
    nil => 0
  | a::tail => let remainder := count n tail in
                if n =? a then 1+remainder
                else remainder
  end.

Lemma insert_incr: forall n li, count n (insert n li) = count n li + 1.
Proof.
intros n li.
induction li.
(* Base case: li = nil. *)
simpl. (* Compute insert() once *)
rewrite Nat.eqb_refl.
reflexivity.
(* Indutive step. IHli : count n (insert n li) = count n li + 1
                  Goal : count n (insert n (a :: li)) = count n (a :: li) + 1 *)
simpl. (* Inserts the whole "if then else" clause... *)
case (n <=? a).
(* Case in which n is appended before a::li *)
(* The LHS has count(n::a::li). One recursive step can be taken here. *)
simpl.
rewrite Nat.eqb_refl.
ring.

(* Case in which n is added to li after a. So we got a::(insert n li) *)
simpl.
(* One recursive step: did a cause a +1 to the count or not? *)
case (n =? a).
rewrite IHli.
ring.
exact IHli.
Qed.

