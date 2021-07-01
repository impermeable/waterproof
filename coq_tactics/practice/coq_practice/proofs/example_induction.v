Require Import Arith.

(* sum_n(n) = ∑_{i=0}^{n-1}i   *)
Fixpoint sum_n (n: nat) : nat :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Compute sum_n 3.
Compute sum_n 0.
Compute sum_n 5.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
induction n.
(* Base case *)
reflexivity.
(* Recursive case *)
assert (SnSn: S n * S n = n * n + 2*n + 1).
ring.
rewrite SnSn.
rewrite <- IHn.
(* Unline in 'Coq in a Hurry', 
  'simpl.' also expands 2 * multiplication... 
  ... Looks messy but 'ring' still works.*)
simpl.
ring.
Qed.



