Require Import Arith.

Print Nat.pred.

Lemma pred_S_eq : forall x y, x = S y -> Nat.pred x = y.
Proof.
(* Assume the premise of the implication.
  That is, assume x = S(y)  *)
intros x y q.
(* This expands 'Nat.pred' in the goal 'Nat.pred x = y'
  with its definition. *)
unfold Nat.pred.
(* Hey now x in the local context fits this definition.
  Substitute it in the goal: *)
rewrite q.
reflexivity.
Qed.