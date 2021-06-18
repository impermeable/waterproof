(* For all types A: for all functions P and Q that map
  from A to a proposition. If P(x) holds for all x ∈ A, 
  or if Q(y) holds for all y ∈ A, 
  then for all z ∈ A either P(z) or Q(z) holds.
*) 
Lemma exercise : forall A:Type, forall P Q: A -> Prop,
  (forall x, P x)\/(forall y, Q y) -> forall x, P x \/ Q x.
Proof.
(* Assume some x ∈ A and ∀[x, P(x)] ∨ ∀[y, Q(y)] *)
intros.
destruct H as [H_P | H_Q].
(* In case ∀[x, P(x)], then the P(x) part of the conclusion holds. *)
left.
apply H_P.
(* Same idea for the case ∀[x, Q(x)] *)
right.
apply H_Q.
Qed.
