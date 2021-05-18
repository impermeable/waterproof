Lemma example: forall a b: Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
(* destruct H as [H1 H2].
  exact H1. *)
intuition.
Qed.