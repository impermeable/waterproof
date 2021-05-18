Lemma or_is_commutative: forall A B, A \/ B -> B \/ A.
Proof.
(* Combines three flags: Assume any A, Assume any B and Assume A /\ B. 
  The conclusion ∀[A, B: A /\ B -> ...] will be drawn implicitly
  and automatically. *)
intros A B H.
(* We now have A \/ B in the context. Make a case distinction: *)
destruct H as [H1 | H2].
(* H1: A holds. 
  Now we want to prove the *right* side of "_ \/ _" of the goal "B \/ A".
  But we are already assuming A holds which we need to prove.
  So just point that out with "assumption".
  ';' combines two tactics. *)
right; assumption.
(* H2: B holds. Then it follows that B \/ A holds. *)
left; assumption.
Qed.
