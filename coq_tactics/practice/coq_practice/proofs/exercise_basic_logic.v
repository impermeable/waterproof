Require Import Bool.
Require Import Arith.

Lemma exercise_1 : 
  forall A B C: Prop, A/\(B/\C) -> (A/\B)/\C.
Proof.
intros A B C H.
SearchPattern (_ /\ (_ /\ _)).
destruct H as [H_A H_BC].
destruct H_BC as [H_B H_C].
SearchPattern (bool -> bool -> _ /\ _).
SearchPattern (Prop -> bool).
apply conj.
apply conj.
assumption.
assumption.
assumption.
Qed.




Lemma exercise_2:
  forall A B C D: Prop, (A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
intros A B C D H.
destruct H as [H_AB H2].
destruct H2 as [H_CD H3].
destruct H3 as [H_A H_D].
apply conj.
apply H_AB.
assumption.
apply H_CD.
assumption.
Qed.




Lemma exercise_3: forall A: Prop, ~(A/\~A).
Proof.
intros.
intro.
destruct H as [H_A H_neg_A].
apply H_neg_A.
assumption.
Qed.




Lemma exercise_4: forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
intros.
destruct H as [H_A | H_BC].
  (* Prove the case A holds. *)
  left.
  left.
  assumption.
  (* Prove the case (B \/ C) holds. *)
  destruct H_BC as [H_B | H_B].
    (* Prove the case B holds. *)
    left;right;assumption.
    (* Prove the case C holds. *)
    right;assumption.
Qed.

Lemma exercise_5: forall A B: Prop, (A\/B)/\~A -> B.
Proof.
intros.
destruct H as [H_AB H_not_A].
destruct H_AB as [H_A | H_B].
(* Case A holds. This leads to a contradiction. *)
elim H_not_A.
assumption.
(* Case B holds. Trivial. *)
assumption.
Qed.
