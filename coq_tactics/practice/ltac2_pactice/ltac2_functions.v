From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.


Ltac2 proof_forall_by_refl := fun () => intros x; reflexivity.

Lemma all_x_is_itself2 : forall x: nat, x = x.
Proof.
    proof_forall_by_refl ().
Qed.


Definition proof_forall_by_refl_coq () := intros x; reflexivity.
