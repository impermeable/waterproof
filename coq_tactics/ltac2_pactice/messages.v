From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Lemma test : forall x : nat, x=1 -> x = 1.
Proof.
    intros x H.    
    print (of_string "Hello world!").
    print (of_constr &x).
    print (of_constr &H).
    (* The value of the hypothesis "H: x = 1"*)
    print (of_constr (lazy_match! goal with
        | [h: ?t |-_] =>
            t
        end)).
    exact H.
Qed.

