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


Ltac2 print_all_hypos () :=
    match! goal with
    | [h: ?t |- _] => let h := Control.hyp h in print (
        concat (concat (of_constr h) (of_string " : ")) (of_constr t)); fail
    | [ |- _] => ()
    end.

Lemma test2 : forall x : nat, x=1 -> x = 1.
Proof.
    intros x H. 
    print_all_hypos ().
Abort.

Ltac2 Type exn ::= [ CannotConvertToMessageError(string) ].

Ltac2 to_message x :=
    match x with
    (* This is valid syntax...*)
    | (some_qualid:string) => of_string x
    | constr => of_constr x
    | ident => of_ident x
    | int => of_int x
    | exn => of_exn x
    | _ => fail (Control.raise (CannotConvertToMessageError ""))
    end.
Ltac2 Eval 12.
Ltac2 Eval print (to_message constr:(12)).
