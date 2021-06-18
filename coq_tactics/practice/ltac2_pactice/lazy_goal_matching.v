From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Require Import Bool.
Require Import Arith.
Search (nat -> nat).

(* Hypothesis matching *)

Ltac2 apply_exact () :=
    lazy_match! goal with
    | [ h_ident:_ |- _] =>
        let h := Control.hyp h_ident in exact $h
    end. 

Lemma test: forall x, x=1 -> x=1.
Proof.
    intros x H.
    apply_exact ().
Qed.


(* multiple hypotheses*)
Ltac2 print_hypotheses () :=
    lazy_match! goal with
    | [x : nat, h: _|- _] => 
            print (concat 
            (concat (of_string ( "A natural number " )) (of_ident x))
            (concat (of_string ("   a hypothesis ")) (of_ident h))
            )
    end.

Lemma test3: forall x:nat, x > pred x -> x > 0.
Proof.
    intros x H.
    print_hypotheses ().
    induction x.
    Search (Nat.pred _).
    simpl Nat.pred in H.
    Search (?x > ?x).
    apply gt_irrefl in H.
    Std.contradiction.
    Control.enter (fun h => Std.contradiction true h) @H.
    
Abort.


(* Goal matching *)

Ltac2 intro_forall () :=
    lazy_match! goal with
    | [|- forall x : _, _] =>
        intros x
    end.

Lemma test2: forall x:nat, x = x.
Proof.
    intro_forall ().
    reflexivity.
Qed.