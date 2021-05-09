From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Require Import Bool.

Definition is_of_type (x:nat) (t:Type) : bool :=
    match x with
    | t => true
    end.

Compute is_of_type 1 bool.


Ltac2 match_type (x:constr) (t:constr) :=
    lazy_match! x with
    | nat => (of_string "x is a nat")
    | context [?z] => (concat (of_string "x is type ") (of_constr z))
    | _ => (of_constr x)
    end.

Goal True.
    print (match_type (constr:(2)) (constr:(nat))).
    print (match_type (constr:(1)) (constr:(bool))).