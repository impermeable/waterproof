From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Require Import Bool.

Definition type_of {T : Type} (x : T) := T.

Ltac2 match_type (x:constr) (t:constr) :=
  let tx:=eval cbv in (type_of $x) in
  Constr.equal tx t.

Ltac2 Eval match_type constr:(2) constr:(nat).
Ltac2 Eval match_type constr:(2) constr:(bool).
Ltac2 Eval match_type constr:(true) constr:(bool).

Goal True.
    print (match_type constr:(0) constr:(bool)).
    print (match_type constr:(1) constr:(bool)).