From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Definition double n:nat := 2*n.

Ltac2 Eval eval cbv in (1=1).
Ltac2 Eval eval cbn in (1=1).
Ltac2 Eval eval cbv in (double 1).
Ltac2 Eval eval cbn in (double 1).

Goal forall n, double n = 2*n.
    intros n.
    Ltac2 Eval eval cbv in (double n).
    Ltac2 Eval eval cbn in (double n).