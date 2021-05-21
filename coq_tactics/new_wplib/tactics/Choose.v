From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
Require Import Bool.


Ltac2 Type exn ::= [ TakeError(string) ].

Ltac2 raise_take_error (s:string) := 
    Control.throw (TakeError s).



Ltac2 chooseExistsNoIntro x :=
    exists $x.



Ltac2 chooseExistsWithIntro s t :=
    pose (s := $t).

Ltac2 chooseDestructThreeArguments s u v :=
    destruct $v as [s u].

Ltac2 chooseDestructFourArguments s u v t :=
    destruct $v with $t as [s u].


Ltac2 Notation "Choose" s(constr) :=
    chooseExistsNoIntro s.

Ltac2 Notation "Choose" s(constr) ":=" t(constr) :=
    chooseExistsWithIntro s t.



(*

Ltac2 Notation "Choose" s(opt(constr)) ofType(opt(":=")) t(constr) :=
    match s with
        | None => chooseExistsNoIntro t
        | Some y => chooseExistsWithIntro s t
    end.

*)


Goal exists  n: nat, ((n = n)). 
    Choose 1.
    auto.
Abort.