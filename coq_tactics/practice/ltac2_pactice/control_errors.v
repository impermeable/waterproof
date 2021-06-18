From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Ltac2 Type exn ::= [ MyCustomException(string) ].

Goal True.
Fail Control.throw (MyCustomException("Hello World!")).
Abort.