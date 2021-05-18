From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Ltac2 x := 1.
Compute(1+1). (* Returns "2: nat" as expected.*)
Compute (1 + ltac2:(x)). (* This compiles but has value "S ?Goal: nat".*)
Compute let x := x in  (1 + x). (* The reference x was not found in the current environment.*)
Compute (1 + 'x). (* Syntax error: [term] expected after '+' (in [term]). *)
Compute constr:(1 + x). (* The reference x was not found in the current environment.*)
Compute (1 + $x). (* Unbound value x *)
Compute (1 + @x). (*The reference x was not found in the current environment.*)
Compute (1 + &x). (* Hypothesis "x" not found *)
Compute (1 + [x]). (* Syntax error: [term] expected after '+' (in [term]). *)
Compute (1 + x). (* The reference x was not found in the current environment. *)

