From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

(* Constructing an Ltac2 term.
    This cannot directly be used in Coq-code.*)
Ltac2 x := 2.

(* Gives an error, as x unknown to Coq: *)
(* Print x. *)

(* Prints the name of x, not the value*)
Ltac2 Eval Message.print (Message.of_ident @x).
(* Prints the value of x, and its type. *)
Ltac2 Eval x.


Ltac2 Notation "foo" id(ident) := fun id => (1 * id ).
Ltac2 Eval foo bar.


Lemma  smaller_than_twice : forall n : nat, n <= 2*n.
Proof.
    intros n.

