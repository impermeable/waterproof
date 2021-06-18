From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

(* We can create and call functions*)
Ltac2 hello_world () := Message.print (Message.of_string "Hello world!").
Ltac2 Eval hello_world ().
Goal True.
    hello_world ().
Abort.

(* Mutable types *)
Ltac2 mutable x := 1. (* the value of x can be redefined later*)
Ltac2 y := x. 
Ltac2 Eval y. (* Prints '1'*)

Ltac2 Set x := 2.
Ltac2 Eval x. (* Prints '2'*)
Ltac2 Eval y. (* Prints '2' as well! *)

(* Referencing a variable *)

Ltac2 Eval @x.
Ltac2 Eval ident : (x) .
Ltac2 Eval Message.print (Message.of_ident @x).
Ltac2 Eval constr : (1).
(* Check &x.     -- raises error: Hypothesis "x" not found *)

Ltac2 bar () := let x := '(3+4) in constr:($x + 5).
Ltac2 Eval bar ().

(* Recursive types *)

(* Normal Coq recursive types work. *)
Inductive bin_tree : Type :=
    Leaf : bin_tree
  | Node (child1 child2: bin_tree).

(* No idea how to get this to work:

Ltac2 Type rec bin_tree :=
        Leaf : bin_tree
    | Node (l1, l2::= bin_tree).

*)