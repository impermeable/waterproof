(*
Author: Lulof Pirée (1363638)
Creation date: 12 May 2021

For parsing input to "Ltac2 Notation", 
there is the seq() syntactic class.
Unfortunately the documentation does not describe how
to handle the variables that are parsed by this...

Experimental result: use pattern matching,
denoting the sequence as a tuple enclosed by "(" and ")",
with values separated by ",".
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Ltac2 print_seq s :=
    match s with
    | (a, b) => print (of_constr b); print (of_constr a)
    | _ => ()
    end.


Ltac2 Notation "test_seq" x(seq(constr, "?", constr)) 
    := print_seq x.


Goal True.
    test_seq 1 ? false.
Abort.