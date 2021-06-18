(*
Exercise on datatype definition 

Define a datatype where there are three cases: a
constant, a case where there are three fields, where the first field is a number and
the next two fields are in the datatype being defined, and a case with four fields,
where the first field is a boolean value and the three other fields are in the datatype
being defined.
*)
Require Import Bool.

Inductive meh : Type :=
    C: meh
  | T (n : nat) (m1 m2: meh)
  | F (b: bool) (m1 m2 m3: meh).

Check meh.
Check C.
Check T 1 C C.
Check F false C C C.
Check F false (T 1 C C) C C.
Check T 1 (F true C C C) C.

