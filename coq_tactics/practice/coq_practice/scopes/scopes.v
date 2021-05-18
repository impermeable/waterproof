Require Import Arith.
Require Import ZArith.
Require Import Bool.

(* Add a new scope to the scope-stack. Interpret things like "*" as integer-operations. *)
Open Scope Z_scope.
(* Note that this prints the whole interpretation stack! *)
Locate "_ * _".
(* Print all the notations that the Z_scope overloads/defines *)
Print Scope Z_scope.

Check 0%nat.
Check 33%nat.
Check 0. (* Returns 'Z', cuz the Z_scope is open *)
Check -12.
Check (-12%Z).
(* 
Check (-12%nat). (* Raises error! -12 is not a natural number! *) 
*)
Check true.
Check false.