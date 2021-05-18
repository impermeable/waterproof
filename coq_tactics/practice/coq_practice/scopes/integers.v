Require Import ZArith.
Require Import Arith.
Open Scope Z_scope.

Check -1.
Check Zmult (-1) (-2).
Compute Zmult (-1) (-2).

Compute mult (1%nat) (2%nat).

(* This one doesn't work, as expected:
Compute Zmult(1%nat -2). *)

Open Scope nat_scope.
Check Zmult (-1%Z) (-2%Z).
Compute Zmult (-1%Z) (-2%Z).
Search (Z -> nat).
(* Coq'Art calls this function "Zabs_nat", 
   but apparenlty it has been renamed?*)
Compute Z.abs_nat (-999).