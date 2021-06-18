Require Import Bool.
Require Import Arith.

Definition hi := true.
Check hi.
Compute hi.
Compute hi = true.
Compute hi = false.


Definition is_zero (n:nat) :=
  match n with
    0 => true
  | S p => false
  end.

Compute is_zero 3.
Compute is_zero 0.
Print is_zero.

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Compute sum_n 3. (* Compute 2 + 1 + 0 *)

(* This is basically natural number multiplication.
   Just returns n*s, but computed via addition...*)
Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (p+s)
  end.

Compute sum_n2 4 2.


Fixpoint is_even n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => is_even p
  end.

Print is_even.
Compute is_even 2.
Compute is_even 3.
Compute is_even 1.