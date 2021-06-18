Require Import Arith.
Require Import Bool.

(* Script to check my solution of Ex 2.2 of book Coq'Art.

    I predicted "(nat -> nat) -> (nat -> nat) -> nat -> nat",
    which is correct :)
*)

Definition f:= fun (x:nat) => x.
Definition g:= fun (y:nat) => y.

Definition my_fun := fun (f g:nat->nat) (n:nat) => g(f n).
Check my_fun.