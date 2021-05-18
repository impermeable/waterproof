(*
  Exercise on counting 
  Knowing that the Coq system provides a function Nat.eqb to
  compare two natural numbers 
  (Nat.eqb n p returns true exactly when n = p),
  define a function count list that takes a natural number 
  and a list and returns
  the number of times the natural number occurs in the list.

*)

Require Import List.
Require Import Bool.
Require Import Arith.



(* Exactly the same as Nat.b2n, apparently.*)
Definition bool_to_binary := fun b : bool =>
  if b
  then 1
  else 0.

Print Nat.b2n.

Fixpoint count_occurences (n: nat) (li: list nat): nat :=
  match li with
  nil => 0
  | a::tail => Nat.b2n (Nat.eqb a n) + count_occurences n tail
  end.


Compute count_occurences 999 (1::2::3::6::nil).
Compute count_occurences 1 (1::2::1::1::99::10::nil).