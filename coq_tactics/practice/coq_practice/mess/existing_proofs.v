Require Import Arith.


(* Search (_ <= _) (_ + _). *)



(* this returns some propositions like:
  Nat.add_sub_assoc: forall n m p : nat, p <= m -> n + (m - p) = n + m - p
  Nat.add_sub_swap: forall n m p : nat, p <= n -> n + m - p = n - p + m
*)
(* Search (_ + _). *)

(* SearchPattern works for partial things. 
   '_' is like a wildcard that may contain more than a single variable. *)
(* SearchPattern (_ + _ <= _ + _). *)

(* For some reason, this finds more results than the statement above.
  It seems the extra results contain logical connectives such as \/ and <->,
  which did not occur in the results of SearchPattern...
*)
(* Search (_ + _ <= _ + _). *)

(* For theorems were equality is proven *)
SearchRewrite (_ + (_ - _)).
