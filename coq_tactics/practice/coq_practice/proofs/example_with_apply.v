(* Example proofs using the 'apply' tactic *)

Check le_n.
(* forall n m : nat, n <= m -> n <= S m *)
Check le_S.

Lemma example: 3 <= 5.
Proof.
(* Use n = 3, m = 4. If 3 <= 4 then 3 <= 4+1 = S(4) = 5*)
apply le_S.
(* Now need to prove 3 <= 4. 
   Coq will figure out we need to apply this on n=m=3. *)
apply le_S.
(* Almost there, just need to show 3 <= 3. Seriously. *)
apply le_n.
Qed.

(* Interesting to see how Coq actually saves the proof. Weird. *)
Print example.



(* Second example *)


Require Import Arith.
(* Proof that <= is transitive.
  forall n m p : nat, n <= m -> m <= p -> n <= p *)
Check le_trans.

Lemma exaple2: forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
(* x10 and y10 will be the required propositions:
  x <= 10 and 10 <= y *)
intros x y x10 y10.
(* 'apply le_trans.' does not work: cannot find var m here. *)
(* This is like lambda calculus substitution: *)
apply le_trans with (m := 10).
(* Ok now to prove the conclusion of the transitivity (x <= y), 
  we need to show x <= 10 and 10 <= y. But we aready assumed this! *)
assumption.
assumption.
Qed.




