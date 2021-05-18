Require Import Arith.
Add LoadPath "/home/nifrec/Vault/Documents/bachelor_3/sep_2IPE0/coq_practice/proofs/" as wd.
Load example_inductive_props.


(* Just "1 is not an even number" *)
Lemma not_even_1 : ~ even 1.
Proof.
(* Assume 1 is even, for contradiction. *)
intros H_even1.
(* Ok, so try how even 1 could have been dierived.
  * evenS case, there exists some S (S y) s.t. even y -> even S(S y)) = even x.
    But x = S 0. So 0 = S y. No such y exists, contradiction!
  * even0 case. This would require that 0 = 1. Contradiction! *)
inversion H_even1.
Qed.

(* If some num S(S(x)) is even, also the pred of its pred (=x) is even.
  This is the inversion of the evenS constructor! *)
Lemma even_inv : forall x, even (S (S x)) -> even x.
Proof.
(* Assume some x with "even S(S x)" *)
intros x H.
(* even0 cannot prove the statement (then x would be the pred of pred of 0).
   So only evenS could have be used. So there must exist an y s.t. "even y"
    and "S(S y) = S(S x)", hence y = x. 
    Coq calls the vars x0 and x, not sure which is which.
    Not that is matters cus we have "H0 : x0 = x".*)
inversion H.
exact H1.
Qed.
