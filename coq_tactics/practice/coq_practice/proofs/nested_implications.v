(*
Authors: 
    * Lulof Pirée (1363638)
Creation date: 29 May 2021
*)

Lemma nonsense: forall x y : nat, x = 1 -> y = 1 -> (x = 1 -> x = y).
Proof.
    intros x y.
    (* Only introduces h:(x=1)*)
    intros h.
Abort.

Lemma nonsense2: forall x y : nat, x = 1 -> y = 1 -> (x = 1 -> x = y).
Proof.
    intros x y.
    intros h1 h2 h3.
Abort.