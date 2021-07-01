(** * change.v
Authors: 
    - Lulof Pirée (1363638)
Creation date: 5 June 2021

Experimenting with the [change] tactic of Coq.
*)

Lemma zero_lt_two: 0 < 1 + 1.
Proof.
    change (0 < 1 + 1) with (0 < 2).
    (* As expected, this does not work:*)
    (* change (0 < 2) with (0 < 3). *)
Abort.


Lemma zero_lt_two: 0 < 1 + 1.
Proof.
    change (0 < 2).
Abort.