
Require Import Arith.

Lemma le_mult_mult : forall a b c d: nat,
    (a <= c) -> (b <= d) -> a*b <= c*d.
Proof.
    intros.
    (* Generates 2 subgoals:
        (1/2)
        a * b <= ?m
        (2/2)
        ?m <= c * d

        Clearly, both have a missing variable 'm'.
        So form Coq's perspective this happens:
        "OK, let's use the transitivity of <=. 
        But I only know the (a*b) and (c*d) in
        (a*b)<=m /\ m<=(c*d) ->  (a*b)<=(c*d)"*)
    eapply le_trans.

    (* Apply the lemma that 
        forall n m p : nat, n <= m -> p * n <= p * m*)
    eapply mult_le_compat_l.

    (* We are now going to fix the holes with H0.
        The goals are currently
        (1/2)
        b <= ?m
        (2/2)
        a * ?m <= c * d
        
        H0 Only fits the first goal.
        So "?m" must be "d" then.
        *)
    eexact H0.

    (* Got goal "a*d <= c*d".
       Rewrite it as "a <= c".
       Note that "H : a <= c"!*)
    apply mult_le_compat_r.
    assumption.
Qed.
