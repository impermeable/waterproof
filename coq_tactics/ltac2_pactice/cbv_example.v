Definition f (x:nat) := 2*x.
Lemma cbv_demo: forall y:nat, y <= f(y).
Proof.
  cbv.