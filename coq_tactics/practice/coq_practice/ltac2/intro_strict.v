From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Require Import Arith.


Ltac2 intro_strict s t :=
  match! goal with
    | [ |- forall _ : ?u, _ ] => 
      match u with
      | t => intro s
      | _ => intro s
      end
  end.

Ltac2 Notation "Take" s(ident) ":" t(constr) := 
  intro_strict s t.


Lemma  smaller_than_twice : forall n : nat, n <= 2*n.
Proof.
    Take n : nat.
    (* Ok it ignores the name n...
    At least the type is nat...*)
    induction s.
    (* Base case *)
    reflexivity.
    (* Inductive case*)
    assert (s_leq_Ss:  s <= S s).
    (* Show s <= S s*)
    Search (_ <= (S _)).
    apply Nat.le_succ_diag_r.
    assert (s_leq_Ss_twice: s <= 2 * S s).
    ring.

    

    