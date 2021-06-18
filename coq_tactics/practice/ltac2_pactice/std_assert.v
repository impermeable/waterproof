From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Goal forall n:nat, n = n.

    (* Std.assert expects an AssertType.
        - an intropatterns opt. 
            The whole (Some (Std.IntroNaming (Std.IntroIdentifier @my_assert))) 
            thing just wraps an ident into an intropatterns.
        - constr, the actual thing to assert
        - unit -> unit opt (I just used None)
    *)
    Std.assert (Std.AssertType 
        (Some (Std.IntroNaming (Std.IntroIdentifier @my_assert))) 
        constr:(forall n:nat, n = n) None).
    reflexivity.