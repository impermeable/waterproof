Check False.
Check True.
Check (3=5).
Check (3, 5).
Check 3:nat.
Check (fun x:nat => x=3).
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).

Check (let f := fun x => (x * 3, x) in f 3).

Locate "_ <= _".

Check and.

(* this is a comment *)

(* Compute f(3) where f(x) = (3x, x) *)
Compute let f := fun x => (x*3, x) in f 3.

Check (let my_sum := fun v w x y z => w+v+x+y+z in my_sum 1 2 3 4 5).
Compute (let my_sum := fun v w x y z => w+v+x+y+z in my_sum 1 2 3 4 5).

