(** * waterprove.v
Authors: 
    - Cosmin Manea (1298542)
    - Lulof Pirée (added error)

Creation date: 01 June 2021

The waterprove automation function.
This function calls the automation tactics, [auto], [eauto] and [intuition], 
with a specific set of lemmas.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
Require Import Reals.

Ltac2 Type exn ::= [ AutomationFailure(string) ].

Local Ltac2 fail_automation () := 
        Control.zero (AutomationFailure 
        "Waterproof could not find a proof. 
If you believe the statement should hold, 
try making a smaller step.").

(** * waterprove
    Calls the automation tactics [auto], [eauto] and [intuition], 
    with a specific set of lemmas.

    Arguments:
        - [t: constr], the result to be proven by automation.
        - [s: constr], the list of lemmas to be used in the automation tactics.
        - [n: int], the search depth.

    Does:
        - Calls the automation tactics [auto], [eauto], [intuition (auto)] and [intuition (eauto)], 
          in this order, with search of depth equal to [n] and with the set of lemmas supplied by [s].
        - If no proof is found, print a message conveying the failture.

    Raises exceptions:
        - [AutomationFailure], if no proof of [t] was found.
*)
Ltac2 waterprove (t:constr) (s:constr) (n:int) :=
    let result () :=
        first [
            solve [auto n using $s with *]
            | solve [eauto n using $s with *]
            | solve [ltac1:(s |- intuition (auto using s with *)) 
                (Ltac1.of_constr s)]
            | solve [ltac1:(s |- intuition (eauto using s with *)) 
                (Ltac1.of_constr s)]
            | print (concat 
                  (of_string "Waterproof could not find a proof of ") 
                  (of_constr t)
                );
                fail_automation ()
            ]
    in
    match Control.case result with
    | Val _ => ()
    | Err exn => fail_automation ()
    end.