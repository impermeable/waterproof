(** * string_of_inequalities.v
Authors: 
    - Cosmin Manea (1298542)

Creation date: 06 June 2021

Tactics for strings of inequalities.
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
From Ltac2 Require Import Option.


Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.


(** Functions for proving a step *)

Ltac2 extended_reflexivity () :=
    try (reflexivity); try (apply Rle_refl); try (apply Rge_refl).

Ltac2 extended_assumption () :=
    try (assumption); try (apply Rlt_le; assumption); try (apply Rgt_ge; assumption).

Ltac2 rewrite_all_tac () :=
    match! goal with
        | [h : _ = _ |- _] => let h_val := Control.hyp h in try (rewrite $h_val); extended_reflexivity ()
    end.

Ltac2 prove_step ():=
    try (auto with *); try (rewrite_all_tac ()); try (extended_assumption ()).


(** Functions for performing transitivity *)