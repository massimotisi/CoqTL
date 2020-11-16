Require Import String.
Open Scope string_scope.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.Model.
Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import examples.TT2BDD.TT.
Require Import examples.TT2BDD.BDDv2.

(* Reminders of Coq syntax *)

Inductive Ship : Set := PirateShip | KingShip .

Inductive ActionResult : Set := Success | Failure.

Definition sink_ship (s: Ship) : ActionResult :=
    match s with PirateShip => Failure | KingShip => Success
    end.

Eval compute in (sink_ship PirateShip).
Eval compute in (sink_ship KingShip).

(* End of Reminders of Coq syntax *)


Eval compute in (BuildBDD "bddIdD" "bddName").




