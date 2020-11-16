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

Inductive Day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday
    .

Definition next_week_day (d:Day) : Day :=
    match d with 
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Eval compute in (next_week_day monday).

(* End of Reminders of Coq syntax *)

(*
Definition TT2BDD : BDD :=

    end.
*)


Check BDD.
Check TruthTable.

Inductive Ship : Set := PirateShip.

Inductive ActionResult : Set := Success | Failure.

Definition sink_ship (s: Ship) : ActionResult :=
    match s with PirateShip => Failure 
    end.

Eval compute in (sink_ship PirateShip).

Check BuildBDD "idBDD" "XOR".

