Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import TT2BDD.TT.
Require Import TT2BDD.BDDv2.

(* Reminders of Coq syntax *)

Inductive Day : Type :=
    | monday : Day
    | tuesday : Day
    | wednesday : Day
    | thursday : Day
    | friday : Day
    | saturday : Day
    | sunday : Day
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

