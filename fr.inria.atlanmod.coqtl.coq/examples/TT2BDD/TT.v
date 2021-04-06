Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.

(* Truth Table *)

(** Columns **)

Inductive Var := 
  BuildVar :
  (* name *) string ->
  (* column *) nat ->
  Var.

(** Rows **)

Inductive Row :=
  BuildRow :
  (* inputs *) list nat ->
  (* output *) nat ->
  Row.