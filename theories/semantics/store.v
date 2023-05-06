From stdpp Require Import countable numbers gmap.
From iris.prelude Require Import prelude options.
From osiris.lang Require Import locations lang.

(* This file defines the physical store. *)

(* The store is a map of locations to values. *)

Definition store : Type := gmap loc val.
