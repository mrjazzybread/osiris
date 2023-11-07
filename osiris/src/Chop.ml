open Printf
open Coq

module Make () = struct

(* -------------------------------------------------------------------------- *)

(* Generating fresh names. *)

let c =
  ref 0

let next () =
  let this = !c in
  c := this + 1;
  this

let fresh base =
  sprintf "__%s%d" base (next())

(* -------------------------------------------------------------------------- *)

(* Emitting a list of definitions. *)

let defs : def list ref =
  ref []

let emit def =
  defs := def :: !defs

let emitted () : def list =
  List.rev !defs

(* -------------------------------------------------------------------------- *)

(* Transforming an expression. *)

let rec chop_expr e =
  match e with
  | CAtom s ->
      CAtom s
  | CCon (c, es) ->
      CCon (c, chop_exprs es)
  | CList es ->
      CList (chop_exprs es)
  | CTuple es ->
      CTuple (chop_exprs es)
  | CCut (base, e) ->
      let e = chop_expr e in
      (* Obey the mark: cut off this subterm. *)
      (* Pick a name. *)
      let x = fresh base in
      (* Emit a definition of [x]. *)
      emit { lhs = x; rhs = e };
      (* Return a reference to [x]. *)
      CAtom x

and chop_exprs es =
  List.map chop_expr es

(* -------------------------------------------------------------------------- *)

(* Transforming a definition. *)

let chop_def def : def list =
  let def = { def with rhs = chop_expr def.rhs } in
  emit def;
  emitted()

end

(* -------------------------------------------------------------------------- *)

(* The main transformation function. *)

let chop (def : def) : def list =
  let module M = Make() in
  M.chop_def def
