open Printf
open Rocq

module Make () = struct

(* -------------------------------------------------------------------------- *)

(* Generating fresh names. *)

(* Each base name has its own counter.
   The first definition for a base is named [__base]; subsequent
   definitions for the same base (created by shadowing) are named
   [__base1], [__base2], etc. The table [used] guards against accidental
   collisions between distinct bases. *)

let counters : (string, int) Hashtbl.t =
  Hashtbl.create 33

let used : (string, unit) Hashtbl.t =
  Hashtbl.create 33

let reserve x =
  Hashtbl.add used x ()

let rec fresh base =
  let n = try Hashtbl.find counters base with Not_found -> 0 in
  Hashtbl.replace counters base (n + 1);
  let x = if n = 0 then sprintf "__%s" base else sprintf "__%s%d" base n in
  if Hashtbl.mem used x then fresh base else (reserve x; x)

(* -------------------------------------------------------------------------- *)

(* Emitting a list of definitions. *)

let defs : defs ref =
  ref []

let emit def =
  defs := def :: !defs

let emitted () : defs =
  List.rev !defs

(* -------------------------------------------------------------------------- *)

(* Transforming an expression. *)

let rec cut_expr e =
  match e with
  | CAtom s ->
      CAtom s
  | CCon (c, es) ->
      CCon (c, cut_exprs es)
  | CList es ->
      CList (cut_exprs es)
  | CTuple es ->
      CTuple (cut_exprs es)
  | CCut (base, e) ->
      let e = cut_expr e in
      (* Obey the mark: cut off this subterm. *)
      (* Pick a name. *)
      let x = fresh base in
      (* Emit a definition of [x]. *)
      emit { lhs = x; rhs = e };
      (* Return a reference to [x]. *)
      CAtom x

and cut_exprs es =
  List.map cut_expr es

(* -------------------------------------------------------------------------- *)

(* Transforming a definition. *)

let cut_def def : defs =
  reserve def.lhs;
  let def = { def with rhs = cut_expr def.rhs } in
  emit def;
  emitted()

end

(* -------------------------------------------------------------------------- *)

(* The main transformation function. *)

let cut (def : def) : defs =
  let module M = Make() in
  M.cut_def def
