open Extracted.BinNums
open Extracted.Datatypes

(** Conversions from manually-defined-in-OCaml (O) to extracted types (E) *)

(* See module [E2O]'s interface for more information *)

val z : int -> coq_Z
val nat : int -> nat
val list : ('a -> 'b) -> 'a Stdlib.List.t -> 'b list
val string : Stdlib.String.t -> Extracted.String.string

module O = Translatorlib.Syntax
module E = Extracted.Syntax

(* [val ty : O.ty -> E.ty] *)

val var          : O.var          -> E.var
val name         : O.name         -> E.name
val path         : O.path         -> E.path
val data         : O.data         -> E.data
val field        : O.field        -> E.field
val pat          : O.pat          -> E.pat
val cpat         : O.cpat         -> E.cpat
val pats         : O.pats         -> E.pat list
val fpats        : O.fpats        -> E.(field * pat) list
val coercion     : O.coercion     -> E.coercion
val fcoercions   : O.fcoercions   -> E.fcoercion list
val expr         : O.expr         -> E.expr
val exprs        : O.exprs        -> E.expr list
val fexpr        : O.fexpr        -> E.fexpr
val fexprs       : O.fexprs       -> E.fexpr list
val branch       : O.branch       -> E.branch
val branches     : O.branches     -> E.branch list
val binding      : O.binding      -> E.binding
val bindings     : O.bindings     -> E.binding list
val rec_binding  : O.rec_binding  -> E.rec_binding
val rec_bindings : O.rec_bindings -> E.rec_binding list
val anonfun      : O.anonfun      -> E.anonfun
val mexpr        : O.mexpr        -> E.mexpr
val sitems       : O.sitems       -> E.sitem list
val sitem        : O.sitem        -> E.sitem
