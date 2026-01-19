open Extracted.BinNums
open Extracted.Datatypes

(** Conversions from extracted (E) to manually-defined-in-OCaml types (O) *)

(* Convention: [ty] is the name of the function converting type [ty], so as to
   have [E2O.ty : E.ty -> O.ty] *)

(* There is a lot of shadowing involved, so we sometimes use [Stdlib.Module.t]
   instead of the corresponding predefined type such as [string] or [list] *)

(* [Stdlib] lets us reference OCaml's standard library. Osiris's standard
   library has a different module name to prevent shadowing. *)

val z : coq_Z -> int
val nat : nat -> int
val list : ('a -> 'b) -> 'a list -> 'b Stdlib.List.t
val prod : ('a1 -> 'b1) -> ('a2 -> 'b2) -> ('a1 * 'a2) -> ('b1 * 'b2)
val string : Extracted.String.string -> Stdlib.String.t

module O = Translatorlib.Syntax
module E = Extracted.Syntax (* from syntax.ml, extracted from syntax.v *)

(* Enumeration of [val ty : E.ty -> O.ty] for each syntax type [ty] *)

val var          : E.var                -> O.var
val name         : E.name               -> O.name
val path         : E.path               -> O.path
val data         : E.data               -> O.data
val field        : E.field              -> O.field
val pat          : E.pat                -> O.pat
val cpat         : E.cpat               -> O.cpat
val pats         : E.pat list           -> O.pats
val fpats        : E.(field * pat) list -> O.fpats
val coercion     : E.coercion           -> O.coercion
val fcoercions   : E.fcoercion list     -> O.fcoercions
val expr         : E.expr               -> O.expr
val exprs        : E.expr list          -> O.exprs
val fexpr        : E.fexpr              -> O.fexpr
val fexprs       : E.fexpr list         -> O.fexprs
val branch       : E.branch             -> O.branch
val branches     : E.branch list        -> O.branches
val binding      : E.binding            -> O.binding
val bindings     : E.binding list       -> O.bindings
val rec_binding  : E.rec_binding        -> O.rec_binding
val rec_bindings : E.rec_binding list   -> O.rec_bindings
val anonfun      : E.anonfun            -> O.anonfun
val mexpr        : E.mexpr              -> O.mexpr
val sitems       : E.sitem list         -> O.sitems
val sitem        : E.sitem              -> O.sitem
