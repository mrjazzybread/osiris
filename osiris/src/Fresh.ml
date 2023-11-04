(* -------------------------------------------------------------------------- *)

(* Upon breaking down an AST, one might generate unnamed expressions.
   [fresh_name] below generates fresh names. The names are of the form:
   [prefix][type of the term][unique number]. *)

let prefix = "__osiris__reserved"

let fresh_name =
  let c = ref 0 in
  fun s -> incr c; prefix ^ s ^ (string_of_int !c)
