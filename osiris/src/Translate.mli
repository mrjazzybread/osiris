(**[unit osource u] translates the OCaml typed AST [u], which represents a
   compilation unit, to an Osiris AST. The optional argument [osource] is
   the content of the OCaml source file. *)
val unit : string option -> Typedtree.structure -> Syntax.mexpr
