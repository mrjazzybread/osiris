(**[unit u] translates the OCaml typed AST [u], which represents a
   compilation unit, to an Osiris AST. *)
val unit : Typedtree.structure -> Syntax.mexpr
