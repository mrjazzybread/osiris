(**[unit m u] translates the OCaml typed AST [u], which represents a
   compilation unit, to an Osiris AST. This Osiris AST is wrapped in
   a Coq toplevel definition named [m]. *)
val unit : Syntax.coq_id -> Typedtree.structure -> Syntax.def
