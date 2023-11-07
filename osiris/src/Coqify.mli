(**[module_expression me] transforms the Osiris module expression [e]
   into a Coq term. This Coq term may contain cut marks [CMark], so,
   after applying [Cut.cut], it will give rise to a sequence of Coq
   toplevel definitions.  *)
val module_expression : Syntax.mexpr -> Coq.expression
