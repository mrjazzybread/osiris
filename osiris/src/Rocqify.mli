(**[module_expression me] transforms the Osiris module expression [e]
   into a Rocq term. This Rocq term may contain cut marks [CMark], so,
   after applying [Cut.cut], it will give rise to a sequence of Rocq
   toplevel definitions.  *)
val module_expression : Syntax.mexpr -> Rocq.expression
