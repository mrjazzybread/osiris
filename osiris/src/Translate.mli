(** [Translate] is a functor taking a settings module as a parameter. When
    producing the [Main] executable, it will be instantiated by the module
    [Settings], which parses the command line. This lets the interpreter use
    [Translate] without triggering the side effects in [Settings]. *)
module Make (_ : sig
  val warnings : bool
  val debug : ('a, out_channel, unit) format -> 'a
end) : sig

  (** [unit osource u] translates the OCaml typed AST [u], which represents a
      compilation unit, to an Osiris AST. The optional argument [osource] is the
      content of the OCaml source file. *)
  val unit : string option -> Typedtree.structure -> Syntax.mexpr

end
