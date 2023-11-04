(* [invoke command] invokes an external command (which expects no input)
   and returns its output, if the command succeeds. It returns [None] if
   the command fails. *)

val invoke: string -> string option
