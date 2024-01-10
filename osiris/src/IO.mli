(**[invoke command] invokes an external command (which expects no input)
   and returns its output, if the command succeeds. It returns [None] if
   the command fails. *)
val invoke: string -> string option

(**[read_whole_file filename] reads the file [filename] in text mode and
   returns its contents as a string. *)
val read_whole_file: string -> string
