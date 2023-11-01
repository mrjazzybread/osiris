val module_name : string -> string

val mkmsg : bool -> Format.formatter -> string -> unit

val in_dir : string -> ('a -> 'b) -> 'a -> 'b
val locate_cmt : string -> string

val list_mls : string -> string -> string list * string list * string list
