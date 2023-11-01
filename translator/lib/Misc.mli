val module_name : string -> string

val mkmsg : bool -> Format.formatter -> string -> unit
val mksay : bool -> Format.formatter -> string -> 'a -> 'a
val mksay_with : bool ->
                 Format.formatter ->
                 ('a -> unit, Format.formatter, unit) format -> 'a -> 'a
val mkdo : bool -> ('a -> unit) -> 'a -> 'a

val in_dir : string -> ('a -> 'b) -> 'a -> 'b
val locate_cmt : string -> string

val list_mls : string -> string -> string list * string list * string list
