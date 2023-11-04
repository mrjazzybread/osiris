type filename =
  string

(**[is_absolute filename] determines whether [filename] is an absolute
   file name. It is the negation of [is_relative filename]. *)
val is_absolute : filename -> bool

(**[remove_suffix suffix name] checks that [name] ends with [suffix] and
   removes this suffix. Beware: compared with [Filename.chop_suffix],
   argument order is reversed. *)
val remove_suffix : string -> filename -> filename

(**[add_prefix prefix base] is [prefix ^ base]. *)
val add_prefix : string -> filename -> filename

(**[add_suffix suffix base] is [base ^ suffix]. *)
val add_suffix : string -> filename -> filename

(**[drop k filename] drops the first [k] '/'-separated segments of the
   file name [filename]. This file name must be a relative file name. *)
val drop : int -> filename -> filename

(**[map_basename f filename] applies the transformation [f] to the
   base name of the file name [filename], while preserving its path. *)
val map_basename : (string -> string) -> filename -> filename
