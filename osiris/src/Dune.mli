type module_name =
  string

type filename =
  string

(**A module description in the output of [dune describe]. *)
type module_description =
  { name : module_name
  ; impl : filename option
  ; intf : filename option
  ;  cmt : filename option
  ; cmti : filename option
  }

module M : Map.S with type key = module_name

(**A map of module names to module descriptions. *)
type module_table =
  module_description M.t

(**[describe dirname] invokes [dune describe] in the directory [dirname] and
   parses its output so as to obtain a module table. The output is parsed in a
   lenient way: we look for module descriptions and ignore everything else. *)
val describe : filename -> module_table

(**[impl m table] returns the path of the [.ml] file for module [m]. This is
   a relative path, which begins with something like [_build/default/]. This
   function fails if there is no [.ml] file for this module. *)
val impl : module_name -> module_table -> filename

(**[cmt m table] returns the path of the [.cmt] file for module [m]. This is
   a relative path, which begins with something like [_build/default/]. This
   function fails if there is no [.cmt] file for this module. *)
val cmt  : module_name -> module_table -> filename
