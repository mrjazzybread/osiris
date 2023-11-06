(* This module parses the command line and exposes the settings. *)

(**The root directory of the dune project that we must translate.
   It is set by [--root]. *)
val root : string

(**The destination directory in which we we must place the translated files.
   This directory and its parents are created if they do not exist. It is set
   by [--out]. *)
val out : string

(**The OCaml modules that we must translate. This is either [`All], which
   means that all modules in this project must be translated, or a list of
   OCaml module names. *)
val modules : [ `All | `Modules of string list ]

(**The prefix that must be inserted in front of the name of every translated
   file. E.g., [foo.ml] in the project directory becomes [<mark>foo.v] in the
   destination directory. It is set by [--mark]. *)
val mark: string

(* [debug format ...] sends output to [stderr] only if [--debug] is set. *)
val debug: ('a, out_channel, unit) format -> 'a

(* [say format ...] sends output to [stderr] only if [--verbose] is set. *)
val say: ('a, out_channel, unit) format -> 'a

(**[warn format ...] sends output to [stderr] only if [--warnings] is set. *)
val warn : ('a, out_channel, unit) format -> 'a

(**[warnings] indicates whether [--warnings] is set. *)
val warnings: bool
