open Printf
open Fail

(* -------------------------------------------------------------------------- *)

(* Settings. *)

let root =
  ref None

let out =
  ref None

let modules =
  ref []

let mark =
  ref ""

type strategy = [`Split|`NoSplit]

(* TODO: reset to the empty list by default. *)
let splitting_strategy : strategy list ref =
  ref [`Split]

let debug =
  ref false

let verbose =
  ref false

(* -------------------------------------------------------------------------- *)

(* Definition of the command-line options and parsing. *)

let set_opt setting value =
  setting := Some value

let no_split () =
  splitting_strategy := []

let spec = [
    "--debug", Arg.Set debug, " (undocumented)";
    "--mark", Arg.Set_string mark, " A prefix that is added to every file name (default: empty)";
    "--out", Arg.String (set_opt out), " Output directory (mandatory)";
    "--root", Arg.String (set_opt root), " Dune root directory (mandatory)";
    "--verbose", Arg.Set verbose, " (undocumented)";
    "-no-split", Arg.Unit no_split, " Do not split Coq definitions"; (* TODO clean up *)
  ]

let anonymous m =
  modules := m :: !modules

let usage =
  sprintf "Usage: %s <options> <module names>" Sys.argv.(0)

let () =
  Arg.parse spec anonymous usage

(* -------------------------------------------------------------------------- *)

(* Forget the references of the above variables. *)

let root =
  match !root with
  | None ->
      fail "Missing command line argument: --root <dune root directory>\n"
  | Some root ->
      root

let () =
  match Sys.is_directory root with
  | true ->
      ()
  | false ->
      fail "Not a directory: %s\n" root
  | exception Sys_error _ ->
      fail "Directory does not exist: %s\n" root

let out =
  match !out with
  | None ->
      fail "Missing command line argument: -o <output directory>\n"
  | Some out ->
      out

let () =
  match Sys.is_directory out with
  | true ->
      ()
  | false ->
      fail "Not a directory: %s\n" out
  | exception Sys_error _ ->
      ()

let modules =
  match !modules with
  | ["all"] ->
      `All
  | modules ->
      `Modules modules

let mark =
  !mark

let splitting_strategy =
  !splitting_strategy

let debug =
  !debug

let verbose =
  !verbose

let debug format =
  if debug then fprintf stderr format else ifprintf stderr format

let say format =
  if verbose then fprintf stderr format else ifprintf stderr format
