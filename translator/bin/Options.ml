(* Misc. *)
let usage = "transiris -ml <ml file to convert>@.\
             \t-dune <root of the dune directory>@.\
             \t-cmt <cmt file to use>
             \t-out <path to the output Coq file to write>@.\
             Note: You should either use -dune or -cmt.@."

type mode =
  | Mcmt of string
  | Mml of string
  | Mdune

(* -------------------------------------------------------------------------- *)

(* Variables used to store Arguments. *)

let dune_root = ref ""
let cmt_file = ref ""
let in_file = ref ""
let out_file = ref ""
let mode = ref ""

(* Verbose can be used to display general informations on the translation
   process:
   - progress (ie. what are the current and previous steps),
   - number of definitions in the Coq file.
 *)
let verbose = ref false

(* If [debug] is set, the typedtree and intermediate versions are printed to
   [stderr]. *)
let debug = ref false

(* TODO: reset to the empty list by default. *)
let splitting_strategy : [`Split | `NoSplit] list ref = ref [`Split]

(* -------------------------------------------------------------------------- *)

(* Definition of the command-line options and parsing. *)

let speclist = [
    ("-mode", Arg.Set_string mode, "cmt, ml or dune");
    ("-in-dir", Arg.Set_string in_file, "Directory to translate.");
    ("-ml", Arg.Set_string in_file, "Input OCaml file to read.");
    ("-out", Arg.Set_string out_file, "Output Coq file or directory to produce.\
                                       \ (mandatory)");
    ("-root", Arg.Set_string dune_root, "Root of the dune repository to use.");
    ("-cmt", Arg.Set_string cmt_file, "cmt file to use when retrieving the\
                                       \ typed-tree.");
    ("-verbose", Arg.Set verbose, "(optional)");
    ("-debug", Arg.Set debug, "(optional)");
    ("-no-split", Arg.Unit
                 (fun () ->
                   splitting_strategy := []),
     "Do not split the output Coq definition. (optional)");
  ]

let () = Arg.parse speclist
           (fun _ -> assert false) (* Unknown elements on the command-line are
                                      not permitted. *)
           usage

(* -------------------------------------------------------------------------- *)

(* Forget the references of the above variables. *)

let (dune_root, in_file, out_file, splitting_strategy, cmt_file, mode) =
  !dune_root, !in_file, !out_file, !splitting_strategy, !cmt_file,
  if !mode = "cmt"
  then Mcmt (Misc.module_name !cmt_file)
  else if !mode = "ml"
  then Mml (Misc.module_name !in_file)
  else if !mode = "dune"
  then Mdune
  else assert false

let () = assert (out_file <> "")
let () =
  match mode with
  | Mcmt _ -> assert (cmt_file <> "")
  | Mml _ -> assert (in_file <> "" && dune_root <> "")
  | Mdune -> assert (dune_root <> "")

let verbose = !verbose
let debug = !debug
