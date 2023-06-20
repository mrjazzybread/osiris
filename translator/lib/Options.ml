(* Misc. *)
let usage = "transiris -ml <ml file to convert>@.\
             \t-dune <root of the dune directory>@.\
             \t-cmt <cmt file to use>
             \t-out <path to the output Coq file to write>@.\
             Note: You should either use -dune or -cmt.@."

type splitting_strategy =
  | Split
  | NoSplit

type mode =
  | Mcmt
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
   Each function used to define a translation step will be provided with two
   functions:
   + [verbose_msg: string -> unit], which will either do nothing or print a
     message on [stderr],
   + [verbose_out: string -> unit], which will append to the header of the
     produced Coq file. *)
let verbose = ref false

(* If [debug] is set, the typedtree and intermediate versions are printed to
   [stderr]. *)
let debug = ref false

(* TODO: reset to the empty list by default. *)
let splitting_strategy = ref [Split]

(* -------------------------------------------------------------------------- *)

(* Definition of the command-line options and parsing. *)

let speclist = [
    ("-mode", Arg.Set_string mode, "cmt or ml");
    ("-ml", Arg.Set_string in_file, "Input OCaml file to read. \
                                     (should be used iff -root is)");
    ("-out", Arg.Set_string out_file, "Output Coq file to produce. \
                                       (mandatory)");
    ("-root", Arg.Set_string dune_root, "Root of the dune repository to use \
                                         (mandatory of -cmt is not used)");
    ("-cmt", Arg.Set_string cmt_file, "cmt file to use when retrieving the\
                                       \ typed-tree \
                                       (mandatory of -cmt is not used)");
    ("-verbose", Arg.Set verbose, "(optional)");
    ("-debug", Arg.Set debug, "(optional)");
    ("-no-split", Arg.Unit
                 (fun () ->
                   splitting_strategy := [NoSplit]),
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
  then Mcmt
  else if !mode = "ml"
  then Mdune
  else assert false

let () = assert (out_file <> "")
let () =
  match mode with
  | Mcmt -> assert (cmt_file <> "")
  | Mdune -> assert (in_file <> "" && dune_root <> "")

let verbose = !verbose
let debug = !debug

(* -------------------------------------------------------------------------- *)

let verbose_msg = Misc.mkmsg verbose Format.err_formatter
let debug_msg = Misc.mkmsg debug Format.err_formatter

let verbose_say s = Misc.mksay verbose Format.err_formatter s
let debug_say s = Misc.mksay debug Format.err_formatter s

let verbose_do f = Misc.mkdo verbose f
let debug_do f = Misc.mkdo debug f

let verbose_say_with s a = Misc.mksay_with verbose Format.err_formatter s a
let debug_say_with s a = Misc.mksay_with verbose Format.err_formatter s a

(* -------------------------------------------------------------------------- *)

(* The module name can be deduced from the filename of the input OCaml file: *)
let module_name =
  begin
    match mode with
    | Mdune ->
       in_file
    | Mcmt ->
     cmt_file
  end
  |> String.split_on_char '/' |> Misc.last (* Only keep the filename, not its
                                              path. *)
  |> String.split_on_char '.' |> List.hd (* Strip away the extension
                                            (assuming there is only one '.' in
                                            the  filename). *)
  |> String.capitalize_ascii (* Capitalize the first letter. *)
