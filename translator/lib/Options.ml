let usage = "transiris -cmt <cmt file>"

(* If [input_ml] or [input_cmt] is specified, it shall be translated as a
   stand-alone file. In this case, either [output_coq]
   - is provided, in which case it defines where to print the translation,
   - is not provided, in which case the translation is dumped in the terminal.
   *)
let input_ml = ref "/dev/null"
let input_cmt = ref "/dev/null"
let output_coq = ref "/dev/null"

(* Alternatively, a directory can be provided as input. It should host a dune
   OCaml project that has been compiled already. *)
let input_dir = ref "/dev/null"
let output_dir = ref "/dev/null"

(* The [verbose] option can be used to print comments in the translation.
   The [debug] option can be used to dump the typed AST on [stderr]. *)
let verbose = ref false
let debug = ref false

let speclist = [
    ("-ml", Arg.Set_string input_ml, "Input ML file to read");
    ("-cmt", Arg.Set_string input_cmt, "Input CMT file to read");
    ("-out", Arg.Set_string output_coq, "Output file to use");
    ("-indir", Arg.Set_string input_dir, "Dune directory to translate");
    ("-outdir", Arg.Set_string input_dir,
     "Directory in which one should write the result of the translation.
      (to use together with [-indir].");
    ("-verbose", Arg.Set verbose, ".");
    ("-debug", Arg.Set debug, ".");
  ]

let () = Arg.parse speclist (fun _ -> assert false) usage
let input_ml = !input_ml
let input_cmt = !input_cmt
let output_coq = !output_coq
let input_dir = !input_dir
let output_dir = !output_dir
let verbose = !verbose
let debug = !debug


(* -------------------------------------------------------------------------- *)
(* Miscellaneous functions which are used during the sanity checks below. *)

let check_file s =
  not (Sys.is_directory s) && Sys.file_exists s

let check_dir s =
  Sys.is_directory s

(* -------------------------------------------------------------------------- *)

(* Sanity checks on the arguments passed to the program:
   - one should not try to translate both a single file and a full project at
   once,
   - if files were provided, they should exist,
   - if a directory was provided, it should (not checked yet) :
     + exist,
     + be a valid dune directory,
     + have already been compiled.
 *)
let () = assert (
             match input_ml = "/dev/null",
                   input_cmt = "/dev/null",
                   output_coq = "/dev/null",
                   input_dir = "/dev/null",
                   output_dir = "/dev/null" with
             | false, true, _, true, true ->
                (* An ml file was provided. *)
                check_file input_ml
             | true, false, _, true, true ->
                (* A cmt file was provided. *)
                check_file input_cmt
             | true, true, true, false, false ->
                (* in- and output directories were provided. *)
                check_dir input_dir && check_dir output_dir
             | _ -> false)
