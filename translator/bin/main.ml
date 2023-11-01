open Printf
open Misc
open Options

(* -------------------------------------------------------------------------- *)

  (* [typedtree_of_cmt] takes the content of a [cmt] file as input. If the [cmt]
     contains an OCaml typed tree, it shall return it.
     Otherwise, the function causes a hard failure. *)
let typedtree_of_cmt ({cmt_annots;_}: Cmt_format.cmt_infos) =
  try
    match cmt_annots with
    | Cmt_format.Implementation s -> s
    | _ -> failwith "The cmt does not contain the typed-tree."
  with _ -> assert false

(* -------------------------------------------------------------------------- *)

let print out_file doc_graph =
  let f = open_out out_file in
  fprintf f "From osiris Require Import osiris.\n\n\n\n";
  DAG.to_list doc_graph
  |> List.iter (PPrint.ToChannel.pretty 0.5 100 f);
  fprintf f "\n(* Done. *)%!";
  close_out f

(* -------------------------------------------------------------------------- *)

(* Main code of the translator. *)

exception Skip_file

let translate_one_file module_name out_file (input_cmt : string) =
  let module_name = "_" ^ module_name in
  if verbose then eprintf "Translation process started for %s.\n\n" module_name;
  if verbose then eprintf "Cmt file: %s\n" input_cmt;
  input_cmt
  |> fun s ->
     begin
       try
         Cmt_format.read_cmt s
       with
       | Cmi_format.Error err ->
          match err with
          | Cmi_format.Not_an_interface filename ->
              if verbose then eprintf "'%s' is not an interface; skipping." filename;
              raise Skip_file
          | Cmi_format.Wrong_version_interface (filename, _) ->
             Printf.sprintf
               "'%s' was compiled with the wrong version of OCaml." filename
             |> failwith
          | Cmi_format.Corrupted_interface filename ->
             Printf.sprintf
               "The interface '%s' is corrupted." filename
             |> failwith
     end
  |> typedtree_of_cmt

  (* Convert the typedtree into an Osiris AST. The structure of the program is
     unchanged. The only two differences between the Coq and OCaml versions of
     the Osiris ASTs are:
     - the OCaml AST contains an additional constructor for module-expressions,
       expressions, etc. to represent parts of the AST which will be put in
       different top-level Coq edfinitions.
     - while the Coq AST contains several ad-hoc lists, the OCaml AST does not:
       native lists are used every time.
       This will also help with the translation: one can then use the syntactic
       sugar defined in [theories/lang/sugar.v]. *)
  |> Osiris.of_typedtree module_name

  (* Break down the AST into pieces according to the user-specified
     splitting-strategy.
     Current supported strategies are:
     - NoSplit
     Soon to be added strategies are:
     - SplitTopLevelBindings
     - SplitSubModules
     - ...
     It should be possible to apply several splitting strategies in a row:
     to pass [-split-top-level -split-sub-modules] to the command line should:
     1. split on top-level bindings
     2. in every pieces, split on sub-modules

     Note: the order in which the arguments are provided might influence the
           end-result (eg. the final definitions might appear in a different
           order).
           Therefore, once a strategy is chosen for a file which git tracks, it
           should not be changed unless necessary as it might produce large
           unnecessary diffs.

     It is the function [split] that will choose names for the auxiliary
     definitions. *)
  |> Split.split splitting_strategy

  (* [Preprint.definition_of_ast] provides a translation that works in a similar
     manner than the first translator:
     converts the AST into:
     - [EPlain s], which should be seen as a plain string [s] to print in the
       final document
     - [EConstr (c, [e1; ...; en])], which should be printed as
       [c (e1) ... (en)] in the final document.
     - [EList (c; [e1; ...; en])], which did not exist in the first translator.
       It should be printed as [c [e1; ...; en]], which is useful to use
       syntactic sugar. *)
  |> DAG.map
       (fun (s, m) ->
         let (t, m) = Preprint.definition_of_ast m in
         s, t, m)

  |> Pp.pretty_printer

  (* Finally, pretty-print the generated definitions into the output file
     provided on the command line.
     This pretty-printer is similar of that of the first translator, except that
     it should also print [EList _].
   *)
  |> print out_file

(* -------------------------------------------------------------------------- *)

(* Start the translation depending on the mode:
   - "ml"
      In this mode, the user is expected to provide paths to
      + the "ml" file to translate,
      + the root of the dune project,
      + the output to produce.
      This mode assumes that the files have already been compiled by dune.
   - "cmt"
     In this mode, the user is expected to provide paths to
     + the "cmt" file from which the typed-tree shall be retrieved,
     + the output to produce.
     This mode assumes that the cmt contains the typed-tree.
   - "dune"
     In this mode, the user is expected to provide paths to
     + the directory to translate,
     + the output directory to produce.
     This mode expects the output directory to either be absent or have the same
     structure as the input directory. *)

let () =
  match mode with
  | Mml s ->
      if verbose then eprintf "Beginning the translation pipeline for the file [%s].\n" in_file;
     in_file
     |> in_dir dune_root locate_cmt
     |> (* Never catch [Skip_file]. *)
       translate_one_file s out_file
  | Mcmt s ->
     (* Never catch [Skip_file]. *)
     translate_one_file s out_file cmt_file
  | Mdune ->
     (* 1. parse the input directory. *)
     let mls, vs, dirs = Misc.list_mls in_file out_file in
     (* 2. test if the output directory exists. *)
     List.iter
       (fun dir ->
         try
           Sys.mkdir dir 0o700
         with
         | Sys_error s ->
             if debug then eprintf "Directory already exists: %s ; skipping.\n" s
       )
       dirs;
     (* 3. translate all the files, one by one. *)
     List.iter
       (fun (ml, v) ->
         let name = module_name ml in
         let s = in_dir dune_root locate_cmt ml in
         if verbose then eprintf  "The cmt: '%s'.\n" s;
         try translate_one_file name v s
         with Skip_file -> ())
       (List.combine mls vs)
