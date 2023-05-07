(* [Translator.Options] parses the command line and performs sanity checks
   on its arguments. *)
include Translator.Options

let require_imports =
  [
    ("osiris", ["base"]);
    ("osiris.lang", [ "lang" ]);
  ]


(* -------------------------------------------------------------------------- *)
(* Miscellaneous functions. *)

let use_and_return f e = f e; e
let maybe b e i = if b then use_and_return e i else i
let rec remove_last (l: string list) : string list * string =
  match l with
  | [] -> [], ""
  | h :: [] -> ([], h)
  | h :: t -> let (t, l) = remove_last t in
                 h :: t, l

(* [verbose_msg] can be used to print a message of the form:
   « [verbose] [message] » to [stderr]. *)
let verbose_msg s = if verbose then (Format.fprintf Format.err_formatter "[verbose] %s@." s)
let verbose_do = maybe verbose
let debug_do = maybe debug

(* [comment_and_print] prints an untyped version of the AST using
   [compiler-libs]. *)
let comment_and_print fmt p =
  Format.fprintf fmt "(* Original file:@.%a *)@.@." Pprintast.structure p

(* [header] takes a cmt file and returns a string containing a list of
   [Require Import] needed by the produced Coq file.
   For now, it assumes that the dependencies live in a directory called [libs]
   at the root of the project. *)
let header (ci: Cmt_format.cmt_infos) =
  let rec ocaml_deps fmt = function
    | [] -> ()
    | (h, _) :: t ->
       if not (List.mem h [ci.cmt_modname; "CamlinternalFormatBasics"])
       then Format.fprintf fmt "From osiris.libs Require Import %s.@.%a"
              h ocaml_deps t
       else ocaml_deps fmt t
  in
  let rec coq_deps fmt (l: (string * string list) list) =
    let rec print_line fmt = function
      | [] -> ()
      | h :: t -> Format.fprintf fmt " %s%a" h print_line t
    in
    match l with
    | [] -> ()
    | (prefix, l) :: t ->
       Format.fprintf fmt"From %s Require Import%a.@.%a"
         prefix print_line l
         coq_deps t
  in
  Format.asprintf "(* Converting a single CMT file for [%s]. *)@.@.\
                   (* Auto generated headers. They import the required Coq modules:@.\
                   \   - either translations of the dependencies of the present file@.\
                   \   - or static dependencies defining the language@.\
                   \   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)@.\
                   %a@.%a"
                  ci.cmt_modname
                  coq_deps require_imports
                  ocaml_deps ci.cmt_imports


(* -------------------------------------------------------------------------- *)
(* Actual main Conversion functions... *)


(* ...for a single [cmt] file.

   The function [run_cmt]:
   1. reads the cmt file to know what Coq modules to require,
   Note: The header of the Coq file is not printed right away so that
   ````` verbose messages can be printed without interrupting the
   translation.
   2. opens the ml file to get an untyped AST,
   3. computes the typed AST.

   Note: [run_cmt] prints to a formatter. This way, it is posisble for [run_ml]
   ````` and [run_dune] to decide where the output should be and for the user to
   ask the translation tool either to print the result in a Coq file or to
   dump it in the terminal. *)
let run_cmt fmt input_cmt =
  verbose_msg "Starting the conversion of a single file.";
  let cmt_infos = Cmt_format.read_cmt input_cmt in
  let typedtree =
    match cmt_infos.cmt_annots with
    | Cmt_format.Packed _ -> assert false
    | Cmt_format.Implementation s -> s
    | Cmt_format.Interface _ -> assert false
    | Cmt_format.Partial_implementation _ -> assert false
    | Cmt_format.Partial_interface _ -> assert false
  in
  let headers = header cmt_infos in
  typedtree
  (* Print the untyped AST if verbose is enabled. *)
  |> verbose_do
       (fun p -> comment_and_print fmt (Untypeast.untype_structure p))
  (* Print the typed AST if verbose is enabled.
     (An option -debug should be added to print this AST on [stderr].) *)
  |> debug_do (fun p -> Printtyped.implementation Format.err_formatter p)
  (* Translate the AST. *)
  |> Translator.Translate.translate
  (* Print the final result. *)
  |> Translator.Pp.print fmt cmt_infos.cmt_modname headers



(* ...for a single [ml] file.
   The function [run_ml]:
   1. locates the [ml] file,
   2. looks for a corresponding [cmt] file in the same directory,
   3.a. if a [cmt] file is found, use it
   3.b. otherwise, try to find a dune project in parent directories to get
   the [cmt] file,
   4. calls [run_cmt]. *)
let run_ml fmt input_ml =
  (* 1. *)
  verbose_msg "run_ml: locating the ml file.";
  let (base_directory, file_name) =
    match String.split_on_char '/' input_ml with
    | [] -> assert false
    | _ :: [] ->
       (".", List.hd (String.split_on_char '.' input_ml))
    | l ->
       begin
         let dir, last = remove_last l in
         let dir = String.concat "/" dir in
         let last = List.hd (String.split_on_char '.' last) in
         (dir, last)
       end
  in

  (* 2. *)
  let cmt = base_directory ^ "/" ^ file_name ^ ".cmt" in
  if Sys.file_exists cmt
  then begin (* 3.a. *)
      verbose_msg ("run_ml: some cmt lives with the ml file, using this file.");
      run_cmt fmt cmt
    end
  else begin (* 3.b. *)
      verbose_msg "run_ml: the cmt does not live with the ml file, looking for a cmt created by dune.";
      run_cmt fmt
        (match Translator.Dune.cmt_of_ml verbose_msg base_directory file_name with
         | None -> assert false
         | Some cmt -> cmt)
    end


(* ...for a whole dune project *)
let run_dune () =
  assert false

let () =
  (* Decide what operations to perform depending on the flags passed to the
     translation tool. *)
  if input_dir <> "/dev/null"
  then run_dune ()
  else if input_ml = "/dev/null"
  then run_cmt Format.std_formatter input_cmt
  else run_ml Format.std_formatter input_ml
