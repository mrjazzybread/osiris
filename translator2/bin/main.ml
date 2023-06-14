open Translator2
open Misc

(* [Options] is a module defined in [lib/Option.ml].
   It parses the command line and defines several useful variables such as the
   name of the OCaml file to translate, verbose functions, ... *)
include Options

(* -------------------------------------------------------------------------- *)

  (* [typedtree_of_cmt] takes the content of a [cmt] file as input. If the [cmt]
     contains an OCaml typed tree, it shall return it.
     Otherwise, the function causes a hard failure. *)
let typedtree_of_cmt ({cmt_annots;_}: Cmt_format.cmt_infos) =
  match cmt_annots with
  | Cmt_format.Implementation s -> s
  | _ -> verbose_msg "The cmt does not contain the typed-tree."; assert false

(* -------------------------------------------------------------------------- *)

let print _verbose _debug doc_graph fmt =
  let fmt = Format.formatter_of_out_channel fmt in
  Format.fprintf fmt "From osiris Require Import osiris.@.@.@.@.";
  DAG.to_list doc_graph
  |> List.iter (PPrint.ToFormatter.pretty 0.5 100 fmt);
  Format.fprintf fmt "@.(* Done. *)@?"

let unit = fun _ -> ()

(* -------------------------------------------------------------------------- *)

(* Main code of the translator.
   Each line either:
   - retrieves the typed-tree,
   - provides feedback to users,
   - is a translation pass,
   - breaks the initial program down to several definitions-to-be,
   - prepares the different parts for printing,
   - prints them in the required Coq file.
 *)

let () =
  begin
    match mode with
    | Mdune ->
       in_file
       |> verbose_say_with "Beginning the translation pipeline for the file [%s].@."
     |> in_dir dune_root locate_cmt
    | Mcmt -> cmt_file
  end
  |> Cmt_format.read_cmt
  |> typedtree_of_cmt
  (* If [-debug] is passed to the command line, dump the typed-tree to
     [stderr]. *)
  |> debug_do (Printtyped.implementation Format.err_formatter)

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
  |> Osiris.of_typedtree verbose_msg debug_msg

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
  |> OsirisSplit.split verbose_msg debug_msg
       splitting_strategy module_name

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
         let (t, m) = Preprint.definition_of_ast verbose_msg debug_msg m in
         s, t, m)

  |> Pp.pretty_printer verbose_msg debug_msg

  (* Finally, pretty-print the generated definitions into the output file
     provided on the command line.
     This pretty-printer is similar of that of the first translator, except that
     it should also print [EList _].
     [do_with e f g] is equivalent to:
     [let x = e in
      let _ = g x in
      f x]
   *)
  |> Misc.do_with (open_out out_file) close_out
       (print verbose_msg debug_msg)

  |> unit
