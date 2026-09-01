[@@@warning "-40-42"]
open Printf

(* -------------------------------------------------------------------------- *)

(* Quick-and-dirty error reporting. *)

let die _c =
  exit 1

let fail format =
  kfprintf die stderr format

(* -------------------------------------------------------------------------- *)

(* The format of a module description in the output of [dune describe]. *)

include struct

open Base

type module_description =
  { name : string
  ; impl : string option
  ; intf : string option
  ;  cmt : string option
  ; cmti : string option
  }
[@@deriving of_sexp]

end

type module_name =
  string

type filename =
  string

(* -------------------------------------------------------------------------- *)

(* [extract_module_descriptions e] extracts a list of module descriptions out
   of the S-expression [e], whose structure is not known. Each node is either
   recognized as a module description or recursively searched for module
   descriptions. *)

let rec extract_module_descriptions (e : Base.Sexp.t) accu =
  (* Hard-coded, fragile, patterns to avoid generating AST files for Osiris's
     own ml files when they are in [rocq_osiris]. *)
  (* TODO: support having different modules with the same name. *)
  match e with
  | List (Atom "executables" :: [List (List (Atom "names" :: [List [Atom ("interp" | "Main")]]) :: _)]) ->
    Printf.fprintf stderr "Warning: extract_module_descriptions: skipping translator/interp executable\n";
    accu
  (* [osiris.proph]: the translator gives the constructs it names their own
     meaning, so its OCaml definitions have no Rocq counterpart and must not
     be translated. *)
  | List [Atom "library"; List (List [Atom "name";
      Atom ("translatorlib" | "extracted" | "osiris.proph" as name)] :: _)] ->
    Printf.fprintf stderr "Warning: extract_module_descriptions: skipping S-expression (library ((name %s) ...))\n" name;
    accu
  | _ ->
  match [%of_sexp: module_description] e with
  | mdesc ->
      (* Success: this node is a module description. *)
      mdesc :: accu
  | exception _ ->
      (* Failure: this node is not a module description. *)
      match e with
      | Base.Sexp.Atom _ ->
          accu
      | Base.Sexp.List es ->
          (* Search its children. *)
          List.fold_right extract_module_descriptions es accu

let extract_module_descriptions (e : Base.Sexp.t) : module_description list =
  extract_module_descriptions e []

(* -------------------------------------------------------------------------- *)

(* [describe dirname] invokes [dune describe] in the directory [dirname],
   parses its output, and returns a list of module descriptions. *)

let extract_root (e : Base.Sexp.t) : string =
  match e with
  | Base.Sexp.List items ->
      (match List.find_opt (function
        | Base.Sexp.List [Base.Sexp.Atom "root"; Base.Sexp.Atom _] -> true
        | _ -> false
       ) items with
      | Some (Base.Sexp.List [Base.Sexp.Atom "root"; Base.Sexp.Atom path]) -> path
      | _ -> fail "Could not find (root ...) in dune describe output\n")
  | _ ->
      fail "Unexpected top-level sexp from dune describe\n"

let describe_raw dirname =
  let cmd =
    sprintf "cd %s && dune describe --lang 0.1 --format csexp"
      (Filename.quote dirname)
  in
  match IO.invoke cmd with
  | None ->
      fail "Invoking [dune describe] failed.\n"
  | Some description ->
      let module C = Csexp.Make(Base.Sexp) in
      match C.parse_string description with
      | Error (ofs, msg) ->
          fail "Could not parse the output of [dune describe]: %d: %s\n" ofs msg
      | Ok sexp ->
          (extract_root sexp, extract_module_descriptions sexp)

(* -------------------------------------------------------------------------- *)

(* A list of module descriptions can be turned into a map, where the module
   name is the key. *)

module M = Map.Make(String)

open M

type module_table =
  module_description t

let add name mdesc table =
  if mem name table then
    fail "There are two modules named %s.\n" name
  else
    add name mdesc table

let tabulate mdescs =
  let loop table mdesc = add mdesc.name mdesc table in
  List.fold_left loop empty mdescs

let describe dirname =
  let (root, mdescs) = describe_raw dirname in
  (root, tabulate mdescs)

(* -------------------------------------------------------------------------- *)

(* An accessor. *)

let find (name : module_name) (table : module_table) : module_description =
  try
    find name table
  with Not_found ->
    fail "The module %s does not exist.\n" name

let impl name table =
  match (find name table).impl with
   | Some filename ->
       filename
   | None ->
       fail "No .ml file exists for the module %s.\n" name

let cmt name table =
  match (find name table).cmt with
   | Some filename ->
       filename
   | None ->
       fail "No .cmt file exists for the module %s.\n" name

(* -------------------------------------------------------------------------- *)

(* [cmt_directories root table] returns the unique directories containing .cmt
   files, resolved to absolute paths using [root]. In dune's build tree, .cmi
   files live alongside .cmt files, so these directories form the project's
   OCaml load path. *)
let cmt_directories (root : filename) (table : module_table) : filename list =
  M.fold (fun _ mdesc acc ->
    match mdesc.cmt with
    | None -> acc
    | Some rel ->
        let dir = Filename.dirname (Filename.concat root rel) in
        if List.mem dir acc then acc else dir :: acc
  ) table []
