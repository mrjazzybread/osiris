(* -------------------------------------------------------------------------- *)

(* Quick-and-dirty error reporting. *)

let die _c =
  exit 1

let fail format =
  Printf.kfprintf die stderr format

(* -------------------------------------------------------------------------- *)

(* The format of a module description in the output of [dune describe]. *)

include struct

open Base

type module_description =
  { name : string
  ; impl : string option
  ; intf : string option
  ; cmt : string option
  ; cmti : string option
  }
[@@deriving of_sexp]

end

(* -------------------------------------------------------------------------- *)

(* [extract_module_descriptions e] extracts a list of module descriptions out
   of the S-expression [e], whose structure is not known. Each node is either
   recognized as a module description or recursively searched for module
   descriptions. *)

let rec extract_module_descriptions (e : Base.Sexp.t) accu =
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

(* [describe()] invokes [dune describe] in the current directory, parses its
   output, and returns a list of module descriptions. *)

let describe () =
  match IO.invoke "dune describe --lang 0.1 --format csexp" with
  | None ->
      fail "Invoking [dune describe] failed."
  | Some description ->
      let module C = Csexp.Make(Base.Sexp) in
      match C.parse_string description with
      | Error (ofs, msg) ->
          fail "Could not parse output of [dune describe]: %d: %s\n%!" ofs msg
      | Ok sexp ->
          extract_module_descriptions sexp
