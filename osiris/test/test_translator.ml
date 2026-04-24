open Syntax

(* Instantiate the translator with a silent settings module. *)
module T = Translate.Make(struct
  let warnings = false
  let debug fmt = Printf.ifprintf stdout fmt
end)

(* -------------------------------------------------------------------------- *)

let () = Junit.init "translator"

let check_ast label actual expected =
  if actual = expected then Junit.pass label
  else
    Junit.fail label
      (Printf.sprintf "expected: %s\ngot:      %s"
         (show_mexpr expected) (show_mexpr actual))

let check_contains ?source label haystack needle =
  let n = String.length needle and h = String.length haystack in
  let found =
    n <= h && let rec loop i =
      i <= h - n && (String.sub haystack i n = needle || loop (i + 1))
    in loop 0
  in
  let name = Printf.sprintf "%s contains %S" label needle in
  if found then Junit.pass name
  else
    let context = match source with Some s -> s | None -> haystack in
    Junit.fail name (Printf.sprintf "%S not found in:\n%s" needle context)

(* -------------------------------------------------------------------------- *)

(* Read a .cmt file and reconstruct the typing environment. *)
let read_cmt cmt_file =
  let open Cmt_format in
  match read_cmt cmt_file with
  | { cmt_annots = Implementation t; cmt_initial_env; cmt_loadpath; _ } ->
      Load_path.init ~auto_include:Load_path.no_auto_include
        ~visible:cmt_loadpath.Load_path.visible
        ~hidden:cmt_loadpath.Load_path.hidden;
      (match Envaux.env_of_only_summary cmt_initial_env with
       | exception Envaux.Error error ->
           let buf = Buffer.create 64 in
           Envaux.report_error (Format.formatter_of_buffer buf) error;
           failwith ("env_of_only_summary: " ^ Buffer.contents buf)
       | env -> (t, env))
  | _ -> failwith "not an implementation .cmt"

(* Translate a .cmt file to a Syntax.mexpr (no decoration). *)
let translate cmt_file =
  let (typedtree, _env) = read_cmt cmt_file in
  T.unit None typedtree

(* Render a translated module to Rocq text (no preamble). *)
let render mexpr =
  let rhs = Rocqify.module_expression mexpr in
  let def = Rocq.{ lhs = "__main"; rhs } in
  let defs = Cut.cut def in
  let buf = Buffer.create 256 in
  PPrint.ToBuffer.pretty 1.0 80 buf (Print.defs defs);
  Buffer.contents buf

(* -------------------------------------------------------------------------- *)

let () =
  let simple_cmt = Sys.argv.(1) in
  let arith_cmt  = Sys.argv.(2) in
  let pair_cmt   = Sys.argv.(3) in

  (* --- let x = 42 --- *)
  let simple = translate simple_cmt in
  check_ast "simple" simple
    (MStruct [ILet [Binding (PVar "x", EInt 42)]]);
  let rendered = render simple in
  let simple_src = Junit.read_source simple_cmt in
  check_contains "simple" ~source:simple_src rendered "Definition __main";
  check_contains "simple" ~source:simple_src rendered "EInt 42";
  check_contains "simple" ~source:simple_src rendered {|PVar "x"|};

  (* --- let f x = x + 1 --- *)
  let arith = translate arith_cmt in
  check_ast "arith" arith
    (MStruct [ILet [
      Binding (PVar "f",
        EAnonFun (AnonFun ("x", EIntAdd (EPath ["x"], EInt 1))))]]);

  (* --- let p = (1, 2) --- *)
  let pair = translate pair_cmt in
  check_ast "pair" pair
    (MStruct [ILet [Binding (PVar "p", ETuple [EInt 1; EInt 2])]]);

  Junit.exit_with_status ()
