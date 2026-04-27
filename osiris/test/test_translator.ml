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
  let record_cmt = Sys.argv.(4) in

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

  (* --- records: fields are represented by their declaration position,
         not their name. The translator must always emit field values in
         declaration order (i.e. [label_desc.lbl_pos] order), regardless
         of the order in which the fields appear in the source code. --- *)
  let record = translate record_cmt in
  check_ast "record" record
    (MStruct [
      (* { ra = 1; rb = 2; rc = 3 } — source order = declaration order. *)
      ILet [Binding (PVar "r1",
        ERecord (Immut, [EInt 1; EInt 2; EInt 3]))];
      (* { rc = 30; rb = 20; ra = 10 } — source order is reversed; the
         AST values must still appear in declaration order, so the
         literals end up as [10; 20; 30] (ra=10, rb=20, rc=30). *)
      ILet [Binding (PVar "r2",
        ERecord (Immut, [EInt 10; EInt 20; EInt 30]))];
      (* { rb = 200; rc = 300; ra = 100 } — yet another permutation;
         AST values must again be in declaration order. *)
      ILet [Binding (PVar "r3",
        ERecord (Immut, [EInt 100; EInt 200; EInt 300]))];
      (* { ma = 7; mb = 8 } where [ma] is declared mutable: the [ERecord]
         tag must be [Mut]. *)
      ILet [Binding (PVar "m1",
        ERecord (Mut, [EInt 7; EInt 8]))];
      (* let get_c r = r.rc — access uses declaration position 2. *)
      ILet [Binding (PVar "get_c",
        EAnonFun (AnonFun ("r", ERecordAccess (EPath ["r"], 2))))];
      (* let upd_bc r = { r with rc = 100; rb = 99 } — multi-field update
         with source order rc-first; the [Fexpr]s must be emitted in
         declaration-position order: rb (1) before rc (2). *)
      ILet [Binding (PVar "upd_bc",
        EAnonFun (AnonFun ("r",
          ERecordUpdate (EPath ["r"],
            [Fexpr (1, EInt 99); Fexpr (2, EInt 100)]))))];
    ]);
  let record_src = Junit.read_source record_cmt in
  let rendered_record = render record in
  (* Field positions are rendered as bare integers (not quoted names). *)
  check_contains "record" ~source:record_src rendered_record "Fexpr 1";
  check_contains "record" ~source:record_src rendered_record "Fexpr 2";
  check_contains "record" ~source:record_src rendered_record "ERecordAccess";
  check_contains "record" ~source:record_src rendered_record "ERecordUpdate";

  Junit.exit_with_status ()
