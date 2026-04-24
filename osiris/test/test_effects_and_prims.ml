open Syntax

module T = Translate.Make(struct
  let warnings = false
  let debug fmt = Printf.ifprintf stdout fmt
end)

(* -------------------------------------------------------------------------- *)

let () = Junit.init "effects_and_prims"

let check_ast label actual expected =
  if actual = expected then Junit.pass label
  else
    Junit.fail label
      (Printf.sprintf "expected: %s\ngot:      %s"
         (show_mexpr expected) (show_mexpr actual))

let check_contains label haystack needle =
  let n = String.length needle and h = String.length haystack in
  let found =
    n <= h && let rec loop i =
      i <= h - n && (String.sub haystack i n = needle || loop (i + 1))
    in loop 0
  in
  if found then Junit.pass (Printf.sprintf "%s contains %S" label needle)
  else
    Junit.fail (Printf.sprintf "%s contains %S" label needle)
      (Printf.sprintf "%S not found in:\n%s" needle haystack)

(* -------------------------------------------------------------------------- *)

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

let translate cmt_file =
  let (typedtree, _env) = read_cmt cmt_file in
  T.unit None typedtree

let render mexpr =
  let rhs = Rocqify.module_expression mexpr in
  let def = Rocq.{ lhs = "__main"; rhs } in
  let defs = Cut.cut def in
  let buf = Buffer.create 256 in
  PPrint.ToBuffer.pretty 1.0 80 buf (Print.defs defs);
  Buffer.contents buf

(* -------------------------------------------------------------------------- *)

let () =
  let raise_cmt  = Sys.argv.(1) in
  let effect_cmt = Sys.argv.(2) in
  let refs_cmt   = Sys.argv.(3) in

  (* --- Exceptions: raise and match-with-exception --- *)

  (* let fail () = raise Exit
     The function body is a match on unit; the branch raises Exit.
     Exit is an extensible constructor, so it becomes EXData ["Exit"] []. *)
  let raise_ast = translate raise_cmt in
  check_ast "raise: fail body"
    (match raise_ast with
     | MStruct (ILet [Binding (PVar "fail", b)] :: _) -> MStruct [ILet [Binding (PVar "fail", b)]]
     | _ -> raise_ast)
    (MStruct [ILet [Binding (PVar "fail",
      EAnonFun (AnonFunction [
        Branch (CVal (PData ("()", [])),
          ERaise (EXData (["Exit"], [])))
      ])
    )]]);

  (* catch uses match-with-exception, which produces CExc branches *)
  let raise_text = render raise_ast in
  check_contains "raise: ERaise"   raise_text "ERaise";
  check_contains "raise: CExc"     raise_text "CExc";
  check_contains "raise: PXData"   raise_text {|PXData [ "Exit" ]|};

  (* --- Effects: perform, effect pattern, continue --- *)

  let effect_ast = translate effect_cmt in
  let effect_text = render effect_ast in

  (* IExtend marks the effect constructor declaration *)
  check_contains "effect: IExtend Ask"  effect_text {|IExtend [|};
  (* ask () = perform Ask *)
  check_contains "effect: EPerform"     effect_text "EPerform";
  (* run handler: effect Ask, k -> continue k 42 *)
  check_contains "effect: CEff"         effect_text "CEff";
  check_contains "effect: EContinue"    effect_text "EContinue";
  check_contains "effect: continue val" effect_text "EInt 42";

  (* --- References and while loops --- *)

  (* let incr r = r := !r + 1
     := -> EStore, ! -> ELoad, + -> EIntAdd *)
  let refs_ast  = translate refs_cmt in
  check_ast "refs: incr body"
    (match refs_ast with
     | MStruct (ILet [Binding (PVar "incr", b)] :: _) -> MStruct [ILet [Binding (PVar "incr", b)]]
     | _ -> refs_ast)
    (MStruct [ILet [Binding (PVar "incr",
      EAnonFun (AnonFun ("r",
        EStore (EPath ["r"],
          EIntAdd (ELoad (EPath ["r"]), EInt 1))))
    )]]);

  (* count uses ref, while, load, store *)
  let refs_text = render refs_ast in
  check_contains "refs: ERef"   refs_text "ERef";
  check_contains "refs: ELoad"  refs_text "ELoad";
  check_contains "refs: EStore" refs_text "EStore";
  check_contains "refs: EWhile" refs_text "EWhile";

  Junit.exit_with_status ()
