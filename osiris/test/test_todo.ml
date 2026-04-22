open Syntax

module T = Translate.Make(struct
  let warnings = false
  let debug fmt = Printf.ifprintf stdout fmt
end)

(* -------------------------------------------------------------------------- *)

let pass = ref true

let check_ast label actual expected =
  if actual = expected then
    Printf.printf "OK   [%s]\n%!" label
  else begin
    Printf.printf "FAIL [%s]\n  expected: %s\n  got:      %s\n%!"
      label (show_mexpr expected) (show_mexpr actual);
    pass := false
  end

let find_let name = function
  | MStruct items ->
      let rec loop = function
        | [] -> MStruct []
        | ILet bs :: rest ->
            (match List.find_opt (function Binding (PVar n, _) -> n = name | _ -> false) bs with
             | Some b -> MStruct [ILet [b]]
             | None -> loop rest)
        | _ :: rest -> loop rest
      in
      loop items
  | other -> other

(* Like [check_ast] and [check_contains], but for features not yet implemented.
   A mismatch prints TODO and is not a failure; an unexpected match prints XPASS
   and is a failure (the feature was implemented — promote to a real test). *)

let check_ast_todo label actual expected =
  if actual = expected then begin
    Printf.printf "XPASS [%s] — was TODO, now passes; promote to a real test\n%!" label;
    pass := false
  end else
    Printf.printf "TODO  [%s]\n%!" label

let check_contains_todo label haystack needle =
  if let n = String.length needle and h = String.length haystack in
     n <= h && let rec loop i = i <= h - n &&
       (String.sub haystack i n = needle || loop (i + 1))
     in loop 0
  then begin
    Printf.printf "XPASS [%s contains %S] — was TODO, now passes; promote to a real test\n%!" label needle;
    pass := false
  end else
    Printf.printf "TODO  [%s contains %S]\n%!" label needle

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
  let labeled_cmt   = Sys.argv.(1) in
  let downto_cmt    = Sys.argv.(2) in
  let opaque_cmt    = Sys.argv.(3) in
  let shallow_cmt   = Sys.argv.(4) in
  let pointfree_cmt = Sys.argv.(5) in

  (* --- Labeled arguments ---
     let add ~x ~y = x + y
     Labels should be erased; the result is two nested plain AnonFuns. *)
  let labeled_ast = translate labeled_cmt in
  check_ast_todo "labeled: add body"
    (match labeled_ast with
     | MStruct (ILet [Binding (PVar "add", b)] :: _) -> MStruct [ILet [Binding (PVar "add", b)]]
     | _ -> labeled_ast)
    (MStruct [ILet [Binding (PVar "add",
      EAnonFun (AnonFun ("x",
        EAnonFun (AnonFun ("y",
          EIntAdd (EPath ["x"], EPath ["y"])))))
    )]]);

  (* --- Downto for loop ---
     for i = n downto 1 do ... done should produce an EFor.
     (The direction flag or desugaring is TBD; this test just checks
     that some form of EFor appears rather than EUnsupported.) *)
  let downto_ast  = translate downto_cmt in
  let downto_text = render downto_ast in
  check_contains_todo "downto: EFor" downto_text "EFor";

  (* --- %opaque externals ---
     external unsafe_of_array : 'a array -> 'a iarray = "%opaque"
       should become IExternal ("unsafe_of_array", fun __x0 -> EFreeze __x0)
     external unsafe_to_array : 'a iarray -> 'a array = "%opaque"
       should become IExternal ("unsafe_to_array", fun __x0 -> EUnfreeze __x0)
     The EUnfreeze case currently fails: %opaque always maps to EFreeze. *)
  let opaque_ast = translate opaque_cmt in
  let find_external name = function
    | MStruct items ->
        (match List.find_opt (function IExternal (n, _) -> n = name | _ -> false) items with
         | Some item -> MStruct [item]
         | None -> MStruct [])
    | other -> other
  in
  check_ast "opaque: unsafe_of_array -> EFreeze"
    (find_external "unsafe_of_array" opaque_ast)
    (MStruct [IExternal ("unsafe_of_array",
      EAnonFun (AnonFun ("__x0", EFreeze (EPath ["__x0"]))))]);
  check_ast_todo "opaque: unsafe_to_array -> EUnfreeze"
    (find_external "unsafe_to_array" opaque_ast)
    (MStruct [IExternal ("unsafe_to_array",
      EAnonFun (AnonFun ("__x0", EUnfreeze (EPath ["__x0"]))))]);

  (* --- Shallow effect handlers ---
     open Effect.Shallow makes `match f () with | effect E, k -> ...` a shallow
     handler; the expected translation is EShallowMatch rather than EMatch.
     Currently the translator always produces EMatch regardless. *)
  let shallow_ast  = translate shallow_cmt in
  let shallow_text = render shallow_ast in
  check_contains_todo "shallow: EShallowMatch" shallow_text "EShallowMatch";

  (* --- Point-free and partial continue / discontinue ---
     When fully applied at the call site, EContinue/EDiscontinue fire correctly.
     When used point-free or partially applied, the translator falls back to
     EPath ["continue"] / EApp (EPath ["continue"], k), which has nothing to
     resolve to in Rocq because the IExternal for continue uses the unrecognised
     primitive "caml_continuation_use_and_update_handler_noexc".
     The fix is to eta-expand: point-free `continue` becomes
       EAnonFun (AnonFun ("k", EAnonFun (AnonFun ("v", EContinue (EPath ["k"], EPath ["v"])))))
     and partial `continue k` becomes
       EAnonFun (AnonFun ("v", EContinue (EPath ["k"], EPath ["v"]))). *)
  let pf_ast = translate pointfree_cmt in

  (* Baseline: fully applied — these already work *)
  check_ast "pointfree: resume_42 body"
    (find_let "resume_42" pf_ast)
    (MStruct [ILet [Binding (PVar "resume_42",
      EAnonFun (AnonFun ("k",
        EContinue (EPath ["k"], EInt 42))))]]);

  check_ast "pointfree: dismiss_exn body"
    (find_let "dismiss_exn" pf_ast)
    (MStruct [ILet [Binding (PVar "dismiss_exn",
      EAnonFun (AnonFun ("k",
        EDiscontinue (EPath ["k"], EXData (["Exit"], [])))))]]);

  (* Partial application — should eta-expand the missing argument *)
  let resume_text  = render (find_let "resume"  pf_ast) in
  let dismiss_text = render (find_let "dismiss" pf_ast) in
  check_contains_todo "partial: resume -> EContinue"     resume_text  "EContinue";
  check_contains_todo "partial: dismiss -> EDiscontinue" dismiss_text "EDiscontinue";

  (* Point-free — should eta-expand both arguments *)
  let mc_text = render (find_let "my_continue"    pf_ast) in
  let md_text = render (find_let "my_discontinue" pf_ast) in
  check_contains_todo "pointfree: my_continue -> EContinue"       mc_text "EContinue";
  check_contains_todo "pointfree: my_discontinue -> EDiscontinue" md_text "EDiscontinue";

  (* --- (!) deref ---
     (!) uses %field0 which is intentionally absent from translate_primitive_expr,
     so its IExternal is EUnsupported; point-free (!) produces EPath ["!"] which
     has nothing to resolve to. Expected: EAnonFun (AnonFun ("r", ELoad (EPath ["r"]))). *)
  check_ast "pointfree: deref body"
    (find_let "deref" pf_ast)
    (MStruct [ILet [Binding (PVar "deref",
      EAnonFun (AnonFun ("r", ELoad (EPath ["r"]))))]]);
  let deref_text = render (find_let "my_deref" pf_ast) in
  check_contains_todo "pointfree: my_deref -> ELoad" deref_text "ELoad";

  (* --- Atomic operations ---
     In OCaml 5.4, Atomic.get and Atomic.exchange are no longer declared as
     primitives, so they are not recognised by translate_primitive_application.
     They are also absent from translate_stdlib_application, so even full
     application falls back to EApp.  Atomic.compare_and_set is handled in
     translate_stdlib_application and therefore does work.
     For get/exchange, both full-application and point-free are TODO. *)

  (* Baseline: atomic_cas is in translate_stdlib_application *)
  check_ast "pointfree: atomic_cas body"
    (find_let "atomic_cas" pf_ast)
    (MStruct [ILet [Binding (PVar "atomic_cas",
      EAnonFun (AnonFun ("r",
        EAnonFun (AnonFun ("x",
          EAnonFun (AnonFun ("y",
            ECAS (EPath ["r"], EPath ["x"], EPath ["y"]))))))))]]);

  (* atomic_load and atomic_xchg: even full application is unhandled *)
  check_ast "pointfree: atomic_load body"
    (find_let "atomic_load" pf_ast)
    (MStruct [ILet [Binding (PVar "atomic_load",
      EAnonFun (AnonFun ("r", ELoad (EPath ["r"]))))]]);
  check_ast "pointfree: atomic_xchg body"
    (find_let "atomic_xchg" pf_ast)
    (MStruct [ILet [Binding (PVar "atomic_xchg",
      EAnonFun (AnonFun ("r",
        EAnonFun (AnonFun ("v",
          EExchange (EPath ["r"], EPath ["v"]))))))]]);

  (* Partial applications *)
  let xchg1_text = render (find_let "atomic_xchg1" pf_ast) in
  let cas1_text  = render (find_let "atomic_cas1"  pf_ast) in
  let cas2_text  = render (find_let "atomic_cas2"  pf_ast) in
  check_contains_todo "partial: atomic_xchg1 -> EExchange" xchg1_text "EExchange";
  check_contains_todo "partial: atomic_cas1 -> ECAS"       cas1_text  "ECAS";
  check_contains_todo "partial: atomic_cas2 -> ECAS"       cas2_text  "ECAS";

  (* Point-free *)
  let mal_text  = render (find_let "my_atomic_load"   pf_ast) in
  let mxchg_text = render (find_let "my_atomic_xchg"  pf_ast) in
  let mcas_text  = render (find_let "my_atomic_cas"   pf_ast) in
  check_contains_todo "pointfree: my_atomic_load -> ELoad"     mal_text   "ELoad";
  check_contains_todo "pointfree: my_atomic_xchg -> EExchange" mxchg_text "EExchange";
  check_contains_todo "pointfree: my_atomic_cas -> ECAS"       mcas_text  "ECAS";

  if !pass then print_string "All tests passed.\n"
  else (print_string "Some tests failed.\n"; exit 1)
