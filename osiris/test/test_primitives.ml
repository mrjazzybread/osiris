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

(* Extract a named IExternal from an MStruct. *)
let find_external name = function
  | MStruct items ->
      (match List.find_opt (function IExternal (n, _) -> n = name | _ -> false) items with
       | Some item -> MStruct [item]
       | None -> MStruct [])
  | other -> other

(* Extract the first ILet binding with the given name from an MStruct. *)
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

(* -------------------------------------------------------------------------- *)

let () =
  let primitives_cmt = Sys.argv.(1) in
  let partial_cmt    = Sys.argv.(2) in

  let prims = translate primitives_cmt in
  let part  = translate partial_cmt in

  (* ------------------------------------------------------------------ *)
  (* External declarations: arity-1 primitives                          *)
  (* ------------------------------------------------------------------ *)

  check_ast "prim: neg"
    (find_external "neg" prims)
    (MStruct [IExternal ("neg",
      EAnonFun (AnonFun ("__x0", EIntNeg (EPath ["__x0"]))))]);

  check_ast "prim: succ_"
    (find_external "succ_" prims)
    (MStruct [IExternal ("succ_",
      EAnonFun (AnonFun ("__x0", EIntAdd (EPath ["__x0"], EInt 1))))]);

  check_ast "prim: pred_"
    (find_external "pred_" prims)
    (MStruct [IExternal ("pred_",
      EAnonFun (AnonFun ("__x0", EIntSub (EPath ["__x0"], EInt 1))))]);

  check_ast "prim: not_"
    (find_external "not_" prims)
    (MStruct [IExternal ("not_",
      EAnonFun (AnonFun ("__x0", EBoolNeg (EPath ["__x0"]))))]);

  check_ast "prim: arr_len"
    (find_external "arr_len" prims)
    (MStruct [IExternal ("arr_len",
      EAnonFun (AnonFun ("__x0", EArrayLength (EPath ["__x0"]))))]);

  (* ------------------------------------------------------------------ *)
  (* External declarations: arity-2 primitives                          *)
  (* ------------------------------------------------------------------ *)

  check_ast "prim: add"
    (find_external "add" prims)
    (MStruct [IExternal ("add",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntAdd (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: sub"
    (find_external "sub" prims)
    (MStruct [IExternal ("sub",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntSub (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: mul"
    (find_external "mul" prims)
    (MStruct [IExternal ("mul",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntMul (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: div_"
    (find_external "div_" prims)
    (MStruct [IExternal ("div_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntDiv (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: mod_"
    (find_external "mod_" prims)
    (MStruct [IExternal ("mod_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntMod (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: land_"
    (find_external "land_" prims)
    (MStruct [IExternal ("land_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntLand (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: lor_"
    (find_external "lor_" prims)
    (MStruct [IExternal ("lor_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntLor (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: lxor_"
    (find_external "lxor_" prims)
    (MStruct [IExternal ("lxor_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntLxor (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: lsl_"
    (find_external "lsl_" prims)
    (MStruct [IExternal ("lsl_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntLsl (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: lsr_"
    (find_external "lsr_" prims)
    (MStruct [IExternal ("lsr_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntLsr (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: asr_"
    (find_external "asr_" prims)
    (MStruct [IExternal ("asr_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EIntAsr (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: eq_"
    (find_external "eq_" prims)
    (MStruct [IExternal ("eq_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpEq (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: ne_"
    (find_external "ne_" prims)
    (MStruct [IExternal ("ne_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpNe (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: lt_"
    (find_external "lt_" prims)
    (MStruct [IExternal ("lt_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpLt (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: gt_"
    (find_external "gt_" prims)
    (MStruct [IExternal ("gt_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpGt (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: le_"
    (find_external "le_" prims)
    (MStruct [IExternal ("le_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpLe (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: ge_"
    (find_external "ge_" prims)
    (MStruct [IExternal ("ge_",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpGe (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: phys_eq"
    (find_external "phys_eq" prims)
    (MStruct [IExternal ("phys_eq",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EOpPhysEq (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: arr_get"
    (find_external "arr_get" prims)
    (MStruct [IExternal ("arr_get",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EArrayGet (EPath ["__x0"], EPath ["__x1"]))))))]);

  check_ast "prim: arr_make"
    (find_external "arr_make" prims)
    (MStruct [IExternal ("arr_make",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EArrayMake (EPath ["__x0"], EPath ["__x1"]))))))]);

  (* ------------------------------------------------------------------ *)
  (* External declarations: arity-3 primitives                          *)
  (* ------------------------------------------------------------------ *)

  check_ast "prim: arr_set"
    (find_external "arr_set" prims)
    (MStruct [IExternal ("arr_set",
      EAnonFun (AnonFun ("__x0",
        EAnonFun (AnonFun ("__x1",
          EAnonFun (AnonFun ("__x2",
            EArraySet (EPath ["__x0"], EPath ["__x1"], EPath ["__x2"]))))))))]);

  (* ------------------------------------------------------------------ *)
  (* Call sites: full applications inline the primitive                 *)
  (* ------------------------------------------------------------------ *)

  (* let sum a b = a + b  →  EIntAdd (EPath ["a"], EPath ["b"]) *)
  check_ast "call: sum"
    (find_let "sum" part)
    (MStruct [ILet [Binding (PVar "sum",
      EAnonFun (AnonFun ("a",
        EAnonFun (AnonFun ("b",
          EIntAdd (EPath ["a"], EPath ["b"]))))))]]);

  (* let is_lt a b = a < b  →  EOpLt *)
  check_ast "call: is_lt"
    (find_let "is_lt" part)
    (MStruct [ILet [Binding (PVar "is_lt",
      EAnonFun (AnonFun ("a",
        EAnonFun (AnonFun ("b",
          EOpLt (EPath ["a"], EPath ["b"]))))))]]);

  (* let get arr i = Array.get arr i  →  EArrayGet *)
  check_ast "call: get"
    (find_let "get" part)
    (MStruct [ILet [Binding (PVar "get",
      EAnonFun (AnonFun ("arr",
        EAnonFun (AnonFun ("i",
          EArrayGet (EPath ["arr"], EPath ["i"]))))))]]);

  (* let set arr i v = Array.set arr i v  →  EArraySet *)
  check_ast "call: set"
    (find_let "set" part)
    (MStruct [ILet [Binding (PVar "set",
      EAnonFun (AnonFun ("arr",
        EAnonFun (AnonFun ("i",
          EAnonFun (AnonFun ("v",
            EArraySet (EPath ["arr"], EPath ["i"], EPath ["v"]))))))))]]);

  (* ------------------------------------------------------------------ *)
  (* Call sites: partial applications fall back to EApp                 *)
  (* ------------------------------------------------------------------ *)

  (* let add5 = (+) 5  →  EApp (EPath ["+"], EInt 5) *)
  check_ast "partial: add5"
    (find_let "add5" part)
    (MStruct [ILet [Binding (PVar "add5",
      EApp (EPath ["+"], EInt 5))]]);

  (* let lt0 = (<) 0  →  EApp (EPath ["<"], EInt 0) *)
  check_ast "partial: lt0"
    (find_let "lt0" part)
    (MStruct [ILet [Binding (PVar "lt0",
      EApp (EPath ["<"], EInt 0))]]);

  (* let get_at arr = Array.get arr  →  EApp (EPath ["Array"; "get"], EPath ["arr"]) *)
  check_ast "partial: get_at"
    (find_let "get_at" part)
    (MStruct [ILet [Binding (PVar "get_at",
      EAnonFun (AnonFun ("arr",
        EApp (EPath ["Array"; "get"], EPath ["arr"]))))]]);

  if !pass then print_string "All tests passed.\n"
  else (print_string "Some tests failed.\n"; exit 1)
