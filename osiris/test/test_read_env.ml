let read_env cmt_file =
  let open Cmt_format in
  match read_cmt cmt_file with
  | { cmt_annots = Implementation _; cmt_initial_env; cmt_loadpath; _ } ->
      Load_path.init ~auto_include:Load_path.no_auto_include
        ~visible:cmt_loadpath.Load_path.visible
        ~hidden:cmt_loadpath.Load_path.hidden;
      (match Envaux.env_of_only_summary cmt_initial_env with
       | exception Envaux.Error error ->
           let buf = Buffer.create 64 in
           Envaux.report_error (Format.formatter_of_buffer buf) error;
           failwith ("env_of_only_summary: " ^ Buffer.contents buf)
       | env -> env)
  | _ -> failwith "not an implementation .cmt"

(* Look up the type of a value by longident and return it as a string. *)
let type_of env lident =
  match Env.lookup_value ~loc:Location.none lident env with
  | exception Not_found -> None
  | (_, vdesc) -> Some (Format.asprintf "%a" Printtyp.type_expr vdesc.Types.val_type)

let () = Junit.init "read_env"

let check_type env lident expected =
  let name = String.concat "." (Longident.flatten lident) in
  match type_of env lident with
  | None ->
      Junit.fail name "not found in env"
  | Some actual when actual = expected ->
      Junit.pass (Printf.sprintf "%s : %s" name actual)
  | Some actual ->
      Junit.fail name (Printf.sprintf "expected '%s' got '%s'" expected actual)

let () =
  let fixture_cmt   = Sys.argv.(1) in
  let fixture_a_cmt = Sys.argv.(2) in
  let fixture_b_cmt = Sys.argv.(3) in

  (* Fixture.cmt: stdlib is opened, so standard values are directly accessible. *)
  let env = read_env fixture_cmt in
  check_type env (Longident.Lident "succ") "int -> int";
  check_type env (Longident.Lident "not")  "bool -> bool";

  (* FixtureA.cmt: same stdlib initial env; we just check it loads. *)
  let _ = read_env fixture_a_cmt in
  Junit.pass "FixtureA: env loaded";

  (* FixtureB.cmt: type-checked against FixtureA, so FixtureA is in scope. *)
  let env_b = read_env fixture_b_cmt in
  let fixture_a = Location.mknoloc (Longident.Lident "FixtureA") in
  check_type env_b (Longident.Ldot (fixture_a, Location.mknoloc "hello")) "string";
  check_type env_b (Longident.Ldot (fixture_a, Location.mknoloc "add"))   "int -> int -> int";

  Junit.exit_with_status ()
