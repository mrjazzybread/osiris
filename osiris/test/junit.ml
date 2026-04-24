(* Tiny JUnit XML emitter for the translator tests.

   Each test executable records results via [pass] / [fail] / [todo] /
   [xpass]; at exit we write a JUnit XML file if [JUNIT_OUT] is set. The XML
   is consumed by GitLab CI's test reports widget.

   Status meanings:
   - Pass:  the assertion holds
   - Fail:  hard failure — counts as <failure> in the JUnit report
   - Todo:  known unfinished feature — emitted as <skipped>
   - Xpass: a TODO that unexpectedly passes — emitted as <failure>, since the
            TODO should be promoted to a real test *)

type status =
  | Pass
  | Fail of string
  | Todo of string
  | Xpass of string

type case = {
  name : string;
  status : status;
}

let cases : case list ref = ref []
let suite_name = ref "tests"

let init suite = suite_name := suite

let record name status = cases := { name; status } :: !cases

let pass name =
  record name Pass;
  Printf.printf "OK    [%s]\n%!" name

let fail name msg =
  record name (Fail msg);
  Printf.printf "FAIL  [%s] %s\n%!" name msg

let todo name msg =
  record name (Todo msg);
  Printf.printf "TODO  [%s] %s\n%!" name msg

let xpass name msg =
  record name (Xpass msg);
  Printf.printf "XPASS [%s] %s — promote to a real test\n%!" name msg

(* Best-effort read of the .ml source corresponding to a .cmt path. Used by
   check_contains to show the original OCaml expression in failure messages
   instead of the translated Rocq output. *)
let read_source cmt_file =
  let src_file = Filename.remove_extension cmt_file ^ ".ml" in
  try In_channel.with_open_text src_file In_channel.input_all
  with Sys_error _ -> Printf.sprintf "(source not found: %s)" src_file

let escape s =
  let b = Buffer.create (String.length s) in
  String.iter (function
    | '<'  -> Buffer.add_string b "&lt;"
    | '>'  -> Buffer.add_string b "&gt;"
    | '&'  -> Buffer.add_string b "&amp;"
    | '"'  -> Buffer.add_string b "&quot;"
    | '\'' -> Buffer.add_string b "&apos;"
    | c    -> Buffer.add_char b c) s;
  Buffer.contents b

let count_if p = List.length (List.filter p !cases)

let n_fail () = count_if (fun c -> match c.status with Fail _ | Xpass _ -> true | _ -> false)
let n_skip () = count_if (fun c -> match c.status with Todo _ -> true | _ -> false)
let n_pass () = List.length !cases - n_fail () - n_skip ()

let emit path =
  let cs = List.rev !cases in
  let oc = open_out path in
  Printf.fprintf oc "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
  Printf.fprintf oc "<testsuites>\n";
  Printf.fprintf oc "  <testsuite name=\"%s\" tests=\"%d\" failures=\"%d\" skipped=\"%d\">\n"
    (escape !suite_name) (List.length cs) (n_fail ()) (n_skip ());
  List.iter (fun c ->
    Printf.fprintf oc "    <testcase classname=\"%s\" name=\"%s\""
      (escape !suite_name) (escape c.name);
    match c.status with
    | Pass ->
        Printf.fprintf oc "/>\n"
    | Fail msg ->
        Printf.fprintf oc ">\n      <failure message=\"assertion failed\">%s</failure>\n    </testcase>\n"
          (escape msg)
    | Todo msg ->
        Printf.fprintf oc ">\n      <skipped message=\"TODO\">%s</skipped>\n    </testcase>\n"
          (escape msg)
    | Xpass msg ->
        Printf.fprintf oc ">\n      <failure message=\"XPASS — promote TODO to a real test\">%s</failure>\n    </testcase>\n"
          (escape msg)
  ) cs;
  Printf.fprintf oc "  </testsuite>\n</testsuites>\n";
  close_out oc

let () =
  at_exit (fun () ->
    match Sys.getenv_opt "JUNIT_OUT" with
    | None -> ()
    | Some path -> emit path)

(* Print a summary and exit non-zero if any hard failures occurred. *)
let exit_with_status () =
  Printf.printf "\nSummary [%s]: %d passed, %d todo, %d failed\n%!"
    !suite_name (n_pass ()) (n_skip ()) (n_fail ());
  if n_fail () > 0 then exit 1
