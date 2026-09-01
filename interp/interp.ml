open Printf

(* Extracted modules *)
open Extracted.Syntax
open Extracted.Run

(* OCaml's stdlib; shadows some extracted modules such as List and String *)
open Stdlib


(* Parsing commandline arguments *)

let noorder = ref false
let debug = ref false
let detcheck = ref false
let random = ref false
let show_ast = ref false
let verbose = ref false
let warnings = ref true

let filename = ref None

let usage_msg = sprintf "Usage: %s <options> <file.ml>" Sys.argv.(0)

let () =
  let open Arg in
  parse
    (align [
        "--noorder", Set noorder, " Evaluation order is less constrained, typically used with --random or --detcheck (default: compiler evaluation order)";
        "--debug", Set debug, " (passed to Osiris translator)";
        "--detcheck", Set detcheck, " Determinism check: do no print, but compare output traces, prints the first difference found";
        "--no-warnings", Clear warnings, " Disable warnings (default: enabled)";
        "--show-ast", Set show_ast, " Show AST of typed tree (default: disabled)";
        "--random", Unit (fun () -> random := true; Random.self_init ()), " When faced with a choice during evaluation, choose a random branch (default: choose the first option)";
        "--verbose", Set verbose, " Displays intermediate evaluation steps";
        "--warnings", Set warnings, " Enable warnings (default: enabled)"])
    (fun anon ->
       if !filename <> None || not (Filename.check_suffix anon "ml") then
         raise (Arg.Bad ("Error at argument: " ^ anon));
       filename := Some anon)
    usage_msg;
  if !random && !detcheck then
    fprintf stderr "Warning: option --random unused if --detcheck is set.\n%!"

let filename =
  match !filename with
  | Some s -> s
  | None -> fprintf stderr "%s\n%!" usage_msg; exit 0

(* Use Osiris's [Translate] module with a dummy [Settings] module *)
module Translate =
  Translatorlib.Translate.Make(struct
    let warnings = !warnings
    let debug format = (if !debug then fprintf else ifprintf) stderr format
  end)


(** Handling the special I/O effect allocated at [io_loc] *)

type 'a iostep =
  | StepIn_int of (int -> 'a)
  | StepIn_str of (string -> 'a)
  | StepOut of string * 'a

(** Interpret interactively an [iostep] by actually printing to standard output
    or reading from standard input *)
let interactive_io (s : 'a iostep) : 'a =
  match s with
  | StepIn_int f -> f (read_int ())
  | StepIn_str f -> f (read_line ())
  | StepOut (o, a) -> printf "%s%!" o; a

(** Convert argument list [args] (e.g. [["print_int"; 3]] or [["read_int"; ()]])
    passed to the I/O effect into a ['a iostep], through a continuation [k]
    taking the returned value as argument (respectively [VUnit] for [print_int],
    or say [Vint 4] for [read_int]) *)
let iostep_from_args (args : coq_val list) (k : coq_val -> 'a) : 'a iostep =
  let err =
    Failure
      (sprintf "I/O error with argument list [%s]"
         (String.concat ";" List.(map E2O.string (map string_of_val args)))) in
  let name, arg =
    match [@warning "-4"] args with
    | [VString name; arg] -> E2O.string name, arg
    | _ -> raise err in
  let unit = VData (O2E.string "()", []) in
  match [@warning "-4"] name, arg with
  | "print_int", VInt n -> StepOut (string_of_int (E2O.z n), k unit)
  | "print_string", VString s -> StepOut (E2O.string s, k unit)
  | "print_endline", VString s -> StepOut (E2O.string s ^ "\n", k unit)
  | "print_newline", u when u = unit -> StepOut ("\n", k unit)
  | "read_int", u when u = unit -> StepIn_int (fun n -> k (VInt (O2E.z n)))
  | "read_line", u when u = unit -> StepIn_str (fun s -> k (VString (O2E.string s)))
  | _ -> raise err

(* Some stepping functions below take a stepping function [step], taking a
   [config] and returning a [step_result] *)

(** Stepping function that detects special I/O effects, those at location
    [io_loc], out of the results of the [step] function. Returns an [iostep]
    tagged with [`IO] or the normal output of [step], tagged with [`Silent]. *)
let io_step step cfg =
  match step cfg with
  | Step l -> `Silent (Step l)
  | Final f ->
    match f with
    | FRet _ | FCrash | FThrow _ | FConcurrent | FStuck -> `Silent (Final f)
    | FPerform (eff, k) ->
      match [@warning "-4"] eff with
      | VXData(loc, args) when loc = io_loc ->
        `IO (iostep_from_args args (fun v -> (fst cfg, k (O2Ret v))))
      | _ -> `Silent (Final f)

(** Stepping function that forbids reads and discards final states, used for
    collecting outputs. Returns a list of configuration tagged with [`Silent],
    or a pair of the output string and the continuation configuration, tagged
    with [`Output]. *)
let output_step step cfg =
  match io_step step cfg with
  | `Silent (Step l) -> `Silent l
  | `Silent (Final _) -> `Silent []
  | `IO io ->
    match io with
    | StepOut (s, cfg) -> `Output (s, cfg)
    | StepIn_int _ | StepIn_str _ -> failwith "determinism check forbids reads"

(** [determinism_check step cfg] checks that all output traces that [cfg] can
    generate are all the same, in which case [None] is returned. Otherwise,
    [Some (trace, o1, o2)] is returned where [trace] is a common prefix and [o1]
    and [o2] is the first difference. *)

(* It does so by calling [det_check_silence], that evaluates configurations in
   the list [active] until one performs an output event [o], in which case its
   continuation becomes [paused], and the other configurations become [active]
   and [det_check_output] checks that they all also output [o], it which case it
   calls [det_check_silence] again. If a configuration outputs something else,
   evaluation stops and the difference is returned. *)

let rec det_check_silence step trace active =
  match active with
  | [] -> None
  | cfg :: active ->
    match output_step step cfg with
    | `Silent cfgs -> det_check_silence step trace (cfgs @ active)
    | `Output (o, cfg) -> det_check_output step (o :: trace) o [cfg] active
and det_check_output step trace output paused active =
  match active with
  | [] -> det_check_silence step trace paused
  | cfg :: active ->
    match output_step step cfg with
    | `Silent cfgs -> det_check_output step trace output paused (cfgs @ active)
    | `Output (o, cfg') ->
      if o <> output then
        Some (List.rev trace, output, o)
      else
        det_check_output step trace output (cfg' :: paused) active

let determinism_check step cfg = det_check_silence step [] [cfg]


(** Interactive run *)

let interactive_run step cfg =
  (* How to choose which branch when encountering a non-confluent step *)
  let choose =
    if !random then
      fun l -> List.(nth l (Random.int (length l)))
    else
      List.hd
  in

  (* Collect some stats *)
  let steps = ref 0 in
  let choices = ref 0 in

  let t = Sys.time () in
  let print_info (store, micro) =
    printf "Stats: %d steps, %d choices in branching, %f seconds elapsed\n"
      !steps
      !choices
      (Sys.time () -. t);
    printf "Store: %s\n" (E2O.string (string_of_store store));
    printf "Micro: %s\n" (E2O.string (string_of_microvx micro))
  in

  (* Run io step function until termination *)
  let rec run cfg =
    incr steps;
    if !verbose then
      printf "Step: %s\n%!" (E2O.string (string_of_microvx (snd cfg)));
    match io_step step cfg with
    | `IO io -> run (interactive_io io)
    | `Silent r ->
      match r with
      | Final (FRet _) -> cfg
      | Final FCrash -> fprintf stderr "Crash\n%!"; exit 1
      | Final (FThrow _) -> fprintf stderr "Unhandled exception\n%!"; exit 1
      | Final (FPerform (_, _)) -> fprintf stderr "Unhandled effect\n%!"; exit 1
      | Final FConcurrent -> fprintf stderr "Unsupported concurrent operation\n%!"; exit 1
      | Final FStuck -> fprintf stderr "Stuck prophecy resolution\n%!"; exit 1
      | Step l ->
        match l with
        | [] -> failwith "Step []"
        | [cfg'] -> run cfg'
        | _ :: _ :: _ -> incr choices; run (choose l)
  in
  let cfg = run cfg in
  if !verbose then (print_newline(); print_info cfg)


let () =
  (* Parse file passed as first argument as an OCaml typedtree *)
  let typedtree = Read.typedtree_of_filename filename in

  (* Translate it into an osiris AST, then into extracted syntax *)
  let mexpr : Translatorlib.Syntax.mexpr =
    Translate.unit (Some filename) typedtree.structure in
  if !show_ast then
    fprintf stdout "Typed tree:\n%s\n\n" (Translatorlib.Syntax.show_mexpr mexpr);
  let mexpr : Extracted.Syntax.mexpr = O2E.mexpr mexpr in

  flush_all ();

  (* Choose evaluation options between "usual" and "liberal" *)
  let strat =
    Extracted.Strategy.(
      if !noorder then
        (module LiberalStrategy : Strategy)
      else
        (module UsualStrategy : Strategy))
  in

  let module R = Extracted.Run.RunF(val strat) in
  let module E = Extracted.Eval.EvalF(val strat) in

  (* Make [mexpr] into a configuration (store, micro) *)
  let env = io_env @ effect_stdlib_env in
  let store = io_store in
  let config = (store, E.eval_mexpr env mexpr) in

  if !detcheck then
    match determinism_check R.step config with
    | Some (history, out1, out2) ->
      printf "Different outputs detected: '%s' vs '%s'\n" out1 out2;
      printf "common output prefix: [%s]\n%!" (String.concat "; " history)
    | None -> printf "Detected no non-deterministic behavior.\n%!"
  else
    interactive_run R.step config
