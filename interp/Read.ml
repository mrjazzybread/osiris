[@@@warning "-27"]

(* This file provides a function that, given the name of an ml file, returns a
   [Typedtree.implementation] by calling functions from [ocaml-compiler-libs]. *)

(* Reference that is used to store the typed tree *)
let ref_to_impl : Typedtree.implementation option ref = ref None


(* most of this file is code adapted from https://github.com/ocaml/ocaml *)


(* from ocaml/driver/compile_common.ml *)

open Compile_common

let typecheck_impl (i : info) parsetree =
  Typemod.type_implementation i.target i.env parsetree

let compile_common__implementation info ~backend =
  Clflags.dont_write_files := true;
  Misc.try_finally ?always:None ?exceptionally:None (fun () ->
      let structure : Parsetree.structure = parse_impl info in
      let impl : Typedtree.implementation = typecheck_impl info structure in
      ref_to_impl := Some impl;
    )


(* from ocaml/driver/compile.ml *)

let compile__implementation ~start_from ~source_file ~output_prefix : unit (* Typedtree.implementation *) =
  Compile_common.with_info
    ~native:false
    ~tool_name:"osiris-interpreter"
    ~dump_ext:"cmo"
    (Unit_info.make
      ~source_file
      Impl
      "osiris_unused_prefix"
    )
  @@ fun info ->
  compile_common__implementation info ~backend:(fun _ _ -> ())


(* from ocaml/driver/maindriver.ml *)

module Options = Main_args.Make_bytecomp_options (Main_args.Default.Main)

let main argv ppf =
  let program = "__not_a_program__" in
  Clflags.add_arguments __LOC__ Options.list;
  Clflags.add_arguments __LOC__
    ["-depend", Arg.Unit Makedepend.main_from_option,
     "<options> Compute dependencies (use 'ocamlc -depend -help' for details)"];
  match
    Compenv.readenv ppf Before_args;
    Compenv.parse_arguments (ref argv) Compenv.anonymous program;
    Compmisc.read_clflags_from_env ();
    if !Clflags.plugin then
      Compenv.fatal "-plugin is only supported up to OCaml 4.08.0";
    begin try
      Compenv.process_deferred_actions
        { log = ppf;
          compile_implementation = compile__implementation;
          compile_interface = Compile.interface;
          ocaml_mod_ext = ".cmo";
          ocaml_lib_ext = ".cma"
        }
    with Arg.Bad msg ->
      begin
        prerr_endline msg;
        Clflags.print_arguments program;
        exit 2
      end
    end
  with
  | exception (Compenv.Exit_with_status n) ->
    n
  | () ->
    Compmisc.with_ppf_dump ~file_prefix:"profile"
      (fun ppf -> Profile.print ppf !Clflags.profile_columns);
    0
  | exception x ->
  Location.report_exception ppf x;
  2

(** Calls [main] with a custom [argv] containing the filename from which we want
    to extract the [Typedtree.implementation] *)

let typedtree_of_filename (filename : string) : Typedtree.implementation =
  let my_argv = [|"<none>"; filename; "-stop-after"; "typing"|] in
  let err = main my_argv Format.err_formatter in
  if err <> 0 then exit err else
    match !ref_to_impl with
    | None -> failwith "running main failed to produce a Typedtree.implementation"
    | Some impl -> impl
