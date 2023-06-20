open OsirisAst
open Fresh

(* -------------------------------------------------------------------------- *)

(* This section of the OCaml file defines functions to split the term at every
   node. One function by type of node is defined.
   TODO: try to factorize the code using a single GADT to represent every part
   of the AST. *)

let rec split_all_binding _verbose _debug name binding : ast DAG.t =
  (* TODO. *)
  DAG.init (name, OBinding binding)

and split_all_rec_binding _verbose _debug name rec_binding : ast DAG.t =
  match rec_binding with
  | RecBinding (n, AnonFun (v, e)) ->
     let gname = fresh_name "split_all_rec_binding" in
     let g : ast DAG.t = DAG.init (Some gname, OExpr e) in
     let rec_binding : rec_binding =
       RecBinding (n, AnonFun (v, EDef gname)) in
     DAG.init (name, ORecBinding rec_binding)
     |> DAG.add [g]
  | RecBDef _ -> DAG.init (name, ORecBinding rec_binding)

and split_all_sitem verbose debug name sitem : ast DAG.t =
  let split_all_module = split_all_module verbose debug in
  let split_all_binding = split_all_binding verbose debug in
  let split_all_rec_binding = split_all_rec_binding verbose debug in
  match sitem with
  | ILet bindings ->
     let deps : (string * ast DAG.t) list =
       List.map
         (fun (binding: binding) ->
           let name = fresh_name "split_all_sitem" in
           name, split_all_binding (Some name) binding)
         bindings in
     let bindings = List.map (fun (s, _) -> BDef s) deps in
     DAG.init (name, OSItem (ILet bindings))
     |> DAG.add (List.map snd deps)


  | ILetRec rec_bindings ->
     let deps : (string * ast DAG.t) list =
       List.map
         (fun (rec_binding: rec_binding) ->
           let name = fresh_name "split_all_sitem" in
           name, split_all_rec_binding (Some name) rec_binding)
         rec_bindings in
     let rec_bindings = List.map (fun (s, _) -> RecBDef s) deps in
     DAG.init (name, OSItem (ILetRec rec_bindings))
     |> DAG.add (List.map snd deps)

  | IModule (n, m) ->
     let gname = fresh_name "split_all_sitem" in
     let g = split_all_module (Some gname) m in
     DAG.init (name, OSItem (IModule (n, MDef gname)))
     |> DAG.add [g]

  | CDef _ | IOpen _ | IInclude _ ->
     (* Leaves of the AST. *)
     DAG.init (name, OSItem sitem)

and split_all_module verbose debug name (m: mexpr) : ast DAG.t =
  let split_all_module = split_all_module verbose debug in
  let split_all_sitem = split_all_sitem verbose debug in
  match m with
  | MPath _ | MDef _ ->
     (* Leaves of the AST. *)
     DAG.init (name, OModule m)

  | MStruct sitems ->
     let deps : (string * ast DAG.t) list =
       List.map
         (fun (sitem: sitem) ->
           let name = fresh_name "split_all_module" in
           name, split_all_sitem (Some name) sitem)
         sitems in
     let sitems = List.map (fun (s, _) -> CDef s) deps in
     DAG.init (name, OModule (MStruct sitems))
  |> DAG.add (List.map snd deps)

  | MCoercion (m, c) ->
     let gname = fresh_name "split_all_module" in
     let g = split_all_module (Some gname) m in
     DAG.init (name, OModule (MCoercion (MDef gname, c)))
     |> DAG.add [g]

(* Main function. *)
let split_all verbose debug (ast : ast) : ast DAG.t =
  let split_all_module = split_all_module verbose debug in
  match snd ast with
  | OModule m -> split_all_module (fst ast) m
  |  _ -> DAG.init ast

(* [split_all] is shadowed by a wrapper hiding the [reset] integer. *)
let split_all verbose debug ast =
  DAG.flat_map (split_all verbose debug) ast

(* -------------------------------------------------------------------------- *)

(* Main splitting functions.
   [one_strategy] applies one splitting strategy. *)
let one_strategy verbose debug strategy ast : ast DAG.t =
  let split_all = split_all verbose debug in
  match strategy with
  | Options.Split -> split_all ast
  | Options.NoSplit -> ast

(* [split] splits an AST into a graph of ASTs. *)
let split verbose debug (splitting_strategy: Options.splitting_strategy list)
      osiris_ast: ast DAG.t =
  (* First create a first graph containing a single node: the Osiris AST
     annotated by the name of the module.*)
  let init : ast DAG.t = DAG.init osiris_ast in

  (* Then iterate over the list of strategies provided on the command line,
     each transforming the AST. *)
  List.fold_right
    (one_strategy debug verbose) splitting_strategy init
