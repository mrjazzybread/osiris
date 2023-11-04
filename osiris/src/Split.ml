open Syntax
open Fresh

(* -------------------------------------------------------------------------- *)

(* This section of the OCaml file defines functions to split the term at every
   node. One function by type of node is defined.
   TODO: try to factorize the code using a single GADT to represent every part
   of the AST. *)

let rec split_all_binding name binding : def DAG.t =
  (* TODO. *)
  DAG.init { lhs = name; rhs = OBinding binding }

and split_all_rec_binding name rec_binding : def DAG.t =
  match rec_binding with
  | RecBinding (n, AnonFun (v, e)) ->
     let gname = fresh_name "split_all_rec_binding" in
     let g : def DAG.t = DAG.init { lhs = gname; rhs = OExpr e } in
     let rec_binding : rec_binding =
       RecBinding (n, AnonFun (v, ELink gname)) in
     DAG.init { lhs = name; rhs = ORecBinding rec_binding }
     |> DAG.add [g]
  | RecBLink _ ->
      DAG.init { lhs = name; rhs = ORecBinding rec_binding }

and split_all_sitem name sitem : def DAG.t =
  match sitem with
  | ILet bindings ->
     let deps : (string * def DAG.t) list =
       List.map
         (fun (binding: binding) ->
           let name = fresh_name "split_all_sitem" in
           name, split_all_binding name binding)
         bindings in
     let bindings = List.map (fun (s, _) -> BLink s) deps in
     DAG.init { lhs = name; rhs = OSItem (ILet bindings) }
     |> DAG.add (List.map snd deps)


  | ILetRec rec_bindings ->
     let deps : (string * def DAG.t) list =
       List.map
         (fun (rec_binding: rec_binding) ->
           let name = fresh_name "split_all_sitem" in
           name, split_all_rec_binding name rec_binding)
         rec_bindings in
     let rec_bindings = List.map (fun (s, _) -> RecBLink s) deps in
     DAG.init { lhs = name; rhs = OSItem (ILetRec rec_bindings) }
     |> DAG.add (List.map snd deps)

  | IModule (n, m) ->
     let gname = fresh_name "split_all_sitem" in
     let g = split_all_module gname m in
     DAG.init { lhs = name; rhs = OSItem (IModule (n, MLink gname)) }
     |> DAG.add [g]

  | ILink _ | IOpen _ | IInclude _ ->
     (* Leaves of the AST. *)
     DAG.init { lhs = name; rhs = OSItem sitem }

and split_all_module name (m: mexpr) : def DAG.t =
  match m with
  | MPath _ | MLink _ ->
     (* Leaves of the AST. *)
     DAG.init { lhs = name; rhs = OModule m }

  | MStruct sitems ->
     let deps : (string * def DAG.t) list =
       List.map
         (fun (sitem: sitem) ->
           let name = fresh_name "split_all_module" in
           name, split_all_sitem name sitem)
         sitems in
     let sitems = List.map (fun (s, _) -> ILink s) deps in
     DAG.init { lhs = name; rhs = OModule (MStruct sitems) }
  |> DAG.add (List.map snd deps)

  | MCoercion (m, c) ->
     let gname = fresh_name "split_all_module" in
     let g = split_all_module gname m in
     DAG.init { lhs = name; rhs = OModule (MCoercion (MLink gname, c)) }
     |> DAG.add [g]

(* Main function. *)
let split_all (def : def) : def DAG.t =
  match def.rhs with
  | OModule m -> split_all_module def.lhs m
  |  _ -> DAG.init def

(* [split_all] is shadowed by a wrapper hiding the [reset] integer. *)
let split_all def =
  DAG.flat_map split_all def

(* -------------------------------------------------------------------------- *)

(* Main splitting functions.
   [one_strategy] applies one splitting strategy. *)
let one_strategy strategy def : def DAG.t =
  match strategy with
  |   `Split -> split_all def
  | `NoSplit -> def

(* [split] splits an AST into a graph of ASTs. *)
let split (splitting_strategy: [`Split | ` NoSplit] list)
      osiris_ast: def DAG.t =
  (* First create a first graph containing a single node: the Osiris AST
     annotated by the name of the module.*)
  let init : def DAG.t = DAG.init osiris_ast in

  (* Then iterate over the list of strategies provided on the command line,
     each transforming the AST. *)
  List.fold_right
    one_strategy splitting_strategy init
