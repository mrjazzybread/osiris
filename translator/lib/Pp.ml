open Ast
open PPrint

(* [document_of_expr] translates an expression into a document. *)
let rec document_of_expr e =
  match e with
  | EPlain s ->
      string s
  | EConstr (c, es) ->
      parens (flow space (string c :: List.map document_of_expr es))

(* Recursive definitions. *)
let print_rec_def (name, e) =
  match name with
  | None -> assert false (* recursive functions have names. *)
  | Some name ->
      let anonfun : expr =
        match e with
         | EConstr ("EAnonFun", [anonfun]) ->
             anonfun
         | _ ->
             (* The right-hand side of a [let rec] definition must
                be a function. We do not allow recursive values of
                other types. *)
             assert false
      in
      EConstr ("RecBinding", [ string_literal name; anonfun ])

(* Non-recursive definitions. *)
let print_nonrec_def (name, e) =
  let p =
    match name with
    | Some x -> EConstr ("PVar", [ string_literal x ])
    | None -> EConstr ("PAny", [])
  in
  EConstr ("Binding", [p; e])

let rec list nil cons (xs : expr list) : expr =
  match xs with
  | [] ->
      EConstr (nil, [])
  | x :: xs ->
      EConstr (cons, [x; list nil cons xs])

let definitions lets : document =
  let (recflag, symbols) = lets in

  (* Generic pretty-printer for bindings. *)
  let ilet ilet cons nil f =
    EConstr (ilet, [list nil cons (List.map f symbols)])
    |> document_of_expr
  in

  (* Each element of [lets] is a top-level [let].
     (The elements of [lets] are linked with [and] in the source file.) *)
  if recflag
  then
    ilet "ILetRec" "RecBiCons" "RecBiNil" print_rec_def
  else
    ilet "ILet" "BiCons" "BiNil" print_nonrec_def

let rec document_of_tast = function
  | [] -> empty
  | h :: h' :: t ->
     concat [definitions h ;
             hardline; semi; hardline;
             document_of_tast (h' :: t)]
  | h :: [] ->
     concat [definitions h ; hardline]


(* An element of type [ast] is a list of lists [l] of top-level definitions,
   where the elements of [l] are defined within the same [let ... and ...]
   construct.
   Each top-level definition is represented by an element of type
   [ string option * (* Name of the symbol. *)
     bool          * (* Is the symbol recursive? *)
     expr            (* Expression *)
   ].

   [transform_ast] groups the top-level symbols by [let ... and ...]
   constructs. *)
let transform_ast (ast: (string option * bool * expr) list list)
    : (bool * ((string option * expr) list)) list =
  let facto (l: (string option * bool * expr) list) :
            bool * (string option * expr) list =
    match l with
    | [] -> (false, [])
    | (_, b, _) :: _ ->
       (b, List.map (fun (n, _, e) -> (n, e)) l)
  in
  List.map facto ast

let print_ast fmt (ast: ast) =
  ast
  |> List.filter (fun l -> l <> [])
  |> transform_ast
  |> document_of_tast
  |> align |> nest 2
  |> (PPrint.ToFormatter.pretty 0.5 100) fmt

let print fmt module_name headers (a: ast) : unit =
  Format.fprintf fmt
                 "%s@.@.\
                  (* Generated code: *)@.\
                  Definition %s : mexpr := @.\
                  \  MkStruct [ @.%a ].@.\
                  @.(* END. *)"
                 headers module_name
                 print_ast a
