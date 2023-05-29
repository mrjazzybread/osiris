open Ast
open PPrint


let newline_construct_k (c: string) =
  let l1 = ["ELet"; "BiCons"] in
  if List.mem c l1 then (true, true)
  else if c = "EFun1Var" then (true, false)
  else (false, false)


let string_of_var c (v: string) : string =
  if String.contains v '.' && c = "EVar"
  then
    begin
      v
      |> String.split_on_char '.'
      |> List.map (fun s -> "\"" ^ s ^ "\"")
      |> String.concat ";"
      |> fun s -> "EMkPath [" ^ s ^"]"
    end
  else c ^ " \"" ^ v ^ "\""

(* [document_of_expr b] translates an expression into a document.
   The boolean [b] indicates whether parenthesis are needed around the
   expression. *)
let rec document_of_expr (b: bool) e =
  let maybeparens =
    match b with
    | true -> parens
    | false -> fun i -> i
  in
  match e with
  | EPlain s -> string s
  | EConstr (c, l) ->
     match l with
     | [ EPlain v ] ->
        if c = "EVar" || c = "PVar"
        then maybeparens (string (string_of_var c v))
        else maybeparens (flow space (string c :: List.map (document_of_expr true) l))
     | _ ->
        match newline_construct_k c with
        | true, b ->
           begin
             let hl = if b then hardline else space in
             match l with
             | [e1; e2] ->
                let d1 = document_of_expr true e1 in
                let d2 = document_of_expr false e2 in
                [string c;
                 nest 2 (hl ^^ d1);
                 space; dollar; hardline;
                 d2]
                |> concat |> maybeparens
             | _ -> assert false
           end
        | false, _ ->
           maybeparens (flow space (string c ::
                                      List.map (document_of_expr true) l))

(* Recursive definitions. *)
let print_rec_def (name, expr) =
  match name with
  | None -> assert false (* recursive functions have names. *)
  | Some name ->
      let anonfun : expr =
        match expr with
         | EConstr ("EAnonFun", [anonfun]) ->
             anonfun
         | _ ->
             (* The right-hand side of a [let rec] definition must
                be a function. We do not allow recursive values of
                other types. *)
             assert false
      in
      concat [
        string "RecBinding"; space;
        string ("\""^name^"\""); space; dollar; hardline;
        document_of_expr true anonfun
      ]
      |> nest 2

(* Non-recursive definitions. *)
let print_nonrec_def (name, expr) =
  let patt: document =
    match name with
    | Some n -> string ("PVar \""^n^"\"")
    | None -> string "PAny"
  in
  concat [
      string "Binding"; space;
      parens patt; hardline;
      document_of_expr true expr ]
  |> nest 2

let definitions lets =
  let (recflag, symbols) = lets in

  (* Generic pretty-printer for bindings. *)
  let ilet ilet cons nil f =
    let bindings: document =
      List.fold_right
        (fun (name, expr) res ->
          let binding: document = f (name, expr) in
          concat [ string cons ; hardline;
                   parens binding; space; dollar; hardline;
                   res ]
          |> nest 2)
        symbols (string nil)
    in
    nest 2 (concat [
                string ilet ; space; lparen ; hardline ;
                bindings;
                rparen ])
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
