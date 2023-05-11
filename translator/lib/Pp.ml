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
   The boolean [b] indicates whether parentehsis are needed around the
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

let definition = function
  | (None, false, h) ->
     (nest 2 (flow space [
            string "ILet (Binding1 PAny $"; hardline;
            (align (document_of_expr false h ^^ char ')'));
            repeat 2 hardline;
          ]))
  | (Some n, false, h) ->
     (nest 2 (concat [
         string "ILet (Binding1 (PVar \"";
         string n;
         string "\") $"; hardline;
         (align (document_of_expr false h ^^ char ')'));
         repeat 2 hardline;
     ]))
  | (Some n, true, EConstr ("EFun1Var", [EPlain var; body])) ->
     (nest 2 (concat [
                  string "ILetRec (RecBinding1 \"";
                  string n; string "\""; space;
                  string var; space; dollar; hardline;
                  (align (document_of_expr false body ^^ char ')'));
                  repeat 2 hardline
     ]))
  | Some n, true, (EConstr ("EFun1Pat", [pat; body])) ->
     let v = "__osiris_reserved_arg_name" in

     (* [body] is gradually replaced by a match over [pat] *)
     let branch = EConstr ("Branch", [ pat ; body ]) in
     let branches = EConstr ("BrCons", [ branch ; EPlain "BrNil" ]) in
     let match_expr = EConstr ("EMatch", [ EConstr ("EVar", [EPlain v]);
                                           branches ]) in

     (nest 2 (concat [
                  string "ILetRec (RecBinding1 \"";
                  string n; string "\" \""; string v ; string "\"";
                  space; dollar; hardline;
                  (align (document_of_expr false match_expr ^^ rparen));
                  repeat 2 hardline
     ]))
  | _ -> assert false

let rec document_of_ast = function
  | [] -> empty
  | h :: h' :: t ->
     concat [definition h ; semi; hardline; document_of_ast (h' :: t)]
  | h :: [] ->
     concat [definition h ; hardline]

let print_ast fmt ast =
  (PPrint.ToFormatter.pretty 0.5 100) fmt (document_of_ast ast)

let print fmt module_name headers (a: ast) : unit =
  Format.fprintf fmt
                 "%s@.@.\
                  (* Generated code: *)@.\
                  Definition %s : mexpr :=
                    MkStruct [ %a ].@.\
                  @.(* END. *)"
                 headers module_name
                 print_ast a
