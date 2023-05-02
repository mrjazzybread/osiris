open Ast
open PPrint


let newline_construct_k (c: string) =
  let l1 = ["ELet"; "BiCons"] in
  if List.mem c l1 then (true, true)
  else if c = "EFun" then (true, false)
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
  | (None, h) ->
     (* TODO: The representation of [let _ = e] and [let () = e] should change
        so that these expressions are taken into account by the definitions
        following them !
        Eg. It is not possible to reason about the following code
            let a = ref 0
            let () = a := 1
            let b = !a
            ...
            let z = ...

        An alternative would be to translate the above (assuming this is the sole
        content of a file) as:
            let <some name> =
                let a = ref 0 in
                a := 1;
                let b = !a
                ...
                let z = ...
                (a, (b, .., (y, z)))

        This is still a silent error so that the translator can still be used. *)
     (nest 2 (flow space [
            string "Definition";
            string "pleasedontclash (*This is not a name. *)";
            string ":="; hardline;
            (align (document_of_expr false h ^^ dot));
            repeat 2 hardline;
          ]))
  | (Some n, h) ->
     (nest 2 (concat [
         string "Definition"; space;
         string n; space;
         string ":="; hardline;
         (align (document_of_expr false h ^^ char '.'));
         repeat 2 hardline;
       ]))

let rec document_of_ast = function
  | [] -> empty
  | h :: t ->
     concat [definition h ; hardline; document_of_ast t]

let print_ast fmt ast =
  (PPrint.ToFormatter.pretty 0.5 100) fmt (document_of_ast ast)

let print fmt headers (a: ast) : unit =
  Format.fprintf fmt
                 "%s@.@.\
                 (* Generated code: *)@.\
                 %a"
                 headers print_ast a
