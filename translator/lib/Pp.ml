open Ast
open PPrint

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

let rec document_of_expr = function
  | EPlain s -> string s
  | EConstr (c, l) ->
     match l with
     | [ EPlain v ] ->
        if c = "EVar" || c = "PVar"
        then parens (string (string_of_var c v))
        else parens (flow space (string c :: List.map document_of_expr l))
     | _ ->
        parens (flow space (string c :: List.map document_of_expr l))

let definition = function
  | (None, h) ->
     (* TODO: The representation of [let _ = e] and [let () = e] should change so
        that these expressions are taken into account by the definitions following
        them !
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
            (align (group (concat [document_of_expr h; dot])))
          ]))
  | (Some n, h) ->
     (nest 2 (concat [
         string "Definition"; space;
         string n; space;
         string ":= ";
         (align (group (concat [document_of_expr h; char '.';])))
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
