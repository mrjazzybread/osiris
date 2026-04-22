let fail () = raise Exit

let catch () =
  match fail () with
  | exception Exit -> false
  | _ -> true
