let mem x l =
  let open struct type exn += Found end in
  match
    List.iter
      (fun y ->
	if x = y then
	  raise Found
	else
	  ())
      l
   with
   | exception Found -> true
   | _ -> false