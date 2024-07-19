let sum l =
  let x = ref 0 in
  let () =
    List.iter
      (fun y -> x := !x + y)
      l
  in
  !x