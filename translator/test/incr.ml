let new_counter () =
  let c = ref 0 in
  let upd i = c := i in
  let get () = !c in
  (get, upd)
