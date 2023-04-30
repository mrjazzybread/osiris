let new_counter () =
  let c = ref 0 in
  let upd i = c := i in
  let get () = !c in
  (get, upd)

let _ =
  let (get, upd) = new_counter () in
  let c = get () in
  let () = upd 13 in
  let res = get () - c in
  res
