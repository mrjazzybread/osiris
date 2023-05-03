let new_counter () =
  let c = ref 0 in
  let upd i = c := i in
  let get () = !c in
  (get, upd)

let _ =
  let res = new_counter () in
  let get = fst res in
  let upd = snd res in
  let c = get () in
  let () = upd 13 in
  let res = get () - c in
  res

let _test =
  let (get, upd) = new_counter () in
  let c = get () in
  let () = upd 13 in
  let res = get () - c in
  res
