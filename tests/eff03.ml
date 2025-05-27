open Effect
open Effect.Deep

type _ Effect.t += E : int -> int Effect.t

let x =
  let r = ref 1 in
  try
    perform (E (2 * perform (E 1)))
    with effect E n, k -> r := !r + 1; continue k (n + !r)

let () = print_int x
