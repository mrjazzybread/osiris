open Effect
open Effect.Deep

type _ Effect.t += E : int Effect.t

let () =
  print_int
    (try
       1 + perform E
     with
       effect E, k -> continue k 2)

type _ Effect.t += F : int Effect.t

let () =
  print_int
    (try
       perform E * 10 + perform F
    with
    | effect E, k -> continue k 2
    | effect F, k -> continue k 3)

let () =
  print_int (
    let r = ref 1 in
    try perform E * 10 + perform E with
      effect E, k -> r := !r + 1; continue k !r
  )

let r = ref 1
let f () = try perform E with effect E, k -> let n = !r in continue k (1 + n * perform E)
let x = try f () with effect E, k -> r := 2; continue k (2 * !r)
let () = print_int x

let r = ref 1
let f () = try perform E with effect E, k -> continue k (1 + !r * perform E)
let x = try f () with effect E, k -> r := 2; continue k (2 * !r)
let () = print_int x
