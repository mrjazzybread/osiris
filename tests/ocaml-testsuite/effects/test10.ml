(* TEST *)

open Effect
open Effect.Deep

module Random = struct
  let r = ref 0
  let int n = r := !r + 1; (!r * 1299709) mod n
end
let ignore _ = ()

type _ t += Peek : int t
type _ t += Poke : unit t

let rec a i = perform Peek + Random.int i
let rec b i = a i + Random.int i
let rec c i = b i + Random.int i

let rec d i =
  Random.int i +
  try c i with
  effect Poke, k -> continue k ()

let rec e i =
  Random.int i +
  try d i with
  | effect Peek, k ->
    (* ignore (Deep.get_callstack k 100); *)
    continue k 42

let _ =
  ignore (e 1);
  print_string "ok\n"
