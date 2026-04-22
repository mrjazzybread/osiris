(* A simple spin-lock backed by a boolean ref cell.
   [false] = unlocked, [true] = locked. *)

let create () = Atomic.make false

let acquire lk =
  while not (Atomic.compare_and_set lk false true) do () done

let release lk =
  Atomic.set lk false
