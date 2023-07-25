module Counter (* TODO: add coercions to the translator : sig
  type counter
  val make : unit -> counter
  val incr : counter -> unit
  val set : counter -> int -> unit
  val get : counter -> int
end *)
= struct
  type counter = int ref
  let make () = ref 0
  let incr c = c := !c + 1
  let set c v = assert (!c <= v) ;
                c := v
  let get c = !c
end
