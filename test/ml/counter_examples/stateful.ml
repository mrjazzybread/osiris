module Counter (* TODO: add coercions to the translator. : sig
  val incr : unit -> unit
  val set : int -> unit
  val get : unit -> int
end *)
= struct
  let c = ref 0
  let incr () = c := !c + 1
  let set v = assert (!c <= v) ;
              c := v
  let get () = !c
end
