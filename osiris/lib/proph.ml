(* Prophecy variables. *)

(* A prophecy variable is a ghost device: it lets a proof name a value that
   the execution has not produced yet. It has no runtime meaning.

   [Proph.create ()] allocates a fresh prophecy. Osiris recognizes this call
   by name and translates it to an internal notion of prophecy allocation, so
   the definition below is never the one that gets verified. A program that
   uses prophecies must therefore depend on this library.

   A resolution is deliberately NOT a function of this module. It is written
   as an attribute on the operation whose result is being predicted,

     Atomic.compare_and_set r seen v [@resolve p tag]

   which resolves [p] with the pair of that operation's result and [tag]. *)

type t = unit ref

let create () : t = ref ()
