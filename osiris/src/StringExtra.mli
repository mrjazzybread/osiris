(**[count p s] returns the number of characters [c] in the string [s]
   such that [p c] is true. *)
val count: (char -> bool) -> string -> int

(**[double p s] is a copy of the string [s] where every character [c]
   such that [p c] is true has been doubled (that is, repeated twice
   in succession). *)
val double: (char -> bool) -> string -> string
