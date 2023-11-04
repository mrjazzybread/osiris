(**[fail format ...] displays a message on [stderr] and exits the program
   with exit code 1. *)
val fail : ('a, out_channel, unit, 'b) format4 -> 'a

(**[warn format ...] displays a message on [stderr]. *)
val warn : ('a, out_channel, unit) format -> 'a
