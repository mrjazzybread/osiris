open Coq

(**[chop def] turns a single Coq toplevel definition into a nonempty list
   of such definitions. The marks [EMark] indicate where terms should be
   chopped off. *)
val chop : def -> def list
