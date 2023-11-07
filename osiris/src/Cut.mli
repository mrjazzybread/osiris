open Coq

(**[cut def] turns a single Coq toplevel definition into a nonempty list
   of such definitions. The marks [CCut] indicate where terms should be
   cut off. *)
val cut : def -> defs
