val fail : ('a, out_channel, unit, 'b) format4 -> 'a
val dune_root : string
val mark: string
val out : string
val modules : [`All|`Modules of string list]
type strategy = [`Split|`NoSplit]
val splitting_strategy : strategy list

(* This function sends output to [stderr] if [--debug] is set. *)
val debug: ('a, out_channel, unit) format -> 'a

(* This function sends output to [stderr] if [--verbose] is set. *)
val say: ('a, out_channel, unit) format -> 'a
