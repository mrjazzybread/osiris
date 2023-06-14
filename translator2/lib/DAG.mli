type 'a t

val init : 'a -> 'a t

val add : 'a t -> 'a list -> 'a t

val size : 'a t -> int

val to_list : 'a t -> 'a list

val map : ('a -> 'b) -> 'a t -> 'b t