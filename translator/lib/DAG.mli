type 'a t

val init : 'a -> 'a t

val size : 'a t -> int

val to_list : 'a t -> 'a list

val add : 'a t list -> 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val flat_map : ('a -> 'b t) -> 'a t -> 'b t