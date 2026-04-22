(* Full applications: all arguments supplied, primitive fires directly *)
let sum a b      = a + b
let is_lt a b    = a < b
let get arr i    = Array.get arr i
let set arr i v  = Array.set arr i v

(* Partial applications: fewer args than arity — falls back to EApp *)
let add5         = ( + ) 5
let lt0          = ( < ) 0
let get_at arr   = Array.get arr
