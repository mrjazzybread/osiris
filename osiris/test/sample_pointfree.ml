open Effect
open Effect.Deep

type _ Effect.t += Ask : int t
type _ Effect.t += Fail : exn t

(* --- continue / discontinue --- *)

(* Fully applied — EContinue/EDiscontinue fire directly at the call site *)
let resume_42   k = continue    k 42
let dismiss_exn k = discontinue k Exit

(* Partial application: 1 of 2 args *)
let resume  k = continue    k
let dismiss k = discontinue k

(* Point-free: used as bare values *)
let my_continue    = continue
let my_discontinue = discontinue

(* --- References: (!) --- *)

(* Fully applied — produces ELoad *)
let deref r = !r

(* Point-free *)
let my_deref = (!)

(* --- Atomic operations --- *)

(* Fully applied — each produces its Osiris node *)
let atomic_load   r     = Atomic.get r
let atomic_xchg   r v   = Atomic.exchange r v
let atomic_cas    r x y = Atomic.compare_and_set r x y
(* Partial application *)
let atomic_xchg1  r   = Atomic.exchange r
let atomic_cas1   r   = Atomic.compare_and_set r
let atomic_cas2   r x = Atomic.compare_and_set r x

(* Point-free *)
let my_atomic_load = Atomic.get
let my_atomic_xchg = Atomic.exchange
let my_atomic_cas  = Atomic.compare_and_set
