type t = { ra : int; rb : int; rc : int }

(* Source order matches declaration order. *)
let r1 = { ra = 1; rb = 2; rc = 3 }

(* Source order is the reverse of declaration order. *)
let r2 = { rc = 30; rb = 20; ra = 10 }

(* Source order is yet another permutation. *)
let r3 = { rb = 200; rc = 300; ra = 100 }

(* A mutable record. The mutability tag should be [Mut]. *)
type mt = { mutable ma : int; mb : int }
let m1 = { ma = 7; mb = 8 }

(* Field access: [rc] is at declaration position 2. *)
let get_c r = r.rc

(* Multi-field record update with source order [rc; rb] (i.e. reversed
   relative to declaration). The translator must produce [Fexpr]s in
   declaration-position order: rb (1), then rc (2). *)
let upd_bc r = { r with rc = 100; rb = 99 }
