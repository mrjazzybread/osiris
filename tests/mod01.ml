module M0 = struct end
module M1 = struct let x = 1 end
module M2 = struct let x = 2 end
module M4 = struct module M3 = struct let x = 3 end end

let () = print_int M1.x
let () = print_int M4.M3.x
let () = let open M1 in print_int x
let () = let open M1 in let open M2 in print_int x
let () = let open M2 in let open M1 in print_int x
let () = let open M4 in print_int M3.x
let () = let open M4.M3 in print_int x

let () = let module M = struct let x = 2 end in print_int M.x
let () = let open struct let x = 2 end in print_int x


(* unsupported construct: signature ascription *)
(*
module type S = sig end
let () = let open M1 in let open (M2 : S) in print_int x
let () = let open (M1 : S) in let open M2 in print_int x
module M' = (M1 : sig val x : int end)
module M' : sig val x : int end = M1
let () = print_int M'.x
*)

let () = let open struct include M1 end in let open struct include M2 end in print_int x
let () = let open struct open    M1 end in let open struct include M2 end in print_int x
let () = let open struct include M1 end in let open struct open    M2 end in print_int x

(* unsupported: functor *)
(*
module F (M : sig val x : int end) = struct let y = 30 + M.x end
let () = print_int (let module M' = F(M1) in M'.y)
*)

let () = print_newline ()
