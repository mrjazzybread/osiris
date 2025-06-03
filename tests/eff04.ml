open Effect
open Effect.Deep

let print s i = print_string s; print_string ":"; print_int i; print_newline ()

type _ Effect.t +=
  | E : int -> int Effect.t
  | F : int -> int Effect.t
  | G : int -> int Effect.t

let c1 f = try f () with effect E n, k -> print "E" n; continue k (n * 2 + perform (F (n + 1)))
let c2 f = try f () with effect F n, k -> print "F" n; continue k (n * 2 + perform (G (n + 2)))
let c3 f = try f () with effect G n, k -> print "G" n; continue k (n * 2 + 2)
let c f = print "end" (c3 (fun () -> c2 (fun () -> c1 f)))

let () = c @@ fun () -> perform (E 1) + 2
let () = c @@ fun () -> let a = perform (E 1) in a + perform (F 2)
let () = c @@ fun () -> perform (E 1) + perform (F 2)
let () = c @@ fun () -> perform (E (perform (F (perform (G 1)))))
let () = c @@ fun () -> perform (G (perform (F (perform (E 1)))))
let () = c @@ fun () -> perform (G (perform (E (perform (F 1)))))
let () = c @@ fun () -> perform (F (perform (G (perform (F (perform (F 1)))))))
let () = c @@ fun () -> perform (F (perform (F (perform (F (perform (F 1)))))))
let () = c @@ fun () -> perform (F (perform (E (perform (F (perform (F 1)))))))
