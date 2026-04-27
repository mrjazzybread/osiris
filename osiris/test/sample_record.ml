type t = { rx : int; ry : int }

let r1 = { rx = 1; ry = 2 }
let r2 = { ry = 4; rx = 3 }
let get_y r = r.ry
let set_x r = { r with rx = 5 }
