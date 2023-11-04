let die _c =
  exit 1

let fail format =
  Printf.kfprintf die stderr format
