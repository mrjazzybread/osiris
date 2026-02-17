let sum n =
  let a = Array.init n (fun i -> i + 1) in
  Array.fold_left (+) 0 a
