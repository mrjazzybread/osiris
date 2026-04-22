let incr r = r := !r + 1

let count n =
  let i = ref 0 in
  while !i < n do incr i done;
  !i
