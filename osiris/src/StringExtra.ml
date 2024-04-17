open String

let[@inline] postincrement r =
  let x = !r in
  r := x + 1;
  x

let count p s =
  let k = ref 0 in
  let n = length s in
  for i = 0 to n - 1 do
    if p s.[i] then incr k
  done;
  !k

let double p s =
  let k = count p s in
  if k = 0 then s else
  let n = length s in
  let b = Bytes.create (n + k) in
  let j = ref 0 in
  let[@inline] write c = Bytes.set b (postincrement j) c in
  for i = 0 to n - 1 do
    let c = s.[i] in
    write c;
    if p c then write c
  done;
  Bytes.to_string b
