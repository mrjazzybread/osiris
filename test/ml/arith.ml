let add x y=
  let z = y in
  let (t, v) =
    let t = z in
    let z = t in
    let t = 0 * z in
    (x, t) in
  t + (v + z)

let rec mult x y =
  if y = 0
  then 0
  else if y < 0
  then - (mult x (-y))
  else
    begin
      assert (0 < y);
      x + (mult x (y -1))
    end
