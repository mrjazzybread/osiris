let sum_downto n =
  let s = ref 0 in
  for i = n downto 1 do
    s := !s + i
  done;
  !s
