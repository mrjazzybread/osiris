let print n = print_int n; print_newline ()

let () =
  print 1;
  print (- ( -2));
  print (1 + 2);
  print (let x = 2 in x + x);
  print ((fun x -> x + 2) 3);
  print (2 * 3);
  print (2 * 3 + 1);
  print (2 * (3 + 1));
  print (95 / 10);
  print (109 mod 11)

let () =
  (* TODO: max_int; abs; land, ^, int_of_char, etc  *)
  for a = -10 to 10 do
    print (succ a);
    print (pred a);
    for b = -10 to 10 do
      print (a + b);
      print (a * b);
      print (a - b);
      if b <> 0 then print (a / b);
      if b <> 0 then print (a mod b);
    done
  done

let () =
  let f x = (x + 3) * (x / 2) + if x > 2 then 10 else 20 in
  print (f 0 + f 1 + f 10)


let f x = (x + 3) * (x / 2) + if x > 2 then 10 else 20

let rec map f = function [] -> [] | x :: l -> f x :: map f l

let rec sum = function [] -> 0 | x :: l -> x + sum l

let rec seq a b = if a > b then [] else a :: seq (a + 1) b

let () = print (sum (map f (seq 0 20)))
