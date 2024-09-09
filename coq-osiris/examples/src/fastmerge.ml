(** Efficient implementation of merge sort. **)

let rec length_aux len = function
    [] -> len
  | _::l -> length_aux (len + 1) l

let length l = length_aux 0 l

(* Reverse the first list, then append it to the second list.
  e.g. rev_append [A;B;C] [F;E;D] = [C;B;A;F;E;D]*)
let rec rev_append l1 l2 =
  match l1 with
    [] -> l2
  | a :: l -> rev_append l (a :: l2)

let rev l = rev_append l []

(* Note: [rev_append] is faster than [append] *)
let merge_aux (cmp : int -> int -> bool)
    (fix : int list -> int list -> int list -> int list)
    l1 l2 accu =
  match l1, l2 with
  | [], l2 -> rev_append l2 accu
  | l1, [] -> rev_append l1 accu
  | h1::t1, h2::t2 ->
      if cmp h1 h2
      then fix t1 l2 (h1::accu)
      else fix l1 t2 (h2::accu)

(* Merge the lists while reversing the ordering *)
let rev_merge l1 l2 =
  let rec rev_merge_aux l1 l2 accu =
    merge_aux (<=) rev_merge_aux l1 l2 accu in
  rev_merge_aux l1 l2 []

(* [A;B;C] [D;E;F] => [C;B;A;F;E;D]
   Flip the ordering and then merge it *)
let rev_merge_rev l1 l2 =
  let rec rev_merge_rev_aux l1 l2 accu =
    merge_aux (>) rev_merge_rev_aux l1 l2 accu in
  rev_merge_rev_aux l1 l2 []

let sort_2_aux cmp x1 x2 =
  if cmp x1 x2 then [x1; x2] else [x2; x1]

let sort_2 = sort_2_aux (<=)
let rev_sort_2 = sort_2_aux (>)

let sort_3_aux cmp x1 x2 x3 =
  if cmp x1 x2 then
    if cmp x2 x3 then [x1; x2; x3]
    else if cmp x1 x3 then [x1; x3; x2]
    else [x3; x1; x2]
  else if cmp x1 x3 then [x2; x1; x3]
  else if cmp x2 x3 then [x2; x3; x1]
  else [x3; x2; x1]

let sort_3 = sort_3_aux (<=)
let rev_sort_3 = sort_3_aux (>)

let fast_merge_sort l =
  let rec sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl -> (sort_2 x1 x2, tl)
    | 3, x1 :: x2 :: x3 :: tl -> (sort_3 x1 x2 x3, tl)
    | n, l ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = rev_sort n1 l in
        let s2, tl = rev_sort n2 l2 in
        (rev_merge_rev s1 s2, tl)
  and rev_sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl -> (rev_sort_2 x1 x2, tl)
    | 3, x1 :: x2 :: x3 :: tl -> (rev_sort_3 x1 x2 x3, tl)
    | n, l ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = sort n1 l in
        let s2, tl = sort n2 l2 in
        (rev_merge s1 s2, tl)
  in
  let len = length l in
  if len < 2 then l else fst (sort len l)
