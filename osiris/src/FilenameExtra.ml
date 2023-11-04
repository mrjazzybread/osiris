open Filename
open Fail

type filename =
  string

let is_absolute filename =
  not (is_relative filename)

let remove_suffix suffix name =
  try
    chop_suffix name suffix
  with Invalid_argument _ ->
    fail "Error: %s does not end with %s\n" name suffix

let add_prefix prefix base =
  prefix ^ base

let add_suffix suffix base =
  base ^ suffix

let dir_sep_char : char =
  assert (String.length Filename.dir_sep = 1);
  String.get Filename.dir_sep 0

let rec drop k xs =
  if k = 0 then xs else match xs with [] -> [] | _ :: xs -> drop (k-1) xs

let drop k filename =
  assert (is_relative filename);
  filename
  |> String.split_on_char dir_sep_char (* split into '/'-separated segments *)
  |> drop k                            (* drop the first [k] segments *)
  |> String.concat dir_sep             (* reconstruct the filename *)

let map_basename f filename =
  concat (dirname filename) (f (basename filename))
