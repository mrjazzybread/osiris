open Filename
open Sys
open Fail

(* This code relies on the fact that [dirname "foo"] is ".". *)

let rec ensure_directory_exists dirname =
  match Sys.is_directory dirname with
  | true ->
      ()
  | false ->
      fail "Not a directory: %s.\n" dirname
  | exception Sys_error _ ->
      ensure_parent_directory_exists dirname;
      mkdir dirname 0o700

and ensure_parent_directory_exists filename =
  ensure_directory_exists (dirname filename)
