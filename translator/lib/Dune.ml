(* -------------------------------------------------------------------------- *)
(* Miscellaneous functions. *)

let in_dir verbose d f =
  let current = Sys.getcwd () in
  verbose ("switching from "^current^" to "^d^".");
  Sys.chdir d;
  let res = f () in
  Sys.chdir current;
  verbose ("switching back to "^current^".");
  res



(* -------------------------------------------------------------------------- *)
(* Dune-related functions *)

(* [cmt_of_ml] tries to find the cmt file associated to some ml file in 
   a project that relies on Dune.
   In order to achieve this, it jumps into the directory of the ml file and
   runs [dune describe]. It parses the output to find the cmt file. *)
let cmt_of_ml verbose dir name: string option =
  (* TODO: rewrite the following functions using Lwt instead of Unix in order
     to be more portable. *)

  (* TODO: fix "dune describe" so that it behaves as expected.  *)
  let find_root () =
    let command = "dune describe |
                   head -n1 | awk '{ print $2 }' | tr -d ')' |
                   # the following line should be removed once the call to
                   # dune describe is fixed.
                   sed 's-/bin$--' | sed 's-/lib$--'"
    in
    let och = Unix.open_process_in command in
    let output = input_line och in
    let _ = Unix.close_process_in och in
    output
  in

  let find_cmt () =
    let command =
      (* TODO: fix the output of the dune-describe command
        "dune describe | \
       grep -o '([/a-z_A-Z\\.]*"^name^".cmt)' | \
       tr -d '()'" *)
      "find . -name '*"^name^".cmt'"
      in
    let och = Unix.open_process_in command in
    let output =
      try Some (Unix.realpath (input_line och))
      with End_of_file -> None
    in
    let _ = Unix.close_process_in och in
    output
  in

  let root = in_dir verbose dir find_root in
  in_dir verbose root find_cmt

