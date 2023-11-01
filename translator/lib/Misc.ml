(* -------------------------------------------------------------------------- *)

(* Helpers to define verbose/debugging functions. *)


let mkmsg b f s = if b
                  then Format.fprintf f "%s@." s
                  else ()

let mksay b f s a = if b
                    then (Format.fprintf f "%s@!," s; a)
                    else a

let mksay_with b f s sa = if b
                            then (Format.fprintf f s sa ; sa)
                            else sa

let mkdo b f a = if b
                 then (f a; a)
                 else a

(* -------------------------------------------------------------------------- *)

let do_with (b: 'b) (f: 'b -> 'c) (g: 'a -> 'b -> 'd) (a: 'a) : ('d * 'c) =
  let a = a
  and b = b in
  let left = g a b in
  let right = f b in
  (left, right)

(* -------------------------------------------------------------------------- *)

(* [in_dir d f a] changes directory to [d], executes [f a] and goes back to the
   initial working directory. *)
let in_dir new_dir f a =
  let old_dir = Unix.getcwd () in
  Unix.chdir new_dir;
  let res = f a in
  Unix.chdir old_dir;
  res

(* -------------------------------------------------------------------------- *)

(* Transforming an OCaml file name to an OCaml module name. *)

let module_name (filename : string) : string =
  filename
  |> Filename.basename         (* Keep just the base name. *)
  |> Filename.remove_extension (* Remove the extension. *)
  |> String.capitalize_ascii   (* Capitalize the first letter. *)

(* -------------------------------------------------------------------------- *)

(* [exec_one_line cmd] executes the command [cmd: string] and returns the last
   line returned by the command.
   Note: If the command fails or does not provide an output, so will this
         function. *)
let exec_one_line cmd =
  let process = Unix.open_process_in cmd in
  let line = input_line process in
  let _ = Unix.close_process_in process in
  line

let exec_lines cmd =
  let rec readlines chan =
    try
      let line = input_line chan in
      line :: readlines chan
    with End_of_file ->
      []
  in
  let process = Unix.open_process_in cmd in
  let res = readlines process in
  let _ = Unix.close_process_in process in
  res

  (* [locate_cmt f] finds the [cmt] corresponding to the [ml] file [f].
     Note: The function assumes:
           - that the [ml] file is part of a dune project,
           - that dune build has been executed,
           - that dune produced the [cmt] file.
           - As there is no API to dune, I do not know how to fetch these
             information without using shell script.
             Note that the result could be predicted if dune's target was known
             in advance; but it might not always be "default".

     Explanation of the command:
       "dune describe" is the cli of dune. It provides information on the files
                       which are known to dune.
       "grep -A4 [f]" allows to grep the output of the previous command.
                      Why "-A4"?
                                 "grep [f]" looks for the line of the output of
                                            "dune describe" that contains the
                                            name of the file whose [cmt] we want
                                  "-A4" fetches the four next lines of the
                                        parsed output.
                                        The line "(cmt ...)" providing the
                                        information we want is three ilnes down
                                        from "(file [f])".
                                        As the output of "dune describe" is
                                        limited in width, we also need the next
                                        line.
       "awk '/cmt/ { print $NF }'" select the lines among the five we now have
                                   to only include the one(s) containing "cmt",
                                 and only keep the last column.
       "tail -n1" keeps the last line (on which is the name of the result)
       "tr -d ')'" removes spaces and parentheses. Note that "tr -d')'" is
                   indeed enough, as there are no more spaces (grep) and '('
                   (format of the output of "dune describe"). *)
let locate_cmt (file: string) =
  try
    (* Do not break the following line; it breaks the system call. *)
    ("dune describe | grep -A 4 " ^ file ^ " | awk '/cmt/ { print $NF }' | grep cmt | tail -n1 | tr -d ' ()'")
    |> exec_one_line
  with
  | _ ->
     try
       (* If the previous command does not work, try to find the cmt file by hand
          in [_build]. The command should be updated to be more robust. *)
       begin try
           (Format.sprintf
              "realpath \"$(find . -name '*%s.cmt' | grep 'byte')\""
              (module_name file))
           |> exec_one_line
         with _ ->
           (Format.sprintf
              "realpath \"$(find . -name '*__%s.cmt' | head -n1)\""
              (module_name file))
           |> exec_one_line
       end
     with _ ->
       Printf.sprintf "[locate_cmt] failed for %s in %s." file (Sys.getcwd ())
       |> failwith

(* -------------------------------------------------------------------------- *)

(* Recursively read a directory and list its [ml] files components. *)

(* The function returns two trees: one storing the sub-directories and one
   storing the files. *)
let list_mls din dout =
  let din =
    exec_one_line (Printf.sprintf "realpath '%s'" din)
  in
  let mls =
    Printf.sprintf "find %s -iname '*.ml' -exec realpath {} \\;" din
    |> exec_lines
  and outs =
    Printf.sprintf "find %s -iname '*.ml' -exec realpath {} \\; | \
                    sed 's~ml$~v~' | \
                    sed 's|%s|%s|'" din din dout
    |> exec_lines
  and dirs =
    Printf.sprintf "find %s -type d | \
                    sed 's~%s~%s~' | \
                    sort" din din dout
    |> exec_lines in
  mls, outs, dirs
