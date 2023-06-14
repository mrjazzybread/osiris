(* -------------------------------------------------------------------------- *)

(* Additional functions on lists. *)

let rec filtermap f = function
  | [] -> []
  | h :: t -> match f h with
              | None -> filtermap f t
              | Some h -> h :: filtermap f t

let rec last = function
  | [] -> assert false
  | h :: [] -> h
  | _ :: t -> last t

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

(* [exec_one_line cmd] executes the command [cmd: string] and returns the last
   line returned by the command.
   Note: If the command fails or does not provide an output, so will this
         function. *)
let exec_one_line cmd =
  let process = Unix.open_process_in cmd in
  let line = input_line process in
  let _ = Unix.close_process_in process in
  line

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
  (* Do not break the following line; it breaks the system call. *)
  ("dune describe | grep -A 4 " ^ file ^ " | awk '/cmt/ { print $NF }' | grep cmt | tail -n1 | tr -d ' ()'")
  |> exec_one_line
