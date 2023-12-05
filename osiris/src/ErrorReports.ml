open Lexing

let extract text (pos1, pos2) : string option =
  let ofs1 = pos1.pos_cnum
  and ofs2 = pos2.pos_cnum in
  let len = ofs2 - ofs1 in
  try
    Some (String.sub text ofs1 len)
  with Invalid_argument _ ->
    (* In principle, this should not happen, but it might, so we make this
       a non-fatal error. *)
    None

let sanitize text =
  String.map (fun c ->
    if Char.code c < 32 then ' ' else c
  ) text

(* If we were willing to depend on [Str], we could implement [compress] as
   follows:

   let compress text =
     Str.global_replace (Str.regexp "[ \t\n\r]+") " " text

 *)

let rec compress n b i j skipping =
  if j < n then
    let c, j = Bytes.get b j, j + 1 in
    match c with
    | ' ' | '\t' | '\n' | '\r' ->
        let i = if not skipping then (Bytes.set b i ' '; i + 1) else i in
        let skipping = true in
        compress n b i j skipping
    | _ ->
        let i = Bytes.set b i c; i + 1 in
        let skipping = false in
        compress n b i j skipping
  else
    Bytes.sub_string b 0 i

let compress text =
  let b = Bytes.of_string text in
  let n = Bytes.length b in
  compress n b 0 0 false

let shorten k text =
  let n = String.length text in
  if n <= 2 * k + 3 then
    text
  else
    String.sub text 0 k ^
    "..." ^
    String.sub text (n - k) k
