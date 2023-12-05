open Lexing

(* [extract text (pos1, pos2)] extracts the sub-string of [text] delimited
   by the positions [pos1] and [pos2]. *)

val extract: string -> position * position -> string option

(* [sanitize text] eliminates any special characters from the text [text].
   A special character is a character whose ASCII code is less than 32.
   Every special character is replaced with a single space character. *)

val sanitize: string -> string

(* [compress text] replaces every run of at least one whitespace character
   with exactly one space character. *)

val compress: string -> string

(* [shorten k text] limits the length of [text] to [2k+3] characters. If the
   text is too long, a fragment in the middle is replaced with an ellipsis. *)

val shorten: int -> string -> string
