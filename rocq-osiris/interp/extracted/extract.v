From Stdlib Require Import Extraction String Ascii.
From osiris.lang Require notations.
From osiris.semantics Require strategy eval run.
From osiris.stdlib Require Import Stdlib Externals.

(* Suppress warnings of the form "Warning: The identifier Externals__eq contains
   __ which is reserved for the extraction" *)
Set Warnings "-extraction-reserved-identifier -extraction-opaque-accessed -extraction-default-directory".

Set Extraction Output Directory ".".

(* Suppress warnings that are typical to extracted code *)
Set Extraction File Comment "*) [@@@warning ""-4-33-67""] (*".

(* Use some of OCaml's predefined types instead of making new ones *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Realization of axioms *)

(* int_size is defined to be `Sys.word_size - 1`, which is usually 63. *)
Extract Constant int.int_size => "(let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1)) in nat_of_int (Sys.word_size - 1))".
(* max_array_length is defined to be `Sys.max_array_length`, which is usually 2^54 - 1 *)
Extract Constant int.max_array_length => "(let rec pos_of_int n = if n <= 1 then Coq_xH else if n mod 2 = 0 then Coq_xO (pos_of_int (n / 2)) else Coq_xI (pos_of_int (n / 2)) in Zpos (pos_of_int Sys.max_array_length))".
Extract Constant int.max_array_positive => "()".
Extract Constant int.max_array_representable => "()".
Extract Constant PrimFloat.float => "Float.t".
(* External compare are currently unsupported *)
Extract Constant Stdlib__compare => "VClo ([], AnonFun (EmptyString, EUnsupported))".

Separate Extraction
  ascii_of_N list_ascii_of_string
  notations
  strategy
  eval
  run
.
