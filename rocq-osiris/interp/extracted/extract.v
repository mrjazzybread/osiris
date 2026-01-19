From Stdlib Require Import Extraction String Ascii.
From osiris.lang Require notations.
From osiris.semantics Require strategy eval run.
From osiris.stdlib Require Import Stdlib Externals.

(* Suppress warnings of the form "Warning: The identifier Externals__eq contains
   __ which is reserved for the extraction" *)
Set Warnings "-extraction-reserved-identifier".

(* Suppress warnings that are typical to extracted code *)
Set Extraction File Comment "*) [@@@warning ""-4-33-67""] (*".

(* Use some of OCaml's predefined types instead of making new ones *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Realization of axioms *)

(* int_size is defined to be 63 *)
Extract Constant int.int_size => "S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))".
Extract Constant PrimFloat.float => "Float.t".
(* External compare are currently unsupported *)
Extract Constant Externals__compare => "VClo ([], AnonFun (EmptyString, EUnsupported))".
Extract Constant Stdlib__compare => "VClo ([], AnonFun (EmptyString, EUnsupported))".

Separate Extraction
  ascii_of_N list_ascii_of_string
  notations
  strategy
  eval
  run
.
