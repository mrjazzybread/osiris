From osiris Require Import base.
From osiris.lang Require Import syntax sugar.

(* The type class [Encode A] stipulates the existence of a function [encode]
   of type [A → val]. This function encodes Coq values of type [A] into
   object-language values of type [val]. *)

Class Encode (A : Type) :=
  { encode: A → val }.

(* A few typical instances. *)

Global Instance Encode_unit : Encode unit :=
  { encode := λ tt, VUnit }.

Global Instance Encode_bool : Encode bool :=
  { encode := λ b, VBool b }.

Global Instance Encode_nat : Encode nat :=
  { encode := λ n, VInt (int.repr (Z.of_nat n)) }.

Global Instance Encode_Z : Encode Z :=
  { encode := λ n, VInt (int.repr n) }.

Global Instance Encode_pair `{Encode A, Encode B} : Encode (A * B) :=
  { encode :=
      λ '(a, b), VPair (encode a) (encode b) }.

Global Instance Encode_option `{Encode A} : Encode (option A) :=
  { encode :=
      λ o, match o with None => VNone | Some v => VSome (encode v) end }.

Global Instance Encode_val : Encode val :=
  { encode := λ v, v }.

Fixpoint encode_list `{Encode A} (xs : list A) :=
  match xs with
  | []      => vNil
  | x :: xs => vCons (encode x) (encode_list xs)
  end.

Global Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (xs : list A),
  encode_list xs = encode xs.
Proof.
  reflexivity.
Qed.
