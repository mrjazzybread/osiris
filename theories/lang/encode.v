From osiris Require Import base.
From osiris.lang Require Import int locations syntax sugar.

(* The type class [Encode A] stipulates the existence of a function [encode]
   of type [A → val]. This function encodes Coq values of type [A] into
   object-language values of type [val]. *)

Class Encode (A : Type) :=
  { encode: A → val }.

(* This declaration is supposed to tell Coq that a goal of the form [Encode ?A]
   should *not* be solved by instantiating [?A] in an arbitrary way. *)

Global Hint Mode Encode + : typeclass_instances.

(* A notation. *)

Notation "# v" := (encode v) (at level 8, format "# v").

(* -------------------------------------------------------------------------- *)

(* The tactic [encode] expects a goal of the form [v = encode x],
   where typically [v] is a known value and [x] is a metavariable.
   Finding a suitable instantiation of [x] amounts to inverting
   the function [encode]. *)

Create HintDb encode.

Ltac encode :=
  eauto with encode.

Local Ltac solve_encode :=
  intros; subst; eauto.

(* -------------------------------------------------------------------------- *)

(* Values. *)

(* Sometimes a value is reflected as itself at the logical level. *)

(* This may be used, for instance, for functions, or for modules. *)
(* TODO clarify when/why this instance is used *)

(* This instance has low priority because it should be used only
   when there is no other choice. *)

Global Instance Encode_val : Encode val :=
  { encode := λ v, v }.

Lemma solve_encode_val v :
  v = #v.
Proof. solve_encode. Qed.

(* This hint is disabled because it creates problems. It can indeed create
   confusion and lead the tactic [encode] to constructing terms that involve
   nested applications of the function [encode] -- something that should
   never happen.

Global Hint Resolve solve_encode_val | 1000 : encode.
 *)

(* -------------------------------------------------------------------------- *)

(* Unit. *)

Global Instance Encode_unit : Encode unit :=
  { encode := λ tt, VUnit }.

Lemma solve_encode_unit x :
  () = x →
  VUnit = #x.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_unit : encode.

(* -------------------------------------------------------------------------- *)

(* Booleans. *)

Global Instance Encode_bool : Encode bool :=
  { encode := λ b, VBool b }.

Lemma solve_encode_false b :
  false = b →
  VFalse = #b.
Proof. solve_encode. Qed.

Lemma solve_encode_true b :
  true = b →
  VTrue = #b.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_false solve_encode_true : encode.

(* -------------------------------------------------------------------------- *)

(* Natural numbers. *)

Global Instance Encode_nat : Encode nat :=
  { encode := λ n, VInt (repr (Z.of_nat n)) }.

Lemma solve_encode_nat i n :
  i = repr (Z.of_nat n) →
  VInt i = #n.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_nat : encode.

(* -------------------------------------------------------------------------- *)

(* Integer numbers. *)

Global Instance Encode_Z : Encode Z :=
  { encode := λ n, VInt (repr n) }.

Lemma solve_encode_int i z :
  i = repr z →
  VInt i = #z.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_int : encode.

(* This should help: *)

Global Hint Resolve
   neg_repr
   add_repr_repr
   sub_repr_repr
   mul_repr_repr
   divs_repr_repr
   mods_repr_repr
   eq_repr_repr
   lt_repr_repr
: encode.

(* TODO add hints that help prove [representable z]. *)

(* -------------------------------------------------------------------------- *)

(* Options. *)

Global Instance Encode_option `{Encode A} : Encode (option A) :=
  { encode :=
      λ o, match o with None => VNone | Some v => VSome #v end }.

Lemma solve_encode_None `{Encode A} (o : option A) :
  None = o →
  VNone = #o.
Proof. solve_encode. Qed.

Lemma solve_encode_Some `{Encode A} v (o : option A) (x : A) :
  Some x = o →
  v = #x →
  VSome v = #o.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_None solve_encode_Some : encode.

(* -------------------------------------------------------------------------- *)

(* Memory locations. *)

(* This instance is needed, for instance, for memory locations. *)

Global Instance Encode_loc : Encode loc :=
  { encode := λ l, VLoc l }.

Lemma solve_encode_loc l :
  VLoc l = #l.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_loc : encode.

(* -------------------------------------------------------------------------- *)

(* Lists. *)

Fixpoint encode_list `{Encode A} (xs : list A) :=
  match xs with
  | []      => vNil
  | x :: xs => vCons #x (encode_list xs)
  end.

Global Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (xs : list A),
  encode_list xs = #xs.
Proof. solve_encode. Qed.

Lemma solve_encode_Nil `{Encode A} (xs : list A) :
  [] = xs →
  vNil = #xs.
Proof. solve_encode. Qed.
  (* TODO If [xs] and [A] are metavariables then Coq will refuse
          to apply this lemma because it cannot guess [A].
          A work-around is to explicitly add [@solve_encode_Nil A]
          in the context for a specific type [A] of interest. *)

Lemma solve_encode_Cons `{Encode A} (xs : list A) x xs' v1 v2 :
  x :: xs' = xs →
  v1 = #x →
  v2 = #xs' →
  vCons v1 v2 = #xs.
Proof. solve_encode. Qed.

Global Hint Resolve
  encode_list_is_encode
  solve_encode_Nil solve_encode_Cons
: encode.

(* -------------------------------------------------------------------------- *)

(* Pairs, or tuples of arity 2. *)

Global Instance Encode_tuple2
  `{Encode A, Encode B}
  : Encode (A * B)
  | 10 (* lower priority than tuple3 and tuple4 below *)
:=
  { encode := λ '(a, b), VPair #a #b }.

Lemma solve_encode_tuple2
  `{Encode A} `{Encode B}
  (a : A) (b : B)
  va vb
  t :
  (a, b) = t →
  va = #a →
  vb = #b →
  VPair va vb = #t.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_tuple2
| 10 (* lower priority than tuple3 and tuple4 below *)
 : encode.

(* -------------------------------------------------------------------------- *)

(* Tuples of arity 3. *)

Global Instance Encode_tuple3
  `{Encode A} `{Encode B} `{Encode C}
  : Encode (A * B * C)
  | 5 (* higher priority than tuple2; lower priority than tuple3 *)
:=
  { encode := λ '(a, b, c), VTuple3 #a #b #c }.

Lemma solve_encode_tuple3
  `{Encode A} `{Encode B} `{Encode C}
  (a : A) (b : B) (c : C)
  va vb vc
  t :
  (a, b, c) = t →
  va = #a →
  vb = #b →
  vc = #c →
  VTuple3 va vb vc = #t.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_tuple3
| 5 (* higher priority than tuple2; lower priority than tuple3 *)
: encode.

(* -------------------------------------------------------------------------- *)

(* Tuples of arity 4. *)

Global Instance Encode_tuple4
  `{Encode A} `{Encode B} `{Encode C} `{Encode D}
  : Encode (A * B * C * D)
  | 0 (* higher priority than tuple2 and tuple3 above *)
:=
  { encode := λ '(a, b, c, d), VTuple4 #a #b #c #d }.

Lemma solve_encode_tuple4
  `{Encode A} `{Encode B} `{Encode C} `{Encode D}
  (a : A) (b : B) (c : C) (d : D)
  va vb vc vd
  t :
  (a, b, c, d) = t →
  va = #a →
  vb = #b →
  vc = #c →
  vd = #d →
  VTuple4 va vb vc vd = #t.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_tuple4
| 0 (* higher priority than tuple2 and tuple3 above *)
: encode.
