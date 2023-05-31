From osiris Require Import base.
From osiris.lang Require Import syntax sugar.

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
  { encode := λ n, VInt (int.repr (Z.of_nat n)) }.

Lemma solve_encode_nat i n :
  i = int.repr (Z.of_nat n) →
  VInt i = #n.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_nat : encode.

(* -------------------------------------------------------------------------- *)

(* Integer numbers. *)

Global Instance Encode_Z : Encode Z :=
  { encode := λ n, VInt (int.repr n) }.

Lemma solve_encode_int i z :
  i = int.repr z →
  VInt i = #z.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_int : encode.

(* This should help: *)

Global Hint Resolve
   int.neg_repr
   int.add_repr_repr
   int.sub_repr_repr
   int.mul_repr_repr
   int.divs_repr_repr
   int.mods_repr_repr
   int.eq_repr_repr
   int.lt_repr_repr
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

(* Values. *)

(* This instance is needed, for instance, for memory locations. *)

Global Instance Encode_val : Encode val :=
  { encode := λ v, v }.

Lemma solve_encode_val v :
  v = #v.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_val : encode.

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

(* The lemma [solve_encode_tuple2] has 12 arguments. *)

(* We cannot let [eapply] apply this lemma, as Coq would make
   incorrect choices of the types A, B. *)

Global Hint Extern 1 (_ = _) =>
  notypeclasses refine (@solve_encode_tuple2
    _ _ _ _ _ _ _ _
    _ _ _ _
  )
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

(* The lemma [solve_encode_tuple3] has 17 arguments. *)

Global Hint Extern 1 (_ = _) =>
  notypeclasses refine (@solve_encode_tuple3
    _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _
    _
  )
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

(* The lemma [solve_encode_tuple4] has 22 arguments. *)

Global Hint Extern 1 (_ = _) =>
  notypeclasses refine (@solve_encode_tuple4
    _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _
    _ _ _ _ _ _
  )
  : encode.
