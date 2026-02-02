From osiris Require Import base.
From osiris.semantics Require Import outcome.
From osiris.lang Require Import syntax.
From iris.base_logic.lib Require Import iprop.

(* The type class [Encode A] stipulates the existence of a function [encode]
   of type [A → val]. This function encodes Coq values of type [A] into
   object-language values of type [val]. *)

Class Encode (A : Type) :=
  { encode: A → val }.

(* We will later make [encode] opaque. We keep [encode'] transparent
   to compute the encoding at will. *)

Definition encode' {A : Type} := @encode A.

Lemma encode_encode' {A} :
  ∀ a, (@encode A a) = (encode' a).
Proof. tauto. Qed.

(* This declaration is supposed to tell Coq that a goal of the form [Encode ?A]
   should *not* be solved by instantiating [?A] in an arbitrary way. *)

Global Hint Mode Encode + : typeclass_instances.

(* A notation. *)

Notation "# v" := (encode v) (at level 8, format "# v").

(* -------------------------------------------------------------------------- *)

(* The function [encode] is sometimes, but not always, required to be
   injective. *)

Class EncodeInjective `{Encode A} :=
  { encode_injective : ∀ a1 a2 : A, #a1 = #a2 → a1 = a2 }.

(* -------------------------------------------------------------------------- *)

(* The tactic [encode] expects a goal of the form [v = encode x],
   where typically [v] is a known value and [x] is a metavariable.
   Finding a suitable instantiation of [x] amounts to inverting
   the function [encode]. *)

(* The tactic [encode] either succeeds or leaves the goal intact.
   Use [solve[encode]] if you wish to require success. *)

Create HintDb encode.

Ltac encode :=
  eauto with encode.

Local Ltac solve_encode :=
  intros; subst; eauto.

(* -------------------------------------------------------------------------- *)

(* One justification for [Observe] appears in pure_rules.v, to generalize
   [pure_bind] to more than just [@bind val val] *)

(* Given an encodable value of type [A], it can be observed as a particular
   value [V]. *)
Class Observe A (EncA: Encode A) V : Type :=
  { observe : A -> V }.

Arguments Observe A {EncA} V.
Arguments observe {_ _ _ _}.

Global Instance observe_encode {A} `{Encode A}:
  Observe A val :=
  {| observe := encode |}.

(* NOTE : Do not declare an instance of [Observe val val], as it will
   instantiate evars eagerly to this instance when it is not desired.
   (Even if its weight is very high.) *)

Notation "♯ x" := (observe x) (at level 5, format "♯ x").

Definition returns {A V} `{Observe A V} (φ : A -> Prop):=
  λ (v : V), ∃ a, v = observe a ∧ φ a.


Section lift_specs.

  (* Utility functions for writing postconditions on [ewp] *)

  Context {Σ : gFunctors}.

  Context {A X : Type}.

  (* Lifting specifications in Iris logic. *)

  Definition ilift (ζ : X -d> iProp Σ) (Φ : A -d> iProp Σ) : outcome2 A X -d> iProp Σ :=
    (λ v, match v with
          | O2Ret r => Φ r
          | O2Throw e => ζ e
          end)%I.

  Global Instance ilift_ne n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist n) ==>
            eq ==> (dist n)) ilift.
  Proof. repeat intro; subst; destruct y1; eauto. Qed.

  Global Instance ilift_proper :
    Proper (pointwise_relation _ (≡) ==>
            pointwise_relation _ (≡) ==>
            eq ==> (≡)) ilift.
  Proof. repeat intro; subst; destruct y1; eauto. Qed.

  Definition ireturns {V} `{Observe A V} (Φ : A → iProp Σ) : V → iProp Σ :=
    λ v, (∃ a : A, ⌜v = ♯ a⌝ ∗ Φ a)%I.

End lift_specs.

From osiris.lang Require Import int locations thread_ids notations.

(* -------------------------------------------------------------------------- *)

(* Values. *)

(* Sometimes a value is reflected as itself at the logical level. *)

(* This may be used, for instance, for functions, or for modules. *)
(* Because pure builds in [encode], this instance is needed when writing a [pure]
  judgement about an expression that returns a function. *)

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
  { encode := λ x, let '() := x in VUnit }.
  (* We deconstruct [x] because we want an equation [VUnit = #?x] to
     force an instantiation of [x] with [()]. *)

Lemma solve_encode_unit :
  VUnit = #().
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

(* Booleans, reflected as Coq propositions. *)

(* The function [truth : Prop → bool] maps a Coq proposition
   to the corresponding Boolean value. Defining this function
   requires Hilbert's [ε] operator. *)

From Stdlib Require Import Classical Epsilon.

Definition inh_bool : inhabited bool.
Proof. constructor. constructor. Qed.

Definition truth (P : Prop) : bool :=
  epsilon inh_bool (λ (b : bool), if b then P else ¬P).

(* If [P] is false then [truth P] is [false]. *)

Lemma truth_false (P : Prop) :
  ¬ P →
  truth P = false.
Proof.
  intros H.
  unfold truth.
  assert (existence: exists (b : bool), if b then P else ¬P).
  { exists false. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  match goal with |- context[epsilon ?w ?P] => generalize (epsilon w P) end.
  intros [|]; tauto.
Qed.

Lemma truth_False :
  truth False = false.
Proof.
  eauto using truth_false.
Qed.

(* If [P] is true then [truth P] is [true]. *)

Lemma truth_true (P : Prop) :
  P →
  truth P = true.
Proof.
  intros H.
  unfold truth.
  assert (existence: exists (b : bool), if b then P else ¬P).
  { exists true. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  match goal with |- context[epsilon ?w ?P] => generalize (epsilon w P) end.
  intros [|]; tauto.
Qed.

Lemma truth_True :
  truth True = true.
Proof.
  eauto using truth_true.
Qed.

(* [truth P] determines which of [P] and [¬P] holds. *)

Lemma truth_elim (P : Prop) :
  if truth P then P else ¬P.
Proof.
  case_eq (truth P); intro Heq.
  (* [NNPP] is Peirce's law. *)
  { eapply NNPP. intro H. eapply truth_false in H. congruence. }
  { intro H. eapply truth_true in H. congruence. }
Qed.

(* If [truth P] is [false] then  [P] is false. *)

Lemma truth_false_elim (P : Prop) :
  truth P = false →
  ¬ P.
Proof.
  intros H. generalize (truth_elim P). rewrite H. tauto.
Qed.

(* If [truth P] is [true] then  [P] is true. *)

Lemma truth_true_elim (P : Prop) :
  truth P = true →
  P.
Proof.
  intros H. generalize (truth_elim P). rewrite H. tauto.
Qed.

(* [truth : Prop → bool] is the inverse of [Is_true : bool → Prop]. *)

Lemma truth_Is_true b :
  truth (Is_true b) = b.
Proof.
  destruct b; simpl; [ rewrite truth_True | rewrite truth_False ]; eauto.
Qed.

Lemma Is_true_truth P :
  Is_true (truth P) ↔ P.
Proof.
  generalize (truth_elim P).
  generalize (truth P).
  intros [|]; simpl; tauto.
Qed.

(* The truth of [¬P] is the negation of the truth of [P]. *)

Lemma truth_neg P :
  truth (¬P) = negb (truth P).
Proof.
  generalize (truth_elim P). generalize (truth P).
  intros [|]; simpl; intros.
  { eapply truth_false. tauto. }
  { eapply truth_true. tauto. }
Qed.

(* If [b] reflects [P], [truth P] is [b] *)

Lemma truth_reflect P b : reflect P b → truth P = b.
Proof.
  inversion 1; auto using truth_true, truth_false.
Qed.

(* Similar but formulated in a way [lia] understands *)

Lemma truth_eq_true P b : (b = true ↔ P) → truth P = b.
Proof.
  destruct b; intros.
  - intuition auto using truth_true.
  - assert (¬P) by firstorder congruence.
    auto using truth_false.
Qed.

(* A Coq proposition can be encoded as an OCaml Boolean value. *)

(* In other words, the logical model of an OCaml Boolean value
   can be a Coq proposition. *)

Global Instance Encode_Prop : Encode Prop :=
  { encode := λ P, VBool (truth P) }.

(* Allowing the tactic [encode] to use [solve_encode_False] and
   [solve_encode_True], where [P] is a metavariable, leads Coq to
   instantiate [P] with an arbitrary proposition that happens to be
   provably false or provably true. *)

(* So, the following two lemmas are currently *not* added to the
   hint database [encode]. *)

Lemma solve_encode_False (P : Prop) :
  ¬ P →
  VFalse = #P.
Proof.
  intros H. apply truth_false in H. simpl. rewrite H. reflexivity.
Qed.

Lemma solve_encode_True (P : Prop) :
  P →
  VTrue = #P.
Proof.
  intros H. apply truth_true in H. simpl. rewrite H. reflexivity.
Qed.

(* Global Hint Resolve solve_encode_False solve_encode_True : encode. *)

Lemma encode_truth (P : Prop) : #(truth P) = #P.
Proof.
  unfold encode, Encode_Prop.
  by destruct (truth P).
Qed.

Lemma iff_truth (P Q : Prop) : P ↔ Q → truth P = truth Q.
Proof.
  generalize (truth_elim P), (truth_elim Q).
  do 2 destruct (truth _); tauto.
Qed.

Lemma iff_encode (P Q : Prop) : P ↔ Q → #P = #Q.
Proof.
  unfold encode, Encode_Prop.
  by intros ->%iff_truth.
Qed.

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

Global Instance Encode_int : Encode int :=
  { encode := λ n, VInt n }.

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
  lnot_repr
  land_repr_repr
  lor_repr_repr
  lxor_repr_repr
  lsl_repr_repr
  lsr_repr_repr
  asr_repr_repr
: encode.

(* -------------------------------------------------------------------------- *)

(* First-class continuations. *)

Global Instance Encode_cont : Encode cont :=
  { encode := λ l, VCont l }.

Lemma solve_encode_cont (l : cont) :
  VCont l = #l.
Proof. solve_encode. Qed.

(* -------------------------------------------------------------------------- *)

(* Environments. *)

Global Instance Encode_env : Encode env :=
  { encode := λ η, VStruct η }.

Lemma solve_encode_env η :
  VStruct η = #η.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_env
| 0 (* higher priority than encoding lists *)
  : encode.

(* -------------------------------------------------------------------------- *)

(* Floats. *)

Global Instance Encode_float : Encode PrimFloat.float :=
  { encode := λ f, VFloat f }.

(* -------------------------------------------------------------------------- *)

(* Char. *)

Global Instance Encode_char: Encode char :=
  { encode := λ f, VChar f }.

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

(* Thread identifiers. *)

(* This instance is needed, for instance, for memory locations. *)

Global Instance Encode_thread : Encode thread :=
  { encode := λ ι, VThread ι }.

Lemma solve_encode_thread ι :
  VThread ι = #ι.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_thread : encode.

(* -------------------------------------------------------------------------- *)

(* Lists. *)

Fixpoint encode_list `{Encode A} (xs : list A) :=
  match xs with
  | []      => VNil
  | x :: xs => VCons #x (encode_list xs)
  end.

Global Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (xs : list A),
  encode_list xs = #xs.
Proof. solve_encode. Qed.

Lemma solve_encode_Nil `{Encode A} (xs : list A) :
  [] = xs →
  VNil = #xs.
Proof. solve_encode. Qed.

Lemma solve_encode_Cons `{Encode A} (xs : list A) x xs' v1 v2 :
  x :: xs' = xs →
  v1 = #x →
  v2 = #xs' →
  VCons v1 v2 = #xs.
Proof. solve_encode. Qed.

Global Hint Resolve
  encode_list_is_encode
  solve_encode_Nil solve_encode_Cons
: encode.

(* Useful for [pure (evals η _) φ ψ]. *)
Global Instance observe_list {A} `{Encode A}:
  Observe (list A) (list val) | 100 :=
  {| observe := (map encode.encode) |}.

Lemma solve_observe_nil A (Enc:Encode A) :
  forall (xs : list A),
    [] = xs →
    nil = ♯xs.
Proof. intros; subst; cbn; eauto. Qed.

Lemma solve_observe_cons {A} {Enc: Encode A} :
  forall (v : val) (a : A) tl vtl (x : list A),
    a :: tl = x ->
    v = # a ->
    vtl = ♯ tl ->
    v :: vtl = ♯ x.
Proof.
  induction tl; intros; subst; eauto.
Qed.

Global Hint Extern 0 (_ :: _ = ♯ _) =>
  simple eapply solve_observe_cons : encode.
Global Hint Extern 100 ([] = ♯ _) =>
  simple eapply solve_observe_nil: encode.

(* -------------------------------------------------------------------------- *)

(* Pairs, or tuples of arity 2. *)

Definition encode_pair `{Encode A, Encode B} : (A * B) -> val :=
  λ '(a, b), VPair #a #b.

Global Instance Encode_tuple2
  `{Encode A, Encode B}
  : Encode (A * B)
  | 10 (* lower priority than tuple3 and tuple4 below *)
:=
  { encode := encode_pair }.

Lemma encode_pair_is_encode `{Encode A, Encode B} :
  ∀ (p : A * B),
    encode_pair p = #p.
Proof. solve_encode. Qed.

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

Global Hint Resolve encode_pair_is_encode solve_encode_tuple2
| 10 (* lower priority than tuple3 and tuple4 below *)
 : encode.

(* -------------------------------------------------------------------------- *)

(* Tuples of arity 3. *)

Global Instance Encode_tuple3
  `{Encode A} `{Encode B} `{Encode C}
  : Encode (A * B * C)
  | 5 (* higher priority than tuple2; lower priority than tuple3 *)
:=
  { encode := λ '(a, b, c), VTuple [ #a; #b; #c] }.

Lemma solve_encode_tuple3
  `{Encode A} `{Encode B} `{Encode C}
  (a : A) (b : B) (c : C)
  va vb vc
  t :
  (a, b, c) = t →
  va = #a →
  vb = #b →
  vc = #c →
  VTuple [va; vb; vc] = #t.
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
  { encode := λ '(a, b, c, d), VTuple [ #a; #b; #c; #d] }.

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
  VTuple [va; vb; vc; vd] = #t.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_tuple4
| 0 (* higher priority than tuple2 and tuple3 above *)
  : encode.

(* -------------------------------------------------------------------------- *)

(* Strings. *)

Global Instance Encode_string : Encode string :=
  { encode := λ s, VString s }.

Lemma encode_string_is_encode s :
  VString s = #s.
Proof. solve_encode. Qed.
