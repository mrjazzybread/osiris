From stdpp Require Import base tactics.
From stdpp Require Import options.

From osiris.lang Require Import syntax encode.

From Coq Require Import Wellfounded.Inverse_Image.

(** This file defines [type_nel] (synonym: [types]), the type used for the
    argument on encoded function types. *)

(* A heteregeneous and non-empty list over encodable types.
   ("nel" for non-empty list.)

   This structure is used for the definition of [Spec] when
   specifying the type or arguments for a function.
   (See [program_logic/pure/spec_rules.v].) *)

Inductive type_nel : Type :=
| Tbase (τ : Type) (_ : Encode τ) : type_nel
| Tcons (τ : Type) (_ : Encode τ) : type_nel -> type_nel.

Global Arguments Tbase _ {_}.
Global Arguments Tcons _ {_} _.

Notation types := type_nel.

(* The type signature of a function that takes type list [τ]
   as an argument. *)

Fixpoint fun_type (τ : types) (T : Type) : Type :=
  match τ with
  | Tbase X => ∀ (x : X), T
  | Tcons X τ' => ∀ (x : X), fun_type τ' T
  end.

Notation "A -#> B" := (fun_type A B) (at level 99, right associativity).

(* An eliminator for elements of [fun_type]. *)

Definition tfold {X Y} {τ : types}
  (step : ∀ {A : Type}, (A → Y) → Y)
  (base : X → Y)
  : (τ -#> X) → Y :=
(*  We use a [fix] because, for better term-printing in proofs. *)
  (fix rec {τ} : (τ -#> X) → Y :=
     match τ with
     | Tbase T =>
         λ f, step (λ x, base (f x))
     | Tcons T τ' =>
         λ f, step (λ x, @rec τ' (f x))
     end) τ.
Global Arguments tfold {_ _ !_} _ _ /.

(* TODO: Do we want this to be the default inductive principle? *)

Lemma τs_ind (P : ∀ τs : types, Prop) :
  (∀ T (H : Encode T), P (Tbase T)) →
  (∀ T (H : Encode T) (b : types), P b → P (@Tcons _ H b)) →
  ∀ TT, P TT.
Proof.
  intros ? HS TT; induction TT as [|T b IH]; simpl;
    try done; by apply HS.
Qed.

(** Coercion from [types] to [Type]. *)

Fixpoint coerce_to_type (τ : types) : Type :=
  match τ with
  | Tbase X => X
  | Tcons X τ => X * (coerce_to_type τ)
  end.
Global Arguments coerce_to_type _ : simpl never.

(* Coq has no idea that [type_cons] has anything to do with [types].
   This only becomes a problem when concrete arguments of the list need to be
   typechecked. To work around this, we annotate the notations below with
   extra information to guide unification.

   (N.B. Trick and comment from [stdpp].) *)

Notation TBase a :=
  (a : coerce_to_type (Tbase _)) (only parsing).
(* The casts and annotations are necessary for Coq to typecheck nested [TCons]
   as well as the final [TBase] in a chain of [TCons]. *)
Notation TCons a b :=
  (@pair _ (coerce_to_type _) a b : (coerce_to_type (Tcons _ _)))
    (only parsing).

Coercion coerce_to_type : types >-> Sortclass.

(* Apply a function (with formal arguments encoded with [types]) with
   concrete arguments. *)

Fixpoint tapp {τs : types} {U} : (τs -#> U) -> τs → U :=
  match τs with
  | Tbase X => λ F x, F x
  | Tcons _ r => λ (F : Tcons _ r -#> U) '(pair x b),
      tapp (F x) b
  end.
(* The bidirectionality hint [&] simplifies defining arg_app-based notation *)
(* such as the atomic updates and atomic triples in Iris. *)
Global Arguments tapp {!_ _} & _ !_ /.
Global Coercion tapp : fun_type >-> Funclass.

(* Inversion for [coerce_to_type] *)

Lemma tinv {τs : types} (a : τs) :
  match τs as τs return τs → Prop with
  | Tbase X => λ a : X, ∃ x, a = TBase x
  | Tcons _ f => λ a, ∃ x a', a = TCons x a'
  end a.
Proof. destruct τs; [ | destruct a ]; eauto. Qed.
Lemma Tbase_inv `{Encode X} (a : Tbase X) : ∃ x, a = TBase x.
Proof. exact (tinv a). Qed.
Lemma Tcons_inv `{H : Encode X} arg_τ (a : @Tcons _ H arg_τ) :
  ∃ x a', a = TCons x a'.
Proof. exact (tinv a). Qed.

(* Map over the return type of a function (of type [τs -#> T]). *)

Fixpoint tmap {T U} {τs : types} : (T → U) → (τs -#> T) → τs -#> U :=
  match τs with
  | Tbase X =>
      λ (F : T → U) (f : X -> T) (x : X), F (f x)
  | Tcons X arg_τ' =>
      λ (F : T → U) (f : Tcons _ arg_τ' -#> T) (x : X),
        tmap F (f x)
  end.
Global Arguments tmap {_ _ !_} _ _ /.

Lemma tmap_app {T U} {τ : types}
  (F : T → U) (t : τ -#> T) (x : τ) :
  (tmap F t) x = F (t x).
Proof.
  induction τ as [|X H f IH]; simpl in *.
  - destruct (Tbase_inv x) as [x' ->]. done.
  - destruct (Tcons_inv _ x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
Qed.

(* Forms an instance of [Fmap]. *)

Global Instance tfmap {τ} : FMap (fun_type τ) := λ T U, tmap.

Lemma fmap_app {T U} {τ : types} (F : T → U) (t : τ -#> T) (x : τ) :
  (F <$> t) x = F (t x).
Proof. apply tmap_app. Qed.

(** Operate below [fun]s with argument [τ]. *)

Fixpoint tbind {U} {τ : types} : (τ → U) → τ -#> U :=
  match τ with
  | Tbase X => λ F (x : X), F x
  | Tcons X arg_τ' => λ (F : Tcons _ arg_τ' → U) (x : X),
      tbind (λ a, F (TCons x a))
  end.
Global Arguments tbind {_ !_} _.

(* Show that tapp ∘ tbind is the identity. *)

Lemma tapp_bind {U} {τ : types} (f : τ → U) x :
  (tbind f) x = f x.
Proof.
  induction τ as [|X H b IH]; simpl in *.
  - destruct (Tbase_inv x) as [x' ->]. done.
  - destruct (Tcons_inv _ x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
Qed.

(** Identity function. *)

Definition tid {τ : types} : τ -#> τ := tbind id.

Lemma tid_eq {τ : types} (x : τ) :
  tid x = x.
Proof. unfold tid. rewrite tapp_bind. done. Qed.

Definition tcompose {τ1 τ2 τ3 : types} :
  (τ2 -#> τ3) → (τ1 -#> τ2) → (τ1 -#> τ3) :=
  λ t1 t2, tbind (compose (tapp t1) (tapp t2)).

Lemma tcompose_eq {τ1 τ2 τ3 : types}
  (f : τ2 -#> τ3) (g : τ1 -#> τ2) x :
  tcompose f g $ x = (f ∘ g) x.
Proof. unfold tcompose. rewrite tapp_bind. done. Qed.

Notation "'τ[' x ; .. ; y ; z ]" :=
  (Tcons x (.. (Tcons y (Tbase z)) ..))
  (format "'τ['  '[hv' x ; .. ; y ; z ']' ]").
Notation "'τ[' x ]" := (Tbase x)
  (format "τ[ x ]").
(* This adds (tapp ∘ tbind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ#' x .. y , e" :=
  (tbind (λ x, .. ((λ y, e)) .. ))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ#'  x  ..  y ']' ,  e") : stdpp_scope.

(** Quantifiers *)

Definition tforall {τ : types} (Ψ : τ → Prop) : Prop :=
  tfold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) Datatypes.id (tbind Ψ).
Global Arguments tforall {!_} _ /.
Definition texists {τ : types} (Ψ : τ → Prop) : Prop :=
  tfold ex Datatypes.id (tbind Ψ).
Global Arguments texists {!_} _ /.

Notation "'∀#' x .. y , P" := (tforall (λ x, .. (tforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀#  x  ..  y ,  P") : stdpp_scope.
Notation "'∃#' x .. y , P" := (texists (λ x, .. (texists (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃#  x  ..  y ,  P") : stdpp_scope.

Lemma tforall_equiv {τ : types} (Ψ : τ → Prop) :
  tforall Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold tforall. induction τ as [|X H ft IH].
  - simpl. split; done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (Tcons_inv _ a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

Lemma exists_equiv {τ : types} (Ψ : τ → Prop) :
  texists Ψ ↔ ex Ψ.
Proof.
  symmetry. induction τ as [|X H ft IH].
  - simpl. split; done.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (Tcons_inv _ p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH (λ a, Ψ (TCons x a))). eauto.
    + rewrite <-(IH (λ a, Ψ (TCons p a))).
      intros [??]. eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Global Typeclasses Opaque tforall texists.
Global Hint Extern 1 (tforall _) =>
  progress cbn [tforall tfold tbind tapp] : typeclass_instances.
Global Hint Extern 1 (texists _) =>
  progress cbn [texists tfold tbind tapp] : typeclass_instances.

Fixpoint to_vals {τ : types} : τ-#> list val :=
  match τ with
  | Tbase H => tbind (λ x, [#x])
  | @Tcons X H b =>
      λ (x : X), @tbind _ b (λ tt, #x :: (to_vals tt))
  end.

Lemma tforall_unroll `{Encode X} (τ : types) (P : Tcons X τ -> Prop) :
  (∀# (x : Tcons X τ), P x) = (∀ (x : X), ∀# (v : τ), P (x, v)).
Proof. reflexivity. Qed.

Lemma forall_unroll `{Encode X} (τ : types) (P : Tcons X τ -> Prop) :
  (∀ (x : Tcons X τ), P x) <-> (∀ (x : X), ∀ (v : τ), P (x, v)).
Proof.
  rewrite <- (tforall_equiv P). rewrite tforall_unroll.
  split; intros HP x; by apply (tforall_equiv).
Qed.
