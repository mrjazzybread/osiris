From stdpp Require Import base tactics.
From stdpp Require Import options.

From osiris Require Import base.
From osiris.logic Require Import list_z.
From osiris.lang Require Import syntax encode.

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

Lemma τs_ind (P : ∀ τs : types, Prop) :
  (∀ T (H : Encode T), P (Tbase T)) →
  (∀ T (H : Encode T) (b : types), P b → P (@Tcons _ H b)) →
  ∀ TT, P TT.
Proof.
  intros ? HS TT; induction TT as [|T b IH]; simpl;
    try done; by apply HS.
Qed.

(** Coercion from [types] to [Type]. *)

(* For example, [coerce_to_type (Tcons nat (Tcons Z (Tbase Z)))] should
   produce the type [(nat * (Z * Z))]. *)

Fixpoint coerce_to_type (τ : types) : Type :=
  match τ with
  | Tbase X    => X
  | Tcons X τ' => X * coerce_to_type τ'
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
  | Tbase X => λ (F : Tbase X -#> U) (x : Tbase X), F x
  | Tcons X r => λ (F : Tcons _ r -#> U) '(pair x xs : X * coerce_to_type r),
      tapp (F x) xs
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
  (format "'τ[' '[hv' x ; .. ; y ; z ']' ]").
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

Lemma tforall_unroll `{Encode X} (τ : types) (P : Tcons X τ -> Prop) :
  (∀# (x : Tcons X τ), P x) = (∀ (x : X), ∀# (v : τ), P (x, v)).
Proof. reflexivity. Qed.

Lemma forall_unroll `{Encode X} (τ : types) (P : Tcons X τ -> Prop) :
  (∀ (x : Tcons X τ), P x) <-> (∀ (x : X), ∀ (v : τ), P (x, v)).
Proof.
  rewrite <- (tforall_equiv P). rewrite tforall_unroll.
  split; intros HP x; by apply (tforall_equiv).
Qed.

Section types_helpers.

  Fixpoint to_vals {τ : types} : τ -> list val :=
    match τ with
    | Tbase _ => λ x, [#x]
    | @type_nel.Tcons X H b => λ '(x, xs), #x :: @to_vals b xs
    end.

  Global Instance observe_types (τ : types) : Observe τ (list val) :=
    { observe τ := to_vals τ }.

  Fixpoint τ_length (τ : types) : Z :=
    match τ with
    | Tbase _ => 1%Z
    | type_nel.Tcons _ τ => 1 + τ_length τ
    end.

  Lemma to_vals_length (τ : types) :
    ∀ (xs : τ), list_z.length (to_vals xs) = τ_length τ.
  Proof.
    induction τ.
    - intros x. simpl. unfold tapp. by simpl.
    - intros (x & xs). simpl. length.
      rewrite IHτ. lia.
  Qed.

  Instance types_lookup : Lookup Z Type types :=
    λ i xs, if decide (i < 0)%Z then None else
      let fix go (i : nat) (τ : types) {struct τ} : option Type :=
        match τ, i with
        | Tbase X, 0%nat => Some X
        | Tbase _, _ => None
        | type_nel.Tcons X _, 0%nat => Some X
        | type_nel.Tcons _ τ, (S i0) => go i0 τ
        end
        in
      go (Z.to_nat i) xs.

  Instance types_lookup_total : LookupTotal Z Type types :=
    λ i xs, if decide (i < 0)%Z then ()%type else
      let fix go (i : nat) (τ : types) {struct τ} : Type :=
        match τ, i with
        | Tbase X, 0%nat => X
        | Tbase _, _ => unit
        | type_nel.Tcons X _, 0%nat => X
        | type_nel.Tcons _ τ, (S i0) => go i0 τ
        end
      in
      go (Z.to_nat i) xs.

  Definition types_go : nat -> types -> Type :=
    fix go (i : nat) (τ : types) {struct τ} : Type :=
      match τ, i with
      | Tbase X, 0%nat => X
      | Tbase _, _ => unit
      | type_nel.Tcons X _, 0%nat => X
      | type_nel.Tcons _ τ', S i0 => go i0 τ'
      end.

  Fixpoint tau_lookup_go (τ : types) (i : nat) : τ -> types_go i τ :=
    match τ, i return τ -> types_go i τ with
    | Tbase X, 0%nat => fun xs => xs
    | Tbase _, _ => fun _ => tt
    | type_nel.Tcons X _, 0%nat => fun xs => fst xs
    | type_nel.Tcons _ τ', S i0 => fun xs => tau_lookup_go τ' i0 (snd xs)
    end.

  Definition τ_lookup_total {τ : types} (f : Z) (xs : τ) : τ !!! f.
  Proof.
    unfold lookup_total, types_lookup_total.
    case_decide.
    - exact tt.
    - exact (tau_lookup_go τ (Z.to_nat f) xs).
  Defined.

  Global Instance encode_types_lookup {τ : types} {f : Z} : Encode (τ !!! f).
  Proof.
    unfold lookup_total, types_lookup_total.
    case_decide. { apply _. }
    generalize (Z.to_nat f).
    induction τ; intros n.
    - destruct n; apply _.
    - destruct n.
      + apply _.
      + apply IHτ.
  Defined.

  Global Instance inhabited_val : Inhabited val :=
    { inhabitant := VUnit }.

  Local Instance Encode_types_aux {τ} n : Encode (types_go n τ).
  Proof.
    revert n.
    induction τ; intros n.
    - simpl. destruct n; apply _.
    - simpl. destruct n; first apply _.
      apply IHτ.
  Defined.

  Local Lemma lookup_total_to_vals_aux {τ : types} (xs : τ) n :
    (to_vals xs) !!! n = #(tau_lookup_go τ n xs).
  Proof.
    revert xs n.
    induction τ as [X H | X H b IH]; intros xs n.
    - destruct n as [|n'] eqn:Hnat; first reflexivity.
      simpl.
      rewrite list.lookup_total_nil. reflexivity.
    - pose proof (Tcons_inv b xs) as [x [xs' ->]].
      simpl.
      destruct n as [|n'] eqn:Hnat; first reflexivity.
      rewrite (list.lookup_total_cons_ne_0 _ _ _); last lia.
      apply IH.
  Qed.

  Lemma lookup_total_to_vals {τ : types} (xs : τ) (f : Z) :
    (to_vals xs) !!! f = #(τ_lookup_total f xs).
  Proof.
    unfold τ_lookup_total, encode_types_lookup, lookup_total, types_lookup_total, listz_lookup_total.
    case_decide as Hlt. { reflexivity. }
    generalize (Z.to_nat f) as n; intros n; clear dependent f.
    apply lookup_total_to_vals_aux.
  Qed.

  Definition valid_field f τ := (0 ≤ f < τ_length τ)%Z.

  Fixpoint tau_insert_go (τ : types) (i : nat) : types_go i τ → τ → τ :=
    match τ, i return types_go i τ → τ → τ with
    | Tbase X, 0%nat        => fun x _ => x
    | Tbase _, _            => fun _ xs => xs
    | type_nel.Tcons X _, 0%nat => fun x xs => (x, snd xs)
    | type_nel.Tcons _ τ', S i0 => fun x xs => (fst xs, tau_insert_go τ' i0 x (snd xs))
    end.

  Definition τ_insert {τ : types} (f : Z) (x : τ !!! f) (xs : τ) : τ.
  Proof.
    unfold lookup_total, types_lookup_total in x.
    revert x. case_decide.
    - intros _. exact xs.
    - intro x. exact (tau_insert_go τ (Z.to_nat f) x xs).
  Defined.

  Local Lemma insert_to_vals_aux {τ : types} (xs : τ) n (x : types_go n τ) :
    to_vals (tau_insert_go τ n x xs) = <[n := #x]> (to_vals xs).
  Proof.
    revert xs n x.
    induction τ as [X H | X H b IH]; intros xs n x.
    - destruct n as [|n']; first reflexivity.
      simpl. update. reflexivity.
    - pose proof (Tcons_inv b xs) as [y [xs' ->]].
      simpl.
      destruct n as [|n']; simpl.
      + reflexivity.
      + rewrite IH. reflexivity.
  Qed.

  Lemma insert_to_vals {τ : types} (xs : τ) (f : Z) (x : τ !!! f) :
    to_vals (τ_insert f x xs) = <[ f := #x ]> (to_vals xs).
  Proof.
    revert x.
    unfold τ_insert, encode_types_lookup, lookup_total, types_lookup_total, insert, listz_insert.
    case_decide as Hlt. { auto. }
    generalize (Z.to_nat f) as n; intros n; clear dependent f.
    intros x.
    apply insert_to_vals_aux.
  Qed.

End types_helpers.

Notation "xs !!τ f" := (τ_lookup_total f xs) (at level 20).
Notation "<[ f τ= x ]> xs" := (τ_insert f x xs)
  (at level 5, right associativity, format "<[  f  τ=  x  ]>  xs").

(** Quantifiers *)

From iris.bi Require Import interface.
From iris.base_logic.lib Require Import iprop.
Include universes.


  Definition bi_tforall {PROP : bi} {τ : types} (Ψ : τ → PROP) : PROP :=
    tfold (λ (T : Type@{_}) (b : T → PROP), ∀ x : T, b x)%I Datatypes.id (tbind Ψ).
  Global Arguments bi_tforall {_ !_} _ /.
  Definition bi_texist {PROP : bi} {τ : types} (Ψ : τ → PROP) : PROP :=
    tfold (@bi_exist PROP) Datatypes.id (@tbind PROP τ Ψ).
  Global Arguments bi_texist {_ !_} _ /.

  Notation "'∀#' x .. y , P" := (bi_tforall (λ x, .. (bi_tforall (λ y, P)) .. ))
                                (at level 200, x binder, y binder, right associativity,
                                  format "∀#  x  ..  y ,  P") : bi_scope.
  Notation "'∃#' x .. y , P" := (bi_texist (λ x, .. (bi_texist (λ y, P)) .. ))
                                (at level 200, x binder, y binder, right associativity,
                                  format "∃#  x  ..  y ,  P") : bi_scope.


  Lemma bi_tforall_equiv {Σ} {τ : types} (P : τ → iProp Σ) :
    (∀# xs, P xs)%I ≡ (∀ xs, P xs)%I.
  Proof.
    unfold bi_tforall.
    induction τ as [|X H τ IH].
    - simpl; done.
    - apply bi.iff_equiv. { apply _. } { apply _. }
      simpl. apply bi.equiv_iff. apply bi.equiv_entails_2.
      + apply bi.forall_intro. intros [x xs].
        specialize (IH (λ xs, P (x, xs))). simpl in IH.
        etransitivity. { apply (bi.forall_elim x). }
        etransitivity. { apply bi.equiv_entails_1_1. apply IH. }
        apply (bi.forall_elim (Ψ:=λ xs, P (x, xs))).
      + apply bi.forall_intro. intro x.
        specialize (IH (λ xs, P (x, xs))).
        etransitivity. 2:{ apply bi.equiv_entails_1_2. apply IH. }
        apply bi.forall_intro. intros xs.
        apply bi.forall_elim.
  Qed.


  Lemma bi_texist_equiv {Σ} {τ : types} (P : τ → iProp Σ) :
    (∃# xs, P xs)%I ≡ (∃ xs, P xs)%I.
  Proof.
    unfold bi_tforall.
    induction τ as [|X H τ IH].
    - simpl; done.
    - apply bi.iff_equiv. { apply _. } { apply _. }
      simpl. apply bi.equiv_iff. apply bi.equiv_entails_2.
      + apply bi.exist_elim. intro x.
        specialize (IH (λ xs, P (x, xs))). simpl in IH.
        etransitivity. { apply bi.equiv_entails_1_1. apply IH. }
        apply bi.exist_elim. intro xs.
        apply bi.exist_intro.
      + apply bi.exist_elim. intros [x xs].
        etransitivity. 2:{ apply (bi.exist_intro x). }
        simpl.
        etransitivity. 2:{ apply bi.equiv_entails_1_2. apply IH. }
        simpl.
        apply (bi.exist_intro (Ψ:=λ xs, P (x, xs))).
  Qed.
