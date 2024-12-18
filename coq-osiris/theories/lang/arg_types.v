(** This file is a based off of stdpp's implementation of telescopes.
    The original can be found at
    [https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.telescopes.html] *)

From stdpp Require Import base tactics.
From stdpp Require Import options.

From osiris.lang Require Import syntax encode.

From Coq Require Import Wellfounded.Inverse_Image.

(** Heterogeneous non-empty lists over encodable (non-empty) types. *)

Inductive arg_type : Type :=
| Arg1 (X : Type) (_ : Encode X) : arg_type
| ArgS (X : Type) (_ : Encode X) : arg_type -> arg_type.

Global Arguments Arg1 _ {_}.
Global Arguments ArgS _ {_} _.

Fixpoint args_fun (arg_τ : arg_type) (T : Type) : Type :=
  match arg_τ with
  | Arg1 X => ∀ (x : X), T
  | ArgS X arg_τ' => ∀ (x : X), args_fun arg_τ' T
  end.

Notation "arg_τ -#> A" :=
  (args_fun arg_τ A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [args_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition args_fold {X Y} {arg_τ : arg_type} (step : ∀ {A : Type}, (A → Y) → Y) (base : X → Y)
  : (arg_τ -#> X) → Y :=
  (fix rec {arg_τ} : (arg_τ -#> X) → Y :=
     match arg_τ as arg_τ return (arg_τ -#> X) → Y with
     | Arg1 T => λ f, step (λ x, base (f x))
     | ArgS T arg_τ' => λ f, step (λ x, @rec arg_τ' (f x))
     end) arg_τ.
Global Arguments args_fold {_ _ !_} _ _ /.

(** A duplication of the type [sigT] to avoid any connection to other universes
 *)
Record arg_cons (X : Type) (T : Type) : Type := ArgCons
  { arg_head : X;
    arg_tail : T }.
Global Arguments ArgCons {_ _} _ _.
Global Arguments arg_head {_ _} _.
Global Arguments arg_tail {_ _} _.

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Fixpoint arg_to_type (t : arg_type) : Type :=
  match t with
  | Arg1 X => X
  | ArgS X arg_τ => arg_cons X (arg_to_type arg_τ)
  end.
Global Arguments arg_to_type _ : simpl never.

(* Coq has no idea that [arg_cons] has anything to do with
   telescopes. This only becomes a problem when concrete telescope arguments
   (of concrete telescopes) need to be typechecked. To work around this, we
   annotate the notations below with extra information to guide unification.
 *)

Notation TArg1 a := (a : arg_to_type (Arg1 _)) (only parsing).
(* The casts and annotations are necessary for Coq to typecheck nested [TArgS]
   as well as the final [TArg1] in a chain of [TArgS]. *)
Notation TArgS a b :=
  (@ArgCons _ (arg_to_type _) a b : (arg_to_type (ArgS _ _))) (only parsing).
Coercion arg_to_type : arg_type >-> Sortclass.

Lemma arg_ind (P : ∀ TT, arg_to_type TT → Prop) :
  (∀ T (H : Encode T) t, P (Arg1 T) (TArg1 t)) →
  (∀ T (H : Encode T) (b : arg_type) x xs, P b xs → P (@ArgS _ H b) (TArgS x xs)) →
  ∀ TT (xs : arg_to_type TT), P TT xs.
Proof.
  intros H0 HS TT. induction TT as [|T b IH]; simpl.
  - apply H0.
  - intros [x xs]. by apply HS.
Qed.

Fixpoint arg_app {arg_τ : arg_type} {U} : (arg_τ -#> U) -> arg_τ → U :=
  match arg_τ as arg_τ return (arg_τ -#> U) -> arg_τ → U with
  | Arg1 X => λ F x, F x
  | ArgS _ r => λ (F : ArgS _ r -#> U) '(ArgCons x b),
      arg_app (F x) b
  end.
(* The bidirectionality hint [&] simplifies defining arg_app-based notation
such as the atomic updates and atomic triples in Iris. *)
Global Arguments arg_app {!_ _} & _ !_ /.
Global Coercion arg_app : args_fun >-> Funclass.

(** Inversion lemma for [arg_to_type] *)
Lemma arg_inv {arg_τ : arg_type} (a : arg_to_type arg_τ) :
  match arg_τ as arg_τ return arg_to_type arg_τ → Prop with
  | Arg1 _ => λ a, ∃ x, a = TArg1 x
  | ArgS _ f => λ a, ∃ x a', a = TArgS x a'
  end a.
Proof. destruct arg_τ; [ | destruct a ]; eauto. Qed.
Lemma arg_1_inv `{Encode X} (a : Arg1 X) : ∃ x, a = TArg1 x.
Proof. exact (arg_inv a). Qed.
Lemma arg_S_inv `{H : Encode X} {arg_τ : arg_type} (a : @ArgS _ H arg_τ) :
  ∃ x a', a = TArgS x a'.
Proof. exact (arg_inv a). Qed.

(** Map below a [args_fun] *)
Fixpoint args_map {T U} {arg_τ : arg_type} : (T → U) → (arg_τ -#> T) → arg_τ -#> U :=
  match arg_τ as arg_τ return (T → U) → (arg_τ -#> T) → arg_τ -#> U with
  | Arg1 X => λ (F : T → U) (f : X -> T) (x : X), F (f x)
  | @ArgS X _ arg_τ' => λ (F : T → U) (f : ArgS _ arg_τ' -#> T) (x : X),
                  args_map F (f x)
  end.
Global Arguments args_map {_ _ !_} _ _ /.

Lemma args_map_app {T U} {arg_τ : arg_type} (F : T → U) (t : arg_τ -#> T) (x : arg_τ) :
  (args_map F t) x = F (t x).
Proof.
  induction arg_τ as [|X H f IH]; simpl in *.
  - destruct (arg_1_inv x) as [x' ->]. done.
  - destruct (arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
Qed.

Global Instance arg_fmap {arg_τ : arg_type} : FMap (args_fun arg_τ) := λ T U, args_map.

Lemma args_fmap_app {T U} {arg_τ : arg_type} (F : T → U) (t : arg_τ -#> T) (x : arg_τ) :
  (F <$> t) x = F (t x).
Proof. apply args_map_app. Qed.

(** Operate below [args_fun]s with argument [arg_τ]. *)
Fixpoint arg_bind {U} {arg_τ : arg_type} : (arg_τ → U) → arg_τ -#> U :=
  match arg_τ as arg_τ return (arg_τ → U) → arg_τ -#> U with
  | Arg1 X => λ F (x : X), F x
  | @ArgS X _ arg_τ' => λ (F : ArgS _ arg_τ' → U) (x : X),
      arg_bind (λ a, F (TArgS x a))
  end.
Global Arguments arg_bind {_ !_} _.

(* Show that arg_app ∘ arg_bind is the identity. *)
Lemma args_app_bind {U} {arg_τ : arg_type} (f : arg_τ → U) x :
  (arg_bind f) x = f x.
Proof.
  induction arg_τ as [|X H b IH]; simpl in *.
  - destruct (arg_1_inv x) as [x' ->]. done.
  - destruct (arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
Qed.

(** We can define the identity function and composition of the [-#>] function
space. *)
Definition args_fun_id {arg_τ : arg_type} : arg_τ -#> arg_τ := arg_bind id.

Lemma args_fun_id_eq {arg_τ : arg_type} (x : arg_τ) :
  args_fun_id x = x.
Proof. unfold args_fun_id. rewrite args_app_bind. done. Qed.

Definition args_fun_compose {TT1 TT2 TT3 : arg_type} :
  (TT2 -#> TT3) → (TT1 -#> TT2) → (TT1 -#> TT3) :=
  λ t1 t2, arg_bind (compose (arg_app t1) (arg_app t2)).

Lemma args_fun_compose_eq {TT1 TT2 TT3 : arg_type} (f : TT2 -#> TT3) (g : TT1 -#> TT2) x :
  args_fun_compose f g $ x = (f ∘ g) x.
Proof. unfold args_fun_compose. rewrite args_app_bind. done. Qed.

(** Notation *)
Notation "'tele[' x ; .. ; y ; z ]" :=
  (ArgS x (.. (ArgS y (Arg1 z)) ..))
  (format "'tele['  '[hv' x ; .. ; y ; z ']' ]").
Notation "'tele[' x ]" := (Arg1 x)
  (format "tele[ x ]").

Notation "'tele_arg[' x ; .. ; y ; z ]" :=
  (TArgS x ( .. (TArgS y (TArg1 z)) ..))
  (format "tele_arg[  '[hv' x ;  .. ;  y ;  z ']' ]").
Notation "'tele_arg[' x ]" := (TArg1 x)
  (format "'tele_arg[' x ]").

(** Notation-compatible telescope mapping *)
(* This adds (args_app ∘ args_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ#' x .. y , e" :=
  (arg_app (arg_bind (λ x, .. (arg_app (arg_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ#'  x  ..  y ']' ,  e") : stdpp_scope.

(** Telescopic quantifiers *)
Definition forallArgs {arg_τ : arg_type} (Ψ : arg_τ → Prop) : Prop :=
  args_fold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) (id) (arg_bind Ψ).
Global Arguments forallArgs {!_} _ /.
Definition existArgs {arg_τ : arg_type} (Ψ : arg_τ → Prop) : Prop :=
  args_fold ex (λ x, x) (arg_bind Ψ).
Global Arguments existArgs {!_} _ /.

Notation "'∀#' x .. y , P" := (forallArgs (λ x, .. (forallArgs (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀#  x  ..  y ,  P") : stdpp_scope.
Notation "'∃#' x .. y , P" := (existArgs (λ x, .. (existArgs (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃#  x  ..  y ,  P") : stdpp_scope.

Lemma forallArgs_forall {arg_τ : arg_type} (Ψ : arg_τ → Prop) :
  forallArgs Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold forallArgs. induction arg_τ as [|X H ft IH].
  - simpl. split; done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

Lemma etexist_exist {arg_τ : arg_type} (Ψ : arg_τ → Prop) :
  existArgs Ψ ↔ ex Ψ.
Proof.
  symmetry. induction arg_τ as [|X H ft IH].
  - simpl. split; done.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH (λ a, Ψ (TArgS x a))). eauto.
    + rewrite <-(IH (λ a, Ψ (TArgS p a))).
      intros [??]. eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Global Typeclasses Opaque forallArgs existArgs.
Global Hint Extern 1 (forallArgs _) =>
  progress cbn [forallArgs args_fold arg_bind arg_app] : typeclass_instances.
Global Hint Extern 1 (existArgs _) =>
  progress cbn [existArgs args_fold arg_bind arg_app] : typeclass_instances.

Fixpoint to_vals_aux {TT : arg_type} : TT -#> list val :=
  match TT as TT with
  | @Arg1 X H => arg_bind (λ x, [#x])
  | @ArgS X H b =>
      λ (x : X), @arg_bind _ b (λ tt, #x :: (to_vals_aux tt))
  end.

Definition to_vals {TT : arg_type} (args : TT) : list val :=
  to_vals_aux args.

Lemma spec_once `{Encode X} (arg_τ : arg_type) (P : ArgS X arg_τ -> Prop) :
  (∀# (args : ArgS X arg_τ), P args) = (∀ (x : X), ∀# (args : arg_τ), P {| arg_head := x; arg_tail := args |}).
Proof. reflexivity. Qed.

Lemma spec_once_tele `{Encode X} (arg_τ : arg_type) (P : ArgS X arg_τ -> Prop) :
  (∀ (args : ArgS X arg_τ), P args) <-> (∀ (x : X), ∀ (args : arg_τ), P {| arg_head := x; arg_tail := args |}).
Proof.
  rewrite <- (forallArgs_forall P). rewrite spec_once.
  split; intros HP x; by apply (forallArgs_forall).
Qed.

(** [to_tuple_type] is a mapping from an argument type [arg_τ] to an
    equivalent product type. *)

Fixpoint to_product_type_aux (arg_τ : arg_type) : Type -> Type :=
  match arg_τ with
  | Arg1 X => λ Y, prod Y X
  | ArgS X arg_τ' => λ Y, (to_product_type_aux arg_τ') (prod Y X)
  end.

Definition to_product_type (arg_τ : arg_type) : Type :=
  match arg_τ with
  | Arg1 X => X
  | ArgS X arg_τ' => (to_product_type_aux arg_τ') X
  end.

Arguments to_product_type_aux / arg_τ.
Arguments to_product_type / arg_τ.

Lemma ttt_eq2 `{Encode X, Encode Y} (arg_τ : arg_type) :
  to_product_type (ArgS (X * Y) arg_τ) -> to_product_type (ArgS X (ArgS Y arg_τ)).
Proof. done. Defined.

(** [to_tuple] maps an argument of type [arg_τ] to a tuple of type
    [to_product_type arg_τ]. *)

Fixpoint to_tuple_aux `{Encode Y} {arg_τ : arg_type}
  (args : arg_τ) : Y -> to_product_type (ArgS Y arg_τ) :=
  match arg_τ return arg_τ -> Y -> to_product_type (ArgS Y arg_τ) with
  | Arg1 X => λ (args : X) (y : Y),
      (y, args)
  | ArgS X arg_τ' =>
      λ args (y : Y),
      let x := args.(arg_head) in
      let args := args.(arg_tail) in
      ttt_eq2 _ ((to_tuple_aux args) (y, x))
  end args.

Definition to_tuple {arg_τ : arg_type} (args : arg_τ) : to_product_type arg_τ :=
  match arg_τ return arg_τ -> to_product_type arg_τ with
  | Arg1 X => λ (x : X), x
  | ArgS X arg_τ' =>
      λ args,
      let x := args.(arg_head) in
      let args := args.(arg_tail) in
      (to_tuple_aux args) x
  end args.

Arguments to_tuple_aux {_ _ !_} args /.
Arguments to_tuple {!_} args /.

(* [wf_argTuples] lifts a well-founded order on a product type to the
   equivalent argument type. *)

(* TODO Move *)

Lemma wf_argTuples {arg_τ : arg_type} (R : to_product_type arg_τ -> to_product_type arg_τ -> Prop) :
  well_founded R ->
  well_founded (λ (arg1 arg2 : arg_τ), R (to_tuple arg1) (to_tuple arg2)).
Proof. intros. by apply wf_inverse_image. Qed.
