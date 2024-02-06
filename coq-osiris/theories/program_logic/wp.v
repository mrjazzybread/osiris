From Coq Require Import Program.Equality.

From iris.prelude Require Import options.
From iris.base_logic.lib Require Import own.

From iris.program_logic Require Import language.

From osiris Require Export syntax semantics.

(** *Weakest precondition

  We instantiate an instance of [LanguageMixin], which do not include evalueuation
  contexts.

  This is an "exception-handling" Hoare triple, which considers two cases for its
  postcondition, each for the return and exception continuation cases.

    We use the notation

          WP (try m f h)
            {{ | RET x => ϕ x ;
                | EXN x => ψ x }}.

    to indicate that the expression may return a valueue and satisfy postcondition
    ϕ, or throw an exception and satisfy postcondition ψ. *)

(** *Language instance *)
Section exp_def.

  Context {res exn : Type}.

  Variant value :=
    | Res (r : res)
    | Exn (e : exn).

  (* Instantiation of (non-context based) Iris language for Osiris. *)
  Notation exp := (micro res exn).

  (* Naive projection between valueues and expressions. *)
  Definition of_value (v : value) : exp :=
    match v with
    | Res r => Ret r
    | Exn e => Throw e
    end.

  Definition to_value (e : exp) : option value :=
    match e with
    | Ret a => Some (Res a)
    | Throw e => Some (Exn e)
    | _ => None
    end.

  (* Lifting specifications in Coq *)
  Definition lift_pure (ϕ : res -> Prop) (v : value) : Prop :=
    match v with
    | Res r => ϕ r
    | Exn _ => False
    end.

  Definition lift_exn (ψ : exn -> Prop) (v : value) : Prop :=
    match v with
    | Exn e => ψ e
    | Res _ => False
    end.

  Definition lift (ϕ : res -> Prop) (ψ : exn -> Prop) (v : value) : Prop :=
    match v with
    | Res r => ϕ r
    | Exn e => ψ e
    end.

  Section iProp.

    Context {Σ : gFunctors}.

    Notation iProp := (iProp Σ).

    (* Lifting specifications in Iris logic *)
    Definition lift_ipure (ϕ : res -> iProp) (v : value) : iProp :=
      match v with
      | Res r => ϕ r
      | Exn _ => False
      end.

    Definition lift_iexn (ψ : exn -> iProp) (v : value) : iProp :=
      match v with
      | Exn e => ψ e
      | Res _ => False
      end.

    Definition ilift (ϕ : res -> iProp) (ψ : exn -> iProp) (v : value) : iProp :=
      match v with
      | Res r => ϕ r
      | Exn e => ψ e
      end.

    Definition ipure (ϕ : value -> iProp) (v : res) : iProp := ϕ (Res v).

    Definition iexn (ψ : value -> iProp) (e : exn) : iProp := ψ (Exn e).

  End iProp.

End exp_def.

Notation "ϕ ↑" := (lift_ipure ϕ) (at level 20).
Notation "ψ ⤉ " := (lift_iexn ψ) (at level 30).
Notation "'|' 'RET' x '=>' e ';' '|' 'EXN' y '=>' f " :=
  (ilift (fun x => e) (fun y => f))
(at level 200, right associativity, format
"'[v ' '['  '|'  'RET'  x  '=>'  e ';' ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").


Section exp_properties.

  Lemma is_not_ret_or_throw_to_value {A E} m :
    is_not_ret m ->
    is_not_throw m ->
    @to_value A E m = None.
  Proof.
    intros H; destruct m; inversion H; intros H'; inversion H'; eauto.
  Qed.

  Lemma to_value_is_not_ret {A E} (m : micro A E) :
    to_value m = None -> is_not_ret m.
  Proof.
    intros H; destruct m; inversion H; eauto.
  Qed.

  Lemma to_value_None_bind {A B E} (m1 : micro A E) (m2 : A -> micro B E):
    to_value m1 = None ->
    to_value (bind m1 m2) = None.
  Proof.
    intros; destruct m1; eauto; inversion H.
  Qed.

  Lemma to_value_is_Some {A E} (m : micro A E) v:
    to_value m = Some v ->
    (∃ v', v = Exn v' /\ m = Throw v') \/
    (∃ v', v = Res v' /\ m = Ret v').
  Proof.
    intros; destruct m; inversion H; subst; [right | left]; eauto.
  Qed.

  Lemma to_value_None_try {A B E' E}
    (m : micro A E') (f : A -> micro B E) (h : E' -> micro B E) :
    to_value m = None ->
    to_value (try m f h) = None.
  Proof.
    intros; destruct m; eauto; inversion H.
  Qed.

  Lemma step_not_value {A E} {σ σ'} {m m' : micro A E} :
    step.step (σ, m) (σ', m') ->
    to_value m = None.
  Proof.
    destruct m; inversion 1; try dependent destruction H8; eauto.
  Qed.

End exp_properties.

Section lang_instance.

  Context {res exn : Type}.

  (* N.B.: We ignore the observation and list of expressions for now. *)
  Definition prim_step
    (e : micro res exn) (σ : store) (obs : list nat)
    (e' : micro res exn) (σ' : store) (exprs : list (micro res exn)) : Prop :=
    step.step (σ, e) (σ', e') /\ exprs = [].

  Definition osiris_lang_mixin :
    LanguageMixin of_value to_value prim_step.
  Proof.
    constructor; auto.
    { intros; destruct v; auto. }
    { intros; destruct e; inversion H; auto. }
    { intros; destruct e; inversion H; auto; subst; inversion H0. }
  Defined.

  Canonical Structure osiris_lang := Language (osiris_lang_mixin).

End lang_instance.

(* -------------------------------------------------------------------------- *)

(* Simple properties about the instantiated language ([reducible/try/step]). *)

Section lang_properties.

  Lemma reducible_try {A B E' E}
    (m1 : micro A E') (f : A -> micro B E) (h : E' -> micro B E) σ:
    reducible (Λ := osiris_lang) m1 σ ->
    reducible (Λ := osiris_lang) (try m1 f h) σ.
  Proof.
    intros H.
    destruct H as (?&?&?&?&?).
    repeat eexists; eapply step_try; apply H.
    Unshelve. all: eauto.
  Qed.

  Lemma reducible_bind {A B E}
    (m1 : micro A E) (m2 : A -> micro B E) σ:
    reducible (Λ := osiris_lang) m1 σ ->
    reducible (Λ := osiris_lang) (bind m1 m2) σ.
  Proof.
    intros H.
    destruct H as (?&?&?&?&?).
    repeat eexists; eapply step_bind; apply H.
    Unshelve. all: eauto.
  Qed.

  Lemma can_step_reducible {R E} (e : micro R E) σ :
    can_step (σ, e) <-> reducible e σ.
  Proof.
    split.
    { intros []. destruct x. repeat eexists; apply H. }
    { intros []. destruct H as (?&?&?&?). repeat eexists; apply H. }
    Unshelve. all : exact nil.
  Qed.

  Lemma prim_step_simp {A E} e σ es obs e' σ':
    prim_step e σ es e' σ' obs ->
    step.step (A := A) (E := E) (σ, e) (σ', e').
  Proof.
    by intros [].
  Qed.

End lang_properties.

(** *Basic resource algebra for Osiris
  (store can be represented as an authoritative gmap, for now.) *)
From iris.algebra Require Import gmap_view.

From iris.algebra Require Export dfrac.
From iris.program_logic Require Export weakestpre.

Section ghost_instances.

  Context (Σ : gFunctors).

  Class osirisGpreS := {
    osirisGpreS_inG :: inG Σ (gmap_viewR locations.loc (leibnizO syntax.val))
  }.

  Class osirisGS := OsirisGS
   { osiris_inG :: osirisGpreS;
     osiris_invGS : invGS_gen HasNoLc Σ;
     osiris_store_name : gname }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _} _ : assert.
#[global] Arguments osiris_store_name {_} _ : assert.

Section definitions.

  Context {Σ : gFunctors} {hG : osirisGS Σ}.

  Definition store_interp (σ : store) : iProp Σ :=
    own (osiris_store_name hG)
      (gmap_view_auth (DfracOwn 1%Qp) (σ : gmap _ (leibnizO _))).

End definitions.

(** *Iris instantiation *)
#[global] Instance osiris_irisG `{!osirisGS Σ} : forall R E,
  irisGS_gen HasNoLc (@osiris_lang R E) Σ := {
    iris_invGS := osiris_invGS Σ;
    state_interp σ _ _ _ := (store_interp σ)%I;
    fork_post _ := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _ }.

From osiris Require Export syntax semantics.
