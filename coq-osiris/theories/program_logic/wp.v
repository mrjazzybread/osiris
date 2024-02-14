From Coq Require Import Program.Equality.

From iris.base_logic.lib Require Import own gen_heap.

From iris.program_logic Require Import language.

From osiris Require Export syntax semantics.

(** *Weakest precondition

  We instantiate an instance of [LanguageMixin], which do not include evaluation
  contexts.

  This is an "exception-handling" Hoare triple, which considers two cases for its
  postcondition, each for the return and exception continuation cases.

    We use the notation

          WP (try m f h)
            {{ | RET x => ϕ x ;
                | EXN x => ψ x }}.

    to indicate that the expression may return a outcome and satisfy postcondition
    ϕ, or throw an exception and satisfy postcondition ψ. *)

(** *Language instance *)
Section exp_def.

  Context {res exn : Type}.

  (* The definition of "outcomes" which is used for the weakest-precondition
    definition.

    i.e. Our postcondition over Osiris programs can be over either a pure result
    [Res r] or an exceptional result [Exn e]. *)
  Variant outcome :=
    | Res (r : res)
    | Exn (e : exn).

  (* Instantiation of (non-context based) Iris language for Osiris. *)
  Notation exp := (micro res exn).

  (* Naive projection between outcomes and expressions. *)
  Definition of_outcome (v : outcome) : exp :=
    match v with
    | Res r => Ret r
    | Exn e => Throw e
    end.

  Definition to_outcome (e : exp) : option outcome :=
    match e with
    | Ret a => Some (Res a)
    | Throw e => Some (Exn e)
    | _ => None
    end.

  (* Lifting specifications in Coq *)
  Definition lift_pure (ϕ : res -> Prop) (v : outcome) : Prop :=
    match v with
    | Res r => ϕ r
    | Exn _ => False
    end.

  Definition lift_exn (ψ : exn -> Prop) (v : outcome) : Prop :=
    match v with
    | Exn e => ψ e
    | Res _ => False
    end.

  Definition lift (ϕ : res -> Prop) (ψ : exn -> Prop) (v : outcome) : Prop :=
    match v with
    | Res r => ϕ r
    | Exn e => ψ e
    end.

  Section iProp.

    Context {Σ : gFunctors}.

    Notation iProp := (iProp Σ).

    (* Lifting specifications in Iris logic. *)

    (* [lift_ipure] is especially useful for lifting specifications over pure
      results to specifications which may handle exceptional results. *)
    Definition lift_ipure (ϕ : res -> iProp) (v : outcome) : iProp :=
      match v with
      | Res r => ϕ r
      | Exn _ => False
      end.

    Definition lift_iexn (ψ : exn -> iProp) (v : outcome) : iProp :=
      match v with
      | Exn e => ψ e
      | Res _ => False
      end.

    Definition ilift (ϕ : res -> iProp) (ψ : exn -> iProp) (v : outcome) : iProp :=
      match v with
      | Res r => ϕ r
      | Exn e => ψ e
      end.

    Definition ipure (ϕ : outcome -> iProp) (v : res) : iProp := ϕ (Res v).
    Definition iexn (ψ : outcome -> iProp) (e : exn) : iProp := ψ (Exn e).

  End iProp.

End exp_def.

Notation "ϕ ↑" := (lift_ipure ϕ) (at level 20).
Notation "ψ ⤉ " := (lift_iexn ψ) (at level 30).
Notation "'|' 'RET' x '=>' e ';' '|' 'EXN' y '=>' f " :=
  (ilift (fun x => e) (fun y => f))
(at level 200, right associativity, format
"'[v ' '['  '|'  'RET'  x  '=>'  e ';' ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").

(** *Basic properties about [outcome] *)
Section exp_properties.

  Lemma outcome_roundtrip {A E} (a : @outcome A E) :
    to_outcome (of_outcome a) = Some a.
  Proof.
    destruct a; auto.
  Qed.

  Lemma is_not_ret_or_throw_to_outcome {A E} m :
    is_not_ret m ->
    is_not_throw m ->
    @to_outcome A E m = None.
  Proof.
    intros H; destruct m; inversion H; intros H'; inversion H'; eauto.
  Qed.

  Lemma to_outcome_is_not_ret {A E} (m : micro A E) :
    to_outcome m = None -> is_not_ret m.
  Proof.
    intros H; destruct m; inversion H; eauto.
  Qed.

  Lemma to_outcome_None_bind {A B E} (m1 : micro A E) (m2 : A -> micro B E):
    to_outcome m1 = None ->
    to_outcome (bind m1 m2) = None.
  Proof.
    intros; destruct m1; eauto; inversion H.
  Qed.

  Lemma to_outcome_is_Some {A E} (m : micro A E) v:
    to_outcome m = Some v ->
    (∃ v', v = Exn v' /\ m = Throw v') \/
    (∃ v', v = Res v' /\ m = Ret v').
  Proof.
    intros; destruct m; inversion H; subst; [right | left]; eauto.
  Qed.

  Lemma to_outcome_None_try {A B E' E}
    (m : micro A E') (f : A -> micro B E) (h : E' -> micro B E) :
    to_outcome m = None ->
    to_outcome (try m f h) = None.
  Proof.
    intros; destruct m; eauto; inversion H.
  Qed.

  Lemma step_not_outcome {A E} {σ σ'} {m m' : micro A E} :
    step.step (σ, m) (σ', m') ->
    to_outcome m = None.
  Proof.
    destruct m; inversion 1; try dependent destruction H8; eauto.
  Qed.

End exp_properties.

(** *Typeclass instance for Iris [Language] mixin *)
Section lang_instance.

  Context {res exn : Type}.

  (* N.B.: We ignore the observation and list of expressions for now. *)
  (* TODO: The [exprs] might want to keep track of a log of expressions *)
  Definition prim_step
    (e : micro res exn) (σ : store) (obs : list nat)
    (e' : micro res exn) (σ' : store) (exprs : list (micro res exn)) : Prop :=
    step.step (σ, e) (σ', e') /\ exprs = [].

  Definition osiris_lang_mixin :
    LanguageMixin of_outcome to_outcome prim_step.
  Proof.
    constructor; auto.
    { apply outcome_roundtrip. }
    { intros; destruct e; inversion H; auto. }
    { intros; destruct e; inversion H; auto; subst; inversion H0. }
  Defined.

  Canonical Structure osiris_lang := Language (osiris_lang_mixin).

End lang_instance.

(* -------------------------------------------------------------------------- *)

(* Simple properties about the instantiated language ([reducible/try/step]). *)
Section lang_properties.

  Local Ltac simp_reducible := eexists nil, _, _, nil; split; [ | done].

  Lemma reducible_try {A B E' E}
    (m1 : micro A E') (f : A -> micro B E) (h : E' -> micro B E) σ:
    reducible (Λ := osiris_lang) m1 σ ->
    reducible (Λ := osiris_lang) (try m1 f h) σ.
  Proof.
    intros H; destruct H as (?&?&?&?&?).
    simp_reducible; eapply step_try; apply H.
  Qed.

  Lemma reducible_bind {A B E}
    (m1 : micro A E) (m2 : A -> micro B E) σ:
    reducible (Λ := osiris_lang) m1 σ ->
    reducible (Λ := osiris_lang) (bind m1 m2) σ.
  Proof.
    intros H.
    destruct H as (?&?&?&?&?).
    simp_reducible; eapply step_bind; apply H.
  Qed.

  Lemma can_step_reducible {R E} (e : micro R E) σ :
    can_step (σ, e) <-> reducible e σ.
  Proof.
    split.
    { intros []. destruct x. simp_reducible; apply H. }
    { intros []. destruct H as (?&?&?&?). eexists; apply H. }
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
    #[global] osirisGpreS_iris :: invGpreS Σ;
    #[global] osirisGpreS_inG :: gen_heapGpreS locations.loc syntax.val Σ
  }.

  Class osirisGS := OsirisGS
   { osiris_inG :: osirisGpreS;
    (* This gives us fancy updates (without allowing Later Credits). *)
     osiris_invGS :: invGS_gen HasNoLc Σ;
    (* This gives us a heap, which maps locations to values. *)
     osiris_heapGS :: gen_heapGS locations.loc syntax.val Σ; }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _} : assert.

Definition store_interp {Σ H} (σ : store) :=
  @gen_heap_interp locations.loc _ _ syntax.val Σ H σ.

(** *Iris instantiation *)
#[global] Instance osiris_irisG `{!osirisGS Σ} : forall R E,
  irisGS_gen HasNoLc (@osiris_lang R E) Σ := {
    iris_invGS := osiris_invGS Σ;
    state_interp σ _ _ _ := (store_interp σ)%I;
    fork_post _ := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _ }.

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation *)
Notation "'WP' e @ s ; E {{ 'RET' v , Q } }" := (wp s E e%E (lift_ipure (λ v, Q)))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e {{ 'RET' v , Q } }" := (wp NotStuck ⊤ e%E (lift_ipure (λ v, Q)))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' {{  '[' 'RET'  v ,  '/' Q  ']' } } ']'") : bi_scope.
(* N.B.: we don't use [bi_scope] here to avoid a notation conflict with
  pre-existing notation; might be brittle *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat  ;  Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ NotStuck; ⊤ {{ RET v , Φ v }}).

(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris Require Export syntax semantics lang.
