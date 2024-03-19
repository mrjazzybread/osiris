From iris.base_logic.lib Require Import own gen_heap.
From iris.algebra Require Import gmap_view dfrac.
From iris.program_logic Require Export weakestpre.

From osiris Require Export syntax semantics.

(* ========================================================================== *)

(** *Iris [Language] instance for Osiris *)

(* [osiris] is an instance of an Iris [Language], i.e. it has a small-step
   semantics and notion of values (here, we use [outcome2]). *)

(* With this instance, the default [wp] (Iris weakest precondition) can be
   derived. We define our custom [ewp] later in this file to reason about
   effectful programs. *)

Section lang_instance.

  Context {res exn : Type}.

  (* N.B.: We ignore the observation and list of expressions for now. *)
  Definition prim_step
    (e : micro res exn) (σ : store) (obs : list nat)
    (e' : micro res exn) (σ' : store) (exprs : list (micro res exn)) : Prop :=
    step.step (σ, e) (σ', e') /\ exprs = [].

  Definition osiris_lang_mixin :
    LanguageMixin inject2 outcome2_opt prim_step.
  Proof.
    constructor; auto.
    { apply outcome2_opt_inject2. }
    { intros * Ho; destruct e; inversion Ho; auto. }
    { intros * Ho; destruct e; inversion Ho; auto; subst; inversion H. }
  Defined.

  Canonical Structure osiris_lang := Language (osiris_lang_mixin).

End lang_instance.

(* -------------------------------------------------------------------------- *)

(** *Basic resource algebra for Osiris *)

(* The store is viewed as an authorative ghost map. *)

Section ghost_instances.

  Context (Σ : gFunctors).

  Class osirisGpreS := {
      #[global] osirisGpreS_iris :: invGpreS Σ;
      #[global] osirisGpreS_inG :: gen_heapGpreS locations.loc step.block Σ
    }.

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_heapGS :: gen_heapGS locations.loc step.block Σ; }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _} : assert.

Definition osiris_state_interp {Σ H} (σ : store) :=
  @gen_heap_interp locations.loc _ _ step.block Σ H σ.

(* -------------------------------------------------------------------------- *)

(** *Iris instantiation *)
#[global] Instance osiris_irisG `{!osirisGS Σ} : forall R E,
    irisGS_gen HasNoLc (@osiris_lang R E) Σ := {
    iris_invGS := osiris_invGS Σ;
    state_interp σ _ _ _ := (osiris_state_interp σ)%I;
    fork_post _ := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _ }.

(* ========================================================================== *)

(** *Effect-aware Weakest Precondition *)

(* The type [handleable A E] represents computations that can be handled by a
   match-expression:

      Either
      (1) a pure computation with result of type A,
      (2) an exception of type [E], or
      (3) a perform effect that performs effect of type [C.eff] and the
          rest of its computation.  *)

Inductive handleable (A E : Type) : Type :=
  HRet : A → handleable A E
| HThrow : E → handleable A E
| HPerform : C.eff -> (outcome2 syntax.val exn -> micro A E) → handleable A E.

Arguments handleable {A E}.

Arguments HRet {A E}.
Arguments HThrow {A E}.
Arguments HPerform {A E}.

(* Check whether a computation is [handleable]. *)
Definition is_handleable {A X} (m : micro A X) : option handleable :=
  match m with
  | Ret v => Some (HRet v)
  | Throw e => Some (HThrow e)
  | Stop CPerform e k => Some (HPerform e k)
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)

From osiris.program_logic Require Export protocols.

Section ewp.

  Context {A X : Type}.

  (* Carrier type of protocols *)
  Context {P : Type}.

  Context `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ}
           `{@protocol_wf Σ P}.

  Definition ewp_pre
    (ewp: coPset -d> micro A X -d> P -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> micro A X -d> P -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    λ E m Ψ φ,
    (match is_handleable m with
      (* [EWP1] *)
      | Some (HRet v) => |={E}=> φ (O2Ret v)
      | Some (HThrow v) => |={E}=> φ (O2Throw v)
      (* [EWP2] *)
      | Some (HPerform v k) =>
         |={E}=> prot_spec Ψ v (fun w : syntax.val => ▷ ewp E (continue k w) Ψ φ)
      (* [EWP3] *)
      | None =>
          ∀ σ ns κ κs n, state_interp σ ns (κ ++ κs) n ={E, ∅}=∗
            ⌜can_step (σ, m)⌝ ∗
            (∀ σ' m', ⌜step.step (σ, m) (σ', m')⌝ ={∅}=∗ ▷ |={∅,E}=>
              (state_interp σ' (S ns) κs n ∗ ewp E m' Ψ φ))
      end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n wp wp' Hwp E m Φ.
    repeat intro.
    do 2 (f_contractive || f_equiv); cycle 1.
    { repeat (f_contractive || f_equiv);
        apply Hwp. }

    repeat (f_contractive || f_equiv).
    intro.
    repeat (f_contractive || f_equiv).
    apply Hwp.
  Qed.

  Definition ewp_def := fixpoint ewp_pre.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e Ψ Φ} : rename.

End ewp.

(* -------------------------------------------------------------------------- *)

(** Notation. *)

Notation "'EWP' e @ E <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def E e%E Ψ Φ)
    (at level 20, e, Ψ, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'")
    : bi_scope.

(* -------------------------------------------------------------------------- *)

Section ewp_properties.

Context {A X P : Type}.

Context `{!irisGS_gen HasNoLc (@osiris_lang A X) Σ} `{protocol_wf Σ P}.
Implicit Type P : iProp Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : A.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {E} m Ψ {φ} :
  EWP m @ E <| Ψ |> {{ φ }} ⊣⊢ ewp_pre ewp_def E m Ψ φ.
Proof. rewrite /ewp_def; apply (@fixpoint_unfold _ _ _ ewp_pre). Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n Ψ:
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m Ψ).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ' HΦ.
  ewp_unfold_all.
  repeat ((by rewrite IH; [done|lia|];
          let v := fresh "v" in
          intros v; eapply dist_le; [apply HΦ|lia])
          + (f_contractive || f_equiv)).
  intro.

  (f_contractive || f_equiv). eapply IH; auto.
  intros v; eapply dist_le; [apply HΦ|lia].
Qed.

Global Instance ewp_proper E m Ψ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m Ψ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m n Ψ:
  TCEq (is_handleable m) None →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m Ψ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  do 23 (f_contractive || f_equiv). auto.
Qed.

End ewp_properties.

(* ========================================================================== *)

(* Utility functions for writing postconditions on [ewp] *)

Section lift_specs.

  Context {Σ : gFunctors}.

  Context {A E : Type}.

  Notation iProp := (iProp Σ).

  (* Lifting specifications in Iris logic. *)

  (* [lift_ret_spec] is especially useful for lifting specifications over pure
      results to specifications which may handle exceptional results. *)
  Definition lift_ret_spec (ϕ : A -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Ret r => ϕ r
    | _ => False
    end.

  Definition lift_exn_spec (ψ : E -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Throw e => ψ e
    | _ => False
    end.

  Definition ilift (ϕ : A -> iProp) (ψ : E -> iProp) (v : outcome2 A E) : iProp :=
    match v with
    | O2Ret r => ϕ r
    | O2Throw e => ψ e
    end.

End lift_specs.

(* ========================================================================== *)

(** *Notation *)

Notation "ϕ ↑" := (lift_ret_spec ϕ) (at level 20).
Notation "ψ ⤉ " := (lift_exn_spec ψ) (at level 30).
Notation "'|' 'RET' x '=>' e ';' '|' 'EXN' y '=>' f " :=
  (ilift (fun x => e) (fun y => f))
    (at level 200, right associativity, format
    "'[v ' '['  '|'  'RET'  x  '=>'  e ';' ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation. *)
Notation "'RET' v , Q" :=
  (lift_ret_spec (λ v, Q))
    (at level 20, Q at level 200,
      format "'RET'  v ,  '/' Q") : bi_scope.

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation of an encoded value. *)
Notation "'RET' '#' v , Q" :=
  (lift_ret_spec (λ v', (∃ v, (bi_pure (v' = osiris.lang.encode.encode v)) ∧ Q)%I))
    (at level 20, Q, v at level 200,
      format "'RET'  '#' v ,  '/' Q") : bi_scope.

(* Notation for [ewp] *)

Notation "'EWP' e <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ Φ)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|' '>' {{  '[' Φ  ']' } } ']'") : bi_scope.

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E prot_abort Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e {{ Φ } }" :=
  (ewp_def ⊤ e%E prot_abort Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ '  {{  Φ  } } ']' ']'")
    : bi_scope.

(* N.B.: we don't use [bi_scope] here to avoid a notation conflict with
  pre-existing notation; might be brittle *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat  ;  Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e {{ RET v , Φ v }}).

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E prot_abort Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e @ E {{ 'RET' v , Q } }" :=
  (ewp_def E e%E prot_abort (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  '[' 'RET'  v ,  '/' Q  ']' } } ']' ']'")
    : bi_scope.

Notation "'EWP' e {{ Φ } }" :=
  (ewp_def ⊤ e%E prot_abort Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ '  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e {{ 'RET' v , Q } }" :=
  (ewp_def ⊤ e%E prot_abort (lift_ret_spec (λ v, Q)))
    (at level 20, e, Q at level 200,
      format "'[' 'EWP'  e  '/' '[ '  {{  '[' 'RET'  v ,  '/' Q  ']' } } ']' ']'")
    : bi_scope.


(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris Require Export syntax.
(* LATER: import [semantics] after [eval, pure] compiles *)
From osiris.semantics Require Export code micro step.
