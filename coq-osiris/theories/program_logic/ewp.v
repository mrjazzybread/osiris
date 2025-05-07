From iris.base_logic.lib Require Import own gen_heap.
From iris.algebra Require Import gmap_view dfrac.
From iris.program_logic Require Export weakestpre.

From osiris.program_logic Require Import wp_step.
From osiris Require Export thread_ids syntax semantics.

Definition discrete_fun2 {A B} := λ (C : A -> B → ofe), ∀ (x : A) (y : B), C x y.

Section discrete_fun2.

  Context {A B : Type} {C : A -> B -> ofe}.
  Implicit Types f g : discrete_fun2 C.

  Global Instance discrete_fun2_dist : Dist (discrete_fun2 C) :=
    λ n (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡{n}≡ g x y.

  Global Instance discrete_fun2_equiv : Equiv (discrete_fun2 C) :=
    λ (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡ g x y.

  Definition discrete_fun2_ofe_mixin : OfeMixin (discrete_fun2 C).
  Proof.
    split.
    - split; [ intros Hequiv n | intros Hdist ].
      + rewrite /dist /discrete_fun2_dist.
        intros x' y'. specialize (Hequiv x' y'). by rewrite Hequiv.
      + rewrite /equiv /discrete_fun2_equiv.
        intros x' y'. apply equiv_dist. intros n.
        specialize (Hdist n x' y'). apply Hdist.
    - intros n. rewrite /dist. split.
      + intros f x y. auto.
      + intros f g Hdist x y.
        symmetry.
        apply Hdist.
      + intros f g h Hdistfg Hdistgh.
        rewrite /discrete_fun2_dist in Hdistfg Hdistgh |-*.
        intros x y.
        transitivity (g x y); auto.
    - intros n m f g Hdist Hlt.
      rewrite /dist /discrete_fun2_dist. intros x y.
      eapply dist_le. apply Hdist. lia.
  Qed.

  Canonical Structure discrete_fun2O : ofe := Ofe (discrete_fun2 C) discrete_fun2_ofe_mixin.

  Program Definition discrete_fun2_chain (c : chain discrete_fun2O)
    (x : A) (y : B) : chain (C x y) := {| chain_car n := c n x y |}.
  Next Obligation. intros c x y n i ?. by apply (chain_cauchy c). Qed.
  Global Program Instance discrete_fun2_cofe `{∀ x y, Cofe (C x y)} : Cofe discrete_fun2O :=
    { compl c x y := compl (discrete_fun2_chain c x y) }.
  Next Obligation. intros ? n c x y. apply (conv_compl n (discrete_fun2_chain c x y)). Qed.

  Global Instance discrete_fun2_inhabited `{∀ x y, Inhabited (C x y)} : Inhabited discrete_fun2O :=
    populate (λ _, inhabitant).

End discrete_fun2.

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
      osiris_heapGS :: gen_heapGS locations.loc step.block Σ;
      (* This gives us a heap, which maps threads to their aliveness. *)
      thread_heapGS :: gen_heapGS thread_ids.thread thread_state Σ;
    }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _ _} : assert.

Definition osiris_state_interp {Σ H} (σ : store) :=
  @gen_heap_interp locations.loc _ _ step.block Σ H σ.

Definition osiris_thread_interp {Σ H} (π : gmap thread thread_state) :=
  @gen_heap_interp thread_ids.thread _ _ thread_state Σ H π.

Definition state_interp {Σ Hs Ht} : (store * threadpool) -> iProp Σ :=
  (λ '(σ, π), @osiris_state_interp Σ Hs σ ∗ @osiris_thread_interp Σ Ht π)%I.


(* Notations for ghost resouces. *)

Notation "l ↦ v" :=
  (pointsto l (DfracOwn 1) v)
    (at level 20, format "l  ↦  v") : bi_scope.

Global Instance osiris_cont_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS cont block Σ.
Proof. unfold cont; simpl. apply osiris_heapGS. assumption. Defined.

Definition isCont `{osirisGS Σ} (k : cont) (sk : outcome2 val exn -> microvx)
  : iProp Σ :=
  gen_heap.pointsto k (DfracOwn 1) (K sk).

Definition isShot `{osirisGS} (k : cont) : iProp Σ :=
  k ↦ Shot.

(* -------------------------------------------------------------------------- *)

(** *Iris instantiation *)
(* #[global] Instance osiris_irisG `{!osirisGS Σ} : forall R E, *)
(*     irisGS_gen HasNoLc (@osiris_lang R E) Σ := { *)
(*     iris_invGS := osiris_invGS Σ; *)
(*     state_interp σ _ _ _ := (osiris_state_interp σ)%I; *)
(*     fork_post _ := True%I; *)
(*     num_laters_per_step _ := 0; *)
(*     state_interp_mono _ _ _ _ := fupd_intro _ _ }. *)

(* ========================================================================== *)

(** *Effect-aware Weakest Precondition *)

(* The type [handleable A E] represents computations that can be handled by a
   match-expression:

      Either
      (1) a pure computation with result of type A,
      (2) an exception of type [E],
      (3) a crash, or
      (4) a perform effect that performs effect of type [C.eff] and the
          rest of its computation.  *)

Inductive ewp_case (A E : Type) : Type :=
  ERet : A → ewp_case A E
| EThrow : E → ewp_case A E
| ECrash : ewp_case A E
| EPerform : C.eff -> (outcome2 val exn -> micro A E) → ewp_case A E
| EStep : ewp_case A E.

Arguments ewp_case {A E}.

Arguments ERet {A E}.
Arguments EThrow {A E}.
Arguments ECrash {A E}.
Arguments EPerform {A E}.
Arguments EStep {A E}.

(* Check whether a computation is a special [ewp_case]. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => ERet v
  | Throw e => EThrow e
  | Crash _ => ECrash
  | Stop CPerf e k => EPerform e k
  | _ => EStep
  end.

(* -------------------------------------------------------------------------- *)

(* Definition of protocols, inherited from [Hazel] *)
From osiris.Hazel Require Export protocols.

(** *Definition of the effectful weakest precondition *)

Section ewp.

  Context `{!osirisGS Σ}.

  Definition locals : Type := thread * iEff Σ.

  Definition local_thread (ℓ : locals) := ℓ.1.
  Definition local_prot (ℓ : locals) := ℓ.2.

  Definition ewp_pre
    (ewp : ∀ A' X', coPset -d> micro A' X' -d> locals -d> (outcome2 A' X' -d> iPropO Σ) -d> iPropO Σ) :
    (∀ (A X : Type),
        coPset -d> micro A X -d> locals -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ A X E m ℓ φ,
      (match is_ewp_case m with
       (* [EWP1]: Pure and exceptional values *)
       | ERet v => |={E}=> φ (O2Ret v)
       | EThrow v => |={E}=> φ (O2Throw v)
       | ECrash => |={E}=> False
       (* [EWP2]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k] with the
          same protocol. *)
       | EPerform e k =>
           |={E}=> (local_prot ℓ) allows perform e << λ o, ▷ ewp A X E (k o) ℓ φ >>
       (* [EWP3]: Non-effectful step of computation;
          this portion follows to the typical weakest precondition for Iris *)
       | EStep =>
           ∀ σ π, state_interp (σ, π) ={E, ∅}=∗
             ⌜can_progress (σ, π, m, (local_thread ℓ))⌝ ∗
             (∀ σ' π' m' μ, ⌜wp_step (σ, π, m, local_thread ℓ) (σ', π', m', μ)⌝ ={∅}=∗ ▷ |={∅,E}=>
                (state_interp (σ', π') ∗
                 ewp A X E m' ℓ φ ∗
                 [∗ list] '(ι, m) ∈ μ, ewp val exn E m (ι, ⊥) (λ _, True)))
       end)%I.

  Global Arguments ewp_pre _ {A X}.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n wp wp' Hwp A X E m Φ.
    repeat intro.
    f_equiv.
    { repeat (f_contractive || f_equiv || apply Hwp); cycle 1.
      repeat intro. f_contractive. apply Hwp. }
    do 17 f_equiv. f_contractive.
    f_equiv. f_equiv. f_equiv.
    - apply Hwp.
    - f_equiv. f_equiv. f_equiv.
      destruct a6; simpl. apply Hwp.
  Qed.

  Definition ewp_def : ∀ A X, coPset -> micro A X -d> (thread * iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

  Global Arguments ewp_def {A X}.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e ιΨ Φ} : rename.

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
Context `{osirisGS Σ}.
(* Context `{!irisGS_gen HasNoLc (@osiris_lang val exn) Σ}.   *)
Implicit Type P : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {E} (m : micro A X) ιΨ {φ} :
  ewp_def E m ιΨ φ ⊣⊢ ewp_pre (@ewp_def _ _) E m ιΨ φ.
Proof.
  rewrite {1}/ewp_def.
  apply (@fixpoint_unfold _ discrete_fun2_cofe _ ewp_pre).
Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n ιΨ :
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m ιΨ).
Proof.
  revert m ιΨ. induction (lt_wf n) as [n _ IH]=> m [ι Ψ] Φ Ψ' HΦ.
  ewp_unfold_all.
  f_equiv.
  - repeat f_equiv.
  - repeat f_equiv.
  - repeat f_equiv.
    intro. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 17 f_equiv.
    f_contractive. f_equiv. f_equiv. f_equiv.
    apply IH; auto; intro; auto.
    eapply dist_lt; auto.
Qed.

Global Instance ewp_proper E m ιΨ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m ιΨ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m n ιΨ:
  TCEq (is_ewp_case m) EStep →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m ιΨ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
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
  Definition lift_ret_spec (ϕ : A -d> iProp) : outcome2 A E -d> iProp :=
    (λ v, match v with
          | O2Ret r => ϕ r
          | _ => False
          end)%I.

  Definition lift_exn_spec (ψ : E -d> iProp) : outcome2 A E -d> iProp :=
    (λ v, match v with
          | O2Throw e => ψ e
          | _ => False
          end)%I.

  Definition ilift (ϕ : A -d> iProp) (ψ : E -d> iProp) : outcome2 A E -d> iProp :=
    (λ v, match v with
          | O2Ret r => ϕ r
          | O2Throw e => ψ e
          end)%I.

  Global Instance lift_ret_spec_ne n :
    Proper (pointwise_relation _ (dist n) ==> eq ==> (dist n)) lift_ret_spec.
  Proof. repeat intro; subst; destruct y0; eauto. Qed.

  Global Instance lift_ret_spec_proper :
    Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) lift_ret_spec.
  Proof. repeat intro; subst; destruct y0; eauto. Qed.

  Global Instance lift_exn_spec_ne n :
    Proper (pointwise_relation _ (dist n) ==> eq ==> (dist n)) lift_exn_spec.
  Proof. repeat intro; subst; destruct y0; eauto. Qed.

  Global Instance lift_exn_spec_proper :
    Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) lift_exn_spec.
  Proof. repeat intro; subst; destruct y0; eauto. Qed.

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

End lift_specs.

Definition lift_ret_enc_spec {E Σ} `{encode.Encode A} (ϕ : A -d> iProp Σ) : outcome2 val E -d> iProp Σ :=
    lift_ret_spec (λ (v' : val), (∃ (v : A), ⌜v' = osiris.lang.encode.encode v⌝ ∗ ϕ v)%I).

(* ========================================================================== *)

(** *Notation *)

Notation "ϕ ↑" := (lift_ret_spec ϕ) (at level 20).
Notation "ψ ⤉ " := (lift_exn_spec ψ) (at level 30).
Notation "'RET' x '=>' e '|' 'EXN' y '=>' f " :=
  (ilift (fun x => e) (fun y => f))
    (at level 200, right associativity,
      format
        "'[v '   '['  'RET'  x  '=>'  e ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").

Notation "'RET' '#' x '=>' e '|' 'EXN' y '=>' f " :=
  (ilift (fun x => (∃ v, (bi_pure (x = osiris.lang.encode.encode v)) ∗ e)%I) (fun y => f))
    (at level 200, right associativity, format
    "'[v ' '['    'RET'  '#' x  '=>'  e ']' '/' '[' '|'  'EXN'  y  '=>'  f ']' ']'").

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation. *)
Notation "'ensures' v , Q" :=
  (lift_ret_spec (λ v, Q))
    (at level 20, Q at level 200, v binder,
      format "'ensures'  v ,  '/' Q") : bi_scope.

(* Custom notation for hoare triples which state a postcondition only over the
    return continuation of an encoded value. *)
Notation "'ensures' '#' v , Q" :=
  (lift_ret_enc_spec (λ v, Q))
    (at level 20, Q at level 200, v binder,
      format "'ensures'  '#' v ,  '/' Q") : bi_scope.

(* Notation for [ewp] *)

Notation "'EWP' e <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ Φ)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|' '>'  {{  '[' Φ  ']' } } ']'") : bi_scope.

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E (_, iEff_bottom) Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e {{ Φ } }" :=
  (ewp_def ⊤ e%E (_, iEff_bottom) Φ)
    (at level 20, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ '  {{  Φ  } } ']' ']'")
    : bi_scope.

(* N.B.: we don't use [bi_scope] here to avoid a notation conflict with
  pre-existing notation; might be brittle *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat  ;  Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e {{ ensures v , Φ v }}).

(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris Require Export syntax.
From osiris.semantics Require Export code micro step.
