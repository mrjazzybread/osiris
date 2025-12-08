From iris.base_logic.lib Require Import own gen_heap ghost_map invariants.
From iris.algebra Require Import gmap_view dfrac gset auth excl.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.

From osiris.program_logic Require Import thread_step.
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

  Context (A X : Type).

  Class osirisGpreS := {
      (* #[global] osirisGpreS_iris :: invGpreS Σ; *)
      #[global] osiris_gen_GpreS :: gen_heapGpreS locations.loc step.block Σ;
    }.

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_genGS :: gen_heapGS locations.loc step.block Σ;
      (* This gives us a ghost map for thread postconditions. *)
      osiris_thread_postGS :: ghost_mapG Σ thread (outcome2 val exn -d> iPropO Σ);
      osiris_thread_post_name : gname;
    }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _ _ _} : assert.

(* Notations for ghost resouces. *)

Notation "l ↦ v" :=
  (pointsto l (DfracOwn 1) v)
    (at level 20, format "l  ↦  v") : bi_scope.

Global Instance osiris_cont_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS cont block Σ.
Proof. unfold cont; simpl. apply (osiris_genGS Σ). Defined.

Definition isCont `{osirisGS Σ} (k : cont) (sk : outcome2 val exn -> microvx)
  : iProp Σ :=
  gen_heap.pointsto k (DfracOwn 1) (K sk).

Definition isShot `{osirisGS} (k : cont) : iProp Σ :=
  k ↦ Shot.

Section ghost_resources.

  Context `{!osirisGS Σ}.

  Definition osiris_state_interp (σ : store) :=
    @gen_heap_interp locations.loc _ _ step.block Σ _ σ.

  (* [valid_thread ι P] is an exclusive token that can be exchanged for
     the postcondition resource P o when thread ι terminates with outcome o.
     This token is one-shot: it can only be used once to claim the resource. *)
  Definition valid_thread (ι : thread) (P : outcome2 val exn -d> iPropO Σ) : iProp Σ :=
    ι ↪[osiris_thread_post_name Σ]□ P.

  Global Instance valid_thread_persistent ι P :
    Persistent (valid_thread ι P).
  Proof. apply _. Qed.

  Definition osiris_thread_interp π : iProp Σ :=
    ghost_map_auth (@osiris_thread_post_name Σ _) 1 π.

  Definition state_interp : (store * post_map Σ) -> iProp Σ :=
    (λ '(σ, π), osiris_state_interp σ ∗ osiris_thread_interp π)%I.

  (** If we have a [valid_thread] resource, then the thread exists in the threadpool
      and we can look up its postcondition from the ghost map. *)
  Lemma valid_thread_lookup π ι P :
    osiris_thread_interp π -∗
    valid_thread ι P -∗
    osiris_thread_interp π ∗ ⌜π !! ι = Some P⌝.
  Proof.
    iIntros "Hti #Hvalid".
    rewrite /valid_thread.
    iDestruct (ghost_map_lookup with "Hti Hvalid") as %Hlookup.
    iSplitL; last by (iPureIntro; eassumption).
    iFrame.
  Qed.


  (** Allocate a new thread in the threadpool with a given postcondition.
      This gives us a [valid_thread] resource (exclusive) and an [alive_token] for the new thread.

      The alive_token must be consumed when the thread terminates to establish
      the postcondition P in the invariant. The valid_thread can later be exchanged
      for the postcondition resource P o. *)
  Lemma thread_alloc π ι (P : outcome2 val exn -d> iPropO Σ) :
    π !! ι = None →
    osiris_thread_interp π ==∗
      osiris_thread_interp (<[ ι := P ]> π) ∗ valid_thread ι P.
  Proof.
    iIntros (Hlookup) "Hauth".
    (* Insert P into the postcondition ghost map and get valid_thread *)
    iMod (ghost_map_insert_persist ι P with "Hauth") as "[Hauth Hvalid]"; first done.
    by iFrame.
  Qed.

End ghost_resources.

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

(* The type [ewp_case A E] represents computations that are handled
   differently by [ewp]:

      Either
      (1) a pure computation with result of type (outcome2 A E),
      (2) a crash, or
      (3) a perform effect that performs effect of type [C.eff] and the
          rest of its computation.
      (4) a computation that can take a step *)

Inductive ewp_case (A E : Type) : Type :=
  WPOutcome : (outcome2 A E) → ewp_case A E
| WPCrash : ewp_case A E
| WPPerform : C.eff -> (outcome2 val exn -> micro A E) → ewp_case A E
| WPStep : ewp_case A E
| WPJoin : thread → (outcome2 val exn → micro A E) → ewp_case A E.

Arguments ewp_case {A E}.

Arguments WPOutcome {A E}.
Arguments WPCrash {A E}.
Arguments WPPerform {A E}.
Arguments WPStep {A E}.
Arguments WPJoin {A E}.

(* Check whether a computation is a special [ewp_case]. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => WPOutcome (O2Ret v)
  | Throw e => WPOutcome (O2Throw e)
  | Crash => WPCrash
  | Stop CPerf e k => WPPerform e k
  | Stop CJoin ι k => WPJoin ι k
  | _ => WPStep
  end.

Lemma thread_step_is_WPStep {Σ A X} σ π (m m' : micro A X) ι σ' μ :
  @thread_step Σ A X (σ, m, ι, π) (σ', m', μ) ->
  is_ewp_case m = WPStep.
Proof.
  intros Hwp.
  destruct_thread_step; reflexivity.
Qed.

Lemma inv_is_ewp_case_outcome {A X} (m : micro A X) o :
  is_ewp_case m = WPOutcome o →
  m = inject2 o.
Proof. destruct m; try by inversion 1. destruct c; discriminate 1. Qed.

(* -------------------------------------------------------------------------- *)

(* Definition of protocols, inherited from [Hazel] *)
From osiris.Hazel Require Export protocols.

(** *Definition of the effectful weakest precondition *)

Section ewp.

  Context `{!osirisGS Σ}.

  Definition params : Type := thread * iEff Σ.

  Definition current_thread (p : params) := p.1.

  Definition ewp_pre
    (ewp : ∀ {A X}, coPset -d> micro A X -d> params -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    (∀ {A X}, coPset -d> micro A X -d> params -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ A X E m params φ,
      (match is_ewp_case m with
       (* [EWP1]: Pure and exceptional values *)
       | WPOutcome o => |={E}=> φ o
       | WPCrash => |={E}=> False
       (* [EWP2]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k] with the
          same protocol. *)
       | WPPerform e k =>
           |={E}=> params.2 allows perform e << λ o, ▷ ewp E (k o) params φ >>
       (* [EWP3]: Non-effectful step of computation;
          this portion follows to the typical weakest precondition for Iris *)
       | WPStep =>
           let '(ι, Ψ) := params in
           ∀ σ π,
             state_interp (σ, π) ={E, ∅}=∗
             ⌜can_progress σ π m ι⌝ ∗
             (∀ σ' m' μ,
                 ⌜thread_step (σ, m, ι, π) (σ', m', μ)⌝ ={∅}=∗ ▷ |={∅,E}=>
                ewp E m' (ι, Ψ) φ ∗
                match μ with
                | None => state_interp (σ', π)
                | Some (ι', m') => ∃ φ', state_interp (σ', <[ ι' := λ o, □ φ' o ]> π) ∗ ewp E m' (ι', ⊥) ( λ o, □ φ' o)
              end)
       | WPJoin ι' k =>
           ∀ σ π,
             state_interp (σ, π) ={E, ∅}=∗
             ⌜ι' ∈ dom π⌝ ∗
             (∀ o φ',
                 ⌜π !! ι' = Some φ'⌝ ∗ φ' o ={∅}=∗ ▷ |={∅,E}=>
                ewp E (k o) params φ ∗ state_interp (σ, π))
       end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n ewp ewp' Hwp A X E m [ι Ψ] φ.
    f_equiv.
    - do 2 f_equiv. intro P. f_contractive. apply Hwp.
    - repeat (f_contractive || f_equiv || apply Hwp).
    - repeat (f_contractive || f_equiv || apply Hwp).
  Qed.

  Definition ewp_def : ∀ A X, coPset -> micro A X -d> params -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e ιΨ Φ} : rename.
  Global Arguments ewp_def {A X}.

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
Implicit Type P : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {E} (m : micro A X) ιΨ {φ} :
  ewp_def E m ιΨ φ ⊣⊢ ewp_pre (@ewp_def Σ _) E m ιΨ φ.
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
  f_equiv. f_equiv.
  - do 8 f_equiv.
  - repeat f_equiv.
    intro. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 18 (f_contractive || f_equiv).
    apply IH; eauto.
    f_equiv.
    eapply dist_lt; eauto.
  - do 16 (f_contractive || f_equiv).
    apply IH; eauto.
    f_equiv.
    eapply dist_lt; eauto.
Qed.

Global Instance ewp_proper E m ιΨ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m ιΨ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m n ι Ψ:
  TCEq (is_ewp_case m) WPStep →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m (ι,Ψ)).
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
