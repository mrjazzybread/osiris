From iris.base_logic.lib Require Import own gen_heap ghost_map invariants.
From iris.algebra Require Import gmap_view dfrac gset auth excl.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.

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

  Context (A X : Type).

  Class osirisGpreS := {
      (* #[global] osirisGpreS_iris :: invGpreS Σ; *)
      #[global] osiris_gen_GpreS :: gen_heapGpreS locations.loc step.block Σ;
      #[global] osirisGpreS_thread :: gen_heapGpreS thread (micro A X) Σ;
    }.

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_genGS :: gen_heapGS locations.loc step.block Σ;
      (* This gives us a threadpool, which maps threads to their state. *)
      osiris_threadGS :: gen_heapGS thread (micro A X) Σ;
      (* This gives us a ghost map for thread postconditions. *)
      osiris_thread_postGS :: ghost_mapG Σ thread (outcome2 A X -d> iPropO Σ);
      osiris_thread_post_name : gname;
    }.

End ghost_instances.

#[global] Arguments OsirisGS Σ {_ _ _ _ _ _ _ _} : assert.

Section ghost_resources.

  Context `{!osirisGS Σ A X}.

  Definition osiris_state_interp (σ : store) :=
    @gen_heap_interp locations.loc _ _ step.block Σ _ σ.

  Definition valid_thread (ι : thread) (P : outcome2 A X -d> iPropO Σ) : iProp Σ :=
    ghost_map_elem (@osiris_thread_post_name _ _ _ _) ι DfracDiscarded P.

  Global Instance valid_thread_persistent ι P :
    Persistent (valid_thread ι P).
  Proof. apply _. Qed.

  Definition thread_inv (π : thpool A X) (πp : gmap thread (outcome2 A X -d> iPropO Σ)) : iProp Σ :=
    ∀ ι s, ⌜π !! ι = Some s⌝ -∗
      ⌜is_Some (πp !! ι)⌝ ∗
      ∃ N, inv N (∀ o, ⌜is_outcome s = Some o⌝ -∗ ∃ Ψ, ⌜πp !! ι = Some Ψ⌝ ∗ □ Ψ o).

  Definition osiris_thread_interp (π : thpool A X)  : iProp Σ :=
    (∃ πp : gmap thread (outcome2 A X -d> iPropO Σ),
      ⌜dom πp = dom π⌝ ∗
      @gen_heap_interp thread _ _ (micro A X) Σ _ π ∗
      ghost_map_auth (@osiris_thread_post_name _ _ _ _) 1 πp ∗
      thread_inv π πp)%I.

  Definition state_interp : (store * thpool A X) -> iProp Σ :=
    (λ '(σ, π), osiris_state_interp σ ∗ osiris_thread_interp π)%I.

  Lemma valid_thread_valid π ι P :
    osiris_thread_interp π -∗
    valid_thread ι P -∗
    osiris_thread_interp π ∗
    ∃ s, ⌜π !! ι = Some s⌝ ∗
         (⌜s = Alive⌝ ∨ ∃ (o : outcome2 val exn), ⌜s = Dead o⌝ ∗ □ P o).
  Proof.
    iIntros "(%πp & %Hdom & Hgen & Hauth & #Htinv) Hι".
    rewrite /valid_thread.
    iDestruct (ghost_map_lookup with "Hauth Hι") as %Hlookup.
    assert (is_Some (π !! ι)) as [s Hlookup'].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_dom. exists P. assumption. }
    iSplitL. { iFrame. iFrame "%". iFrame "#". }
    iSpecialize ("Htinv" $! ι s Hlookup').
    iExists s; iFrame "%".
    iDestruct "Htinv" as "[$ | (%o & %Ψ & -> & %Hlookupp & HΨ)]".
    iRight.
    iExists o.
    iSplitR; [ iPureIntro; reflexivity | ].
    rewrite Hlookupp in Hlookup.
    inversion Hlookup; subst.
    iApply "HΨ".
  Qed.

  (* Lemma thread_alloc π ι (P : outcome2 val exn -d> iPropO Σ) : *)
  (*   π !! ι = None -> *)
  (*   osiris_thread_interp π ==∗ *)
  (*     osiris_thread_interp (<[ ι := Alive ]> π) ∗ *)
  (*     valid_thread ι P. *)
  (* Proof. *)
  (*   iIntros (Hfresh_π) "(%πp & %Hdomeq & Hπ & Hauth & Htinv)". *)
  (*   rewrite /osiris_thread_interp /valid_thread. *)
  (*   iMod (gen_heap_alloc with "Hπ") as "[Hπ _]"; first done. *)
  (*   iMod (ghost_map_insert ι P with "Hauth") as "[Hauth Hfrag]". *)
  (*   { apply not_elem_of_dom. rewrite <- Hdomeq. apply not_elem_of_dom. assumption. } *)
  (*   iMod (ghost_map_elem_persist with "Hfrag") as "#Hfrag". *)
  (*   iModIntro. iFrame "Hπ Hauth". iFrame "#". *)
  (*   iSplitR; [ iPureIntro; rewrite !dom_insert; f_equiv; assumption | ]. *)
  (*   iIntros (ι' s Hlookup). *)
  (*   iSpecialize ("Htinv" $! ι' s). *)
  (*   apply lookup_insert_Some in Hlookup. *)
  (*   destruct Hlookup. *)
  (*   iLeft. { iPureIntro. by destruct H. } *)
  (*   destruct H as [Hneq Hlookup]. *)
  (*   iSpecialize ("Htinv" $! Hlookup). *)
  (*   iDestruct "Htinv" as "[$ | (%o & %Ψ & -> & %Hlookup' & HΨ)]". *)
  (*   iRight. *)
  (*   iExists o, Ψ. *)
  (*   iSplitR; [ iPureIntro; reflexivity | ]. *)
  (*   iFrame. *)
  (*   iPureIntro. *)
  (*   rewrite lookup_insert_ne; last apply Hneq. *)
  (*   apply Hlookup'. *)
  (* Qed. *)

  (* Helper lemmas for tracking postcondition map updates during fork/join *)

  (** ** Pattern for handling Fork and Join operations

      When proving rules that involve fork or join operations, the postcondition
      map [πp] must be updated to stay in sync with the operational threadpool [π].

      ** Fork pattern:
      When you have a [ForkS] step that creates a new thread [ι'], you must:
      1. Use [thread_alloc] or [fork_step_alloc_postcondition] to update [πp]
      2. Choose an appropriate postcondition [P] for the new thread
      3. Obtain a [valid_thread ι' P] resource for reasoning about the thread

      Example: When forking a thread with computation [m], typically use
      postcondition [λ _, True] if you don't care about the thread's result.

      ** Join pattern:
      When you have a [JoinS] step on thread [ι'], you can:
      1. Use the [valid_thread ι' P] resource to access the thread's postcondition
      2. The thread's result [o] should satisfy [P o]
      3. Use [join_step_get_postcondition] to verify the thread is in both [π] and [πp]
  *)

  (** When a [ForkS] step occurs, the postcondition map must be updated
      to include the newly forked thread with its postcondition. *)
  (* Lemma fork_step_alloc_postcondition {A X} σ π ι v1 v2 *)
  (*       (k : outcome2 val exn -> micro A X) ι' m' μ (P : outcome2 val exn -d> iPropO Σ) : *)
  (*   π !! ι' = None -> *)
  (*   wp_step (σ, π, Stop CFork (v1, v2) k, ι) (σ, <[ ι' := Alive ]> π, m', μ) -> *)
  (*   osiris_state_interp σ -∗ *)
  (*   osiris_thread_interp π ==∗ *)
  (*     osiris_state_interp σ ∗ *)
  (*     osiris_thread_interp (<[ ι' := Alive ]> π) ∗ *)
  (*     valid_thread ι' P. *)
  (* Proof. *)
  (*   iIntros (Hπ Hstep) "Hσ Hti". *)
  (*   iFrame "Hσ". *)
  (*   iApply (thread_alloc with "Hti"); assumption. *)
  (* Qed. *)

  (** When a [JoinS] step occurs on thread [ι'], we can access its postcondition
      from the ghost map. The thread must already be Dead in the operational
      threadpool. *)
  (* Lemma join_step_get_postcondition {A X} σ π ι ι' *)
  (*       (k : outcome2 val exn -> micro A X) o m' μ (P : outcome2 val exn -d> iPropO Σ) : *)
  (*   π !! ι' = Some (Dead o) -> *)
  (*   wp_step (σ, π, Stop CJoin ι' k, ι) (σ, π, m', μ) -> *)
  (*   osiris_thread_interp π -∗ *)
  (*   valid_thread ι' P -∗ *)
  (*   osiris_thread_interp π ∗ ⌜is_Some (π !! ι')⌝ ∗ P o. *)
  (* Proof. *)
  (*   iIntros (Hπ Hstep) "Hti #Hvalid". *)
  (*   iPoseProof (valid_thread_valid with "Hti Hvalid") as *)
  (*     "($ & %s & %Hlookup & Htinv)". *)
  (*   iDestruct "Htinv" as "[-> | (%o' & -> & #HP)]". *)
  (*   { rewrite Hlookup in Hπ. *)
  (*     discriminate Hπ. } *)
  (*   rewrite Hlookup in Hπ. *)
  (*   inversion Hπ; subst. *)
  (*   iFrame "#". *)
  (*   iPureIntro. eexists; eauto. *)
  (* Qed. *)

End ghost_resources.


(* Notations for ghost resouces. *)

Notation "l ↦ v" :=
  (pointsto l (DfracOwn 1) v)
    (at level 20, format "l  ↦  v") : bi_scope.

Global Instance osiris_cont_heapGS `{osirisGS Σ A X} : gen_heap.gen_heapGS cont block Σ.
Proof. unfold cont; simpl. apply (osiris_genGS Σ A X). Defined.

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

(* The type [ewp_case A E] represents computations that can be handled by a
   match-expression:

      Either
      (1) a pure computation with result of type A,
      (2) an exception of type [E],
      (3) a crash, or
      (4) a perform effect that performs effect of type [C.eff] and the
          rest of its computation.  *)

Inductive ewp_case (A E : Type) : Type :=
  EOutcome : (outcome2 A E) → ewp_case A E
| ECrash : ewp_case A E
| EPerform : C.eff -> (outcome2 val exn -> micro A E) → ewp_case A E
| EStep : ewp_case A E.

Arguments ewp_case {A E}.

Arguments EOutcome {A E}.
Arguments ECrash {A E}.
Arguments EPerform {A E}.
Arguments EStep {A E}.

(* Check whether a computation is a special [ewp_case]. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => EOutcome (O2Ret v)
  | Throw e => EOutcome (O2Throw e)
  | Crash _ => ECrash
  | Stop CPerf e k => EPerform e k
  | _ => EStep
  end.

Lemma wp_step_is_EStep {A X} σ π (m : micro A X) ι σ' π' μ :
  π !! ι = Some m ->
  @wp_step A X (σ, π, ι) (σ', π', μ) ->
  is_ewp_case m = EStep.
Proof.
  intros Hlookup Hwp.
  destruct_wp_step; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Definition of protocols, inherited from [Hazel] *)
From osiris.Hazel Require Export protocols.

(** *Definition of the effectful weakest precondition *)

Section ewp.

  Context `{!osirisGS Σ A X}.

  Definition params : Type := thread * iEff Σ.

  Definition local_thread (ℓ : params) := ℓ.1.
  Definition local_prot (ℓ : params) := ℓ.2.

  Definition ewp_pre
    (ewp : coPset -d> micro A X -d> params -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    (coPset -d> micro A X -d> params -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ E m ℓ φ,
      (match is_ewp_case m with
       (* [EWP1]: Pure and exceptional values *)
       | EOutcome o => |={E}=> φ o
       | ECrash => |={E}=> False
       (* [EWP2]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k] with the
          same protocol. *)
       | EPerform e k =>
           |={E}=> (local_prot ℓ) allows perform e << λ o, ▷ ewp E (k o) ℓ φ >>
       (* [EWP3]: Non-effectful step of computation;
          this portion follows to the typical weakest precondition for Iris *)
       | EStep =>
           ∀ σ π,
             state_interp (σ, π) ={E, ∅}=∗
             ⌜can_progress (σ, π, (local_thread ℓ))⌝ ∗
             (∀ σ' π' m' μ,
                ⌜wp_step (σ, π, local_thread ℓ) (σ', @insert _ _ _ insert_thpool (local_thread ℓ) m' π', μ)⌝ ={∅}=∗ ▷ |={∅,E}=>
                  state_interp (σ', π') ∗
                  ewp E m' ℓ φ ∗
                  [∗ list] '(ι, m) ∈ μ, ewp E m (ι, ⊥) (λ _, True))
       end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n ewp ewp' Hwp E m Φ.
    repeat intro.
    f_equiv.
    { repeat (f_contractive || f_equiv || apply Hwp); cycle 1.
      repeat intro. f_contractive. apply Hwp. }
    (* ∀ σ π, state_interp ={E,∅}=∗ ... *)
    do 17 f_equiv.
    (* ▷ |={∅,E}=> ... *)
    f_contractive. do 2 f_equiv.
    (* ewp A X E m' ... *)
    f_equiv.
    - apply Hwp.
    - repeat f_equiv.
      apply Hwp.
  Qed.

  Definition ewp_def : coPset -> micro A X -d> (thread * iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

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
Context `{osirisGS Σ A X}.
Implicit Type P : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

Notation wp := (wp (PROP:=iProp Σ)).

Lemma ewp_unfold {E} (m : micro A X) ιΨ {φ} :
  ewp_def E m ιΨ φ ⊣⊢ ewp_pre ewp_def E m ιΨ φ.
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
    intro. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 21 (f_contractive || f_equiv).
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
