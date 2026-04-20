From iris.base_logic.lib Require Import own gen_heap ghost_map invariants saved_prop token.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import gmap_view dfrac gset auth excl ofe.
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
      eapply dist_le. apply Hdist. apply Hlt.
  Qed.

  Canonical Structure discrete_fun2O : ofe := Ofe (discrete_fun2 C) discrete_fun2_ofe_mixin.

  Program Definition discrete_fun2_chain (c : chain discrete_fun2O)
    (x : A) (y : B) : chain (C x y) := {| chain_car n := c n x y |}.
  Next Obligation. intros c x y n i ?. by apply (chain_cauchy c). Qed.

  Program Definition discrete_fun2_bchain {n} (c : bchain discrete_fun2O n)
    (x : A) (y : B) : bchain (C x y) n := {| bchain_car n Hn := c n Hn x y |}.
  Next Obligation. intros n c x y m p Hm Hp Hmp. by apply (bchain_cauchy n c). Qed.

  Global Program Instance discrete_fun2_cofe `{∀ x y, Cofe (C x y)} :
      Cofe discrete_fun2O := {
    compl c x y := compl (discrete_fun2_chain c x y);
    lbcompl n Hn c x y := lbcompl Hn (discrete_fun2_bchain c x y)
  }.
  Next Obligation.
    intros ? n c x y.
    apply (conv_compl n (discrete_fun2_chain c x y)).
  Qed.
  Next Obligation. intros ? n Hn c m Hm x y. by rewrite (conv_lbcompl _ _ Hm). Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc x y. apply lbcompl_ne=> ?? /=. by apply Hc.
  Qed.

  Global Instance discrete_fun2_inhabited `{∀ x y, Inhabited (C x y)} : Inhabited discrete_fun2O :=
    populate (λ _, inhabitant).

End discrete_fun2.

(* -------------------------------------------------------------------------- *)

(** *Basic resource algebra for Osiris *)

(* The store is viewed as an authoritative ghost map. *)

Section ghost_instances.

  Context (Σ : gFunctors).

  (* We have to declare ghost state singletons for our global state,
     which are documented here:
     https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md?ref_type=heads#advanced-topic-ghost-state-singletons
   *)

  (* The [osirisGpreS] typeclass is used for ghost-state initialisation
     in our proof of adequacy. *)

  Class osirisGpreS := {
      #[global] osirisGpreS_iris :: invGpreS Σ;
      #[global] osiris_gen_GpreS :: gen_heapGpreS locations.loc mem_block Σ;
      #[global] osiris_thread_gen_GpreS :: gen_heapGpreS thread gname Σ;
      #[global] osiris_savedPredG :: savedPredG Σ (outcome2 val exn);
      osiris_tokenG :: tokenG Σ;
      #[global] osiris_array_ghostG :: ghost_mapG Σ syntax.block (list locations.loc);
    }.

  (* The [osirisGS] typeclass is what we use in our proofs.
     The "simple" ghost state is inherited from [osirisGpreS].

     The other ghost-state singletons which are stated explicitly are those
     that require an initialisation lemma in the proof of adequacy,
     such as [gen_heap_init] for the heap and the postcondition-tracking map. *)

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_genGS :: gen_heapGS locations.loc mem_block Σ;
      (* This gives us a ghost map for thread postconditions (stored as gnames). *)
      osiris_thread_postGS :: gen_heapGS thread gname Σ;
      (* savedPropG is inherited from osirisGpreS via osiris_inG *)
      (* This gives us tokens, for resource transfer when joining threads *)
      (* This gives us a ghost map tracking array locations (persistent per array). *)
      osiris_array_ghostGS :: ghost_mapG Σ syntax.block (list locations.loc);
      osiris_array_name : gname;
    }.

End ghost_instances.

(* Provide a minimal gFunctors for invariants, the store, and named postconditions for threads. *)
Definition osirisΣ : gFunctors :=
  #[ invΣ;
     gen_heapΣ locations.loc mem_block;
     gen_heapΣ thread gname;
     savedPredΣ (outcome2 val exn);
     tokenΣ;
     ghost_mapΣ syntax.block (list locations.loc)
    ].

(* Show that inclusion of [osirisΣ] in [Σ] is enough to instantiate [osirisGpreS Σ]. *)
Global Instance subG_heapGpreS {Σ} : subG osirisΣ Σ → osirisGpreS Σ.
Proof. solve_inG. Qed.

#[global] Arguments OsirisGS Σ {_ _ _ _ _ _} : assert.

(* Notations for ghost resouces. *)

Notation "l ↦ dq v" :=
  (pointsto l dq (Val v))
    (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(* We declare that [cont] can be used as keys for pointstos. *)
Global Instance osiris_cont_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS cont mem_block Σ.
Proof. unfold cont; simpl. apply (osiris_genGS Σ). Defined.

Definition isCont `{osirisGS Σ} (k : cont) (sk : outcome2 val exn -> microvx)
  : iProp Σ :=
  gen_heap.pointsto k (DfracOwn 1) (Kont sk).

Definition isShot `{osirisGS} (k : cont) : iProp Σ :=
  pointsto k (DfracOwn 1) Shot.

(* We declare that [block] can be used as keys for pointstos. *)
Global Instance osiris_block_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS syntax.block mem_block Σ.
Proof. unfold block; simpl. apply (osiris_genGS Σ). Defined.

Definition isBlock `{osirisGS Σ} (b : block) dq t : iProp Σ :=
  ∃ ls, gen_heap.pointsto b dq (Dict t ls).

Notation "b ⤇ dq t" :=
  (isBlock b dq t)
    (at level 20, dq custom dfrac at level 1, format "b ⤇ dq  t") : bi_scope.

Section ghost_resources.

  Context `{!osirisGS Σ}.

  Definition osiris_state_interp (σ : store) :=
    @gen_heap_interp locations.loc _ _ mem_block Σ _ σ.

  Definition osiris_thread_interp π : iProp Σ :=
    @gen_heap_interp thread _ _ gname Σ _ π.

  (* [valid_thread ι P] is a persistent token that witnesses thread ι has postcondition P.
     The postcondition P is stored behind a later modality using saved predicates.
     This token can be used to extract the postcondition when the thread terminates. *)
  Definition valid_thread (ι : thread) (P : outcome2 val exn -d> iPropO Σ) : iProp Σ :=
    ∃ γ, pointsto ι DfracDiscarded γ ∗ saved_pred_own γ DfracDiscarded P.

  Global Instance valid_thread_persistent ι P :
    Persistent (valid_thread ι P).
  Proof. apply _. Qed.

  (* Coherence between the ghost array map A and the physical store σ:
     every array registered in A has a corresponding block in σ with the same locations. *)
  Definition osiris_array_coherent (A : gmap syntax.block (list locations.loc)) (σ : store) : Prop :=
    ∀ (a : locations.loc) (ls : list locations.loc),
      A !! (a : syntax.block) = Some ls → ∃ t : mut_tag, σ !! a = Some (Dict t ls).

  Definition osiris_array_interp (σ : store) : iProp Σ :=
    ∃ σ', ghost_map_auth (osiris_array_name Σ) 1 σ' ∗ ⌜osiris_array_coherent σ' σ⌝.

  Definition state_interp : (store * post_map Σ) -> iProp Σ :=
    (λ '(σ, π), osiris_state_interp σ ∗ osiris_thread_interp π ∗ osiris_array_interp σ)%I.

  (* [isArray a ls] is the persistent ghost knowledge that array [a] has locations [ls]. *)
  Definition isArray (a : syntax.block) (ls : list locations.loc) : iProp Σ :=
    (a ↪[osiris_array_name Σ]□ ls ∗ ⌜(list_z.length ls ≤ int.max_array)%Z⌝)%I.

  Global Instance isArray_pers a ls : Persistent (isArray a ls).
  Proof. apply _. Qed.

  Lemma isArray_valid a ls1 ls2 :
    isArray a ls1 -∗ isArray a ls2 -∗ ⌜ls2 = ls1⌝.
  Proof.
    iIntros "(Ha & _) (Ha' & _)".
    iPoseProof (ghost_map_elem_agree with "Ha Ha'") as "%H".
    iPureIntro. exact (eq_sym H).
  Qed.

  Lemma isArray_length a ls :
    isArray a ls -∗ ⌜(list_z.length ls ≤ int.max_array_length)%Z⌝.
  Proof. iIntros "(_ & $)". Qed.

  (* Helper: coherence is preserved when updating only the tag of a block. *)
  Lemma osiris_array_coherent_set_tag A σ l t t' ls :
    σ !! l = Some (Dict t ls) →
    osiris_array_coherent A σ →
    osiris_array_coherent A (<[l := Dict t' ls]>σ).
  Proof.
    intros Hσl Hcoh a ls_a Hlookup.
    destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
    destruct (decide (a = l)) as [->|Hne].
    - (* a = l: ls_a must equal ls *)
      rewrite Hσl in Hσa. injection Hσa as <-.
      exists t'. rewrite lookup_insert. subst. rewrite decide_True_pi. done.
    - exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  (* Helper: coherence is preserved when allocating a new block. *)
  Lemma osiris_array_coherent_alloc_block A σ (l : locations.loc) ls :
    σ !! l = None →
    osiris_array_coherent A σ →
    osiris_array_coherent (<[(l : syntax.block) := ls]>A) (<[l := Dict Mut ls]>σ).
  Proof.
    intros Hfresh Hcoh a ls_a Hlookup.
    destruct (decide (a = l)) as [->|Hne].
    - rewrite lookup_insert in Hlookup. simplify_map_eq.
      exists Mut. rewrite lookup_insert. rewrite decide_True_pi. done.
    - rewrite lookup_insert_ne in Hlookup; last done.
      destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
      exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  (* Helper: coherence preserved when allocating a fresh non-block loc. *)
  Lemma osiris_array_coherent_alloc_nonblock A σ l v :
    σ !! l = None →
    osiris_array_coherent A σ →
    osiris_array_coherent A (<[l := v]>σ).
  Proof.
    intros Hfresh Hcoh a ls_a Hlookup.
    destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
    destruct (decide (a = l)) as [->|Hne].
    - congruence.
    - exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  (* Helper: coherence preserved when updating an existing non-Dict loc. *)
  Lemma osiris_array_coherent_update_nondict A σ l v v' :
    σ !! l = Some v →
    (∀ t ls, v ≠ Dict t ls) →
    osiris_array_coherent A σ →
    osiris_array_coherent A (<[l := v']>σ).
  Proof.
    intros Hσl Hnotdict Hcoh a ls_a Hlookup.
    destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
    destruct (decide (a = l)) as [->|Hne].
    - rewrite Hσl in Hσa. injection Hσa as Hσa. exact (False_rect _ (Hnotdict t_a ls_a Hσa)).
    - exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  (* Derived: osiris_array_interp is preserved when allocating a fresh non-block loc. *)
  Lemma osiris_array_interp_alloc_nonblock σ l v :
    σ !! l = None →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := v]>σ).
  Proof.
    iIntros (Hfresh) "(%A & Hauth & %Hcoh)".
    iExists A. iFrame. iPureIntro.
    exact (osiris_array_coherent_alloc_nonblock A σ l v Hfresh Hcoh).
  Qed.

  (* Derived: osiris_array_interp is preserved when updating an existing non-Dict loc. *)
  Lemma osiris_array_interp_update_nondict σ l v v' :
    σ !! l = Some v →
    (∀ t ls, v ≠ Dict t ls) →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := v']>σ).
  Proof.
    iIntros (Hσl Hnotdict) "(%A & Hauth & %Hcoh)".
    iExists A. iFrame. iPureIntro.
    exact (osiris_array_coherent_update_nondict A σ l v v' Hσl Hnotdict Hcoh).
  Qed.

  (* Specialised: osiris_array_interp is preserved when updating a Val location. *)
  Lemma osiris_array_interp_update_val σ l (v : val) v' :
    σ !! l = Some (Val v) →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := v']>σ).
  Proof.
    iIntros (Hσl).
    iApply osiris_array_interp_update_nondict; first done.
    intros t ls. discriminate.
  Qed.

  (* Specialised: osiris_array_interp is preserved when allocating a Kont loc. *)
  Lemma osiris_array_interp_alloc_kont σ l k :
    σ !! l = None →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := Kont k]>σ).
  Proof.
    iIntros (Hfresh).
    iApply osiris_array_interp_alloc_nonblock. done.
  Qed.

  (* Specialised: osiris_array_interp is preserved when updating a Kont to Shot. *)
  Lemma osiris_array_interp_kont_to_shot σ l k :
    σ !! l = Some (Kont k) →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := Shot]>σ).
  Proof.
    iIntros (Hσl).
    iApply osiris_array_interp_update_nondict; first done.
    intros t ls. discriminate.
  Qed.

  (* Derived: osiris_array_interp is preserved for block tag updates. *)
  Lemma osiris_array_interp_set_tag σ l t t' ls :
    σ !! l = Some (Dict t ls) →
    osiris_array_interp σ -∗ osiris_array_interp (<[l := Dict t' ls]>σ).
  Proof.
    iIntros (Hσl) "(%A & Hauth & %Hcoh)".
    iExists A. iFrame. iPureIntro.
    exact (osiris_array_coherent_set_tag A σ l t t' ls Hσl Hcoh).
  Qed.

  (** If we have a [valid_thread] resource, then the thread exists in the threadpool
      and we can look up its gname from the ghost map, which points to the postcondition. *)
  Lemma valid_thread_lookup π ι P :
    osiris_thread_interp π -∗
    valid_thread ι P -∗
    osiris_thread_interp π ∗ ∃ γ, ⌜π !! ι = Some γ⌝ ∗ saved_pred_own γ DfracDiscarded P.
  Proof.
    iIntros "Hti #Hvalid".
    rewrite /valid_thread.
    iDestruct "Hvalid" as (γ) "[#Hpt #Hsaved]".
    iDestruct (gen_heap_valid with "Hti Hpt") as %Hlookup.
    iFrame "Hti". iExists γ. iFrame "Hsaved". iPureIntro. done.
  Qed.

  (** Allocate a new thread in the threadpool with a given postcondition.

      This gives us a [valid_thread] resource
      that witnesses the thread's postcondition. *)
  Lemma thread_alloc π ι (P : outcome2 val exn -d> iPropO Σ) :
    π !! ι = None →
    osiris_thread_interp π ==∗
      ∃ γ, osiris_thread_interp (<[ ι := γ ]> π) ∗ pointsto ι DfracDiscarded γ ∗ saved_pred_own γ DfracDiscarded P.
  Proof.
    iIntros (Hlookup) "Hauth".
    (* Allocate a saved predicate for the postcondition P *)
    iMod (saved_pred_alloc P DfracDiscarded) as (γ) "#Hsaved"; first done.
    (* Insert γ into the thread ghost map *)
    iMod (gen_heap_alloc π ι γ with "Hauth") as "(Hauth & Hvalid & _)"; first done.
    (* Make the pointsto persistent *)
    iMod (pointsto_persist with "Hvalid") as "#Hvalid".
    iModIntro. iExists γ. iFrame "Hauth".
    (* Package up valid_thread *)
    iFrame "Hvalid Hsaved".
  Qed.

End ghost_resources.

(* ========================================================================== *)

(** *Effect-aware Weakest Precondition *)

(* The type [ewp_case A E] represents computations that are handled
   differently by [ewp]:

      Either
      (1) a terminated computation with result of type (outcome2 A E),
      (2) a crash
      (3) a performed effect
      (4) a computation that can take a step
      (5) a join
 *)

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

(* Determine which [ewp_case] a given [m] is. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => WPOutcome (O2Ret v)
  | Throw e => WPOutcome (O2Throw e)
  | Crash => WPCrash
  | Stop CPerf e k => WPPerform e k
  | Stop CJoin ι' k => WPJoin ι' k
  | _ => WPStep
  end.

Lemma thread_step_is_WPStep {A X} σ π (m m' : micro A X) σ' μ :
  thread_step (σ, m, π) (σ', m', μ) ->
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

Section ewp_def.

  Context `{!osirisGS Σ}.

  (* [ewp] takes four parameters:
     - [ι]: the identifier of the current thread
     - [E]: the mask i.e. set of names we may open.
     - [m]: the ongoing computation, an element of the [micro] monad.
     - [Ψ]: the current protocol (in the sense of Hazel)
     - [φ]: the postcondition
   *)

  Definition ewp_pre
    (ewp : ∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    (∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ A X E m Ψ φ,
      (match is_ewp_case m with
       (* [EWP1]: Returned values and raised exceptions. *)
       | WPOutcome o => |={E}=> φ o
       (* [EWP2]: Undefined and undesirable behaviour. *)
       | WPCrash => |={E}=> False
       (* [EWP3]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k]. *)
       | WPPerform e k =>
           |={E}=> Ψ allows perform e << λ o, ▷ ewp E (k o) Ψ φ >>
       (* [EWP4]: [m] is a computation that can take a step. *)
       | WPStep =>
           ∀ σ π,
             state_interp (σ, π) ={E, ∅}=∗
             ⌜can_progress σ (dom π) m⌝ ∗
             ∀ σ' m' μ,
               ⌜thread_step (σ, m, dom π) (σ', m', μ)⌝ ={∅}=∗ ▷ |={∅,E}=>
               ewp E m' Ψ φ ∗
               match μ with
               | None => state_interp (σ', π)
               | Some (ι', mforked) =>
                   ∃ φ' γ, state_interp (σ', <[ι' := γ]> π) ∗
                           saved_pred_own γ DfracDiscarded φ' ∗
                           ewp ⊤ mforked ⊥ (λ o, □ φ' o)
               end
       (* [EWP5]: A request to join a thread [ι']. *)
       | WPJoin ι' k =>
           ∀ σ π,
             state_interp (σ, π) ={E, ∅}=∗
             match π !! ι' with
             | None => |={∅, E}=> ▷ False
             | Some γ =>
                 ∃ φ', saved_pred_own γ DfracDiscarded φ' ∗
                       ▷ (∀ o, □ φ' o ={∅}=∗ |={∅,E}=>
                          ewp E (k o) Ψ φ ∗ state_interp (σ, π))
             end
       end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n ewp ewp' Hwp A X E m Ψ φ.
    f_equiv. do 2 f_equiv. intro o. f_contractive. apply Hwp.
    - repeat (f_contractive || f_equiv || apply Hwp).
    - repeat (f_contractive || f_equiv || apply Hwp).
  Qed.

  Definition ewp_def : ∀ A X, coPset -> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e Ψ Φ} : rename.
  Global Arguments ewp_def {A X}.

End ewp_def.

(* -------------------------------------------------------------------------- *)

Section ewp_properties.

Context {A X P : Type}.
Context `{osirisGS Σ}.
Implicit Type Ψ : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

(* Notation wp := (wp (PROP:=iProp Σ)). *)

Lemma ewp_unfold {E} {Ψ} {φ} (m : micro A X)  :
  ewp_def E m Ψ φ ⊣⊢ ewp_pre (@ewp_def Σ _) E m Ψ φ.
Proof.
  rewrite {1}/ewp_def.
  apply (@fixpoint_unfold _ _ discrete_fun2_cofe _ ewp_pre).
Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n Ψ :
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m Ψ).
Proof.
  induction (lt_wf n) as [n _ IH] in m, Ψ |-* => Φ Ψ' HΦ.
  ewp_unfold_all.
  f_equiv. f_equiv.
  - do 8 f_equiv.
  - repeat f_equiv. intro o. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 18 (f_contractive || f_equiv).
    apply IH; eauto.
    f_equiv.
    eapply dist_lt; eauto.
  - do 17 (f_contractive || f_equiv).
    + apply IH; eauto. f_equiv. eapply dist_lt; eauto.
Qed.

Global Instance ewp_proper E m Ψ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m Ψ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m Ψ n:
  TCEq (is_ewp_case m) WPStep →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m Ψ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
Qed.

End ewp_properties.


(* ========================================================================== *)

From osiris.lang Require Import encode.

Definition impure {A V X} `{osirisGS Σ} `{Observe A V}
  (E : coPset) (m : micro V X) (Ψ : iEff Σ) (ζ : X → iProp Σ) (Φ : A → iProp Σ) : iProp Σ :=
  ewp_def E m Ψ (ilift ζ (ireturns Φ)).

(* ========================================================================== *)

(** *Notation *)

(* Bottom instance for function types, needed for the ⊥ in notations *)
Global Instance bottom_fun {Σ} {A : Type} : Bottom (A → iProp Σ) := λ _, False%I.

(* Notation for [impure] *)

(* Notations with explicit exceptional postcondition.
   The exception postcondition comes BEFORE the return postcondition
   so the parser can distinguish from the short form. *)

Notation "'imp' e ⟨⟨ ζ ⟩⟩ {{ Φ }}" :=
  (impure ⊤ e%E ⊥ ζ%I Φ%I)
    (at level 20, e, Φ, ζ at level 200,
      format "'[' 'imp'  e  '/' '[ '  ⟨⟨  ζ  ⟩⟩  {{  Φ  '}}' ']' ']'")
    : bi_scope.

Notation "'imp' e @ E ⟨⟨ ζ ⟩⟩ {{ Φ }}" :=
  (impure E e%E ⊥ ζ%I Φ%I)
    (at level 20, e, Φ, ζ at level 200,
      format "'[' 'imp'  e  '/' '[ ' @  E  ⟨⟨  ζ  ⟩⟩  {{  Φ  '}}' ']' ']'")
    : bi_scope.

Notation "'imp' e <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ }}" :=
  (impure ⊤ e%E Ψ%I ζ%I Φ%I)
    (at level 20, e, Φ, ζ at level 200,
      format "'[hv' 'imp'  e  '/' <| Ψ '|>'  ⟨⟨  ζ  ⟩⟩  {{  '[' Φ  ']' '}}' ']'")
    : bi_scope.

Notation "'imp' e @ E <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ }}" :=
  (impure E e%E Ψ%I ζ%I Φ%I)
    (at level 20, e, Ψ, Φ, ζ at level 200,
      format "'[' 'imp'  e  '/' '[ ' @  E  <|  Ψ  '|>'  ⟨⟨  ζ  ⟩⟩  {{  Φ  '}}' ']' ']'")
    : bi_scope.

(* Notations without exceptional postcondition (uses ⊥) *)

Notation "'imp' e {{ Φ }}" :=
  (impure ⊤ e%E ⊥ ⊥ Φ%I)
    (at level 20, e, Φ at level 200,
      format "'[' 'imp'  e  '/' '[ ' {{  Φ  '}}' ']' ']'")
    : bi_scope.

Notation "'imp' e @ E {{ Φ }}" :=
  (impure E e%E ⊥ ⊥ Φ%I)
    (at level 20, e, Φ at level 200,
      format "'[' 'imp'  e  '/' '[ ' @  E  {{  Φ  '}}' ']' ']'")
    : bi_scope.

Notation "'imp' e <| Ψ '|>' {{ Φ }}" :=
  (impure ⊤ e%E Ψ%I ⊥ Φ%I)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'imp'  e  '/' <| Ψ '|>'  {{  '[' Φ  ']' '}}' ']'")
    : bi_scope.

Notation "'imp' e @ E <| Ψ |> {{ Φ }}" :=
  (impure E e%E Ψ%I ⊥ Φ%I)
    (at level 20, e, Ψ, Φ at level 200,
      format "'[' 'imp'  e  '/' '[ ' @  E  <|  Ψ  '|>'  {{  Φ  '}}' ']' ']'")
    : bi_scope.

(* N.B.: we don't use [bi_scope] here to avoid a notation conflict with
  pre-existing notation; might be brittle *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat  ;  Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ imp e {{ Φ }}).

(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris Require Export syntax.
From osiris.semantics Require Export code micro step.
