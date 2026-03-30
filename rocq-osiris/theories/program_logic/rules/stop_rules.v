From Stdlib Require Import Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import thread_step ewp tactics basic_rules escrows.
From osiris.semantics Require Import semantics.
From osiris.logic Require Import big_opLZ.

From osiris.program_logic.pure Require Export pure.
From osiris.program_logic.rules Require Import impure_rules.


Section imp_stop.

  Context `{!osirisGS Σ}.

  Context {A X : Type} `{Hobs : Observe Encoded A}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : Encoded → iProp Σ}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma imp_stop_perform eff k :
    Ψ allows perform eff << λ o, ▷ imp (k o) <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} >> -∗
    imp Stop CPerf eff k <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hperf".
    iApply (ewp_stop_perform with "Hperf").
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* The following lemmas offer reasoning rules for each of the system calls,
     that is, for computations of the form [Stop c x y]. They are simple
     consequences of the operational behavior of these system calls. *)

  (* [CAllocn]. *)

  (* Memory allocation rule for [n] locations at once. *)
  Lemma imp_allocn' vs (k : _ → micro A X) :
    ▷ (∀ (ls : list loc),
          ([∗ listZ] l;v ∈ ls;vs, pointsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤) -∗
          imp (continue k ls) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
      imp (Stop CAllocn vs k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_thread_step. destruct H as (Hlen & Hdup & Hfresh).
    iDestruct (gen_heap_alloc_big with "Hsi") as ">(Hsi & Hpts & Hmt)".
    { apply map_disjoint_spec. intros l x y.
      instantiate (1 := (list_to_map ((λ '(l, v), (l, V v)) <$> zip ls vs))).
      intros HF Hlookup.
      apply elem_of_dom_2 in HF. rewrite dom_list_to_map in HF.
      apply elem_of_list_to_set in HF.
      rewrite <- list_fmap_compose in HF.
      apply list_elem_of_fmap_1 in HF as ([l' v'] & -> & HF).
      apply elem_of_zip_l in HF.
      apply Hfresh in HF.
      rewrite Hlookup in HF. discriminate HF. }
    assert (ls = ((λ '(l,v), (l, V v)) <$> zip ls vs).*1) as Heqls.
    { clear Hdup Hfresh. generalize dependent vs. induction ls; intros ??. reflexivity.
      simpl.
      destruct vs; first discriminate Hlen.
      rewrite -> IHls at 1.
      reflexivity. by inversion Hlen. }
    rewrite Heqls in Hdup.
    iPoseProof (big_sepM_list_to_map _ _ Hdup with "Hpts") as "Hpts".
    iPoseProof (big_sepM_list_to_map _ _ Hdup with "Hmt") as "Hmt".
    clear Heqls Hdup Hfresh.
    ewp_mask_elim. iFrame. iSplitR "Hsi".
    - iApply "H". iFrame "%".
      iInduction ls as [|l ls IH] forall (vs Hlen).
      + destruct vs; last discriminate Hlen. done.
      + destruct vs; first discriminate Hlen.
        iApply big_sepLZ2_cons.
        iDestruct "Hpts" as "(Hl & Hpts)".
        iDestruct "Hmt" as "(Htok & Hmt)".
        iFrame.
        iApply ("IH" with "[] Hpts Hmt"). iPureIntro. by inversion Hlen.
    -
      assert (insertn ls vs σ = list_to_map ((λ '(l, v), (l, V v)) <$> zip ls vs) ∪ σ) as ->.
      { generalize dependent vs.
        induction ls as [|l ls IH]; intros vs Hlen.
        - simpl.
          destruct vs; last discriminate Hlen.
          by rewrite map_empty_union.
        - simpl.
          destruct vs; first discriminate Hlen.
          rewrite IH. rewrite insert_union_l.
          reflexivity. by inversion Hlen. }
      iFrame.
  Qed.

  Lemma imp_allocn vs (k : _ → micro A X) :
    ▷ (∀ ls,
          ([∗ listZ] l;v ∈ ls;vs, pointsto l (DfracOwn 1) (V v)) -∗
          imp (continue k ls) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    imp (Stop CAllocn vs k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_allocn'; iNext.
    iIntros (ls) "Hls".
    iPoseProof (big_sepLZ2_sep with "Hls") as "[Hls _]".
    iApply "H". iFrame.
  Qed.

  Lemma imp_alloc v (k : _ → micro A X) :
    ▷ (∀ (l : loc), pointsto l (DfracOwn 1) (V v) -∗
            imp (continue k [l]) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    imp (Stop CAllocn [v] k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_allocn.
    iIntros "!>" (ls) "Hls".
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlen".
    destruct ls; first discriminate Hlen.
    destruct ls; last (revert Hlen; length; length_nonneg ls; lia).
    iApply "H".
    iApply (big_sepLZ2_singleton (λ _ l v, l↦v)%I with "Hls").
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma imp_store l v v' (k : _ → micro A X) :
    ▷ pointsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        pointsto l (DfracOwn 1) (V v') -∗
        imp (continue k #()) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    imp (Stop CStore (l, v') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iIntros "!> !>".
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    destruct_thread_step.
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    rewrite /step_store_1 /step_store_2 H0.
    ewp_mask_elim. iFrame.

    iApply ("Hwp" with "Hl").
  Qed.

  (* [CLoad]. *)

  (* The standard memory load rule of Separation Logic. *)

  Lemma imp_load l v dq (k: _ → micro A X) :
    ▷ pointsto l dq (V v) ⊢
    ▷ (
        pointsto l dq (V v) -∗
        imp (continue k v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    imp (Stop CLoad l k) @ E <|Ψ|>  ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    destruct Ψ.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_thread_step.

    rewrite /step_load_2 H0.
    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* When forking a thread, we must prove that the forked thread is
     safe, and that the parent thread is safe.
     We learn that the forked thread has an address ι' and is initially alive *)

  Definition isThread `{Observe B val} (ι : thread) ζ Φ : iProp Σ :=
    valid_thread ι (ilift ζ (ireturns Φ)).

  Lemma imp_stop_fork' `{Encode B} μ (φ : B → iProp Σ) v1 v2 (k : _ -> micro A X) :
    ▷ (∀ ι',
         isThread ι' μ φ -∗
         imp call v1 v2 ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ v, □ φ v }} ∗
         imp (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hfork".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_thread_step.
    iMod (thread_alloc π ι _ (not_elem_of_dom_1 _ _ H0) with "Hti")
      as "(%γ & Hti & #Hvalid & #Hsaved)".
    ewp_mask_elim.
    iAssert (valid_thread ι _) as "Hvalid'". iFrame "#".
    iDestruct ("Hfork" with "Hvalid'") as "[Hcall Hcontinue]".
    iFrame "#∗".
    iApply (ewp_mono with "Hcall").
    iIntros ([|]) "/="; last iIntros "$".
    iIntros "(%a' & -> & #Hφ)".
    iModIntro. iExists a'. auto.
  Qed.

  (* We do not expect that the forked thread needs to know its own postcondition. *)
  Lemma imp_stop_fork `{Encode B} μ (φ : B → iProp Σ) v1 v2 (k : _ -> micro A X) :
    ▷ (∀ ι', isThread ι' μ φ -∗ imp (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    ▷ (imp call v1 v2 ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ v, □ φ v }}) -∗
    imp (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hcontinue Hfork".
    iApply (imp_stop_fork' (B:=B)).
    iIntros "!> %ι' #Hvalid".
    iSplitL "Hfork".
    - iApply "Hfork".
    - iApply ("Hcontinue" with "Hvalid").
  Qed.

  (* [CResume]. *)

  (* Resuming a continuation from a location in the store. *)
  Lemma imp_resume l o sk (k: _ → micro A X) :
    isCont l sk ⊢
    (isShot l -∗ ▷ imp (try2 (sk o) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Stop CResume (l, o) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_thread_step.

    (* Update the ghost heap. *)
    iMod (gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
    iSpecialize ("Hwp" with "Hl").
    ewp_mask_elim.
    rewrite /step_resume_1 /step_resume_2 H0. iFrame.
  Qed.

  Lemma imp_resume_crash l o (k: _ → micro A X) :
    isShot l -∗
    imp (crash "resume error: unbound location") @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp (Stop CResume (l, o) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hcrash".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_thread_step.

    (* Update the ghost heap. *)
    ewp_mask_elim.
    rewrite /step_resume_1 /step_resume_2 H0. by iFrame.
  Qed.

End imp_stop.

Section imp_wrap_flip.

  Context `{!osirisGS Σ}.

  Context {A X : Type} `{Hobs : Observe Encoded A}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : Encoded → iProp Σ}.

  Import ewp_rules_tactics.

  (* [CWrap]. *)

  (* Installing a handler with branches [bs] on top of a continuation
     that is located in the store at location [l]. *)

  Lemma imp_wrap_deep l η bs (k: _ -> micro A X) :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs)) -∗
     ▷ imp (continue k l') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Stop CWrap (true, l, η, bs) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* The reduction step must be a successful step. *)
    destruct_thread_step.

    (* Allocate a new location in the heap. *)
    iMod (gen_heap.gen_heap_alloc with "Hsi") as "(Hsi & Hl' & _)"; first done.
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim. iFrame.
  Qed.

  Lemma imp_wrap_shallow l η bs (k: _ -> micro A X) :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs)) -∗
     ▷ imp (continue k l') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Stop CWrap (false, l, η, bs) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* The reduction step must be a successful step. *)
    destruct_thread_step.

    (* Allocate a new location in the heap. *)
    iMod (gen_heap.gen_heap_alloc with "Hsi") as "(Hsi & Hl' & _)"; first done.
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim.
    unfold step_wrap_2.
    by iFrame.
  Qed.

  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma imp_stop_flip u (k: _ → micro A X) :
      ▷(imp continue k true @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} ∧ imp continue k false @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }})
      ⊢ imp (Stop CFlip u k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_thread_step; cbn; iMod "Hmod" as "_"; cbn;
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
    destruct b.
    { iApply (bi.and_elim_l with "H"). }
    { iApply (bi.and_elim_r with "H"). }
  Qed.

End imp_wrap_flip.

Section imp_flip.

  Context `{!osirisGS Σ}.

  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ} {Φ : bool → iProp Σ}.

  Import ewp_rules_tactics.

  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma imp_flip :
      ▷( Φ true ∧ Φ false)
      ⊢ imp code.flip @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_stop_flip. iNext.
    iSplit.
    - iDestruct "H" as "[H _]".
      iApply (imp_ret _ true eq_refl). iFrame.
    - iDestruct "H" as "[_ H]".
      iApply (imp_ret _ false eq_refl). iFrame.
  Qed.

End imp_flip.


Section imp_concurrent.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_fork `{Encode B} {ζ} {Φ : thread → iProp Σ} μ (φ : B → iProp Σ) v1 v2 :
    ▷ (∀ ι',
         isThread ι' μ φ -∗
         imp call v1 v2 ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ o, □ φ o }} ∗
         Φ ι') -∗
    imp (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (imp_stop_fork' (B:=B)).
    iIntros "!>" (ι') "Hvalid"; iDestruct ("HΦ" with "Hvalid") as "[Hcall HΦ]"; iFrame.
    iApply ewp_ret.
    iExists ι'. auto.
  Qed.

  (* [joinable ι φ] allows one to join on [ι] and to recover the non-necessarily
  persistent postcondition [φ] (after opening and closing an invariant) *)

  Definition joinN := nroot .@ "join".
  (* We need the implicit [Encode] to be outside of the existential,
     so that we know the return type when we join thread [ι]. *)
  Definition joinable B `{Observe B val} ι φ :=
    (∃ ζ (Φ : B → iProp Σ),
        isThread ι ζ Φ ∗ ∀ o, ilift ζ Φ o ={↑joinN}=∗ ▷ φ)%I.

  (* Rule for fork when the postcondition of the spawned thread is persistent *)
  Lemma imp_fork_persistent `{Encode B} {ζ : exn → iProp Σ} {Φ : thread → iProp Σ} φ v1 v2 :
    ▷ (∀ ι',
          □ joinable B ι' φ -∗
          imp call v1 v2 {{ λ (_ : B), □ φ }} ∗
          Φ ι') -∗
    imp (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (imp_fork (λ _, False)%I (λ (_ : B), φ)).
    iIntros "!> %ι' #Hvalid".
    iDestruct ("HΦ" with "[]") as "(Hcall & $)".
    { iExists _. iFrame "#".
      iModIntro.
      iIntros ([|]) "/="; [ auto | iIntros ([]) ]. }
    iApply (ewp_mono with "Hcall").
    iIntros ([|]); [ auto | iIntros ([]) ].
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is a list of
  resources that other threads can recover when joining. *)
  Lemma imp_fork_resourceful `{Encode B} {ζ : exn → iProp Σ} {Φ : thread → iProp Σ} φs v1 v2 :
    ▷ (∀ ι',
          ([∗ list] φ ∈ φs, joinable B ι' φ) -∗
          imp call v1 v2 {{ λ (_ : B), [∗] φs }} ∗
          Φ ι') -∗
    imp (fork v1 v2) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".

    (* Given [φs], determine a suitable postcondition [ψ] for the spawned
    thread. This requires the ghost update modality because we allocate
    tokens that will be used to transfer resources. *)
    iApply fupd_ewp. iMod (fupd_mask_subseteq ∅) as "Hmod". set_solver.
    iDestruct (alloc_escrow_list joinN φs) as "> (%φ & #Hescrow_intro & Hescrow_elim)".

    (* In the postcondition of the spawned thread we can transfer the resources
    [φs] into [ψ] by the escrow mechanism *)
    iAssert (▷ ∀ ι, ([∗ list] φ ∈ φs, joinable B ι φ) -∗
      imp call v1 v2 {{ λ (_ : B), □ φ }} ∗ Φ ι)%I
      with "[HΦ]" as "HΦ".
    {
      iIntros "!>" (ι') "Hjs".
      iDestruct ("HΦ" $! ι' with "Hjs") as "(Hcall & $)".
      iPoseProof (imp_mono_pers with "Hcall []") as "$".
      iIntros "!>" (_) "φs".
      iSpecialize ("Hescrow_intro" with "[φs]").
      by rewrite -big_sepL_later.
      iApply (fupd_mask_mono ∅). set_solver.
      iExact "Hescrow_intro".
    }
    iClear "Hescrow_intro".
    iMod "Hmod".

    (* Apply the basic rule for fork, recover [valid_thread] in the post *)
    iApply (imp_fork (B:=B)).
    iIntros "!> !> %ι' #Hvalid".
    iDestruct ("HΦ" $! ι' with "[Hescrow_elim]") as "(Hcall & $)".

    (* From the escrow elimination implication we prove the list of [joinable φ]s *)
    iApply (big_sepL_mono_pers (isThread ι' ⊥ (λ (_ : B), φ)) with "[$]").
    iIntros (k φ' Hk) "(#? & Helim)". iExists ⊥, _.
    iSplit; auto. iIntros ([|]); [ auto | iIntros ([]) ].

    iApply (ewp_mono with "Hcall").
    iIntros ([|]); [ | iIntros ([]) ].
    iIntros "(%v & Henc & Hφ)".
    iFrame.
  Qed.

End imp_concurrent.

Section imp_join_self.

  Context `{!osirisGS Σ}.

  Context {A : Type} `{Hobs : Observe Encoded A}.
  Context {E : coPset} {Ψ : iEff Σ} {Φ : Encoded → iProp Σ}.

  Import ewp_rules_tactics.

  Lemma imp_stop_join {X} `{Observe B val} {ζ : X → iProp Σ} ι' (k : _ -> micro A X) φ μ :
    isThread ι' μ φ -∗
    ▷ (∀ x, □ φ x -∗ imp continue k ♯x @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    ▷ (∀ e, □ μ e -∗ imp discontinue k e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp (Stop CJoin ι' k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hι Hk".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    iPoseProof (valid_thread_lookup with "Hti Hι") as "(Hti & %γ & %Hlookup & Hsaved)".
    assert (ι' ∈ dom π) as Hdom by (apply (elem_of_dom π ι'); eexists; eassumption).
    rewrite Hlookup.
    iFrame.
    iIntros "!> %o #Ho".
    ewp_mask_elim. rewrite /continue /discontinue.
    destruct o; [ iDestruct "Hk" as "[Hk _]" | iDestruct "Hk" as "[_ Hdk]" ].
    - iDestruct "Ho" as "(%v & -> & Hφ)".
      iSpecialize ("Hk" $! v with "Hφ").
      iApply "Hk".
    - iApply ("Hdk" with "Ho").
  Qed.

End imp_join_self.

Section imp_exn.

  Context `{!osirisGS Σ}.

  Context `{Hobs : Observe A val}.
  Context {E : coPset} {Ψ : iEff Σ} {Φ : A → iProp Σ} {ζ : exn → iProp Σ}.

  Lemma imp_join ι' μ φ :
    isThread ι' μ φ -∗
    ▷ (∀ x, □ φ x -∗ Φ x) ∧ ▷ (∀ e, □ μ e -∗ ζ e) -∗
    imp (code.join ι') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hvalid HΦ".
    iApply (imp_stop_join ι' inject2 with "Hvalid [HΦ]").
    iSplit.
    - iIntros "!>" (x) "#Hφ". rewrite /continue /=.
      iApply (@imp_ret _ _ A val). reflexivity. iApply ("HΦ" with "Hφ").
    - iIntros "!>" (e) "#Hμ". rewrite /discontinue /=.
      iSpecialize ("HΦ" with "Hμ").
      iApply (@imp_throw Σ with "HΦ").
  Qed.

End imp_exn.

Section imp_exn.

  Context `{!osirisGS Σ}.

  Context `{Hobs : Observe A val}.
  Context {E : coPset} {Ψ : iEff Σ} {Φ : A → iProp Σ} {ζ : exn → iProp Σ}.

  (* Does not actually need to transfer resources, [φ] could be persistent. To
     be renamed when [joinable] subsumes [valid_thread], i.e. when it can talk
     about the outcome *)
  Lemma imp_join_resourceful ι' φ :
    ↑joinN ⊆ E →
    joinable A ι' φ -∗
    ▷ (▷ φ -∗ (∀ x, Φ x) ∧ (∀ e, ζ e)) -∗
    imp (code.join ι') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "%Hmask (%μ & %φ' & Hthread & Hcont) Hφ".
    iApply (imp_fupd E (code.join ι')).
    iApply (imp_fupd_exn E (code.join ι')).
    iApply (imp_join with "Hthread"). iSplit; iNext.
    - iIntros (x) "#Hφ'".
      iSpecialize ("Hcont" $! (O2Ret x) with "Hφ'").
      iMod (fupd_mask_subseteq (↑joinN)); first assumption.
      iMod "Hcont".
      (* TODO: There should be a more straighforward to introduce the masks. *)
      iApply fupd_wand_l. iFrame. iIntros "_".
      iDestruct ("Hφ" with "Hcont") as "[Hφ _]".
      iApply "Hφ".
    - iIntros (x) "#Hφ'".
      iSpecialize ("Hcont" $! (O2Throw x) with "Hφ'").
      iMod (fupd_mask_subseteq (↑joinN)); first assumption.
      iMod "Hcont".
      iApply fupd_wand_l. iFrame. iIntros "_".
      iDestruct ("Hφ" with "Hcont") as "[_ Hφ]".
      iApply "Hφ".
  Qed.

End imp_exn.

Section imp_eval.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.


  Lemma imp_perform `{Encode A} {Φ : A → iProp Σ} (v : val) :
    Ψ allows perform v << (ilift ζ (ireturns Φ)) >> -∗
    imp perform v @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hallows".
    iApply (ewp_perform with "Hallows").
  Qed.

  Lemma imp_module sitems {Q : env -> iProp Σ} η :
    imp (eval_sitems (η, []) sitems) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ '((_, δ) : envs), Q δ }} -∗
    imp (eval_mexpr η (MStruct sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr.
    iApply (imp_bind with "Hsitems").
    iIntros ([η' δ']) "HQ".
    iApply (imp_ret with "HQ"). encode.
  Qed.

  Lemma imp_sitems_cons {Q : envs → iProp Σ} (φ : envs → iProp Σ) sitem sitems (ηδ : envs) :
    imp (eval_sitem ηδ sitem) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    (∀ ηδ, φ ηδ -∗ imp eval_sitems ηδ sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp (eval_sitems ηδ (sitem :: sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply (imp_bind with "Hsitem").
    iIntros ([η' δ']) "Hφ".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_nil Q ηδ :
    Q ηδ -∗
    imp eval_sitems ηδ [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    simpl_eval_sitems.
    iIntros "HQ". destruct ηδ.
    by iApply (imp_ret with "HQ").
  Qed.

  Lemma imp_sitem_letrec_singleton (spec : val → iProp Σ) x af (η δ : env) :
    spec (VCloRec η [RecBinding x af] x) -∗
    imp (eval_sitem (η, δ) (ILetRec [RecBinding x af])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η0, δ0),
            ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem.
    iApply imp_ret. instantiate (1:=(_,_)). reflexivity.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Lemma imp_sitems_letrec sitems (spec : val → iProp Σ) x af (η δ : env) Q :
    spec (VCloRec η [RecBinding x af] x) -∗
    (∀ v, spec v -∗ imp (eval_sitems ((x, v) :: η, (x, v) :: δ) sitems) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}) -∗
    imp (eval_sitems (η, δ) ((ILetRec [RecBinding x af]) :: sitems)) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hspec Hcov".
    iApply (imp_sitems_cons with "[Hspec]").
    { iApply (imp_sitem_letrec_singleton with "Hspec"). }
    iIntros ([??]) "(% & Hspec & [-> ->])".
    iApply ("Hcov" with "Hspec").
  Qed.

  Local Instance observe_env : Observe env env := { observe := id }.

  Lemma imp_struct_let bs (Q : envs → iProp Σ) (Q' : env → iProp Σ) η δ :
    imp (eval_bindings η bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q' }} -∗
    (∀ η', Q' η' -∗ Q (η' ++ η, η' ++ δ)) -∗
    imp (eval_sitem (η, δ) (ILet bs)) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem.
    iApply (imp_bind with "Hbindings").
    iIntros (η') "HQ'".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hmono" with "HQ'").
  Qed.

  Lemma imp_bindings_cons `{Encode A} (Φ : A → iProp Σ) η e bs Q P p :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ (a : A), Φ a -∗ ⌜pattern η [] p #a (P a) False⌝) -∗
    imp eval_bindings η bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }} -∗
    imp eval_bindings η (Binding p e :: bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
      {{ λ η, ∃ a η' δ', ⌜η = η' ++ δ'⌝ ∗ Φ a ∗ ⌜P a η'⌝ ∗ Q δ' }}.
  Proof.
    iIntros "He Hpat Hbs".
    simpl_eval_bindings.
    iApply (imp_Par with "[He Hpat] Hbs").
    { iApply (imp_bind with "He").
      iIntros (?) "HΦ". iApply imp_widen.
      iDestruct ("Hpat" with "HΦ") as "%Hpat".
      unfold pattern in Hpat. simpl.
      destruct (eval_pat η [] p #x).
      - instantiate (1 := (λ η, ∃ x, Φ x ∗ ⌜P x η⌝)%I).
        iFrame. iFrame "%". auto.
      - contradiction. }
    iSplit.
    { iIntros (?) "Hζ !>".
      iApply (imp_throw with "Hζ"). }
    iIntros (x η') "(%a & HΦ & HP) Hη".
    iNext. rewrite /continue. simpl.
    iApply imp_ret. reflexivity.
    iFrame. auto.
  Qed.

  Lemma imp_bindings_nil η :
    ⊢ imp eval_bindings η [] @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ η, ⌜η = []⌝ }}.
  Proof.
    simpl_eval_bindings.
    iApply imp_ret. reflexivity. auto.
  Qed.

  Lemma imp_bind_var `{Encode A} (Φ : A → iProp Σ) η e name :
    imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval_bindings η [Binding (PVar name) e] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
          {{ λ (η' : env), ∃ a : A, Φ a ∧ ⌜η' = [(name, #a)]⌝ }}.
  Proof.
    iIntros "HSpec".
    iApply (imp_wand with "[HSpec]").
    { iApply (imp_bindings_cons with "HSpec").
      - iIntros (a) "HΦ".
        iPureIntro; apply pat_PVar.
        instantiate (1:=(λ a η, η = [(name, #a)])).
        reflexivity.
      - iApply imp_bindings_nil. }
    iIntros (η') "(%a & % & % & -> & HΦ & -> & ->)".
    iFrame. auto.
  Qed.

  Lemma imp_struct_let_single `{Encode A} (spec : A → iProp Σ) name e (η δ : env) :
    imp (eval η e) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    imp (eval_sitem (η, δ) (ILet [Binding (PVar name) e])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η', δ'),
            ∃ a : A, spec a ∧ ⌜η' = (name, #a) :: η ∧ δ' = (name, #a) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    iApply (imp_struct_let with "[Hspec]").
    { iApply (imp_bind_var with "Hspec"). }
    iIntros (?) "(%a & Hspec & ->)".
    iFrame. iPureIntro; split; reflexivity.
  Qed.

  Lemma imp_sitem_extend es (Q : envs -> iProp Σ) (η δ : env) :
    imp eval_type_extensions es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (δ' : env), Q (δ' ++ η, δ' ++ δ) }} -∗
    imp eval_sitem (η,δ) (IExtend es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem.
    iApply (imp_bind _ _ (λ δ', ret (δ' ++ η, δ' ++ δ)) with "Hes").
    iIntros (η') "HQ".
    iApply (imp_ret with "HQ"); reflexivity.
  Qed.

  Lemma imp_sitems_extend sitems x Q η δ :
    (∀ l, l ↦ #() -∗
          imp eval_sitems ((x, VLoc l) :: η, (x, VLoc l) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η,δ) ((IExtend [x]) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (imp_sitems_cons).
    { iApply (imp_sitem_extend).
      iApply imp_alloc.
      iIntros "!>" (l) "Hl"; simpl; iApply imp_ret. reflexivity.
      Unshelve.
      2: (apply (λ ηδ,
                   (∃ l, ⌜ηδ = ((x, VLoc l) :: η, (x, VLoc l):: δ)⌝ ∗ l ↦ VUnit)%I)).
      simpl.
      iExists l; iFrame. iPureIntro; reflexivity. }
    iIntros ([??]) "(% & -> & Hl)".
    iApply ("Hcov" with "Hl").
  Qed.

  Lemma imp_sitem_open me Q φ (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q (δ' ++ η, δ) ) -∗
    imp eval_sitem (η, δ) (IOpen me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "[Hme]").
    { iApply (imp_as_struct with "Hme"). }
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitem_module m me Q (φ : env → iProp Σ) (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q ((m, #δ') :: η, (m, #δ') :: δ) ) -∗
    imp eval_sitem (η, δ) (IModule m me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "Hme").
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_module {m me sitems Q} (φ : env → iProp Σ) (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ imp eval_sitems ((m, #δ') :: η, (m, #δ') :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η, δ) ((IModule m me) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov".
    iApply (imp_sitems_cons with "[Hme]").
    { iApply (imp_sitem_module with "Hme").
      iIntros (δ') "Hφ".
      instantiate (1 := (λ ηδ, ∃ δ', φ δ' ∗ ⌜ηδ = (_,_)⌝)%I).
      iFrame. auto. }
    iIntros (?) "(% & Hφ & ->)".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_type_extension_cons e es Q :
    ▷ (∀ l, l ↦ #() -∗
            imp eval_type_extensions es @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ δ, Q ((e, VLoc l) :: δ) }}) -∗
    imp eval_type_extensions (e :: es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes".
    iApply imp_alloc.
    iIntros "!>" (l) "Hl".
    iSpecialize ("Hes" with "Hl").
    iApply (imp_bind with "Hes").
    iIntros (η) "HQ".
    iApply (imp_ret with "HQ"). reflexivity.
  Qed.

  Lemma imp_type_extension_nil :
    ⊢ imp eval_type_extensions [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ η, ⌜η = []⌝ }}.
  Proof. simpl. by iApply imp_ret. Qed.

  Lemma imp_let `{Encode A} (spec : A → iProp Σ) x e Q η δ :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    (∀ a, spec a -∗ Q ((x, #a) :: η, (x, #a) :: δ)) -∗
    imp eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He HQ".
    iApply (imp_wand _ (eval_sitem (η, δ) (ILet [Binding (PVar x) e])) with "[He]").
    iApply (imp_struct_let_single with "He").
    iIntros ([η' δ']) "(%a & Ha & -> & ->)".
    iApply ("HQ" with "Ha").
  Qed.

  Lemma imp_sitems_let `{Encode A} (spec : A → iProp Σ) sitems x e Q η δ :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
      (∀ a, spec a -∗
            imp eval_sitems ((x, #a) :: η, (x, #a) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
      imp eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    iApply (imp_let with "He").
    instantiate (1 := (λ ηδ, ∃ a, spec a ∗ ⌜ηδ = (x ~> #a; η, x ~> #a; δ)⌝)%I).
    iIntros (a) "Ha". iFrame. auto.
    iIntros (ηδ) "(%a & Ha & ->)".
    iApply ("Hcov" with "Ha").
  Qed.

  Lemma imp_sitems_external Φ sitems x e Q η δ :
    imp eval [] e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ v, Φ v -∗ imp eval_sitems ((x, v) :: η, (x, v) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η, δ) ((IExternal x e)::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    { simpl_eval_sitem.
      instantiate (1 := (λ ηδ, ∃ x0, ⌜ηδ = (x ~> x0; η, x ~> x0; δ)⌝ ∗ Φ x0)%I).
      iApply (imp_bind with "He").
      iIntros (?) "HΦ".
      iApply imp_ret; first (instantiate (1:=(_,_)); encode).
      by iFrame. }
    iIntros (?) "(% & -> & HΦ)".
    iApply ("Hcov" with "HΦ").
  Qed.

End imp_eval.
