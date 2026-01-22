From Stdlib Require Import Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import thread_step ewp tactics basic_rules escrows.
From osiris.semantics Require Import semantics.

From osiris.program_logic.pure Require Export pure.


Section imp_stop.

  Context `{!osirisGS Σ}.

  Context {A X : Type} `{Hobs : Observe Encoded A}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {ζ : X → iProp Σ} {Φ : Encoded → iProp Σ}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  (* ------------------------------------------------------------------------ *)

  (* The following lemmas offer reasoning rules for each of the system calls,
     that is, for computations of the form [Stop c x y]. They are simple
     consequences of the operational behavior of these system calls. *)

  (* [CAllocn]. *)

  (* The standard memory allocation rule of Separation Logic. *)
  Lemma imp_allocn' n v (k : _ → micro A X) :
    ▷ (∀ ls,
          ⌜length ls = n⌝ ∗
          ([∗ list] l ∈ ls, pointsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤) -∗
          imp^{ι} (continue k ls) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
      imp^{ι} (Stop CAllocn (n, v) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_thread_step. destruct H as (Hlen & Hdup & Hfresh).
    iDestruct (gen_heap_alloc_big with "Hsi") as ">(Hsi & Hpts & Hmt)".
    { apply map_disjoint_spec. intros l x y.
      instantiate (1 := (list_to_map ((λ l, (l, V v)) <$> ls))).
      intros HF Hlookup.
      apply elem_of_dom_2 in HF. rewrite dom_list_to_map in HF.
      apply elem_of_list_to_set in HF.
      rewrite <- list_fmap_compose in HF.
      apply list_elem_of_fmap_1 in HF as (l' & -> & HF).
      apply Hfresh in HF.
      rewrite Hlookup in HF. discriminate HF. }
    assert (ls = ((λ l : loc, (l, V v)) <$> ls).*1) as Heqls.
    { clear Hlen Hdup Hfresh. induction ls. reflexivity.
      simpl. rewrite -> IHls at 1. reflexivity. }
    rewrite Heqls in Hdup.
    iPoseProof (big_sepM_list_to_map _ _ Hdup with "Hpts") as "Hpts".
    iPoseProof (big_sepM_list_to_map _ _ Hdup with "Hmt") as "Hmt".
    clear Heqls Hdup Hfresh.
    ewp_mask_elim. iFrame. iSplitR "Hsi".
    - iApply "H". iFrame "%".
      clear Hlen.
      iInduction ls as [|l ls IH]. done.
      iApply big_sepL_cons.
      iPoseProof (big_sepL_cons with "Hpts") as "(Hl & Hpts)".
      iPoseProof (big_sepL_cons with "Hmt") as "(Htok & Hmt)".
      iFrame.
      iApply ("IH" with "Hpts Hmt").
    - clear Hlen.
      assert (insertn ls σ v = list_to_map ((λ l : loc, (l, V v)) <$> ls) ∪ σ) as ->.
      { induction ls as [|l ls IH].
        - simpl. by rewrite map_empty_union.
        - simpl. rewrite IH. rewrite insert_union_l.
          reflexivity. }
      iFrame.
  Qed.

  Lemma imp_allocn n v (k : _ → micro A X) :
    ▷ (∀ ls,
          ⌜length ls = n⌝ ∗
          ([∗ list] l ∈ ls, pointsto l (DfracOwn 1) (V v)) -∗
          imp^{ι} (continue k ls) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    imp^{ι} (Stop CAllocn (n, v) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_allocn'; iNext.
    iIntros (ls) "(%Hlen & Hls)".
    iPoseProof (big_sepL_sep with "Hls") as "[Hls _]".
    iApply "H". iFrame "%". iFrame.
  Qed.

  Lemma imp_alloc v (k : _ → micro A X) :
    ▷ (∀ l, pointsto l (DfracOwn 1) (V v) -∗
            imp^{ι} (continue k [l]) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    imp^{ι} (Stop CAllocn (1%nat, v) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_allocn.
    iIntros "!>" (ls) "(%Hlen & Hls)".
    destruct ls; first discriminate Hlen.
    destruct ls; last discriminate Hlen.
    iApply "H".
    iDestruct "Hls" as "[$ _]".
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma imp_store l v v' (k : _ → micro A X) :
    pointsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        pointsto l (DfracOwn 1) (V v') -∗
        imp^{ι} (continue k #()) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    imp^{ι} (Stop CStore (l, v') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
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
        imp^{ι} (continue k v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    imp^{ι} (Stop CLoad l k) @ E <|Ψ|>  ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
         imp^{ι'} call v1 v2 @ E ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ v, □ φ v }} ∗
         imp^{ι} (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hfork".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_thread_step.
    iMod (thread_alloc π ι' _ (not_elem_of_dom_1 _ _ H0) with "Hti")
      as "(%γ & Hti & #Hvalid & #Hsaved)".
    ewp_mask_elim.
    iAssert (valid_thread ι' _) as "Hvalid'". iFrame "#".
    iDestruct ("Hfork" with "Hvalid'") as "[Hcall Hcontinue]".
    iFrame "#∗".
    iApply (ewp_mono with "Hcall").
    iIntros ([|]) "/="; last iIntros "$".
    iIntros "(%a' & -> & #Hφ)".
    iModIntro. iExists a'. auto.
  Qed.

  (* We do not expect that the forked thread needs to know its own postcondition. *)
  Lemma imp_stop_fork `{Encode B} μ (φ : B → iProp Σ) v1 v2 (k : _ -> micro A X) :
    ▷ (∀ ι', isThread ι' μ φ -∗ imp^{ι} (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    ▷ (∀ ι', imp^{ι'} call v1 v2 @ E ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ v, □ φ v }}) -∗
    imp^{ι} (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hcontinue Hfork".
    iApply imp_stop_fork'.
    iIntros "!> %ι' #Hvalid".
    iSplitL "Hfork".
    - iApply "Hfork".
    - iApply ("Hcontinue" with "Hvalid").
  Qed.

  (* [CResume]. *)

  (* Resuming a continuation from a location in the store. *)
  Lemma ewp_resume {B Y} ι E l o sk (k: _ → micro B Y) φ ψ :
    isCont l sk ⊢
    (isShot l -∗
     ▷   imp^{ι} (try2 (sk o) k) @ E <| ψ |> {{ φ }}) -∗
    imp^{ι} (Stop CResume (l, o) k) @ E <| ψ |> {{ φ }}.
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

  Lemma ewp_resume_crash {B Y} ι E l o (k: _ → micro B Y) Ψ φ:
    isShot l -∗
    imp^{ι} (crash "resume error: unbound location") @ E <| Ψ |> {{ φ }} -∗
    imp^{ι} (Stop CResume (l, o) k) @ E <| Ψ |> {{ φ }}.
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

  (* [CWrap]. *)

  (* Installing a handler with branches [bs] on top of a continuation
     that is located in the store at location [l]. *)

  Lemma ewp_wrap_deep {B Y} ι E l η bs (k: _ -> micro B Y) φ Ψ :
    (∀ l',
      l'↦
        (K (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs))) -∗
     ▷ imp^{ι} (continue k l') @ E <| Ψ |> {{ φ }}) -∗
    imp^{ι} (Stop CWrap (true, l, η, bs) k) @ E <| Ψ |> {{ φ }}.
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

  Lemma ewp_wrap_shallow {B Y} ι E l η bs (k: _ -> micro B Y) φ Ψ :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs)) -∗
     ▷ imp^{ι} (continue k l') @ E <| Ψ |> {{ φ }}) -∗
    imp^{ι} (Stop CWrap (false, l, η, bs) k) @ E <| Ψ |> {{ φ }}.
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
  Lemma ewp_stop_flip {B Y E} ι u (k: _ → micro B Y) {φ} Ψ :
      ▷(imp^{ι} continue k true @ E <| Ψ |> {{ φ }} ∧ imp^{ι} continue k false @ E <| Ψ |> {{ φ }})
      ⊢ imp^{ι} (Stop CFlip u k) @ E <| Ψ |> {{ φ }}.
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

  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma ewp_flip {E} {φ} ι Ψ :
      ▷( φ (O2Ret true) ∧ φ (O2Ret false))
      ⊢ imp^{ι} flip @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_stop_flip. iNext.
    iSplit.
    - iDestruct "H" as "[H _]".
      by iApply ewp_ret.
    - iDestruct "H" as "[_ H]".
      by iApply ewp_ret.
  Qed.

  Lemma ewp_choose (m1 m2 : micro A exn) E {φ} ι Ψ :
    ▷(imp^{ι} m1 @ E <| Ψ |> {{ φ }} ∧ imp^{ι} m2 @ E <| Ψ |> {{ φ }})
      ⊢ imp^{ι} (choose m1 m2) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_bind.
    iApply ewp_flip. iNext.
    iSplit.
    - iApply (bi.and_elim_l with "H").
    - iApply (bi.and_elim_r with "H").
  Qed.

End imp_stop.


Section imp_concurrent.

  Context `{!osirisGS Σ}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_fork `{Encode B} {ζ} {Φ : thread → iProp Σ} μ (φ : B → iProp Σ) v1 v2 :
    ▷ (∀ ι',
         isThread ι' μ φ -∗
         imp^{ι'} call v1 v2 @ E ⟨⟨ λ e, □ μ e ⟩⟩ {{ λ o, □ φ o }} ∗
         Φ ι') -∗
    imp^{ι} (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply imp_stop_fork'.
    iIntros "!>" (ι') "Hvalid"; iDestruct ("HΦ" with "Hvalid") as "[Hcall HΦ]"; iFrame.
    iApply ewp_ret.
    iExists ι'. auto.
  Qed.

  (* [joinable ι φ] allows one to join on [ι] and to recover the non-necessarily
  persistent postcondition [φ] (after opening and closing an invariant) *)

  Definition joinN := nroot .@ "join".
  Definition joinable ι φ :=
    (∃ `(Henc : Encode B) ζ (Φ : B → iProp Σ),
        isThread ι ζ Φ ∗ ∀ o, ilift ζ Φ o ={↑joinN}=∗ ▷ φ)%I.

  (* Rule for fork when the postcondition of the spawned thread is persistent *)
  Lemma imp_fork_persistent `{Encode B} {ζ : exn → iProp Σ} {Φ : thread → iProp Σ} φ v1 v2 :
    ▷ (∀ ι',
          □ joinable ι' φ -∗
          imp^{ι'} call v1 v2 @ E {{ λ (_ : B), □ φ }} ∗
          Φ ι') -∗
    imp^{ι} (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
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
          ([∗ list] φ ∈ φs, joinable ι' φ) -∗
          imp^{ι'} call v1 v2 @ E {{ λ (_ : B), [∗] φs }} ∗
          Φ ι') -∗
    imp^{ι} (fork v1 v2) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".

    (* Given [φs], determine a suitable postcondition [ψ] for the spawned
    thread. This requires the ghost update modality because we allocate
    tokens that will be used to transfer resources. *)
    iApply ewp_fupd. iMod (fupd_mask_subseteq ∅) as "Hmod". set_solver.
    iDestruct (alloc_escrow_list joinN φs) as "> (%φ & #Hescrow_intro & Hescrow_elim)".

    (* In the postcondition of the spawned thread we can transfer the resources
    [φs] into [ψ] by the escrow mechanism *)
    iAssert (▷ ∀ ι, ([∗ list] φ ∈ φs, joinable ι φ) -∗
      imp^{ι} call v1 v2 @ E  {{ λ _, □ φ }} ∗ Φ ι)%I
      with "[HΦ]" as "HΦ".
    {
      iIntros "!>" (ι') "Hjs".
      iDestruct ("HΦ" $! ι' with "Hjs") as "(Hcall & $)".
      iPoseProof (ewp_pers_mono with "Hcall []") as "$".
      iIntros "!> %o φs". destruct o; last auto.
      iSpecialize ("Hescrow_intro" with "[φs]").
      iDestruct "φs" as "(%v & Henc & Hφs)". by rewrite -big_sepL_later.
      iApply (fupd_mask_mono ∅). set_solver.
      iMod "Hescrow_intro" as "?".
      iModIntro. iExists a. iFrame. iPureIntro. unfold observe, observe_encode. by rewrite <- solve_encode_val.
    }
    iClear "Hescrow_intro".
    iMod "Hmod".

    (* Apply the basic rule for fork, recover [valid_thread] in the post *)
    iApply imp_fork.
    iIntros "!> !> %ι' #Hvalid".
    iDestruct ("HΦ" $! ι' with "[Hescrow_elim]") as "(Hcall & $)".

    (* From the escrow elimination implication we prove the list of [joinable φ]s *)
    iApply (big_sepL_mono_pers (isThread ι' ⊥ (λ (_ : val), φ)) with "[$]").
    iIntros (k φ' Hk) "(#? & Helim)". iExists val, Encode_val, ⊥, _.
    iSplit; auto. iIntros ([|]); [ auto | iIntros ([]) ].

    iApply (ewp_mono with "Hcall").
    iIntros ([|]); [ | iIntros ([]) ].
    iIntros "(%v & Henc & Hφ)".
    iExists a; auto.
  Qed.

  Lemma imp_stop_join {B X'} ι' (k : _ -> micro B X') φ μ :
    isThread ι' μ φ -∗
    ▷ (∀ o, □ φ o -∗ imp^{ι} k o @ E <| Ψ |> {{ Φ }}) -∗
    imp^{ι} (Stop CJoin ι' k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hι Hk".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    iPoseProof (valid_thread_lookup with "Hti Hι") as "(Hti & %γ & %Hlookup & Hsaved)".
    assert (ι' ∈ dom π) as Hdom by (apply (elem_of_dom π ι'); eexists; eassumption).
    rewrite Hlookup.
    iFrame.
    iIntros "!> %o #Ho".
    ewp_mask_elim.
    iApply ("Hk" with "Ho").
  Qed.

  Lemma ewp_join ι E Ψ ι' Φ φ :
    valid_thread ι' φ -∗
    ▷ (∀ o, □ φ o -∗ Φ o) -∗
    imp^{ι} (join ι') @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hvalid HΦ".
    iApply (ewp_stop_join with "Hvalid").
    iNext.
    iIntros (o) "Hdead".
    iApply (ewp_outcome2 with "[HΦ Hdead]").
    iApply ("HΦ" with "Hdead").
  Qed.

  (* Does not actually need to transfer resources, [φ] could be persistent. To
  be renamed when [joinable] subsumes [valid_thread], i.e. when it can talk
  about the outcome *)
  Lemma ewp_join_resourceful ι E Ψ ι' Φ φ :
    ↑joinN ⊆ E →
    joinable ι' φ -∗
    ▷ (∀ o, ▷ φ -∗ Φ o) -∗
    imp^{ι} (join ι') @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "%Hmask (%ψ & #Hvalid & Hcont) HΦ".
    iApply ewp_fupd_post.
    iApply (ewp_join with "[$]").
    iNext. iIntros "%o Hψ".
    iApply "HΦ".
    iSpecialize ("Hcont" with "Hψ").
    iMod (fupd_mask_subseteq (↑joinN) Hmask) as "O".
    iMod "Hcont".
    iMod "O".
    done.
  Qed.

  Lemma ewp_stop_self {B X'} E Ψ u ι Φ (k : _ -> micro B X') :
    ▷ imp^{ι} (k (O2Ret (VThread ι))) @ E <| Ψ |> {{ Φ }} -∗
    imp^{ι} (Stop CSelf u k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hk".
    rewrite {1}(ewp_unfold (Stop CSelf u k)) /ewp_pre /=.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret. destruct_thread_step.
    ewp_mask_elim. iFrame.
  Qed.

  Lemma ewp_self E Ψ ι :
    ⊢ imp^{ι} self @ E <| Ψ |> {{ ensures #ι', ⌜ι' = ι⌝ }}.
  Proof.
    iApply ewp_stop_self. iNext.
    ewp_unfold_head. iModIntro.
    by iExists ι.
  Qed.

End concurrent.

Section ewp_eval.

  Context `{!osirisGS Σ}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ}.

  Lemma ewp_module sitems (Q : val -> iProp Σ) η :
    imp^{ι} (eval_sitems (η, []) sitems) @ E <| Ψ |> {{ ensures '(_, δ), Q (VStruct δ) }} -∗
      imp^{ι} (eval_mexpr η (MStruct sitems)) @E <| Ψ |> {{ ensures v, Q v }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr. iApply ewp_bind.
    iApply (ewp_mono with "Hsitems").
    iIntros ([ ηδ' | e ]); [ simpl | done ].
    destruct ηδ'; iIntros "HQ".
    by iApply ewp_ret.
  Qed.

  Lemma ewp_sitems_cons sitem sitems Q (φ : env * env -> iProp Σ) ηδ:
    imp^{ι} eval_sitem ηδ sitem @ E <| Ψ |> {{ ensures ηδ, φ ηδ }} -∗
      (∀ ηδ, φ ηδ -∗ imp^{ι} eval_sitems ηδ sitems @ E <| Ψ |> {{ Q }}) -∗
      imp^{ι} eval_sitems ηδ (sitem :: sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply ewp_bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

  Lemma ewp_sitems_nil Q ηδ :
    Q (O2Ret ηδ) -∗
      imp^{ι} eval_sitems ηδ [] @ E <| Ψ |> {{ Q }}.
  Proof.
    simpl_eval_sitems.
    by iApply ewp_ret.
  Qed.

  Lemma ewp_sitem_letrec_singleton (spec : val -> iProp Σ) x af η δ :
    spec (VCloRec η [RecBinding x af] x) -∗
      imp^{ι} eval_sitem (η, δ) (ILetRec [RecBinding x af]) @ E <| Ψ |>
      {{ ensures '(η0, δ0),
          ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem. iApply ewp_ret. simpl.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

  Lemma ewp_struct_let bs Q Q' η δ :
    imp^{ι} (eval_bindings η bs) @ E <| Ψ |> {{ ensures η, Q' η }} -∗
      (∀ η', Q' η' -∗ Q (O2Ret (η' ++ η, η' ++ δ))) -∗
      imp^{ι} (eval_sitem (η, δ) (ILet bs)) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hbindings").
    iIntros ([ | ]); [ simpl | done ].
    iIntros.
    iApply ewp_ret.
    by iApply "Hmono".
  Qed.

  Lemma ewp_struct_let_single spec name e η δ :
    imp^{ι} (eval η e) @ E <| Ψ |> {{ ensures v, spec v }} -∗
      imp^{ι} (eval_sitem (η, δ) (ILet [Binding (PVar name) e])) @ E <| Ψ |>
      {{ ensures '(η', δ'),
          ∃ v : val, spec v ∧ ⌜η' = (name, v) :: η ∧ δ' = (name, v) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem; simpl_eval_bindings. iApply ewp_bind.
    iApply (prove_ewp_Par _ _ _ _ _ (λ l, ⌜l = []⌝)%I with "Hspec").
    { by iApply ewp_ret. }
    iIntros (v ?) "Hspec ->". simpl_eval_pat; unfold widen; simpl.
    rewrite try_ret. iApply ewp_ret. simpl. iApply ewp_ret.
    iExists v.
    iFrame. iPureIntro; auto.
  Qed.

  Lemma ewp_sitem_extend es (Q : env * env -> iProp Σ) η δ :
    imp^{ι} eval_type_extensions es @ E <| Ψ |>
      {{ ensures δ', Q (δ' ++ η, δ' ++ δ) }} -∗
      imp^{ι} eval_sitem (η,δ) (IExtend es) @ E <| Ψ |> {{ ensures v, Q v }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl; iIntros "HQ" | done ].
    by iApply ewp_ret.
  Qed.

  Lemma ewp_sitems_extend sitems x Q η δ :
    (∀ ηδ', (∃ l,
              ⌜ηδ' = ((x, VLoc l) :: η, (x, VLoc l) :: δ)⌝ ∗ l ↦ V #()) -∗
              imp^{ι} eval_sitems ηδ' sitems @ E <| Ψ |> {{ Q }}) -∗
      imp^{ι} eval_sitems (η,δ) ((IExtend [x]) :: sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (ewp_sitems_cons).
    { iApply (ewp_sitem_extend).
      iApply ewp_alloc.
      iIntros "!>" (l) "Hl"; simpl; iApply ewp_ret.
      Unshelve.
      2: (apply (λ ηδ,
                   (∃ l, ⌜ηδ = ((x, VLoc l) :: η, (x, VLoc l):: δ)⌝ ∗ l ↦ V VUnit)%I)).
      simpl.
      iExists l; iFrame. iPureIntro; reflexivity. }
    iApply "Hcov".
  Qed.

  Lemma ewp_sitem_open me Q φ η δ δ' :
    imp^{ι} eval_mexpr η me @ E <| Ψ |> {{ ensures v, ⌜ v = VStruct δ' ⌝ ∗ φ δ' }} -∗
    ( ∀ δ', φ δ' -∗ Q (O2Ret (δ' ++ η, δ)) ) -∗
    imp^{ι} eval_sitem (η, δ) (IOpen me) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply ewp_bind. iApply ewp_bind.
    iApply (ewp_mono with "Hme").
    iIntros ([|]); [ simpl | done ].
    iIntros "[-> Hφ]".
    iApply ewp_try. repeat iApply ewp_ret.
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma ewp_type_extension_cons e es Q :
    ▷ (∀ l, l ↦ V #() -∗
          imp^{ι} eval_type_extensions es @ E <| Ψ |>
            {{ ensures δ, Q (O2Ret ((e, VLoc l) :: δ)) }}) -∗
    imp^{ι} eval_type_extensions (e :: es) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hes".
    iApply ewp_alloc.
    iIntros "!>" (l) "Hl".
    iApply ewp_bind. iApply ewp_ret. iApply ewp_bind.
    iSpecialize ("Hes" with "Hl").
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl | done ]; iIntros "HQ".
    by iApply ewp_ret.
  Qed.

  Lemma ewp_type_extension_nil Q :
    Q (O2Ret []) -∗
    imp^{ι} eval_type_extensions [] @ E <| Ψ |> {{ Q }}.
  Proof. iIntros "HQ". simpl. by iApply ewp_ret. Qed.

  Lemma ewp_sitem_let_singleton_var (spec : val -> iProp Σ) x e Q η δ :
    imp^{ι} eval η e @ E <| Ψ |> {{ ensures v, spec v }} -∗
      (∀ v, spec v -∗ Q (O2Ret ((x, v) :: η, (x, v) :: δ))) -∗
      imp^{ι} eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "He HQ".
    simpl_eval_sitem. simpl_eval_bindings.
    iApply (prove_ewp_Par _ _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_ret. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    simpl_eval_pat. iApply ewp_ret.
    by iApply "HQ".
  Qed.

  Lemma ewp_sitems_let_singleton_var (spec : val -> iProp Σ) sitems x e Q η δ :
    imp^{ι} eval η e @ E <| Ψ |> {{ ensures v, spec v }} -∗
      (∀ ηδ', (∃ v, ⌜ηδ' = ((x, v) :: η, (x, v) :: δ)⌝ ∗ spec v) -∗
                imp^{ι} eval_sitems ηδ' sitems @ E <| Ψ |> {{ Q }}) -∗
      imp^{ι} eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "He Hcov".
    simpl_eval_sitems; simpl_eval_bindings; simpl.
    iApply (prove_ewp_Par _ _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_ret. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    unfold widen; simpl_eval_pat; simpl.
    iApply "Hcov".
    iExists v1; by iFrame.
  Qed.

End ewp_eval.
