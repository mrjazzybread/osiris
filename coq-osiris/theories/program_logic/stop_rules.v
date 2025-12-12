Require Import Coq.Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.program_logic Require Import thread_step ewp tactics basic_rules.
From osiris.semantics Require Import semantics.


From osiris.program_logic.pure Require Export pure.


Section ewp_stop.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  (* ------------------------------------------------------------------------ *)

  (* The following lemmas offer reasoning rules for each of the system calls,
     that is, for computations of the form [Stop c x y]. They are simple
     consequences of the operational behavior of these system calls. *)

  (* [CAlloc]. *)

  (* The standard memory allocation rule of Separation Logic. *)

  Lemma ewp_alloc' {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          pointsto l (DfracOwn 1) (V v) ∗ meta_token l ⊤ -∗
          EWP (continue k l) @ E <| Ψ |> {{ φ }}) ⊢
      EWP (Stop CAlloc v k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    destruct Ψ.
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_thread_step.
    (* Allocate a new location in the ghost heap. *)
    iDestruct (gen_heap_alloc with "Hsi") as ">[Hsi [HH HM]]"; first done.
    ewp_mask_elim. iFrame. by iApply "H"; iFrame.
  Qed.

  Lemma ewp_alloc {B Y} E v (k : _ → micro B Y) φ Ψ :
    ▷ (∀ l,
          pointsto l (DfracOwn 1) (V v) -∗
          EWP (continue k l) @ E <| Ψ |>  {{ φ }}) ⊢
    EWP (Stop CAlloc v k) @ E <| Ψ |>  {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_alloc'; iNext.
    iIntros (l) "(Hl & _)".
    iApply ("H" with "Hl").
  Qed.

  (* [CStore]. *)

  (* The standard memory write rule of Separation Logic. *)

  Lemma ewp_store {B Y} E l v v' (k : _ → micro B Y) φ Ψ :
    pointsto l (DfracOwn 1) (V v) ⊢
    ▷ (
        pointsto l (DfracOwn 1) (V v') -∗
        EWP (continue k #()) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CStore (l, v') k) @ E <| Ψ |> {{ φ }}.
  Proof.
    destruct Ψ.
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

  Lemma ewp_load {B Y} E l v dq (k: _ → micro B Y) φ Ψ:
    ▷ pointsto l dq (V v) ⊢
    ▷ (
        pointsto l dq (V v) -∗
        EWP (continue k v) @ E <| Ψ |> {{ φ }}
      ) -∗
    EWP (Stop CLoad l k) @ E <| Ψ |> {{ φ }}.
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

  Lemma ewp_stop_fork {B Y} φ E Ψ v1 v2 (k : _ -> micro B Y) Φ :
    ▷ (∀ ι',
          valid_thread ι' φ -∗
          EWP call v1 v2 @ E <| (ι', ⊥) |> {{ λ o, □ φ o }} ∗
          EWP (continue k (VThread ι')) @ E <| Ψ |> {{ Φ }}) -∗
    EWP (Stop CFork (v1, v2) k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    destruct Ψ.
    iIntros "Hfork".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_thread_step.
    iMod (thread_alloc π ι' φ (not_elem_of_dom_1 _ _ H) with "Hti")
      as "(%γ & Hti & #Hvalid & #Hsaved)".
    ewp_mask_elim.
    iAssert (valid_thread ι' φ) as "Hvalid'". iFrame "#".
    iDestruct ("Hfork" with "Hvalid'") as "[Hcall $]".
    iExists φ, γ. iFrame "Hsi Hti Hcall Hsaved".
  Qed.

  Lemma ewp_fork E Ψ v1 v2 Φ φ :
    ▷ (∀ ι',
          valid_thread ι' φ -∗
          EWP call v1 v2 @ E <| (ι', ⊥) |> {{ λ o, □ φ o }} ∗
          Φ (O2Ret (VThread ι'))) -∗
    EWP (fork v1 v2) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply ewp_stop_fork.
    iIntros "!>" (ι') "Hvalid"; iDestruct ("HΦ" with "Hvalid") as "[Hcall HΦ]"; iFrame.
    iApply ewp_value. iApply "HΦ".
  Qed.

  Lemma ewp_stop_join {B X'} E Ψ ι Φ (k : _ -> micro B X') φ :
    valid_thread ι φ -∗
    ▷ (∀ o, φ o -∗ EWP k o @ E <| Ψ |> {{ Φ }}) -∗
    EWP (Stop CJoin ι k) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hι Hk". destruct Ψ.
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    iPoseProof (valid_thread_lookup with "Hti Hι") as "(Hti & %γ & %Hlookup & Hsaved)".
    assert (ι ∈ dom π) as Hdom by (apply (elem_of_dom π ι); eexists; eassumption).
    rewrite Hlookup.
    iIntros "%φ' Hφ' %o #Ho".
    iPoseProof (saved_prop.saved_pred_agree _ _ _ _ _ o with "Hsaved Hφ'") as "Heq".
    ewp_mask_elim. iFrame.
    iApply "Hk".
    by iRewrite "Heq".
  Qed.

  Lemma ewp_join E Ψ ι Φ φ :
    valid_thread ι φ -∗
    ▷ (∀ o, φ o -∗ Φ o) -∗
    EWP (join ι) @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "Hvalid HΦ".
    iApply (ewp_stop_join with "Hvalid").
    iNext.
    iIntros (o) "Hdead".
    iApply ewp_outcome2.
    iApply ("HΦ" with "Hdead").
  Qed.

  Lemma ewp_stop_self {B X'} E Ψ u ι Φ (k : _ -> micro B X') :
    ▷ EWP (k (O2Ret (VThread ι))) @ E <| (ι, Ψ) |> {{ Φ }} -∗
    EWP (Stop CSelf u k) @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "Hk".
    rewrite {1}(ewp_unfold (Stop CSelf u k)) /ewp_pre /=.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret. destruct_thread_step.
    ewp_mask_elim. iFrame.
  Qed.

  Lemma ewp_self E Ψ ι Φ :
    (Φ (O2Ret (VThread ι))) -∗
    EWP self @ E <| (ι, Ψ) |> {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply ewp_stop_self.
    iApply ewp_value. by iApply "HΦ".
  Qed.

  (* [CResume]. *)

  (* Resuming a continuation from a location in the store. *)

  Lemma ewp_resume {B Y} E l o sk (k: _ → micro B Y) φ ψ :
    isCont l sk ⊢
    (isShot l -∗
     ▷   EWP (try2 (sk o) k) @ E <| ψ |> {{ φ }}) -∗
    EWP (Stop CResume (l, o) k) @ E <| ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hwp". destruct ψ.
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

  Lemma ewp_resume_crash {B Y} E l o (k: _ → micro B Y) Ψ φ:
    isShot l -∗
    EWP (crash "resume error: unbound location") @ E <| Ψ |> {{ φ }} -∗
    EWP (Stop CResume (l, o) k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hl Hcrash". destruct Ψ.
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (gen_heap_valid with "Hsi Hl")  as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_thread_step.

    (* Update the ghost heap. *)
    ewp_mask_elim.
    rewrite /step_resume_1 /step_resume_2 H0. iFrame.
  Qed.

  (* [CWrap]. *)

  (* Installing a handler with branches [bs] on top of a continuation
     that is located in the store at location [l]. *)

  Lemma ewp_wrap_deep {B Y} E l η bs (k: _ -> micro B Y) φ Ψ :
    (∀ l',
      l'↦
        (K (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs))) -∗
     ▷ EWP (continue k l') @ E <| Ψ |> {{ φ }}) -∗
    EWP (Stop CWrap (true, l, η, bs) k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp". destruct Ψ.
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* The reduction step must be a successful step. *)
    destruct_thread_step.

    (* Allocate a new location in the heap. *)
    iMod (gen_heap.gen_heap_alloc with "Hsi") as "(Hsi & Hl' & _)"; first done.
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim.
    iFrame.
  Qed.

  Lemma ewp_wrap_shallow {B Y} E l η bs (k: _ -> micro B Y) φ Ψ :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs)) -∗
     ▷ EWP (continue k l') @ E <| Ψ |> {{ φ }}) -∗
    EWP (Stop CWrap (false, l, η, bs) k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "Hwp". destruct Ψ.
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
  Lemma ewp_stop_flip {B Y E} u (k: _ → micro B Y) {φ} Ψ :
      ▷(EWP continue k true @ E <| Ψ |> {{ φ }} ∧ EWP continue k false @ E <| Ψ |> {{ φ }})
      ⊢ EWP (Stop CFlip u k) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H". destruct Ψ.
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
  Lemma ewp_flip {E} {φ} Ψ :
      ▷( φ (O2Ret true) ∧ φ (O2Ret false))
      ⊢ EWP flip @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_stop_flip. iNext.
    iSplit.
    - iDestruct "H" as "[H _]".
      by iApply ewp_value.
    - iDestruct "H" as "[_ H]".
      by iApply ewp_value.
  Qed.

  Lemma ewp_choose (m1 m2 : micro A exn) E {φ} Ψ :
    ▷(EWP m1 @ E <| Ψ |> {{ φ }} ∧ EWP m2 @ E <| Ψ |> {{ φ }})
      ⊢ EWP (choose m1 m2) @ E <| Ψ |> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_bind.
    iApply ewp_flip. iNext.
    iSplit.
    - iApply (bi.and_elim_l with "H").
    - iApply (bi.and_elim_r with "H").
  Qed.

End ewp_stop.


Section ewp_eval.

  Context `{!osirisGS Σ}.

  Lemma ewp_module η sitems E Ψ (Q : val -> iProp Σ) :
    EWP (eval_sitems (η, []) sitems) @ E <| Ψ |> {{ ensures '(_, δ), Q (VStruct δ) }} -∗
      EWP (eval_mexpr η (MStruct sitems)) @E <| Ψ |> {{ ensures v, Q v }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr. iApply ewp_bind.
    iApply (ewp_mono with "Hsitems").
    iIntros ([ ηδ | e ]); [ simpl | done ].
    destruct ηδ; iIntros "HQ".
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitems_cons ηδ sitem sitems E Ψ Q (φ : env * env -> iProp Σ) :
    EWP eval_sitem ηδ sitem @ E <| Ψ |> {{ ensures ηδ, φ ηδ }} -∗
      (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| Ψ |> {{ Q }}) -∗
      EWP eval_sitems ηδ (sitem :: sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply ewp_bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

  Lemma ewp_sitems_nil ηδ E Ψ Q :
    Q (O2Ret ηδ) -∗
      EWP eval_sitems ηδ [] @ E <| Ψ |> {{ Q }}.
  Proof.
    simpl_eval_sitems.
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitem_letrec_singleton (spec : val -> iProp Σ) η δ x af E Ψ :
    spec (VCloRec η [RecBinding x af] x) -∗
      EWP eval_sitem (η, δ) (ILetRec [RecBinding x af]) @ E <| Ψ |>
      {{ ensures '(η0, δ0),
          ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem. iApply ewp_value. simpl.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

  Lemma ewp_struct_let η δ bs E Ψ Q Q' :
    EWP (eval_bindings η bs) @ E <| Ψ |> {{ ensures η, Q' η }} -∗
      (∀ η', Q' η' -∗ Q (O2Ret (η' ++ η, η' ++ δ))) -∗
      EWP (eval_sitem (η, δ) (ILet bs)) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hbindings").
    iIntros ([ | ]); [ simpl | done ].
    iIntros. iApply ewp_value.
    by iApply "Hmono".
  Qed.

  Lemma ewp_struct_let_single spec η δ name e E Ψ :
    EWP (eval η e) @ E <| Ψ |> {{ ensures v, spec v }} -∗
      EWP (eval_sitem (η, δ) (ILet [Binding (PVar name) e])) @ E <| Ψ |>
      {{ ensures '(η', δ'),
          ∃ v : val, spec v ∧ ⌜η' = (name, v) :: η ∧ δ' = (name, v) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem; simpl_eval_bindings. iApply ewp_bind.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "Hspec").
    { by iApply ewp_value. }
    iIntros (v ?) "Hspec ->". simpl_eval_pat; unfold widen; simpl.
    rewrite try_ret. iApply ewp_value. simpl. iApply ewp_value.
    iExists v.
    iFrame. iPureIntro; auto.
  Qed.

  Lemma ewp_sitem_extend η δ es E Ψ (Q : env * env -> iProp Σ) :
    EWP eval_type_extensions es @ E <| Ψ |>
      {{ ensures δ', Q (δ' ++ η, δ' ++ δ) }} -∗
      EWP eval_sitem (η, δ) (IExtend es) @ E <| Ψ |> {{ ensures v, Q v }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem. iApply ewp_bind.
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl; iIntros "HQ" | done ].
    by iApply ewp_value.
  Qed.

  Lemma ewp_sitems_extend sitems η δ x E Ψ Q :
    (∀ ηδ', (∃ l, ⌜ηδ' = ((x, VLoc l) :: η, (x, VLoc l) :: δ)⌝ ∗ l ↦ V #()) -∗
              EWP eval_sitems ηδ' sitems @ E <| Ψ |> {{ Q }}) -∗
      EWP eval_sitems (η, δ) ((IExtend [x]) :: sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (ewp_sitems_cons).
    { iApply (ewp_sitem_extend).
      iApply ewp_alloc.
      iIntros "!>" (l) "Hl".
      rewrite /continue. iApply ewp_value.
      Unshelve.
      2: (apply (λ ηδ,
              (∃ l, ⌜ηδ = ((x, VLoc l) :: η, (x, VLoc l):: δ)⌝ ∗ l ↦ V VUnit)%I)).
      iExists l; iFrame. iPureIntro; reflexivity. }
    iApply "Hcov".
  Qed.

  Lemma ewp_sitem_open η δ me E Ψ Q φ δ' :
    EWP eval_mexpr η me @ E <| Ψ |> {{ ensures v, ⌜ v = VStruct δ' ⌝ ∗ φ δ' }} -∗
    ( ∀ δ', φ δ' -∗ Q (O2Ret (δ' ++ η, δ)) ) -∗
    EWP eval_sitem (η, δ) (IOpen me) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply ewp_bind. iApply ewp_bind.
    iApply (ewp_mono with "Hme").
    iIntros ([|]); [ simpl | done ].
    iIntros "[-> Hφ]".
    iApply ewp_try. repeat iApply ewp_value.
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma ewp_type_extension_cons e es E Ψ Q :
    ▷ (∀ l, l ↦ V #() -∗
          EWP eval_type_extensions es @ E <| Ψ |>
            {{ ensures δ, Q (O2Ret ((e, VLoc l) :: δ)) }}) -∗
    EWP eval_type_extensions (e :: es) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "Hes". simpl.
    iApply ewp_alloc.
    iModIntro.
    iIntros "%l Hl".
    iApply ewp_bind. iApply ewp_value. iApply ewp_bind.
    iSpecialize ("Hes" with "Hl").
    iApply (ewp_mono with "Hes").
    iIntros ([|]); [ simpl | done ]; iIntros "HQ".
    by iApply ewp_value.
  Qed.

  Lemma ewp_type_extension_nil E Ψ Q :
    Q (O2Ret []) -∗
    EWP eval_type_extensions [] @ E <| Ψ |> {{ Q }}.
  Proof. iIntros "HQ". simpl. by iApply ewp_value. Qed.

  Lemma ewp_sitem_let_singleton_var (spec : val -> iProp Σ) η δ x e E Ψ Q :
    EWP eval η e @ E <| Ψ |> {{ ensures v, spec v }} -∗
      (∀ v, spec v -∗ Q (O2Ret ((x, v) :: η, (x, v) :: δ))) -∗
      EWP eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "He HQ".
    simpl_eval_sitem. simpl_eval_bindings.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_value. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    simpl_eval_pat. iApply ewp_value.
    by iApply "HQ".
  Qed.

  Lemma ewp_sitems_let_singleton_var (spec : val -> iProp Σ) sitems η δ x e E Ψ Q :
    EWP eval η e @ E <| Ψ |> {{ ensures v, spec v }} -∗
      (∀ ηδ', (∃ v, ⌜ηδ' = ((x, v) :: η, (x, v) :: δ)⌝ ∗ spec v) -∗
                EWP eval_sitems ηδ' sitems @ E <| Ψ |> {{ Q }}) -∗
      EWP eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| Ψ |> {{ Q }}.
  Proof.
    iIntros "He Hcov".
    simpl_eval_sitems; simpl_eval_bindings; simpl.
    iApply (prove_ewp_Par _ _ _ _ (λ l, ⌜l = []⌝)%I with "He").
    { iApply ewp_value. iPureIntro; reflexivity. }
    iIntros (v1 v2) "Hspec ->".
    unfold widen; simpl_eval_pat; simpl.
    iApply "Hcov".
    iExists v1; by iFrame.
  Qed.

End ewp_eval.
