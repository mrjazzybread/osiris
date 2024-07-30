From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_iter.

Context `{!osirisGS Σ}.

Context (A : Type) `{Encode A}.

Definition isListIter (iter : val) : iProp Σ :=
  ∀ (ψ : iEff Σ) E (I : list A → iProp Σ) φ (f : val) (l : list A),
    □ (∀ (Xs : list A) (X : A),
          ⌜ (Xs ++ [X]) `prefix_of` l ⌝ -∗
            I Xs -∗
            EWP (call f #X) @ E <| ψ |> {{ | RET v => ⌜ v = VUnit ⌝ ∗ I (Xs ++ [X]);
                                           | EXN e => φ e ∗ I Xs }})
      -∗
      I [] -∗
      EWP (ncall iter [f; #l] ) @E <| ψ |>
      {{ | RET v => ⌜ v = VUnit ⌝ ∗ I l;
         | EXN e => φ e ∗ ∃ Xs, I Xs ∗ ⌜ Xs `prefix_of` l ⌝ }}.

Lemma ewp_module η sitems (Q : val -> iProp Σ) :
  EWP (eval_sitems (η, []) sitems) {{ RET ηδ, let '(_, δ) := ηδ in Q (VStruct δ) }} -∗
  EWP (eval_mexpr η (MStruct sitems)) {{ RET v, Q v }}.
Proof.
  iIntros "Hsitems".
  simpl_eval_mexpr. Bind.
  iApply (ewp_mono with "Hsitems").
  iIntros ([ ηδ | e ]); [ simpl | done ].
  destruct ηδ; iIntros "HQ".
  by Ret.
Qed.

Lemma ewp_sitems_cons ηδ sitem sitems E ψ Q (φ : env * env -> iProp Σ) :
    EWP eval_sitem ηδ sitem @ E <| ψ |> {{ RET ηδ, φ ηδ }} -∗
    (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| ψ |> {{ Q }}) -∗
    EWP eval_sitems ηδ (sitem :: sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov". simpl_eval_sitems.
    Bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

Lemma ewp_sitems_nil ηδ E ψ Q :
  Q (O2Ret ηδ) -∗
    EWP eval_sitems ηδ [] @ E <| ψ |> {{ Q }}.
Proof.
  simpl_eval_sitems.
  by iApply ewp_value.
Qed.

Lemma ewp_sitem_letrec_singleton (spec : val -> iProp Σ) η δ x af E ψ :
    spec (VCloRec η [RecBinding x af] x) -∗
    EWP eval_sitem (η, δ) (ILetRec [RecBinding x af]) @ E <| ψ |>
    {{ RET ηδ, let '(η0, δ0) := ηδ in
               ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
    }}.
Proof.
  iIntros "Hspec".
  simpl_eval_sitem. Ret. simpl.
  iExists _. iFrame. equality.
Qed.

Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

Ltac prove_handler_spec := rewrite deep_handler_spec_unfold; iSplit.

Lemma iter_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{ RET m, module_spec [("iter", isListIter)] m}}.
Proof.
  iIntros. unfold __main.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_sitem_letrec_singleton isListIter).
    unfold isListIter.
    iIntros (Ψ E I φ f l).
    iIntros "#Hf HI".
    simpl. Bind.
    iApply ewp_call_rec; [ reflexivity | ].
    iNext. simpl_eval. Ret. simpl.

    (* assert ([] `prefix_of` l) as Hpref by apply prefix_nil; revert Hpref. *)
    assert ([] ++ l = l) as Heql by reflexivity; revert Heql.
    generalize (@nil A) at 1 4; intro lpre.
    generalize l at 1 4; intro lsuf.
    intros Heql.

    iLöb as "IH" forall (lsuf lpre Heql) "Hf HI".

    destruct lsuf.
    { Simp; Ret.
      iSplit; [ equality | ].
      rewrite app_nil_r in Heql. rewrite Heql.
      iApply "HI". }

    iApply ewp_call_nonrec. iNext.
    iApply ewp_EMatch.
    iApply (ewp_deep_handler _ _ (ieq ?[y])). { Simp; Ret; equality. }

    prove_handler_spec; last first.
    (* No effects are used, so the effectful case is discarded. *)
    { iIntros (??) "HF".
      by iPoseProof (upcl_bottom with "HF") as "F". }

    iIntros (o) "->".
    ltac2:(skip_branch ()).
    iApply ((deep_handle_cons _ _ _ _ _ _ _ _ (λ δ, ∃ xs' x0, a :: lsuf = x0 :: xs' ∧
                 δ = ("l" ~> #xs';
                  "x" ~> #x0;
                  "__osiris_anonymous_arg" ~> encode_list (a :: lsuf);
                  "f" ~> f;
                  "iter" ~> VCloRec stdlib_env [RecBinding "iter" (Anon ("f" => EAnonFun __fun2))] "iter";
                  stdlib_env))) with "[HI]");
       [ specify_cpattern; pattern_match
       |
       | let F := fresh in iIntros (F); try tauto ].
    { exists lsuf, a. split.
      - reflexivity.
      - inversion H0; subst; reflexivity. }
    { iIntros (δ (? & ? & Hal & ->)).
      inversion Hal; subst; clear Hal.
      iApply (ewp_ESeq_exn with "[HI]").
      { Simp.
        iApply (ewp_mono with "[HI]").
        { iApply "Hf".
          - iPureIntro. instantiate (1 := lpre).
            apply prefix_app. apply prefix_cons. apply prefix_nil.
          - iApply "HI". }
      iIntros (o) "Ho". iExact "Ho". }

      { iIntros (e); simpl.
        iIntros "[Hφ HI]". iFrame.
        iExists lpre. iFrame.
        iPureIntro.
        replace lpre with (lpre ++ []) at 1 by (rewrite app_nil_r; reflexivity).
        apply prefix_app, prefix_nil. }

      { iIntros (vu); simpl.
        iIntros "[-> HI]". fold eval.

        iApply ewp_EApp.
        { iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality).
          iApply ewp_call_rec; [ reflexivity | ].
          Simp. Ret. equality. }
        { iApply ewp_EPath; Ret; equality. }

        iApply (ewp_mono with "[HI]").
        { iApply "IH".
          { iPureIntro.
            instantiate (1 := lpre ++ [x0]).
            rewrite (cons_middle x0 lpre x).
            by rewrite app_assoc. }

          { iIntros "!>" (Xs X) "Hpref HI".
            iApply (ewp_mono with "[-]").
            iApply ("Hf" with "Hpref HI").
            iIntros (?) "?". iAssumption. }

          { iApply "HI". } }

        iIntros (?) "?". iAssumption. } }

    destruct H0 as [|]; [ congruence | ].
    destruct H0 as (? & ? & ? & F).
    tauto. }

  iIntros ([δ η]).
  iIntros "(%iter & Hiter & -> & ->)".

  iApply ewp_sitems_nil. simpl.
  unfold module_spec; intros.
  iExists _; iSplit; [ equality | simpl ].
  iSplit; [ | done ].
  iExists _; iSplit; [ equality | iAssumption ].
Qed.
