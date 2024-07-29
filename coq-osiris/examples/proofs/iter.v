From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_iter.

Context `{!osirisGS Σ}.

Context (A : Type) `{Encode A}.

Fixpoint iter_post to E Ψ f (φf : A -> outcome2 val exn -> iProp Σ) (l : list A) :=
  (match l with
   | [] => ⌜to = O2Ret VUnit⌝
   | x :: l =>
       EWP call f #x @ E <|Ψ|> {{ λ o, φf x o ∧
             match o with
             | O2Ret _ => iter_post to E Ψ f φf l
             | O2Throw e => ⌜to = O2Throw e⌝
             end }}
  end)%I.

Definition iter_spec : val -d> iPropI Σ :=
  (λ iter,
    ∀ E Ψ f φf (l : list A),
      (* Calling [iter] on an empty list returns unit. *)
      (* Calling [iter] on [x :: l] gives [φf] and keeps going if the
         outcome of [f x] is not an exception. *)
      (□ (∀ (x : A), EWP call f #x @ E <|Ψ|> {{ φf x }})) -∗
        EWP (ncall iter [ f; #l ]) @ E <|Ψ|> {{ λ o, iter_post o E Ψ f φf l }}
  )%I.

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
    {{ RET m, module_spec [("iter", iter_spec)] m}}.
Proof.
  iIntros. unfold __main.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_sitem_letrec_singleton iter_spec).
    unfold iter_spec.
    iIntros (E Ψ f φf l) "#Hf".
    simpl. with_strategy transparent [call] simpl.
    iApply ewp_eval. iNext.
    simpl_eval. Ret. simpl.

    iLöb as "IH" forall (l).

    destruct l.
    { Simp. Ret. done. }

    Simp. simpl. iApply ewp_bind_exn.
    iSpecialize ("Hf" $! a).
    iApply (ewp_mono with "Hf").
    iIntros (o) "Hφf".
    destruct o; last first.
    { simpl. iApply (ewp_mono with "Hf").
      iIntros (o) "Ho". iFrame. destruct o.

    iApply ewp_call_rec; [ reflexivity | ].
    iNext.

    Simp. Ret. simpl.
    change (VCons #a (encode_list l)) with #(a :: l).
    generalize dependent l. intros l.
    iLöb as "IH" forall (l).
    iApply ewp_call_nonrec. iNext.
    iApply ewp_EMatch.

    iApply (ewp_deep_handler _ _ (ieq ?[y])).
    { Simp. Ret. equality. }

    prove_handler_spec; last first.
    (* No effects are used, so the effectful case is discarded. *)
    { iIntros (??) "HF".
      by iPoseProof (upcl_bottom with "HF") as "F". }

    iIntros (o) "->". unfold __branches1.
    iNext.
    ltac2:(skip_branch ()).
    iApply (deep_handle_cons).
    { specify_cpattern; pattern_match. inversion H0; subst. apply eq_refl. }
    { iIntros (? <-).
      iApply (ewp_ESeq_exn with "[-]").
      iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality).
      { iApply "Hf". }
      { iIntros (?) "Hφ". iFrame. equality. }
      { iIntros (vunit) "Hφ".
        iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality); try eauto.
        iApply ewp_EApp_exn; try (iApply ewp_EPath; Ret; equality); try eauto.
        iIntros (v1 v2) "<- <-"; simpl. iApply ewp_call_rec; [ reflexivity | ].
        Simp. Ret. equality.
        { Simp. Ret. equality. }





      { iIntros (? []). }
      { iIntros (? []). }
      { iIntros (??) "<- <-"; simpl.


      iApply ewp_call_rec.
      (iApply (deep_handle_cons with "[-]"));
      [ specify_cpattern; pattern_match
      |
      | let F := fresh in iIntros (F); try tauto ].
      ltac2:(enter_branch ()).
      pattern_match.
