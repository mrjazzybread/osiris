From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_mem.

Context `{!osirisGS Σ}.

From Coq Require Import List.

Class Eq {A} :=
  {
    eqb : A -> A -> bool;
  }.

Fixpoint memb `{Eq A} (x : A) l :=
  match l with
  | [] => false
  | y :: l =>
      if eqb x y then true else memb y l
  end.

Definition mem_spec mem :=
  (∀ (A : Type) (H : Encode A) (H0 : Eq) (x : A) (l : list A),
      EWP (ncall mem [ #x; #l]) <|⊥|> {{ RET #b, ⌜b = memb x l⌝ }})%I.

Lemma ewp_struct_let η δ bs Q Ψ :
  EWP (eval_bindings η bs) {{ RET η, Ψ η }} -∗
  (∀ η', Ψ η' -∗ Q (O2Ret (η' ++ η, η' ++ δ))) -∗
  EWP (eval_sitem (η, δ) (ILet bs)) {{ Q }}.
Proof.
  iIntros "Hbindings Hmono".
  simpl_eval_sitem.
  Bind. iApply (ewp_mono with "Hbindings").
  iIntros ([ | ]); [ simpl | done ].
  iIntros. Ret.
  by iApply "Hmono".
Qed.

Lemma ewp_struct_let_single spec η δ name e :
  EWP (eval η e) {{ RET v, spec v }} -∗
    EWP (eval_sitem (η, δ) (ILet [Binding (PVar name) e]))
    {{ RET ηδ,
        let '(η', δ') := ηδ in
        ∃ v : val, spec v ∧ ⌜η' = (name, v) :: η ∧ δ' = (name, v) :: δ⌝
    }}.
Proof.
  iIntros "Hspec".
  simpl_eval_sitem; simpl_eval_bindings.
  Bind. Par. Bind.
  iApply (ewp_mono with "Hspec").
  iIntros ([ v | ]); [ simpl | done ].
  iIntros. simpl_extend. unfold widen, try. simpl.
  Ret. simpl.
  iExists v.
  iFrame. equality.
Qed.

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


Lemma ewp_sitem_extend η δ es E ψ (Q : env * env -> iProp Σ) :
  EWP eval_type_extensions es @ E <| ψ |>
    {{ RET δ', Q (δ' ++ η, δ' ++ δ) }} -∗
    EWP eval_sitem (η, δ) (IExtend es) @ E <| ψ |> {{ RET v, Q v }}.
Proof.
  iIntros "Hes".
  with_strategy transparent [eval_sitem] Simp.
  Bind. iApply (ewp_mono with "Hes").
  iIntros ([|]); [ simpl; by iIntros "HQ" | done ].
Qed.

Lemma ewp_sitems_extend sitems η δ x E ψ Q :
  (∀ ηδ', (∃ l, ⌜ηδ' = ((x, VLoc l) :: η, (x, VLoc l) :: δ)⌝ ∗ l ↦ V #()) -∗
            EWP eval_sitems ηδ' sitems @ E <| ψ |> {{ Q }}) -∗
    EWP eval_sitems (η, δ) ((IExtend [x]) :: sitems) @ E <| ψ |> {{ Q }}.
Proof.
  iIntros "Hcov".
  iApply (ewp_sitems_cons).
  { iApply (ewp_sitem_extend).
    iApply ewp_alloc.
    iIntros "!>" (l) "Hl".
    rewrite /continue. Ret.
    Unshelve.
    2: (apply (λ ηδ,
            (∃ l, ⌜ηδ = (x ~> VLoc l; η, x ~> VLoc l; δ)⌝ ∗ l ↦ V VUnit)%I)).
    iExists l; iFrame. equality. }
  iApply "Hcov".
Qed.

Lemma mem_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{RET m, module_spec [("mem", mem_spec)] m}}.
Proof.
  iIntros.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_struct_let_single mem_spec).
    Simp. Ret. simpl.

    unfold mem_spec.
    iIntros (A ? ? x l).

    simpl.
    Bind. iApply ewp_call_nonrec. iNext.
    Simp. Ret. simpl.
    iApply ewp_call_nonrec. iNext.

    iApply ewp_ELetOpen.
    iApply ewp_module.
    iApply ewp_sitems_extend.

    iIntros ([η δ]) "[%found [-> Hfound]]"; clear η δ.

    iApply ewp_sitems_nil; simpl.

    fold eval. iExists _. iSplit; [ equality | ].

    iApply ewp_EMatch.
    iApply ewp_deep_handler.
    { unfold deco.
      (* Specification needed for Iter! *)
      admit.  }

    rewrite deep_handler_spec_unfold; iSplit.
    { iIntros ([ | ]) "Hf".
      iNext. unfold __branches3.
      admit.
      admit. }

    { iIntros (??) "Hprot".
      iPoseProof (upcl_bottom with "Hprot") as "F".
      done. } }

  iIntros ([η δ]) "[%mem [ Hmem [ -> -> ] ] ]".
  iApply ewp_sitems_nil; simpl.
  unfold module_spec.
  iExists _; iSplit; [ equality | ].
  simpl.
  iSplit; [ | trivial ].
  eauto.
Admitted.
