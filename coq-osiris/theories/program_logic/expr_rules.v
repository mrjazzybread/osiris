From iris Require Import gen_heap proofmode.proofmode proofmode.environments.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp basic_rules stop_rules handler_rules tactics fun_spec.

(** Notations for returning a particular value, when it can be determined at the
time a specification is used, e.g. [EWP eval η (EInt 1 + EInt 2) {{ RET= #3 }}] *)

Notation "'RET=' v , Q" :=
  (lift_ret_spec (λ v', (bi_pure (v' = v) ∗ Q)%I))
    (at level 20, Q, v at level 200,
      format "'RET='  v ,  '/' Q") : bi_scope.

Notation "'RET=' v" :=
  (lift_ret_spec (λ v', (bi_pure (v' = v) ∗ emp)%I))
    (at level 20, v at level 200,
      format "'RET='  v") : bi_scope.

Section ewp_binding_rules.

  Context `{!osirisGS Σ}.

  (* -------------------------------------------------------------------------- *)
  (* Auxiliary lemmas that are useful when proving facts about [EWP eval _] *)

  (* LATER: Strange name conflict on [void.void] *)
  Lemma ewp_widen {A E} (e : micro A void.void) Ψ m φ φ' :
    pure_wp e φ ⊥ ->
    (∀ v, ⌜φ v⌝ -∗ φ' (O2Ret v)) -∗
    EWP (widen e : micro A E) @ m <|Ψ|> {{ φ' }}.
  Proof.
    iIntros (He) "H".
    iApply ewp_mono.
    { iApply pure_ewp.
      eapply pure_wp_widen.
      apply He. }
    iIntros ([|]); [ iIntros "%Hφ" | iIntros ([]) ].
    iApply "H". iPureIntro. apply Hφ.
  Qed.

  Lemma ewp_eval_bindings_cons_total η p e bs
    (φ1 : val -> iProp Σ) (φs : val -> env -> Prop) (φ φ' : env -> iProp Σ) E Ψ :
    EWP eval η e @ E <|Ψ|> {{ ensures v, φ1 v }} -∗
    EWP eval_bindings η bs @ E <|Ψ|> {{ ensures v, φ v }} -∗
    (∀ v δ, φ1 v -∗ φ δ -∗ ⌜pure_wp (irrefutably_extend η δ p v) (φs v) ⊥⌝) -∗
    (∀ v δ, φ1 v -∗  ⌜φs v δ⌝ -∗ φ' δ) -∗
    EWP eval_bindings η (Binding p e :: bs) @ E <|Ψ|> {{ ensures v, φ' v }}.
  Proof.
    iIntros "H1 H2 P Hcons /=".
    simpl_eval_bindings.
    iApply (ewp_Par with "H1 H2 [] []");
      [ by iIntros (v) "H" | by iIntros (v) "H" | .. ].
    iIntros (v δ) "H1 H2".
    unfold irrefutably_extend; cbn.
    iDestruct ("P" with "H1 H2") as "%P".
    iApply ewp_widen; first done.
    iIntros (δ') "Hφs".
    iApply ("Hcons" with "H1 Hφs" ).
  Qed.

  Lemma ewp_eval_bindings_nil η E Ψ :
    ⊢ EWP eval_bindings η [] @ E <|Ψ|> {{ RET= [] }}.
  Proof.
    simpl_eval_bindings; by iApply ewp_ret.
  Qed.

  Corollary ewp_eval_bindings_singleton_total {η p e} Φ φ φs E Ψ :
    EWP eval η e @ E <|Ψ|> {{ ensures v, Φ v }} -∗
    (∀ v, Φ v -∗ ⌜pure_wp (irrefutably_extend η nil p v) (φs v) ⊥⌝) -∗
    (∀ v δ, Φ v -∗ ⌜φs v δ⌝ -∗ φ δ) -∗
    EWP eval_bindings η [ Binding p e ] @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H1 P /=".
    iApply (ewp_eval_bindings_cons_total with "H1").
    { iApply ewp_eval_bindings_nil. }
    iIntros (v δ) "HΦ [-> _]".
    by iApply "P".
  Qed.

  Lemma ewp_eval_bindings_cons η p e bs φ1 φs φ E Ψ :
    EWP eval η e @ E <|Ψ|> {{ φ1 }} -∗
    EWP eval_bindings η bs @ E <|Ψ|> {{ φs }} -∗
    (∀ v : exn, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v : exn, φs (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v δ, φ1 (O2Ret v) ∗ φs (O2Ret δ) -∗
      EWP widen (irrefutably_extend η δ p v)  @ E <|Ψ|> {{ φ }}) -∗
    EWP eval_bindings η (Binding p e :: bs) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval_bindings.
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (v δ) "H1 H2". iApply ("P" $! v δ with "[$]").
  Qed.

End ewp_binding_rules.

Section ewp_rules_expr.

  Context `{!osirisGS Σ}.

  (* -------------------------------------------------------------------------- *)
  (* Lemmas about [expr]s *)

  (** * EPath : path → expr *)

  Lemma ewp_EPath η p φ E Ψ :
    EWP lookup_path η p @ E <|Ψ|> {{ ensures v, φ v }} -∗
    EWP eval η (EPath p) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply ewp_try.
    iApply (ewp_mono with "H").
    iIntros ([|[]]) "A/=".
    by iApply ewp_ret.
  Qed.

  (** * EAnonFun : anonfun → expr *)

  Lemma ewp_EAnonFun `{Encode A} η x e φ E Ψ P :
    ▷ (∀ (vx : A), P vx -∗ EWP eval ((x, #vx)::η) e @ E <| Ψ |> {{ ensures v, φ v }}) -∗
    EWP eval η (EAnonFun (AnonFun x e)) @ E <| Ψ |> {{ ensures v, ∀ (vx : A), P vx -∗ EWP (call v #vx) @ E <| Ψ |> {{ ensures v, φ v}} }}.
  Proof.
    iIntros "H". simpl_eval.
    iApply ewp_ret. simpl.
    iIntros (vx) "HP".
    iApply ewp_please. iModIntro.
    by iApply "H".
  Qed.

  Lemma ewp_EAnonFun_partial `{Encode A, Encode B} η x e (φ : B -> iProp Σ) E Ψ P :
    ▷ (∀ (vx : A), P vx -∗ EWP eval ((x, #vx)::η) e @ E <| Ψ |> {{ ensures #v, φ v }}) -∗
    EWP eval η (EAnonFun (AnonFun x e)) @ E <| Ψ |> {{ ensures v, ∀ (vx : A), P vx -∗ EWP (call v #vx) @ E <| Ψ |> {{ ensures #v, φ v}} }}.
  Proof.
    iIntros "H". simpl_eval.
    iApply ewp_ret. simpl.
    iIntros (vx) "HP".
    iApply ewp_please. iModIntro.
    by iApply "H".
  Qed.


  (** * EApp : expr → expr → expr *)

  Lemma ewp_EApp_exn η e1 e2 φ1 φ2 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1 v2, φ1 (O2Ret v1) -∗ φ2 (O2Ret v2) -∗ EWP call v1 v2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (EApp e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval.
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (?) "E /= //". iApply ewp_throw. iApply ("E1" with "E").
    - iIntros (?) "E /= //". iApply ewp_throw. iApply ("E2" with "E").
    - iIntros (? ?) "? ? /=". iApply ("P" with "[$] [$]").
  Qed.

  Lemma ewp_EApp η e1 e2 v1 v2 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v, ⌜v = v1⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v, ⌜v = v2⌝ }} -∗
    EWP call v1 v2 @ E <|Ψ|> {{ φ }} -∗
    EWP eval η (EApp e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (ewp_EApp_exn with "H1 H2"); try iIntros (?) "[]".
    iIntros (? ?) "-> -> //".
  Qed.

  Lemma ewp_EApp' η e1 e2 φ1 φ2 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v, φ1 v }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v, φ2 v }} -∗
    (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗
       EWP call v1 v2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (EApp e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (ewp_EApp_exn with "H1 H2"); try iIntros (?) "[]".
    iIntros (? ?) "Hφ1 Hφ2".
    iApply ("H" with "Hφ1 Hφ2").
  Qed.

  (* The following [ewp_call_*] lemmas just follow the reduction rules for
  function calls when a closure is applied. For better modularity and smaller
  proof terms, it should generally preferred to have a specification ready for
  the available functions values, having abstracted away the closure values.
  Maybe in some cases, though, having a specification for a simple function
  might be too verbose or be too trivial, and one could simply wish to "just
  reduce" the term, in which case those lemmas may be useful. *)
  Lemma ewp_call_nonrec η x_arg body v_arg φ E Ψ:
    ▷EWP eval ((x_arg, v_arg) :: η) body @ E <|Ψ|> {{ φ }} -∗
    EWP call (VClo η (AnonFun x_arg body)) v_arg @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_eval. iNext.
    iApply (ewp_mono with "H").
    iIntros ([]). iApply ewp_ret. iApply ewp_throw.
  Qed.

  Lemma ewp_call_rec η f x body bs v φ E Ψ:
    lookup_rec_bindings bs f = ret (AnonFun x body) ->
    ▷EWP eval ((x, v) :: eval_rec_bindings η bs ++ η) body @ E <|Ψ|> {{ φ }} -∗
    EWP call (VCloRec η bs f) v @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros (Hlk) "H /=". rewrite Hlk /=.
    iApply ewp_eval. iNext.
    iApply (ewp_mono with "H").
    iIntros ([]). iApply ewp_ret. iApply ewp_throw.
  Qed.

  Lemma ewp_call_rec_1 η f x body v φ E Ψ:
    let vf := VCloRec η [RecBinding f (AnonFun x body)] f in
    ▷EWP eval ((x, v) :: (f, vf) :: η) body @ E <|Ψ|> {{ φ }} -∗
    EWP call vf v @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros (vf) "H". iApply ewp_call_rec; auto.
    rewrite /= String.eqb_refl //.
  Qed.

  (** * ETuple : list expr → expr *)

  Lemma ewp_evals η E es φs φe ψ:
    ([∗ list] ei;φi ∈ es;φs,
       EWP eval η ei @ E <| ψ |> {{ RET v => φi v | EXN e => φe e }}) -∗
    EWP evals η es @ E <| ψ |>
      {{   RET vs => [∗ list] vi; φi ∈ vs; φs, φi vi
         | EXN e => φe e}}.
  Proof.
    iIntros "Hφ".
    iInduction es as [ | ei es ] "IH" forall (φs) "Hφ"; simpl_evals.
    - by iApply ewp_ret.
    - iDestruct (big_sepL2_cons_inv_l with "Hφ")
        as (φi φs') "(-> & Hi & H) /=".
      iApply (ewp_Par with "Hi [H]").
      + iApply ("IH" with "H").
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (v1 vs) "H1 H". iApply ewp_ret. iFrame.
  Qed.

  Lemma ewp_ETuple_forward_exn η es φs φe E Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei @ E <|Ψ|> {{ RET v => φi v | EXN e => φe e }}) -∗
    EWP eval η (ETuple es) @ E <|Ψ|>
      {{  RET v => ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; φi ∈ vs; φs, φi vi
        | EXN e => φe e }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono _ _ (  RET vs => [∗ list] vi; φi ∈ vs; φs, φi vi
                          | EXN v => φe v) with "[-]")%I.
    2: by iIntros ([]) "A/="; auto; iApply ewp_ret; simpl; iExists _; auto.
    iInduction es as [ | ei es ] "IH" forall (φs) "H"; simpl_evals.
    - by iApply ewp_ret.
    - iDestruct (big_sepL2_cons_inv_l with "H") as (φi φs') "(-> & Hi & H) /=".
      iApply (ewp_Par with "Hi [H]").
      + iApply ("IH" with "H").
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (v1 vs) "H1 H". iApply ewp_ret. iFrame.
  Qed.

  Lemma ewp_ETuple_forward η es φs E Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei @ E <|Ψ|> {{ ensures v, φi v }}) -∗
    EWP eval η (ETuple es) @ E <|Ψ|>
      {{ ensures v, ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; φi ∈ vs; φs, φi vi }}.
  Proof.
    iApply ewp_ETuple_forward_exn.
  Qed.

  Lemma ewp_ETuple_exn η es φs φ E Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei @ E <|Ψ|> {{ φi }}) -∗
    (∀ vs, ([∗ list] vi; φi ∈ vs; φs, φi (O2Ret vi)) -∗
       φ (O2Ret (VTuple vs))) -∗
    ([∗ list] φi ∈ φs, ∀ e, φi (O2Throw e) -∗ φ (O2Throw e)) -∗
    EWP eval η (ETuple es) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P E". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "[H E]"); first iApply ewp_evals.
    - iPoseProof (big_sepL2_length with "[$]") as "%".
      setoid_rewrite big_sepL2_fmap_r.
      iAssert (
        [∗ list] _;φi ∈ es;φs, ∀ e : exn, φi (O2Throw e) -∗ φ (O2Throw e)
      )%I with "[E]" as "E". by rewrite big_sepL2_const_sepL_r; auto.
      iApply (big_sepL2_wand with "E").
      iApply (big_sepL2_wand with "H").
      iApply big_sepL2_intro. done. iModIntro.
      iIntros (i ei φi _ Eφi) "H E". iApply (ewp_mono with "H").
      iIntros ([v|e]); auto.
    - iIntros ([v|e]); last auto.
      simpl. iIntros "H".
      iApply ewp_ret.
      iApply "P".
      by rewrite big_sepL2_fmap_r.
  Qed.

  (* Results to handle goals generated by ewp_ETuple_* lemmas *)
  Lemma ewp_list_nil η E Ψ :
    ⊢ ([∗ list] ei;φi ∈ []; [], EWP eval η ei @ E <|Ψ|> {{ φi }}).
  Proof. done. Qed.

  Lemma ewp_list_cons η e es φ φs E Ψ :
    EWP eval η e @ E <|Ψ|> {{ φ }} -∗
    ([∗ list] ei;φi ∈ es;φs, EWP eval η ei @ E <|Ψ|> {{ φi }}) -∗
    ([∗ list] ei;φi ∈ (e :: es);(φ :: φs), EWP eval η ei @ E <|Ψ|> {{ φi }}).
  Proof. iIntros "He Hlist". simpl. iFrame. Qed.

  Lemma ewp_list_singleton η e φ E Ψ :
    EWP eval η e @ E <|Ψ|> {{ φ }} -∗
    ([∗ list] ei;φi ∈ [e]; [φ], EWP eval η ei @ E <|Ψ|> {{ φi }}).
  Proof. iIntros "He". simpl. iFrame. Qed.

  Lemma ewp_ETuple η es φs φ E Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei @ E <|Ψ|> {{ ensures v, φi v }}) -∗
    (∀ vs, ([∗ list] vi; φi ∈ vs; φs, φi vi) -∗ φ (VTuple vs)) -∗
    EWP eval η (ETuple es) @ E <|Ψ|> {{ ensures vs, φ vs }}.
  Proof.
    iIntros "H P".
    iApply (ewp_mono_ret with "[H]").
    iApply (ewp_ETuple_forward with "H").
    iIntros (?) "A".
    iDestruct "A" as (vs) "(-> & A)".
    by iApply "P".
  Qed.

  (** macros for ETuple *)

  Lemma ewp_EUnit_exn η φ E Ψ :
    φ (O2Ret VUnit) -∗
    EWP eval η EUnit @ E <|Ψ|> {{ φ }}.
  Proof.
    simpl_eval; iApply ewp_ret.
  Qed.

  Lemma ewp_EUnit_forward η E Ψ :
    ⊢ EWP eval η EUnit @ E <|Ψ|> {{ RET= #() }}.
  Proof.
    simpl_eval; by iApply ewp_ret.
  Qed.

  Lemma ewp_EPair_exn η e1 e2 (φ1 φ2 φ : outcome2 val exn -> _) E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v1 v2, φ1 (O2Ret v1) -∗ φ2 (O2Ret v2) -∗ φ (O2Ret (#(v1, v2)))) -∗
    (∀ e, φ1 (O2Throw e) -∗ φ (O2Throw e)) -∗
    (∀ e, φ2 (O2Throw e) -∗ φ (O2Throw e)) -∗
    EWP eval η (EPair e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 P E1 E2".
    iApply (ewp_ETuple_exn _ _ [φ1; φ2] with "[H1 H2] [P]").
    - by iFrame.
    - iIntros ([ | v1 [ | v2 [ | ? ? ]]]) "H"; simpl; rewrite ?bi.False_sep; auto.
      iDestruct "H" as "(H1 & H2 & _)". iApply ("P" with "[$] [$]").
    - iSplitL "E1"; auto. iSplitL; auto.
  Qed.

  Lemma ewp_EPair_ret η e1 e2 φ1 φ2 E Ψ φ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v, φ1 v }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v, φ2 v }} -∗
    (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗ φ #(v1, v2)) -∗
    EWP eval η (EPair e1 e2) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EPair_exn with "H1 H2 [P]"); auto.
  Qed.

  Lemma ewp_EPair_ret_encode η e1 e2 `{Encode A} `{Encode B} (v1 : A) (v2 : B) R1 R2 E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures #r, ⌜r = v1⌝ ∗ R1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures #r, ⌜r = v2⌝ ∗ R2 }} -∗
    EWP eval η (EPair e1 e2) @ E <|Ψ|> {{ ensures #r, ⌜r = (v1, v2)⌝ ∗ R1 ∗ R2 }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_mono_ret with "[H1 H2]").
    iApply (ewp_ETuple_forward _ _ ([(λ r, ⌜r = #v1⌝ ∗ R1); (λ r,⌜r = #v2⌝ ∗ R2)]))%I.
    - rewrite !big_sepL2_cons.
      iSplitL "H1"; [ | iSplitL "H2"; auto] .
      + iApply (ewp_mono_ret with "H1"). iIntros (?) "H". by iDestruct "H" as (?) "(-> & -> & $)".
      + iApply (ewp_mono_ret with "H2"). iIntros (?) "H". by iDestruct "H" as (?) "(-> & -> & $)".
    - iIntros (?) "H".
      iDestruct "H" as (vs) "(-> & H)".
      iDestruct (big_sepL2_cons_inv_r with "H") as (_v vs') "(-> & (-> & H1) & H)".
      iDestruct (big_sepL2_cons_inv_r with "H") as (_v vs) "(-> & (-> & H2) & H)".
      iDestruct (big_sepL2_nil_inv_r with "H") as "->".
      iExists (v1, v2). iFrame. auto.
  Qed.

  Lemma ewp_EPair_forward η e1 e2 `{Encode A} `{Encode B} (v1 : A) (v2 : B) R1 R2 E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ RET= #v1, R1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ RET= #v2, R2 }} -∗
    EWP eval η (EPair e1 e2) @ E <|Ψ|> {{ RET= #(v1, v2), R1 ∗ R2 }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_mono_ret with "[-]"). iApply (ewp_EPair_ret_encode with "[H1] [H2]").
    { iApply (ewp_mono_ret with "H1"). iIntros (_v) "(-> & H)". iExists v1.
      iSplit; auto. iSplit; auto. iApply "H". }
    { iApply (ewp_mono_ret with "H2"). iIntros (_v) "(-> & H)". iExists v2.
      iSplit; auto. iSplit; auto. iApply "H". }
    iIntros (v) "H". iDestruct "H" as (_r) "(-> & -> & H)". auto.
  Qed.

  (** * EData : data → expr → expr *)

  Definition propagate_exn {A B E} (φ1 : outcome2 A E → iProp Σ)
    (φ2 : outcome2 B E → iProp Σ) : iProp Σ :=
    (∀ e, φ1 (O2Throw e) -∗ φ2 (O2Throw e))%I.

  Definition propagate_ret_fmap {A B E} (f : A → B) (φ1 : outcome2 A E → iProp Σ)
    (φ2 : outcome2 B E → iProp Σ) : iProp Σ :=
    (∀ a, φ1 (O2Ret a) -∗ φ2 (O2Ret (f a)))%I.

  Lemma ewp_EData_exn η c es E ψ φs φ :
    ([∗ list] ei;φi ∈ es;φs, EWP eval η ei @ E <|ψ|> {{ φi }}) -∗
    (∀ vs, ([∗ list] vi;φi ∈ vs;φs, φi (O2Ret vi)) -∗ φ (O2Ret (VData c vs))) -∗
    ([∗ list] φi ∈ φs, ∀ e, φi (O2Throw e) -∗ φ (O2Throw e)) -∗
    EWP eval η (EData c es) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "H P E /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "[H E]"); first iApply ewp_evals.
    - iPoseProof (big_sepL2_length with "[$]") as "%".
      setoid_rewrite big_sepL2_fmap_r.
      iAssert (
        [∗ list] _;φi ∈ es;φs, ∀ e : exn, φi (O2Throw e) -∗ φ (O2Throw e)
      )%I with "[E]" as "E". by rewrite big_sepL2_const_sepL_r; auto.
      iApply (big_sepL2_wand with "E").
      iApply (big_sepL2_wand with "H").
      iApply big_sepL2_intro. done. iModIntro.
      iIntros (i ei φi _ Eφi) "H E". iApply (ewp_mono with "H").
      iIntros ([v|e]); auto.
    - iIntros ([v|e]); last auto.
      simpl. iIntros "H".
      iApply ewp_ret.
      iApply "P".
      by rewrite big_sepL2_fmap_r.
  Qed.

  Lemma ewp_EData η c es E ψ φs φ :
    ([∗ list] ei;φi ∈ es;φs, EWP eval η ei @ E <| ψ |> {{ ensures v, φi v }}) -∗
    (∀ vs : list val, ([∗ list] vi;φi ∈ vs;φs, φi vi) -∗ φ (VData c vs)) -∗
    EWP eval η (EData c es) @ E <|ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "Hes Hmon /=". simpl_eval.
    iApply ewp_bind.
    replace ('vs ← evals η es; ret (VTuple vs)) with (eval η (ETuple es)); last first.
    { simpl_eval; reflexivity. }
    iApply (ewp_mono with "[Hes]"); first by iApply ewp_evals.
    iIntros (args) "Hargs". destruct args; try done.
    iApply ewp_ret.
    iApply ("Hmon" with "Hargs").
  Qed.

  (* E/VConstant is a macro for E/VData *)
  Lemma ewp_EConstant η c E Ψ φ :
    φ (O2Ret (VConstant c)) -∗
    EWP eval η (EConstant c) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". simpl_eval. by iApply ewp_ret.
  Qed.

  (** * EXData : data → expr → expr *)
  Lemma ewp_EXData_exn η π l e E ψ φ1 φ :
    lookup_path η π = ret (VLoc l) ->
    EWP evals η e @ E <|ψ|> {{ φ1 }} -∗
    propagate_exn φ1 φ -∗
    propagate_ret_fmap (λ v : list val, VXData l v) φ1 φ -∗
    EWP eval η (EXData π e) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros (Hlookup) "He Hexn Hret".
    simpl_eval. rewrite Hlookup. simpl.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "He").
    iIntros ([|]) "Hφ".
    - iApply ewp_ret. by iApply "Hret".
    - by iApply "Hexn".
  Qed.

  Lemma ewp_EXData η π l es E ψ φs φ :
    lookup_path η π = ret (VLoc l) ->
    ([∗ list] ei;φi ∈ es;φs, EWP eval η ei @ E <| ψ |> {{ ensures v, φi v }}) -∗
    (∀ vs : list val, ([∗ list] vi;φi ∈ vs;φs, φi vi) -∗ φ (VXData l vs)) -∗
    EWP eval η (EXData π es) @ E <|ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros (Hlookup) "He Hmon".
    simpl_eval. rewrite Hlookup. simpl.
    iApply ewp_bind.
    replace ('vs ← evals η es; ret (VTuple vs)) with (eval η (ETuple es)); last first.
    {  simpl_eval; reflexivity. }
    iApply (ewp_mono with "[He]"); first by iApply ewp_evals.
    iIntros (args) "Hargs". destruct args; try done.
    iApply ewp_ret.
    by iApply "Hmon".
  Qed.

  (** * ERecord : list fexpr → expr *)
  (** * ERecordUpdate : expr → list fexpr → expr *)
  (** * ERecordAccess : expr → field → expr *)
  (** * EBoolConj : expr → expr → expr *)
  (** * EBoolDisj : expr → expr → expr *)
  (** * EBoolNeg : expr → expr *)
  (** * EInt : Z → expr *)

  Lemma ewp_EInt_forward η i E Ψ :
    ⊢ EWP eval η (EInt i) @ E <|Ψ|> {{ RET= #i }}.
  Proof.
    simpl_eval; by iApply ewp_ret.
  Qed.

  Lemma ewp_EInt η i φ E Ψ :
    φ (O2Ret #i) -∗
    EWP eval η (EInt i) @ E <|Ψ|> {{ φ }}.
  Proof.
    simpl_eval; by iApply ewp_ret.
  Qed.

  (** * EMaxInt : expr *)
  (** * EMinInt : expr *)
  (** * EIntNeg : expr → expr *)
  (** * EIntAdd : expr → expr → expr *)

  Lemma ewp_EIntAdd_exn η e1 e2 φ1 φ2 φ E Ψ :
    EWP as_int (eval η e1) @ E <|Ψ|> {{ φ1 }} -∗
    EWP as_int (eval η e2) @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ n1 n2, φ1 (O2Ret n1) ∗ φ2 (O2Ret n2) -∗ φ (O2Ret (VInt (int.M.add n1 n2)))) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval.
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2". iApply ewp_bind. iApply ewp_ret. iApply ewp_ret.
      iApply "P". iFrame.
  Qed.

  Lemma ewp_EIntAdd η e1 e2 φ1 φ2 φ E Ψ :
    EWP as_int (eval η e1) @ E <|Ψ|> {{ ensures n1, φ1 n1 }} -∗
    EWP as_int (eval η e2) @ E <|Ψ|> {{ ensures n2, φ2 n2 }} -∗
    (∀ n1 n2, φ1 n1 ∗ φ2 n2 -∗ φ (VInt (int.M.add n1 n2))) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> {{ ensures n, φ n }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EIntAdd_exn with "H1 H2"); auto.
  Qed.

  Lemma ewp_EIntAdd' η e1 e2 (φ1 φ2 φ : Z -> iProp Σ) E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures #n1, φ1 n1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures #n2, φ2 n2 }} -∗
    (∀ n1 n2, φ1 n1 ∗ φ2 n2 -∗ φ (n1 + n2)%Z) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> {{ ensures #n, φ n }}.
  Proof.
    iIntros "H1 H2 P".
    pose φ1' := (λ v, ∃ n, ⌜v = repr n⌝∗ φ1 n)%I.
    pose φ2' := (λ v, ∃ n, ⌜v = repr n⌝∗ φ2 n)%I.
    iApply (ewp_EIntAdd _ _ _ φ1' φ2' with "[H1] [H2]"); auto.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      iIntros (v) "H". iDestruct "H" as (?) "(-> & H)".
      iApply ewp_ret. iExists _. by iFrame.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H2").
      iIntros (v) "H". iDestruct "H" as (?) "(-> & H)".
      iApply ewp_ret. iExists _. by iFrame.
    - iIntros (i1 i2) "(H1 & H2)".
      iDestruct "H1" as (n1 ->) "H1".
      iDestruct "H2" as (n2 ->) "H2".
      iSpecialize ("P" with "[$]").
      iExists _. iFrame.
      rewrite M.add_repr_repr. auto.
  Qed.

  Lemma ewp_EIntAdd_simple η e1 e2 (n1 n2 : Z) (R1 R2 : iProp Σ) E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ RET= #n1, R1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ RET= #n2, R2 }} -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> {{ RET= #(n1 + n2)%Z, R1 ∗ R2 }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_EIntAdd _ _ _
              (λ r, ⌜r = repr n1⌝ ∗ R1)
              (λ r, ⌜r = repr n2⌝ ∗ R2) with "[H1] [H2]")%I.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      iIntros (?) "(-> & H)". iApply ewp_ret. simpl. auto.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H2").
      iIntros (?) "(-> & H)". iApply ewp_ret. simpl. auto.
    - iIntros (? ?) "((-> & $) & (-> & $))". iPureIntro.
      rewrite M.add_repr_repr //.
  Qed.

  (** * EIntSub : expr → expr → expr *)
  (** * EIntMul : expr → expr → expr *)
  (** * EIntDiv : expr → expr → expr *)
  (** * EIntMod : expr → expr → expr *)
  (** * EIntLand : expr → expr → expr *)
  (** * EIntLor : expr → expr → expr *)
  (** * EIntLxor : expr → expr → expr *)
  (** * EIntLnot : expr → expr *)
  (** * EIntLsl : expr → expr → expr *)
  (** * EIntLsr : expr → expr → expr *)
  (** * EIntAsr : expr → expr → expr *)
  (** * EFloat : float → expr *)
  (** * EChar : char → expr *)
  (** * EString : string → expr *)
  (** * EOpPhysEq : expr → expr → expr *)
  (** * EOpEq : expr → expr → expr *)

  Lemma ewp_EOpEq_exn η e1 e2 φ1 φ2 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1 v2, φ1 (O2Ret v1) ∗ φ2 (O2Ret v2) -∗
      EWP eq_val v1 v2 @ E <|Ψ|> {{ ensures b, φ (O2Ret (VBool b)) }}) -∗
    EWP eval η (EOpEq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval.
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2 /=". iApply ewp_bind.
      (* iApply ewp_bind. *)
      iSpecialize ("P" with "[$]").
      iApply (ewp_mono with "P").
      iIntros ([b|v]) "H /=//".
      by iApply ewp_ret.
  Qed.

  Lemma ewp_EOpEq η e1 e2 (φ1 φ2 : val -> iProp Σ)
    (φ : outcome2 val exn -> iProp Σ) E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ v1 v2, φ1 v1 ∗ φ2 v2 -∗
      EWP eq_val v1 v2 @ E <|Ψ|> {{ ensures b, φ (O2Ret (VBool b)) }}) -∗
    EWP eval η (EOpEq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EOpEq_exn with "H1 H2"); auto.
    1,2: iIntros (?) "[]".
  Qed.

  Lemma ewp_EOpEq_simple_Z η e1 e2 (n1 n2 : Z) (R1 R2 : iProp Σ) E Ψ :
    representable n1 ->
    representable n2 ->
    EWP eval η e1 @ E <|Ψ|> {{ RET= #n1, R1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ RET= #n2, R2 }} -∗
    EWP eval η (EOpEq e1 e2) @ E <|Ψ|> {{ RET= #(n1 =? n2)%Z, R1 ∗ R2 }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (ewp_EOpEq _ _ _
              (λ r, ⌜r = #n1⌝ ∗ R1)
              (λ r, ⌜r = #n2⌝ ∗ R2) with "[H1] [H2]")%I.
    - iApply (ewp_mono_ret with "H1"). iIntros (?) "(-> & $) //".
    - iApply (ewp_mono_ret with "H2"). iIntros (?) "(-> & $) //".
    - iIntros (? ?) "((-> & H1) & (-> & H2))".
      iApply ewp_ret. iFrame. iPureIntro. auto.
      rewrite eq_repr_repr //.
  Qed.

  (** * EOpNe : expr → expr → expr *)
  (** * EOpLt : expr → expr → expr *)
  (** * EOpLe : expr → expr → expr *)
  (** * EOpGt : expr → expr → expr *)
  (** * EOpGe : expr → expr → expr *)

  (** * ELet : list binding → expr → expr *)

  (* Intermediate lemma: using [eval_bindings] hypothesis *)
  Lemma ewp_ELet_exn η bs e φ1 φ E Ψ :
    EWP eval_bindings η bs @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ δ, φ1 (O2Ret δ) -∗ EWP eval (δ ++ η) e @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη E P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hη").
    iIntros ([δ|v]) "H/=".
    - iApply ("P" with "H").
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_ELet {η bs e} (φ' : env -> iProp Σ) φ E Ψ :
    EWP eval_bindings η bs @ E <|Ψ|> {{ ensures v, φ' v }} -∗
    (∀ δ, φ' δ -∗ EWP eval (δ ++ η) e @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη P /=". simpl_eval.
    iApply ewp_bind.
    iApply (ewp_mono with "Hη").
    iIntros ([δ|v]) "H/="; last done.
    iApply ("P" with "H").
  Qed.

  (* Specialized [ELet] lemmas *)

  (* TODO: Have *_singleton *_cons lemmas about relevant expr constructs *)
  Corollary ewp_ELet_singleton_total {η p e e'} (Φ : val -> iProp Σ) φ φ' E Ψ:
    EWP eval η e' @ E <|Ψ|> {{ ensures v, Φ v }} -∗
    (∀ v, Φ v -∗ ⌜pure_wp (irrefutably_extend η nil p v) (φ v) ⊥⌝) -∗
    (∀ v δ, Φ v -∗ ⌜φ v δ⌝ -∗
            EWP eval (δ ++ η) e @ E <|Ψ|> {{ φ' }}) -∗
    EWP eval η (ELet [ Binding p e' ] e) @ E <|Ψ|> {{ φ' }}.
  Proof.
    iIntros "He' HP He".
    iApply (ewp_ELet (λ δ, EWP eval (δ ++ η) e @ E <|Ψ|> {{ φ' }})%I
      with "[He' HP He]").
    { iApply (ewp_eval_bindings_singleton_total with "He' HP").
      iIntros (v δ) "HΦ Hφ".
      iApply ("He" with "HΦ Hφ"). }
    by iIntros (?) "HΦ".
  Qed.

  (* Special case of [let x = e' in e] *)
  Lemma ewp_ELet_PVar_1 {η x e e'} (Φ : val -> iProp Σ) φ E Ψ:
    EWP eval η e' @ E <|Ψ|> {{ ensures v, Φ v }} -∗
    (∀ v, Φ v -∗ EWP eval ((x, v) :: η) e @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet [Binding (PVar x) e'] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELet_singleton_total with "H").
    iIntros (v) "_".
    iPureIntro. unfold irrefutably_extend. simpl_eval_pat.
    apply pure_wp_ret. instantiate (1 := λ v l, l = [(x, v)]).
    reflexivity.
    iIntros (v δ) "HΦ ->".
    by iApply "P".
  Qed.

  (* Alternative form *)
  Lemma ewp_ELet_PVar_1_forward {η x e e' v} R φ E Ψ:
    EWP eval η e' @ E <|Ψ|> {{ RET= v, R }} -∗
    (R -∗ EWP eval ((x, v) :: η) e @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet [ Binding (PVar x) e' ] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELet_PVar_1 with "H").
    iIntros (_v) "(-> & Hv)".
    iApply ("P" with "Hv").
  Qed.

  (* Special case of [let _ = e' in e] *)
  Lemma ewp_ELet_PAny_1 {η e e'} R φ E Ψ:
    EWP eval η e' @ E <|Ψ|> {{ ensures _, R }} -∗
    (R -∗ EWP eval η e @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet [Binding PAny e'] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELet_singleton_total with "H").
    iIntros (v) "_".
    iPureIntro. unfold irrefutably_extend. simpl_eval_pat.
    apply pure_wp_ret. instantiate (1 := λ v l, l = []).
    reflexivity.
    iIntros (v δ) "HΦ ->".
    by iApply "P".
  Qed.

  (** * ELetRec : list rec_binding → expr → expr *)

  Lemma ewp_ELetRec η bs e φ E Ψ :
    let δ := eval_rec_bindings η bs in
    EWP eval (δ ++ η) e @ E <|Ψ|> {{ φ }} -∗
    EWP eval η (ELetRec bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    simpl_eval; auto.
  Qed.

  (** let rec expressions with one function. Here [a : A] is an auxiliary
  variable one can use to relate pre and postconditions, to be able to describe
  e.g. the state in which the function is called, rather than only depend on the
  variable *)
  Lemma ewp_ELetRec_specced_1 {η f x e1 e2 φ E Ψ} {A : Type} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ EWP call vf v <|Ψ|> {{ φf a }}) -∗
       ∀ a v, R a v -∗ EWP eval ((x, v) :: (f, vf) :: η) e1 <|Ψ|> {{ φf a }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ EWP call vf v <|Ψ|> {{ φf a }}) -∗
      EWP eval ((f, vf) :: η) e2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "#He1 He2".
    iApply ewp_ELetRec. simpl.
    iApply "He2".
    iLöb as "IH".
    iModIntro.
    iIntros (a v) "H".
    iApply ewp_call_rec_1.
    iNext.
    iSpecialize ("He1" with "IH H").
    iApply (ewp_mono with "He1").
    auto.
  Qed.

  Lemma ewp_ELetRec_specced_ret_1 {η f x e1 e2 φ E Ψ} {A} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ EWP call vf v <|Ψ|> {{ ensures v', φf a v' }}) -∗
       ∀ a v, R a v -∗ EWP eval ((x, v) :: (f, vf) :: η) e1 <|Ψ|> {{ ensures v', φf a v' }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ EWP call vf v <|Ψ|> {{ ensures v', φf a v' }}) -∗
      EWP eval ((f, vf) :: η) e2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iApply ewp_ELetRec_specced_1.
  Qed.

  (** * ELetModule : module → mexpr → expr → expr *)

  (** * ELetOpen : mexpr → expr → expr *)
  Lemma ewp_ELetOpen η me e E ψ φ :
    EWP eval_mexpr η me @ E <|ψ|> {{ ensures m, ∃ δ, ⌜ m = VStruct δ ⌝ ∗
    EWP eval (δ ++ η) e @ E <|ψ|> {{ φ }} }} -∗
    EWP eval η (ELetOpen me e) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "Hme". simpl_eval.
    iApply ewp_bind.
    rewrite /as_struct. iApply ewp_bind.
    iApply (ewp_mono with "Hme").
    iIntros ([|]) "Hδ"; [ simpl | done].
    iDestruct "Hδ" as "(%δ & -> & He)".
    iApply ewp_widen. { apply pure_wp_ret; apply eq_refl. }
    by iIntros (?) "->".
  Qed.

  (** * ESeq : expr → expr → expr *)

  Lemma ewp_ESeq_exn η e1 e2 φ1 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1, φ1 (O2Ret v1) -∗ EWP eval η e2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (ESeq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H M P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "/= H1".
    - iApply ("P" with "H1").
    - iApply ("M" with "H1").
  Qed.

  Lemma ewp_ESeq η e1 e2 φ E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ ensures _, EWP eval η e2 @ E <|Ψ|> {{ φ }} }} -∗
    EWP eval η (ESeq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". simpl_eval. by iApply ewp_bind.
  Qed.

  (** * EIfThen : expr → expr → expr *)

  Lemma ewp_EIfThen_exn' η eb e1 φb φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit))) -∗
    EWP eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply ewp_ret; auto.
  Qed.

  Lemma ewp_EIfThen_exn η eb e1 φb φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then EWP eval η e1 @ E <|Ψ|> {{ φ }}
           else φ (O2Ret VUnit)) -∗
    EWP eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply ewp_ret; auto.
  Qed.

  Lemma ewp_EIfThen η eb e1 φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ ensures v,
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit)) }} -∗
    EWP eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (ewp_EIfThen_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EIfThenElse : expr → expr → expr → expr *)

  Lemma ewp_EIfThenElse_exn' η eb e1 e2 φb φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ EWP eval η e2 @ E <|Ψ|> {{ φ }})) -∗
    EWP eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply ewp_ret; auto.
  Qed.

  Lemma ewp_EIfThenElse_exn η eb e1 e2 φb φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then EWP eval η e1 @ E <|Ψ|> {{ φ }}
           else EWP eval η e2 @ E <|Ψ|> {{ φ }}) -∗
    EWP eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P". simpl_eval.
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply ewp_ret; auto.
  Qed.

  Lemma ewp_EIfThenElse η eb e1 e2 φ E Ψ :
    EWP eval η eb @ E <|Ψ|> {{ ensures v,
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ EWP eval η e2 @ E <|Ψ|> {{ φ }}) }} -∗
    EWP eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (ewp_EIfThenElse_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EMatch : expr → list branch → expr *)

  Lemma ewp_EMatch η e bs Ψ E Φ :
    EWP deep_handler η e bs @ E <|Ψ|> {{ Φ }} -∗
    EWP eval η (EMatch e bs) @ E <|Ψ|> {{ Φ }}.
  Proof.
    by iIntros "H"; simpl_eval.
  Qed.

  (** * ERaise : expr → expr *)

  Lemma ewp_ERaise η e φ E Ψ :
    EWP eval η e @ E <|Ψ|> {{ RET v => φ (O2Throw v) | EXN v => φ (O2Throw v)}} -∗
    EWP eval η (ERaise e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([]) "/= H //".
    by iApply ewp_throw.
  Qed.

  (** * EWhile : expr → expr → expr *)
  (** * EFor : var → expr → expr → expr → expr *)
  (** * EAssertFalse : expr *)

  (** * EAssert : expr → expr *)

  Lemma ewp_EAssert_exn η e φ1 φ E Ψ :
    (φ (O2Ret #()))
     ∧
    (EWP eval η e @ E <|Ψ|> {{ φ1 }} ∗
     (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
     (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #())))
    ⊢ EWP eval η (EAssert e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply ewp_choose.
    iNext. iSplit.
    - iApply ewp_ret. iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "(H & E & P)".
      iApply ewp_bind_exn.
      iApply ewp_bind_exn.
      iApply (ewp_mono with "H").
      iIntros ([v|v]) "H /=".
      * iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        repeat iApply ewp_ret.
        iApply "H".
      * iApply ("E" with "H").
  Qed.

  Lemma ewp_EAssert_exn_sep η e φ1 φ E Ψ :
    φ (O2Ret #()) ∗
    (φ (O2Ret #()) -∗ EWP eval η e @ E <|Ψ|> {{ φ1 }}) ∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
    (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #()))
    ⊢ EWP eval η (EAssert e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "(R & H & He & P) /=". simpl_eval.
    iApply ewp_choose.
    iNext. iSplit. by iApply ewp_ret.
    iSpecialize ("H" with "R").
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "H /=".
    - iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        by repeat iApply ewp_ret.
    - iApply ("He" with "H").
  Qed.

  Lemma ewp_EAssert η e R E Ψ :
    R ∧ EWP eval η e @ E <|Ψ|> {{ ensures v, ⌜v = VTrue⌝ ∗ R }} -∗
    EWP eval η (EAssert e) @ E <|Ψ|> {{ ensures _, R }}.
  Proof.
    iIntros "H".
    iApply ewp_EAssert_exn.
    iSplit.
    - iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "H".
      iSplitL "H". iAssumption.
      iSplitL. by iIntros. iIntros (v) "$ //".
  Qed.

  Lemma ewp_EAssert_sep η e R E Ψ :
    R ∗ (R -∗ EWP eval η e @ E <|Ψ|> {{ ensures v, ⌜v = VTrue⌝ ∗ R }}) -∗
    EWP eval η (EAssert e) @ E <|Ψ|> {{ ensures _, R }}.
  Proof.
    iIntros "(? & ?)".
    iApply ewp_EAssert_exn_sep. iFrame. eauto.
  Qed.

  (** * ERef : expr → expr *)

  Lemma ewp_ERef_exn η e φ1 φ E Ψ :
    EWP eval η e @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ1 (O2Ret v) -∗ ∀ l, l ↦ (V v) -∗ φ (O2Ret (VLoc l))) -∗
    EWP eval η (ERef e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "H".
    - iApply ewp_alloc. iNext. iIntros (l) "Hl".
      iApply ewp_bind.
      iApply ewp_ret.
      iApply ewp_ret.
      iApply ("P" with "H"). auto.
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_ERef η e φ1 φ E Ψ :
    EWP eval η e @ E <|Ψ|> {{ ensures v, φ1 v }} -∗
    (∀ v, φ1 v -∗ ∀ l, l ↦ (V v) -∗ φ (VLoc l)) -∗
    EWP eval η (ERef e) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ERef_exn with "H"); auto.
  Qed.

  Lemma ewp_ERef' η e φ1 E Ψ :
    EWP eval η e @ E <|Ψ|> {{ ensures v, φ1 v }} -∗
      EWP eval η (ERef e) @ E <|Ψ|>
      {{ ensures r, ∃ l v,
          ⌜r = VLoc l⌝ ∗ l ↦ (V v) ∗ φ1 v }}.
  Proof.
    iIntros "H".
    iApply (ewp_ERef with "H").
    iIntros (v) "H".
    iIntros (l) "Hl".
    iExists l, v; by iFrame.
  Qed.

  (** * ELoad : expr → expr *)

  Lemma ewp_ELoad_exn η e φ1 φ E Ψ :
    EWP as_loc (eval η e) @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l, φ1 (O2Ret l) -∗ ∃ q v, pointsto l q (V v) ∗ ▷(pointsto l q (V v) -∗ φ (O2Ret v))) -∗
    EWP eval η (ELoad e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=". simpl_eval.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([l|v]) "H1".
    - iSpecialize ("P" with "H1").
      iDestruct "P" as (q v) "(Hl & P)".
      iApply (ewp_load with "Hl"). iNext. iIntros "Hl".
      iApply ewp_ret.
      iApply ("P" with "Hl").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_ELoad η e φ1 φ E Ψ :
    EWP as_loc (eval η e) @ E <|Ψ|> {{ ensures l, φ1 l }} -∗
    (∀ l, φ1 l -∗ ∃ q v, pointsto l q (V v) ∗ ▷(pointsto l q (V v) -∗ φ v)) -∗
    EWP eval η (ELoad e) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELoad_exn with "H"); auto.
  Qed.

  Lemma ewp_ELoad_simple η e (l : loc) q (v : val) E Ψ :
    EWP eval η e @ E <|Ψ|> {{ RET= #l }} -∗
    pointsto l q (V v) -∗ EWP eval η (ELoad e) @ E <|Ψ|> {{ RET= v, pointsto l q (V v) }}.
  Proof.
    iIntros "H Hl". iApply (ewp_ELoad _ _ (λ l1, ⌜l = l1⌝%I) with "[H]").
    - iApply ewp_bind. iApply (ewp_mono_ret with "H").
      by iIntros (?) "(-> & ?)"; iApply ewp_ret.
    - iIntros (? ->). iExists _, _; iFrame. auto.
  Qed.

  (** * EStore : expr → expr → expr *)

  Lemma ewp_EStore_exn η e1 e2 φ1 φ2 φ E Ψ :
    EWP as_loc (eval η e1) @ E <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l1 v2, φ1 (O2Ret l1) ∗ φ2 (O2Ret v2) -∗
      ∃ v1, l1 ↦ (V v1) ∗ ▷(l1 ↦ (V v2) -∗ φ (O2Ret VUnit))) -∗
    EWP eval η (EStore e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval.
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (e) "H1". iApply ewp_throw. iApply ("E1" with "H1").
    - iIntros (e) "H2". iApply ewp_throw. iApply ("E2" with "H2").
    - iIntros (l1 v2) "H1 H2".
      iSpecialize ("P" $! l1 v2 with "[$]").
      iDestruct "P" as (v1) "(Hl1 & P)".
      iApply (ewp_store with "Hl1"). iNext; iIntros "Hl1".
      iApply ewp_ret.
      iApply ("P" with "Hl1").
  Qed.

  Lemma ewp_EStore {η e1 e2} (φ1 : loc -d> iPropO Σ) (φ2 : val -d> iPropO Σ) φ E Ψ :
    EWP as_loc (eval η e1) @ E <|Ψ|> {{ ensures l1, φ1 l1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ l1 v2, φ1 l1 ∗ φ2 v2 -∗
      ∃ v1, l1 ↦ (V v1) ∗ ▷(l1 ↦ (V v2) -∗ φ VUnit)) -∗
    EWP eval η (EStore e1 e2) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EStore_exn with "H1 H2"); auto.
  Qed.

  (* Here, [l↦v] is threaded through [e2], as one is more likely to use
     ownership of [l] in [e2] than in [e1] (i.e. we rarely write things like
     [(!r := 1; r) := 2]) *)
  Lemma ewp_EStore_simple η e1 e2 (l : loc) (v v' : val) E Ψ :
    EWP eval η e1 @ E <|Ψ|> {{ RET= #l }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ RET= v', l ↦ (V v) }} -∗
    EWP eval η (EStore e1 e2) @ E <|Ψ|> {{ RET= #(), l ↦ (V v') }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_EStore (λ l1, ⌜l = l1⌝%I)  with "[H1] H2").
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      by iIntros (?) "(-> & ?)"; iApply ewp_ret.
    - iIntros (? ?) "(-> & -> & Hl)". iExists _. iFrame. auto.
  Qed.

  (** * EPerform : expr -> expr *)

  Lemma ewp_EPerform η e E ψ (φ1 : val -d> iPropO Σ) φ :
    EWP eval η e @ E <|ψ|> {{ ensures v, φ1 v }} -∗
    (∀ v, φ1 v -∗ EWP perform v @ E <|ψ|> {{ φ }} ) -∗
    EWP eval η (EPerform e) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "He Hv".
    simpl_eval. iApply ewp_bind.
    iApply (ewp_mono with "He").
    iIntros ([|]) "Hφ1"; [ by iApply "Hv" | done ].
  Qed.

  (** * EContinue : expr -> expr -> expr *)

  Lemma ewp_EContinue' η e1 e2 E ψ (φ1 : cont -d> iPropO Σ) (φ2 : val -d> iPropO Σ)  φ :
    EWP (eval η e1) @ E <|ψ|> {{ ensures #k, φ1 k }} -∗
    EWP eval η e2 @ E <|ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ (k : cont) v, φ1 k -∗ φ2 v -∗
                EWP stop CResume (k, O2Ret v) @ E <|ψ|> {{ φ }}) -∗
    EWP eval η (EContinue e1 e2) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "Hk Hv Hmon".
    simpl_eval.
    iApply (ewp_Par with "[Hk] Hv"); try done.
    { unfold as_cont. iApply ewp_bind.
      iApply (ewp_mono with "Hk").
      iIntros ([|]); last done.
      iIntros "(%v & -> & Hφ1)".
      iApply ewp_ret. instantiate (1 := (λ o, match o with O2Ret v => φ1 v | O2Throw _ => False end)%I).
      iApply "Hφ1". }
    1-2: simpl; iIntros; try done.
    simpl; iIntros (k v) "Hφ1 Hφ2".
    iApply ("Hmon" with "Hφ1 Hφ2").
  Qed.

  Corollary ewp_EContinue η e1 e2 E ψ (φ1 : cont -d> iPropO Σ) (φ2 : val -d> iPropO Σ)  φ :
    EWP (eval η e1) @ E <|ψ|> {{ ensures #k, φ1 k }} -∗
    EWP eval η e2 @ E <|ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ k v, φ1 k -∗ φ2 v -∗
       ∃ sk, isCont k sk ∗
        (isShot k -∗
            ▷ EWP (sk (O2Ret v)) @ E <|ψ|> {{ φ }})) -∗
    EWP eval η (EContinue e1 e2) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 H3".
    iApply (ewp_EContinue' with "H1 H2").
    iIntros (??) "H1 H2".
    iSpecialize ("H3" with "H1 H2").
    iDestruct "H3" as (?) "(H1 & H2)".
    iApply (ewp_resume with "H1").
    iIntros "H1".
    iSpecialize ("H2" with "H1"). iNext.
    by rewrite try2_inject2_right.
  Qed.

  Lemma ewp_EFork_call φ η e1 e2 E Ψ (φ1 φ2 : val -> iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    ▷ (∀ ι v1 v2, valid_thread ι φ -∗ φ1 v1 -∗ φ2 v2 -∗
                  EWP[ι] call v1 v2 @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    simpl_eval.
    iApply (ewp_Par with "H1 H2").
    { iIntros (e) "[]". }
    { iIntros (e) "[]". }
    iIntros (v1 v2) "H1 H2"; simpl.
    iApply ewp_fork.
    iIntros "!>" (ι) "#Hvalid".
    iSplitR ""; [ | ].
    iApply ("Hcall" with "Hvalid H1 H2").
    iExists _; iFrame "#"; iPureIntro; reflexivity.
  Qed.

  Lemma ewp_EFork `{Encode A} P φ η e1 e2 E Ψ (φ2 : A -> iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures #v2, φ2 v2 }} -∗
    ▷ (∀ ι v m, valid_thread ι φ -∗ φ2 v -∗ P v m -∗ EWP[ι] m @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #v, valid_thread v φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (ewp_EFork_call with "H1 H2").
    iIntros "!>" (ι f v2) "#Hvalid HSpec (%v & -> & H2)".
    rewrite iSpec_equation_1.
    iSpecialize ("HSpec" $! v).
    iApply ("Hcall" $! ι v (call f #v) with "Hvalid H2 HSpec").
  Qed.

  Lemma ewp_EFork_call' φ η e1 e2 E Ψ (φ1 φ2 : val -> iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    ▷ (∀ v1 v2, φ1 v1 -∗ φ2 v2 -∗
                  EWP call v1 v2 @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    simpl_eval.
    iApply (ewp_Par with "H1 H2").
    { iIntros (e) "[]". }
    { iIntros (e) "[]". }
    iIntros (v1 v2) "H1 H2"; simpl.
    iApply ewp_fork.
    iIntros "!>" (ι) "#Hvalid".
    iSplitR ""; [ | ].
    iApply ("Hcall" with "H1 H2").
    iExists _; iFrame "#"; iPureIntro; reflexivity.
  Qed.

  Lemma ewp_EFork' `{Encode A} P φ η e1 e2 E Ψ (φ2 : A -> iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> {{ ensures #v2, φ2 v2 }} -∗
    ▷ (∀ v m, φ2 v -∗ P v m -∗ EWP m @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #v, valid_thread v φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (ewp_EFork_call' with "H1 H2").
    iIntros "!>" (f v2) "HSpec (%v & -> & H2)".
    rewrite iSpec_equation_1.
    iSpecialize ("HSpec" $! v).
    iApply ("Hcall" $! v (call f #v) with "H2 HSpec").
  Qed.

  Lemma ewp_EJoin e η E Ψ φ Φ :
    EWP eval η e @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }} -∗
    ▷ (∀ o, □ φ o -∗ Φ o) -∗
    EWP eval η (EJoin e) @ E <|Ψ|> {{ Φ }}.
  Proof.
    iIntros "Hid Hjoined".
    simpl_eval.
    iApply ewp_bind. unfold as_thread. iApply ewp_bind.
    iApply (ewp_mono with "Hid").
    iIntros ([ ι' |]); [ iIntros "Hvalid" | iIntros "[]" ].
    iDestruct "Hvalid" as "(% & -> & Hvalid)".
    iApply ewp_ret.
    iApply (ewp_join with "Hvalid Hjoined").
  Qed.

End ewp_rules_expr.
