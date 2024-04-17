From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang semantics.
From osiris.program_logic Require Import ewp basic_rules.

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

Section ewp_rules_expr.

  Context `{!osirisGS Σ}.

  (** * EPath : path → expr *)

  Lemma ewp_EPath η p φ Ψ :
    EWP lookup_path η p <|Ψ|> {{ RET v, φ v }} -∗
    EWP eval η (EPath p) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H /=".
    iApply ewp_try.
    iApply (ewp_mono with "H").
    iIntros ([|[]]) "A/=".
    by iApply ewp_value.
  Qed.

  (** * EAnonFun : anonfun → expr *)
  (** * EApp : expr → expr → expr *)

  Lemma ewp_EApp_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1 v2, φ1 (O2Ret v1) -∗ φ2 (O2Ret v2) -∗ EWP call v1 v2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (EApp e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (?) "E /= //". iApply ewp_throw. iApply ("E1" with "E").
    - iIntros (?) "E /= //". iApply ewp_throw. iApply ("E2" with "E").
    - iIntros (? ?) "? ? /=". iApply ("P" with "[$] [$]").
  Qed.

  Lemma ewp_EApp η e1 e2 v1 v2 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ RET v, ⌜v = v1⌝ }} -∗
    EWP eval η e2 <|Ψ|> {{ RET v, ⌜v = v2⌝ }} -∗
    EWP call v1 v2 <|Ψ|> {{ φ }} -∗
    EWP eval η (EApp e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (ewp_EApp_exn with "H1 H2"); try iIntros (?) "[]".
    iIntros (? ?) "-> -> //".
  Qed.

  (* The following [ewp_call_*] lemmas just follow the reduction rules for
  function calls when a closure is applied. For better modularity and smaller
  proof terms, it should generally preferred to have a specification ready for
  the available functions values, having abstracted away the closure values.
  Maybe in some cases, though, having a specification for a simple function
  might be too verbose or be too trivial, and one could simply wish to "just
  reduce" the term, in which case those lemmas may be useful. *)
  Lemma ewp_call_nonrec η x_arg body v_arg φ Ψ:
    ▷EWP eval ((x_arg, v_arg) :: η) body <|Ψ|> {{ φ }} -∗
    EWP call (VClo η (AnonFun x_arg body)) v_arg <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply ewp_eval. iNext.
    iApply (ewp_mono with "H").
    iIntros ([]). iApply ewp_value. iApply ewp_throw.
  Qed.

  Lemma ewp_call_rec η f x body bs v φ Ψ:
    lookup_rec_bindings bs f = ret (AnonFun x body) ->
    ▷EWP eval ((x, v) :: eval_rec_bindings η bs ++ η) body <|Ψ|> {{ φ }} -∗
    EWP call (VCloRec η bs f) v <|Ψ|> {{ φ }}.
  Proof.
    iIntros (E) "H /=". rewrite E /=.
    iApply ewp_eval. iNext.
    iApply (ewp_mono with "H").
    iIntros ([]). iApply ewp_value. iApply ewp_throw.
  Qed.

  Lemma ewp_call_rec_1 η f x body v φ Ψ:
    let vf := VCloRec η [RecBinding f (AnonFun x body)] f in
    ▷EWP eval ((x, v) :: (f, vf) :: η) body <|Ψ|> {{ φ }} -∗
    EWP call vf v <|Ψ|> {{ φ }}.
  Proof.
    iIntros (vf) "H". iApply ewp_call_rec; auto.
    rewrite /= String.eqb_refl //.
  Qed.

  (** * ETuple : list expr → expr *)

  Lemma ewp_ETuple_forward_exn η es φs φe Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei <|Ψ|> {{| RET v => φi v; | EXN e => φe e }}) -∗
    EWP eval η (ETuple es) <|Ψ|>
      {{| RET v => ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; φi ∈ vs; φs, φi vi;
        | EXN e => φe e }}.
  Proof.
    iIntros "H /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono _ _ (| RET vs => [∗ list] vi; φi ∈ vs; φs, φi vi;
                          | EXN v => φe v) with "[-]")%I.
    2: by iIntros ([]) "A/="; auto; iApply ewp_value; simpl; iExists _; auto.
    iInduction es as [ | ei es ] "IH" forall (φs) "H".
    - iApply ewp_value. auto.
    - iDestruct (big_sepL2_cons_inv_l with "H") as (φi φs') "(-> & Hi & H) /=".
      iApply (ewp_Par with "Hi [H]").
      + iApply ("IH" with "H").
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (e) "H /=". by iApply ewp_throw.
      + iIntros (v1 vs) "H1 H". iApply ewp_value. iFrame.
  Qed.

  Lemma ewp_ETuple_forward η es φs Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei <|Ψ|> {{ RET v, φi v }}) -∗
    EWP eval η (ETuple es) <|Ψ|> {{ RET v, ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; φi ∈ vs; φs, φi vi }}.
  Proof.
    iApply ewp_ETuple_forward_exn.
  Qed.

  Lemma ewp_ETuple_exn η es φs φ Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei <|Ψ|> {{ φi }}) -∗
    (∀ vs, ([∗ list] vi; φi ∈ vs; φs, φi (O2Ret vi)) -∗ φ (O2Ret (VTuple vs))) -∗
    (∀ φi v, ⌜φi ∈ φs⌝ -∗ φi (O2Throw v) -∗ φ (O2Throw v)) -∗
    EWP eval η (ETuple es) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P E".
    iApply (ewp_mono with "[-]").
    iApply ewp_ETuple_forward_exn.
  Abort. (* TODO prove, but only if this useful *)

  Lemma ewp_ETuple η es φs φ Ψ :
    ([∗ list] ei; φi ∈ es; φs, EWP eval η ei <|Ψ|> {{ RET v, φi v }}) -∗
    (∀ vs, ([∗ list] vi; φi ∈ vs; φs, φi vi) -∗ φ (VTuple vs)) -∗
    EWP eval η (ETuple es) <|Ψ|> {{ RET vs, φ vs }}.
  Proof.
    iIntros "H P".
    iApply (ewp_mono_ret with "[H]").
    iApply (ewp_ETuple_forward with "H").
    iIntros (?) "A".
    iDestruct "A" as (vs) "(-> & A)".
    by iApply "P".
  Qed.

  (** macros for ETuple *)

  Lemma ewp_EUnit_exn η φ Ψ :
    φ (O2Ret VUnit) -∗
    EWP eval η EUnit <|Ψ|> {{ φ }}.
  Proof.
    iApply ewp_value.
  Qed.

  Lemma ewp_EUnit_forward η Ψ :
    ⊢ EWP eval η EUnit <|Ψ|> {{ RET= #() }}.
  Proof.
    by iApply ewp_value.
  Qed.

 Lemma ewp_EPair η e1 e2 `{Encode A} `{Encode B} (v1 : A) (v2 : B) R1 R2 Ψ :
    EWP eval η e1 <|Ψ|> {{ RET #r, ⌜r = v1⌝ ∗ R1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET #r, ⌜r = v2⌝ ∗ R2 }} -∗
    EWP eval η (EPair e1 e2) <|Ψ|> {{ RET #r, ⌜r = (v1, v2)⌝ ∗ R1 ∗ R2 }}.
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

  Lemma ewp_EPair_forward η e1 e2 `{Encode A} `{Encode B} (v1 : A) (v2 : B) R1 R2 Ψ :
    EWP eval η e1 <|Ψ|> {{ RET= #v1, R1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET= #v2, R2 }} -∗
    EWP eval η (EPair e1 e2) <|Ψ|> {{ RET= #(v1, v2), R1 ∗ R2 }}.
  Proof.
    (* TODO *)
  Admitted.

  (** * EData : data → expr → expr *)
  (** * EXData : data → expr → expr *)
  (** * ERecord : list fexpr → expr *)
  (** * ERecordUpdate : expr → list fexpr → expr *)
  (** * ERecordAccess : expr → field → expr *)
  (** * EBoolConj : expr → expr → expr *)
  (** * EBoolDisj : expr → expr → expr *)
  (** * EBoolNeg : expr → expr *)
  (** * EInt : Z → expr *)

  Lemma ewp_EInt_forward η i Ψ :
    ⊢ EWP eval η (EInt i) <|Ψ|> {{ RET= #i }}.
  Proof.
    by iApply ewp_value.
  Qed.

  Lemma ewp_EInt η i φ Ψ :
    φ (O2Ret #i) -∗
    EWP eval η (EInt i) <|Ψ|> {{ φ }}.
  Proof.
    by iApply ewp_value.
  Qed.

  (** * EMaxInt : expr *)
  (** * EMinInt : expr *)
  (** * EIntNeg : expr → expr *)
  (** * EIntAdd : expr → expr → expr *)

  Lemma ewp_EIntAdd_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP as_int (eval η e1) <|Ψ|> {{ φ1 }} -∗
    EWP as_int (eval η e2) <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ n1 n2, φ1 (O2Ret n1) ∗ φ2 (O2Ret n2) -∗ φ (O2Ret (VInt (int.M.add n1 n2)))) -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2". iApply ewp_bind. iApply ewp_value. iApply ewp_value.
      iApply "P". iFrame.
  Qed.

  Lemma ewp_EIntAdd η e1 e2 φ1 φ2 φ Ψ :
    EWP as_int (eval η e1) <|Ψ|> {{ RET n1, φ1 n1 }} -∗
    EWP as_int (eval η e2) <|Ψ|> {{ RET n2, φ2 n2 }} -∗
    (∀ n1 n2, φ1 n1 ∗ φ2 n2 -∗ φ (VInt (int.M.add n1 n2))) -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ RET n, φ n }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EIntAdd_exn with "H1 H2"); auto.
  Qed.

  (* TODO: this may be the preferred style, wait and see *)
  Lemma ewp_EIntAdd' η e1 e2 (φ1 φ2 φ : Z -> iProp Σ) Ψ :
    EWP eval η e1 <|Ψ|> {{ RET #n1, φ1 n1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET #n2, φ2 n2 }} -∗
    (∀ n1 n2, φ1 n1 ∗ φ2 n2 -∗ φ (n1 + n2)%Z) -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ RET #n, φ n }}.
  Proof.
    iIntros "H1 H2 P".
    pose φ1' := (λ v, ∃ n, ⌜v = repr n⌝∗ φ1 n)%I.
    pose φ2' := (λ v, ∃ n, ⌜v = repr n⌝∗ φ2 n)%I.
    iApply (ewp_EIntAdd _ _ _ φ1' φ2' with "[H1] [H2]"); auto.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      iIntros (v) "H". iDestruct "H" as (?) "(-> & H)".
      iApply ewp_value. iExists _. by iFrame.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H2").
      iIntros (v) "H". iDestruct "H" as (?) "(-> & H)".
      iApply ewp_value. iExists _. by iFrame.
    - iIntros (i1 i2) "(H1 & H2)".
      iDestruct "H1" as (n1 ->) "H1".
      iDestruct "H2" as (n2 ->) "H2".
      iSpecialize ("P" with "[$]").
      iExists _. iFrame.
      rewrite M.add_repr_repr. auto.
  Qed.

  (* TODO: this could be better, wait and see *)
  Lemma ewp_EIntAdd_simple η e1 e2 (n1 n2 : Z) (R1 R2 : iProp Σ) Ψ :
    EWP eval η e1 <|Ψ|> {{ RET= #n1, R1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET= #n2, R2 }} -∗
    EWP eval η (EIntAdd e1 e2) <|Ψ|> {{ RET= #(n1 + n2)%Z, R1 ∗ R2 }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_EIntAdd _ _ _
              (λ r, ⌜r = repr n1⌝ ∗ R1)
              (λ r, ⌜r = repr n2⌝ ∗ R2) with "[H1] [H2]")%I.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      iIntros (?) "(-> & H)". iApply ewp_value. simpl. auto.
    - iApply ewp_bind. iApply (ewp_mono_ret with "H2").
      iIntros (?) "(-> & H)". iApply ewp_value. simpl. auto.
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

  Lemma ewp_EOpEq_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1 v2, φ1 (O2Ret v1) ∗ φ2 (O2Ret v2) -∗
      EWP eq_val v1 v2 <|Ψ|> {{ RET b, φ (O2Ret (VBool b)) }}) -∗
    EWP eval η (EOpEq e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H /=". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (n1 n2) "H1 H2 /=". iApply ewp_bind.
      (* iApply ewp_bind. *)
      iSpecialize ("P" with "[$]").
      iApply (ewp_mono with "P").
      iIntros ([b|v]) "H /=//".
      by iApply ewp_value.
  Qed.

  Lemma ewp_EOpEq η e1 e2 φ1 φ2 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ RET v1, φ1 v1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET v2, φ2 v2 }} -∗
    (∀ v1 v2, φ1 v1 ∗ φ2 v2 -∗
      EWP eq_val v1 v2 <|Ψ|> {{ RET b, φ (O2Ret (VBool b)) }}) -∗
    EWP eval η (EOpEq e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EOpEq_exn with "H1 H2"); auto.
    1,2: iIntros (?) "[]".
  Qed.

  (* TODO generalize (maybe to some Comparable typeclass?) *)
  Lemma ewp_EOpEq_simple_Z η e1 e2 (n1 n2 : Z) (R1 R2 : iProp Σ) Ψ :
    representable n1 ->
    representable n2 ->
    EWP eval η e1 <|Ψ|> {{ RET= #n1, R1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET= #n2, R2 }} -∗
    EWP eval η (EOpEq e1 e2) <|Ψ|> {{ RET= #(n1 =? n2)%Z, R1 ∗ R2 }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (ewp_EOpEq _ _ _
              (λ r, ⌜r = #n1⌝ ∗ R1)
              (λ r, ⌜r = #n2⌝ ∗ R2) with "[H1] [H2]")%I.
    - iApply (ewp_mono_ret with "H1"). iIntros (?) "(-> & $) //".
    - iApply (ewp_mono_ret with "H2"). iIntros (?) "(-> & $) //".
    - iIntros (? ?) "((-> & H1) & (-> & H2))".
      iApply ewp_value. iFrame. iPureIntro. auto.
      rewrite eq_repr_repr //.
  Qed.

  (** * EOpNe : expr → expr → expr *)
  (** * EOpLt : expr → expr → expr *)
  (** * EOpLe : expr → expr → expr *)
  (** * EOpGt : expr → expr → expr *)
  (** * EOpGe : expr → expr → expr *)

  (** * ELet : list binding → expr → expr *)

  Lemma ewp_ELet_exn η bs e φ1 φ Ψ :
    EWP eval_bindings η bs <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ δ, φ1 (O2Ret δ) -∗ EWP eval (δ ++ η) e <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELet bs e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hη").
    iIntros ([δ|v]) "H/=".
    - iApply ("P" with "H").
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_eval_bindings_cons_exn η p e bs φ1 φs φ Ψ :
    EWP eval η e <|Ψ|> {{ φ1 }} -∗
    EWP eval_bindings η bs <|Ψ|> {{ φs }} -∗
    (∀ v : exn, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v : exn, φs (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v δ, φ1 (O2Ret v) ∗ φs (O2Ret δ) -∗
      EWP widen (irrefutably_extend δ p v) <|Ψ|> {{ φ }}) -∗
    EWP eval_bindings η (Binding p e :: bs) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (v) "H". iApply ewp_throw. iApply ("E1" with "H").
    - iIntros (v) "H". iApply ewp_throw. iApply ("E2" with "H").
    - iIntros (v δ) "H1 H2". iApply ("P" $! v δ with "[$]").
  Qed.

  Lemma ewp_eval_bindings_cons η p e bs φ1 φs φ Ψ :
    EWP eval η e <|Ψ|> {{ RET v, φ1 v }} -∗
    EWP eval_bindings η bs <|Ψ|> {{ RET δ, φs δ }} -∗
    (∀ v δ, φ1 v ∗ φs δ -∗
      EWP widen (irrefutably_extend δ p v)  <|Ψ|> {{ φ }}) -∗
    EWP eval_bindings η (Binding p e :: bs) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_eval_bindings_cons_exn with "H1 H2"); try iIntros (?) "[]".
    iIntros (v δ) "(H1 & H2) /=".
    iApply ("P" with "[$]").
  Qed.

  Lemma ewp_eval_bindings_1 η p e φ1 φ Ψ :
    EWP eval η e <|Ψ|> {{ RET v, φ1 v }} -∗
    (∀ v, φ1 v -∗ EWP widen (irrefutably_extend [] p v) <|Ψ|> {{ φ }}) -∗
    EWP eval_bindings η [Binding p e] <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 P".
    iApply (ewp_eval_bindings_cons _ _ _ _ _ (λ δ, ⌜δ = []⌝%I) with "H1 []").
    by iApply ewp_value.
    iIntros (v _δ) "(H1 & ->) /=".
    iApply ("P" with "[$]").
  Qed.

  Lemma ewp_eval_bindings_nil_exn η φ Ψ :
    φ (O2Ret []) -∗
    EWP eval_bindings η [] <|Ψ|> {{ φ }}.
  Proof.
    iApply ewp_value.
  Qed.

  Lemma ewp_eval_bindings_nil η φ Ψ :
    φ [] -∗
    EWP eval_bindings η [] <|Ψ|> {{ RET δ, φ δ }}.
  Proof.
    iApply ewp_value.
  Qed.

  (** * ELetRec : list rec_binding → expr → expr *)

  Lemma ewp_ELet η bs e φ Ψ :
    EWP eval_bindings η bs <|Ψ|> {{ RET δ, EWP eval (δ ++ η) e <|Ψ|> {{ φ }} }} -∗
    EWP eval η (ELet bs e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (ewp_ELet_exn with "H"). by iIntros (?) "[]".
    iIntros (δ) "/= H //".
  Qed.

  Lemma ewp_ELetRec η bs e φ Ψ :
    let δ := eval_rec_bindings η bs in
    EWP eval (δ ++ η) e <|Ψ|> {{ φ }} -∗
    EWP eval η (ELetRec bs e) <|Ψ|> {{ φ }}.
  Proof.
    auto.
  Qed.

  (** let rec expressions with one function. Here [a : A] is an auxiliary
  variable one can use to relate pre and postconditions, to be able to describe
  e.g. the state in which the function is called, rather than only depend on the
  variable *)
  Lemma ewp_ELetRec_specced_1 {η f x e1 e2 φ Ψ} {A} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ EWP call vf v {{ φf a }}) -∗
       ∀ a v, R a v -∗ EWP eval ((x, v) :: (f, vf) :: η) e1 {{ φf a }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ EWP call vf v {{ φf a }}) -∗
      EWP eval ((f, vf) :: η) e2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) <|Ψ|> {{ φ }}.
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

  (* TODO: check if this is actually simpler *)
  Lemma ewp_ELetRec_specced_ret_1 {η f x e1 e2 φ Ψ} {A} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ EWP call vf v {{ RET v', φf a v' }}) -∗
       ∀ a v, R a v -∗ EWP eval ((x, v) :: (f, vf) :: η) e1 {{ RET v', φf a v' }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ EWP call vf v {{ RET v', φf a v' }}) -∗
      EWP eval ((f, vf) :: η) e2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) <|Ψ|> {{ φ }}.
  Proof.
    iApply ewp_ELetRec_specced_1.
  Qed.

  (** * ELetModule : module → mexpr → expr → expr *)

  (** * ELetOpen : mexpr → expr → expr *)

  (** * ESeq : expr → expr → expr *)

  Lemma ewp_ESeq_exn η e1 e2 φ1 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1, φ1 (O2Ret v1) -∗ EWP eval η e2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (ESeq e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "/= H1".
    - iApply ("P" with "H1").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_ESeq η e1 e2 φ Ψ :
    EWP eval η e1 <|Ψ|> {{ RET _, EWP eval η e2 <|Ψ|> {{ φ }} }} -∗
    EWP eval η (ESeq e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". iApply ewp_bind. auto.
  Qed.

  (** * EIfThen : expr → expr → expr *)

  Lemma ewp_EIfThen_exn' η eb e1 φb φ Ψ :
    EWP eval η eb <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit))) -∗
    EWP eval η (EIfThen eb e1) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=".
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      repeat iApply ewp_value; auto.
  Qed.

  Lemma ewp_EIfThen_exn η eb e1 φb φ Ψ :
    EWP eval η eb <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then EWP eval η e1 <|Ψ|> {{ φ }}
           else φ (O2Ret VUnit)) -∗
    EWP eval η (EIfThen eb e1) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=".
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      repeat iApply ewp_value; auto.
  Qed.

  Lemma ewp_EIfThen η eb e1 φ Ψ :
    EWP eval η eb <|Ψ|> {{ RET v,
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit)) }} -∗
    EWP eval η (EIfThen eb e1) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (ewp_EIfThen_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EIfThenElse : expr → expr → expr → expr *)

  Lemma ewp_EIfThenElse_exn' η eb e1 e2 φb φ Ψ :
    EWP eval η eb <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ EWP eval η e2 <|Ψ|> {{ φ }})) -∗
    EWP eval η (EIfThenElse eb e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=".
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      repeat iApply ewp_value; auto.
  Qed.

  Lemma ewp_EIfThenElse_exn η eb e1 e2 φb φ Ψ :
    EWP eval η eb <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then EWP eval η e1 <|Ψ|> {{ φ }}
           else EWP eval η e2 <|Ψ|> {{ φ }}) -∗
    EWP eval η (EIfThenElse eb e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=".
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      repeat iApply ewp_value; auto.
  Qed.

  Lemma ewp_EIfThenElse η eb e1 e2 φ Ψ :
    EWP eval η eb <|Ψ|> {{ RET v,
      (⌜v = VTrue ⌝ ∗ EWP eval η e1 <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ EWP eval η e2 <|Ψ|> {{ φ }}) }} -∗
    EWP eval η (EIfThenElse eb e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (ewp_EIfThenElse_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EMatch : expr → list branch → expr *)

  (* This lemma is proved with a single tactic [iApply ewp_try2], but in a
   program proof, using [iApply ewp_try2] might fail *)
  Lemma ewp_EMatch η e bs φ Ψ :
    EWP eval η e <|Ψ|>{{ λ a, EWP eval_match true η a bs <|Ψ|>{{ φ }} }} -∗
    EWP eval η (EMatch e bs) <|Ψ|> {{ φ }}.
  Proof.
    (* TODO, adapt to handle handlers *)
    (* iApply ewp_try2. *)
  Admitted.

  (* TODO: remove? probably handled by Simp *)
  Lemma ewp_eval_match_nil η a φ Ψ :
    (∃ e, ⌜a = O2Throw e⌝ ∗ φ (O2Throw e)) -∗
      EWP eval_match true η a [] <|Ψ|>{{ φ }}.
  Proof.
    iIntros "H".
    iDestruct "H" as (e) "(-> & H)".
    iApply (ewp_throw with "H").
  Qed.

  Lemma ewp_eval_match_cons η a b bs φ Ψ :
    ⊢
      EWP eval_match true η a (b :: bs) <|Ψ|>{{ φ }}.
  Proof.
    (* maybe handled by Simp? TODO *)
  Abort.

  (** * ETryWith : expr → list branch → expr *)

  Lemma ewp_ETryWith η e bs φ Ψ :
    EWP eval η e
      <|Ψ|>{{  | RET v => EWP ret v <|Ψ|>{{ φ }};
               | EXN v => EWP eval_trywith η v bs <|Ψ|>{{ φ }} }} -∗
    EWP eval η (ETryWith e bs) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "?".
    rewrite (eval_eval' _ (ETryWith _ _)) /=.
    by iApply ewp_try.
  Qed.

  (** * ERaise : expr → expr *)

  Lemma ewp_ERaise η e φ Ψ :
    EWP eval η e <|Ψ|> {{ | RET v => φ (O2Throw v); | EXN v => φ (O2Throw v)}} -∗
    EWP eval η (ERaise e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([]) "/= H //".
    by iApply ewp_throw.
  Qed.

  (** * EWhile : expr → expr → expr *)
  (** * EFor : var → expr → expr → expr → expr *)
  (** * EAssertFalse : expr *)

  (** * EAssert : expr → expr *)

  Lemma ewp_EAssert_exn η e φ1 φ Ψ :
    (φ (O2Ret #()))
     ∧
    (EWP eval η e <|Ψ|> {{ φ1 }} ∗
     (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
     (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #())))
    ⊢ EWP eval η (EAssert e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H /=".
    iApply ewp_Choose.
    iNext. iSplit.
    - iApply ewp_value. iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "(H & E & P)".
      iApply ewp_try.
      iApply ewp_bind_exn.
      iApply ewp_bind_exn.
      iApply (ewp_mono with "H").
      iIntros ([v|v]) "H /=".
      * iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        repeat iApply ewp_value.
        iApply "H".
      * iApply ewp_throw. iApply ("E" with "H").
  Qed.

  (* TODO: is this version indeed simpler to use? (&is it less general?) *)
  Lemma ewp_EAssert_exn_sep η e φ1 φ Ψ :
    φ (O2Ret #()) ∗
    (φ (O2Ret #()) -∗ EWP eval η e <|Ψ|> {{ φ1 }}) ∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
    (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #()))
    ⊢ EWP eval η (EAssert e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "(R & H & He & P) /=".
    iApply ewp_Choose.
    iNext. iSplit. by iApply ewp_value.
    iSpecialize ("H" with "R").
    iApply ewp_try.
    iApply ewp_bind_exn.
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "H /=".
    - iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        by repeat iApply ewp_value.
    - iApply ewp_throw. iApply ("He" with "H").
  Qed.

  Lemma ewp_EAssert η e R Ψ :
    R ∧ EWP eval η e <|Ψ|> {{ RET v, ⌜v = VTrue⌝ ∗ R }} -∗
    EWP eval η (EAssert e) <|Ψ|> {{ RET _, R }}.
  Proof.
    iIntros "H".
    iApply ewp_EAssert_exn.
    iSplit.
    - iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "H".
      iSplitL "H". iAssumption.
      iSplitL. by iIntros. iIntros (v) "$ //".
  Qed.

  (* TODO: is this version indeed simpler to use? *)
  Lemma ewp_EAssert_sep η e R Ψ :
    R ∗ (R -∗ EWP eval η e <|Ψ|> {{ RET v, ⌜v = VTrue⌝ ∗ R }}) -∗
    EWP eval η (EAssert e) <|Ψ|> {{ RET _, R }}.
  Proof.
    iIntros "(? & ?)".
    iApply ewp_EAssert_exn_sep. iFrame. eauto.
  Qed.

  (** * ERef : expr → expr *)

  Lemma ewp_ERef_exn η e φ1 φ Ψ :
    EWP eval η e <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ1 (O2Ret v) -∗ ∀ l, mapsto l (DfracOwn 1) (V v) -∗ φ (O2Ret (VLoc l))) -∗
    EWP eval η (ERef e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([v|v]) "H".
    - iApply ewp_alloc. iNext. iIntros (l) "Hl".
      iApply ewp_bind.
      iApply ewp_value.
      iApply ewp_value.
      iApply ("P" with "H"). auto.
    - iApply ("E" with "H").
  Qed.

  Lemma ewp_ERef η e φ1 φ Ψ :
    EWP eval η e <|Ψ|> {{ RET v, φ1 v }} -∗
    (∀ v, φ1 v -∗ ∀ l, mapsto l (DfracOwn 1) (V v) -∗ φ (VLoc l)) -∗
    EWP eval η (ERef e) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ERef_exn with "H"); auto.
  Qed.

  Lemma ewp_ERef' η e φ1 Ψ :
    EWP eval η e <|Ψ|> {{ RET v, φ1 v }} -∗
    EWP eval η (ERef e) <|Ψ|> {{ RET r, ∃ l v, ⌜r = VLoc l⌝ ∗ mapsto l (DfracOwn 1) (V v) ∗ φ1 v }}.
  Proof.
    iIntros "H".
    iApply (ewp_ERef with "H").
    iIntros (v) "H".
    iIntros (l) "Hl".
    iExists l, v; by iFrame.
  Qed.

  (** * ELoad : expr → expr *)

  Lemma ewp_ELoad_exn η e φ1 φ Ψ :
    EWP as_loc (eval η e) <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l, φ1 (O2Ret l) -∗ ∃ q v, mapsto l q (V v) ∗ ▷(mapsto l q (V v) -∗ φ (O2Ret v))) -∗
    EWP eval η (ELoad e) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=".
    iApply ewp_bind_exn.
    iApply (ewp_mono with "H").
    iIntros ([l|v]) "H1".
    - iSpecialize ("P" with "H1").
      iDestruct "P" as (q v) "(Hl & P)".
      iApply (ewp_load with "Hl"). iNext. iIntros "Hl".
      iApply ewp_value.
      iApply ("P" with "Hl").
    - iApply ("E" with "H1").
  Qed.

  Lemma ewp_ELoad η e φ1 φ Ψ :
    EWP as_loc (eval η e) <|Ψ|> {{ RET l, φ1 l }} -∗
    (∀ l, φ1 l -∗ ∃ q v, mapsto l q (V v) ∗ ▷(mapsto l q (V v) -∗ φ v)) -∗
    EWP eval η (ELoad e) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (ewp_ELoad_exn with "H"); auto.
  Qed.

  Lemma ewp_ELoad_simple η e (l : loc) q (v : val) Ψ :
    EWP eval η e <|Ψ|> {{ RET= #l }} -∗
    mapsto l q (V v) -∗ EWP eval η (ELoad e) <|Ψ|> {{ RET= v, mapsto l q (V v) }}.
  Proof.
    iIntros "H Hl". iApply (ewp_ELoad _ _ (λ l1, ⌜l = l1⌝%I) with "[H]").
    - iApply ewp_bind. iApply (ewp_mono_ret with "H").
      by iIntros (?) "(-> & ?)"; iApply ewp_value.
    - iIntros (? ->). iExists _, _; iFrame. auto.
  Qed.

  (** * EStore : expr → expr → expr *)

  Lemma ewp_EStore_exn η e1 e2 φ1 φ2 φ Ψ :
    EWP as_loc (eval η e1) <|Ψ|> {{ φ1 }} -∗
    EWP eval η e2 <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l1 v2, φ1 (O2Ret l1) ∗ φ2 (O2Ret v2) -∗
      ∃ v1, mapsto l1 (DfracOwn 1) (V v1) ∗ ▷(mapsto l1 (DfracOwn 1) (V v2) -∗ φ (O2Ret VUnit))) -∗
    EWP eval η (EStore e1 e2) <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=".
    iApply (ewp_Par with "H1 H2 [E1] [E2]").
    - iIntros (e) "H1". iApply ewp_throw. iApply ("E1" with "H1").
    - iIntros (e) "H2". iApply ewp_throw. iApply ("E2" with "H2").
    - iIntros (l1 v2) "H1 H2".
      iSpecialize ("P" $! l1 v2 with "[$]").
      iDestruct "P" as (v1) "(Hl1 & P)".
      iApply (ewp_store with "Hl1"). iNext; iIntros "Hl1".
      iApply ewp_value.
      iApply ("P" with "Hl1").
  Qed.

  Lemma ewp_EStore η e1 e2 φ1 φ2 φ Ψ :
    EWP as_loc (eval η e1) <|Ψ|> {{ RET l1, φ1 l1 }} -∗
    EWP eval η e2 <|Ψ|> {{ RET v2, φ2 v2 }} -∗
    (∀ l1 v2, φ1 l1 ∗ φ2 v2 -∗
      ∃ v1, mapsto l1 (DfracOwn 1) (V v1) ∗ ▷(mapsto l1 (DfracOwn 1) (V v2) -∗ φ VUnit)) -∗
    EWP eval η (EStore e1 e2) <|Ψ|> {{ RET v, φ v }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (ewp_EStore_exn with "H1 H2"); auto.
  Qed.

  (* Here, [l↦v] is threaded through [e2], as one is more likely to use
     ownership of [l] in [e2] than in [e1] (i.e. we rarely write things like
     [(!r := 1; r) := 2]) *)
  Lemma ewp_EStore_simple η e1 e2 (l : loc) (v v' : val) Ψ :
    EWP eval η e1 <|Ψ|> {{ RET= #l }} -∗
    EWP eval η e2 <|Ψ|> {{ RET= v', mapsto l (DfracOwn 1) (V v) }} -∗
    EWP eval η (EStore e1 e2) <|Ψ|> {{ RET= #(), mapsto l (DfracOwn 1) (V v') }}.
  Proof.
    iIntros "H1 H2".
    iApply (ewp_EStore _ _ _ (λ l1, ⌜l = l1⌝%I)  with "[H1] H2").
    - iApply ewp_bind. iApply (ewp_mono_ret with "H1").
      by iIntros (?) "(-> & ?)"; iApply ewp_value.
    - iIntros (? ?) "(-> & -> & Hl)". iExists _. iFrame. auto.
  Qed.

End ewp_rules_expr.
