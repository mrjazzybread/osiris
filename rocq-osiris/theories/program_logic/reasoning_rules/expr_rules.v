From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.program_logic Require Import ewp tactics fun_spec escrows.
From osiris.program_logic.reasoning_rules Require Import basic_rules impure_rules stop_rules handler_rules.

Section imp_rules_expr.

  Context `{!osirisGS Σ}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ}.
  Context {A : Type} `{EncA : Encode A} {Φ : A → iProp Σ}.

  (* -------------------------------------------------------------------------- *)
  (* Lemmas about [expr]s *)

  (** * EPath : path → expr *)

  Lemma imp_EPath {ζ} η p :
    imp^{ι} lookup_path η p @ E <|Ψ|> {{ Φ }} -∗
    imp^{ι} eval η (EPath p) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply (imp_widen with "H").
  Qed.

  (** * EAnonFun : anonfun → expr *)
  (** * EApp : expr → expr → expr *)
  (* See [funspec.v] *)

  Lemma imp_EApp_exn `{Encode B} {ζ} η e1 e2 ζ1 Φ1 ζ2 (Φ2 : B → iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ e, ζ1 e -∗ ζ e) ∧
    ▷ (∀ e, ζ2 e -∗ ζ e) ∧
    ▷ (∀ f x, Φ1 f -∗ Φ2 x -∗ imp^{ι} call f #x @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} eval η (EApp e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_Par with "H1 H2").
    iSplit; last iSplit.
    - iIntros (?) "E !>".
      iApply imp_throw. iApply ("Hjoin" with "E").
    - iIntros (?) "E !>".
      iApply imp_throw. iApply ("Hjoin" with "E").
    - iIntros (f x) "Hf Hx !>".
      iDestruct "Hjoin" as "[_ [_ Hjoin]]".
      iApply ("Hjoin" with "[$] [$]").
  Qed.

  Lemma imp_EApp' `{Encode B} {ζ} η e1 e2 Φ1 (Φ2 : B → iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ Φ2 }} -∗
    ▷ (∀ f x, Φ1 f -∗ Φ2 x -∗ imp^{ι} call f #x @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} eval η (EApp e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (imp_EApp_exn with "H1 H2").
    iSplit; last iSplit.
    - iIntros "!>" (? []).
    - iIntros "!>" (? []).
    - iExact "H".
  Qed.

  (* The following [imp_call_*] lemmas just follow the reduction rules for
  function calls when a closure is applied. For better modularity and smaller
  proof terms, it should generally preferred to have a specification ready for
  the available functions values, having abstracted away the closure values.
  Maybe in some cases, though, having a specification for a simple function
  might be too verbose or be too trivial, and one could simply wish to "just
  reduce" the term, in which case those lemmas may be useful. *)
  Lemma imp_call_nonrec {ζ} η x_arg body v_arg :
    ▷imp^{ι} eval ((x_arg, v_arg) :: η) body @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp^{ι} call (VClo η (AnonFun x_arg body)) v_arg @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    by iApply imp_please.
  Qed.

  Lemma imp_call_rec {ζ} η f x body bs v :
    lookup_rec_bindings bs f = ret (AnonFun x body) ->
    ▷ imp^{ι} eval ((x, v) :: eval_rec_bindings η bs ++ η) body @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp^{ι} call (VCloRec η bs f) v @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hlk) "H /=". rewrite Hlk /=.
    by iApply imp_please.
  Qed.

  (** * ETuple : list expr → expr *)

  Lemma imp_evals {ζ} η es (Φs : list (val → iProp Σ)) :
    ([∗ list] ei;Φi ∈ es;Φs,
       imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φi }}) -∗
    imp^{ι} evals η es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
          {{ λ (vs : list val), [∗ list] vi; Φi ∈ vs; Φs, Φi vi }}.
  Proof.
    iIntros "HΦs".
    iInduction es as [ | ei es ] "IH" forall (Φs) "HΦs"; simpl_evals.
    - by iApply (imp_ret [] []).
    - iDestruct (big_sepL2_cons_inv_l with "HΦs")
        as (Φi Φs') "(-> & Hi & H) /=".
      iApply (imp_Par Φi ζ _ ζ (eval η ei) (evals η es)
                (pfbind inject2 (λ '(v, vs), ret (v :: vs))) with "Hi [H]").
      { iApply ("IH" with "H"). }
      iSplit; last iSplit.
      + iIntros (e) "Hζ !>". rewrite /discontinue /=.
        iApply (@imp_throw _ _ (list val) (list val) with "Hζ").
      + iIntros (e) "Hζ !>". rewrite /discontinue /=.
        iApply (@imp_throw _ _ (list val) (list val) with "Hζ").
      + iIntros (v vs) "HΦi HΦs". rewrite /continue /=.
        iApply (imp_ret (v :: map id vs) (v :: vs)). reflexivity.
        iIntros "!>".
        iFrame.
  Qed.

  Lemma imp_ETuple_forward_exn {ζ} η es (Φs : list (val → iProp Σ)) :
    ([∗ list] ei; Φi ∈ es; Φs,
       imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φi }}) -∗
    imp^{ι} eval η (ETuple es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
          {{ λ v, ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; Φi ∈ vs; Φs, Φi vi }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply (imp_bind _ _ (λ vs, ret (VTuple vs)) with "[H]").
    iApply (imp_evals with "H").
    iIntros (vs) "HΦs". unfold observe, observe_list, encode.encode, Encode_val.
    replace (map (λ v, v) vs) with vs; last first.
    { by rewrite map_id. }
    iApply imp_ret. encode.
    iFrame. auto.
  Qed.

  Lemma imp_ETuple_forward η es (Φs : list (val → iProp Σ)) :
    ([∗ list] ei; Φi ∈ es; Φs,
       imp^{ι} eval η ei @ E <|Ψ|> {{ Φi }}) -∗
    imp^{ι} eval η (ETuple es) @ E <|Ψ|>
      {{ λ v, ∃ vs, ⌜v = VTuple vs⌝ ∗ [∗ list] vi; Φi ∈ vs; Φs, Φi vi }}.
  Proof.
    iIntros "Himps".
    iApply (imp_ETuple_forward_exn with "Himps").
  Qed.

  Lemma imp_ETuple_exn {ζ} η es ζs Φs :
    ([∗ list] ei; '(ζi, Φi) ∈ es; zip ζs Φs,
       imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζi ⟩⟩ {{ Φi }}) -∗
    (∀ vs, ([∗ list] vi; Φi ∈ vs; Φs, Φi vi) -∗
           ∃ a, ⌜#a = VTuple vs⌝ ∗ Φ a) -∗
    ([∗ list] ζi ∈ ζs, ∀ e, ζi e -∗ ζ e) -∗
    imp^{ι} eval η (ETuple es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H P E". simpl_eval.
    iApply (imp_bind _ _ (λ vs, ret (VTuple vs)) with "[- P]").
    - iApply imp_evals.
      iPoseProof (big_sepL2_length with "[$]") as "%".
      instantiate (1 := Φs).
      admit.
    - iIntros (vs) "Hvs".
      iDestruct ("P" with "Hvs") as "(%a & %Henc & HΦ)".
      replace (VTuple ♯vs) with (#a); last first.
      { unfold observe, observe_list, encode.encode at 2, Encode_val.
        rewrite map_id. apply Henc. }
      iApply imp_ret. reflexivity.
      iApply "HΦ".
  Admitted.

  (* Results to handle goals generated by imp_ETuple_* lemmas *)
  Lemma imp_list_nil η  :
    ⊢ ([∗ list] ei;Φi ∈ []; @nil (val → iProp Σ),
         imp^{ι} eval η ei @ E <|Ψ|> {{ Φi }}).
  Proof. done. Qed.

  (* Lemma imp_ETuple {ζ} η es Φs : *)
  (*   ([∗ list] ei; Φi ∈ es; Φs, imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φi }}) -∗ *)
  (*   (∀ vs, ([∗ list] vi;Φi ∈ vs; Φs, Φi vi) -∗ *)
  (*          ∃ a, ⌜#a = VTuple vs⌝ ∗ Φ a) -∗ *)
  (*   imp^{ι} eval η (ETuple es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "H P". *)
  (*   iApply (imp_mono_ret with "[H]"). *)
  (*   iApply imp_ETuple_forward_exn. *)
  (*   iPoseProof (imp_ETuple_forward_exn with "H") as "H". *)
  (*   Set Printing All. *)
  (*   iApply "H". *)
  (*   iApply (@imp_ETuple_forward_exn ζ η es Φs with "H"). *)
  (*   iIntros (?) "A". *)
  (*   iDestruct "A" as (vs) "(-> & A)". *)
  (*   by iApply "P". *)
  (* Qed. *)

  (** macros for ETuple *)

End imp_rules_expr.

Section imp_rules_exp.

  Context `{!osirisGS Σ}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ}.

  Lemma imp_EUnit_exn {Φ ζ} η :
    Φ tt -∗
    imp^{ι}eval η EUnit @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    simpl_eval; by iApply imp_ret.
  Qed.

  Lemma imp_EUnit_forward {ζ} η :
    ⊢ imp^{ι} eval η EUnit @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ u, ⌜u = tt⌝ }}.
  Proof.
    simpl_eval; iApply imp_ret; [ encode | auto ].
  Qed.

  Lemma imp_EPair2 `{Encode A, Encode B} {ζ Φ} η e1 e2 ζ1 ζ2 (Φ1 : A → iProp Σ) (Φ2 : B → iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    (∀ e, ζ1 e -∗ ζ e) ∧
    (∀ e, ζ2 e -∗ ζ e) ∧
    (∀ a1 a2, Φ1 a1 -∗ Φ2 a2 -∗
              Φ (a1, a2)) -∗
    imp^{ι} eval η (EPair e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin". simpl_eval.
    iApply (imp_Par Φ1 ζ1 _ _ _
              (Par (eval η e2) (ret []) (pfbind inject2 (λ '(v, vs), ret (v :: vs))))
             with "H1 [H2]").
    iApply (imp_Par Φ2 ζ2 _ _ _ (ret []) (pfbind inject2 (λ '(v, vs), ret (v :: vs)))
             with "H2").
    { iApply (imp_ret [] []).
      - unfold observe. instantiate (1 := list val). instantiate (1 := _). reflexivity.
      - instantiate (1 := (λ l, ⌜l=[]⌝)%I). done. }
    { iSplit; last iSplit.
      - iIntros (e) "Hζ2 !>".
        rewrite /discontinue /=.
        iApply (@imp_throw Σ osirisGS0 (list B) (list val) exn _ _ ι E Ψ ζ2 _ e).
        iExact "Hζ2".
      - iIntros (e). instantiate (2 := (λ _, False)%I).
        iIntros ([]).
      - iIntros (b ?) "HΦ2 -> !>".
        rewrite /continue /=.
        instantiate (1 := (λ (l : list B), ∃ b, ⌜l = [b]⌝ ∗ Φ2 b)%I).
        iApply (imp_ret [ #b] [b]). encode.
        iFrame. auto. }
    iSplit; last iSplit.
    - iIntros (e) "Hζ1 !>". rewrite /discontinue /=.
      iApply imp_throw.
      iApply ("Hjoin" with "Hζ1").
    - iIntros (e) "Hζ2 !>". rewrite /discontinue /=.
      iApply imp_throw.
      iApply ("Hjoin" with "Hζ2").
    - iIntros (a ?) "HΦ1 (%b & -> & HΦ2) !>".
      rewrite /continue /=.
      iApply imp_ret. instantiate (1 := (a, b)). encode.
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_EPair `{Encode A, Encode B} {Φ} η e1 e2 (Φ1 : A → iProp Σ) (Φ2 : B → iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ Φ2 }} -∗
    (∀ a b, Φ1 a -∗ Φ2 b -∗ Φ (a, b)) -∗
    imp^{ι} eval η (EPair e1 e2) @ E <|Ψ|> {{ Φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (imp_EPair2 with "H1 H2 [P]"); auto.
  Qed.

  (** * EData : data → expr → expr *)

  Lemma imp_EData `{Encode A} {Φ : A → iProp Σ} {ζ} η c es Φs :
    ([∗ list] ei;Φi ∈ es;Φs,
       imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φi }}) -∗
    (∀ vs,
       ([∗ list] vi;Φi ∈ vs;Φs, Φi vi) -∗
       ∃ a, ⌜#a = VData c vs⌝ ∗ Φ a) -∗
    imp^{ι} eval η (EData c es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H P /=". simpl_eval.
    iApply (imp_bind _ _ (λ v, ret (VData c v)) with "[H]").
    { iApply (imp_evals with "H"). }
    iIntros (vs) "H".
    iDestruct ("P" with "H") as "(%a & %Henc & HΦ)".
    iApply imp_ret; last iFrame. symmetry.
    unfold observe, observe_encode at 1. rewrite Henc.
    unfold observe_list, encode.encode, Encode_val.
    rewrite map_id. reflexivity.
  Qed.

  (* E/VConstant is a macro for E/VData *)
  Lemma imp_EConstant `{Encode A} {Φ : A → iProp Σ} {ζ} (a : A) η c :
    #a = VConstant c →
    Φ a -∗
    imp^{ι} eval η (EConstant c) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Henc) "H". simpl_eval.
    by iApply imp_ret.
  Qed.

  (** * EXData : data → expr → expr *)
  Lemma imp_EXData `{Encode A} {ζ} η π l es (Φs : list (val → iProp Σ)) (Φ : A → iProp Σ) :
    lookup_path η π = ret (VLoc l) →
    ([∗ list] ei;Φi ∈ es;Φs,
       imp^{ι} eval η ei @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φi }}) -∗
    (∀ vs, ([∗ list] vi;Φi ∈ vs;Φs, Φi vi) -∗
           ∃ (a : A), ⌜#a = VXData l vs⌝ ∗ Φ a) -∗
    imp^{ι} eval η (EXData π es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hlookup) "He Hjoin".
    simpl_eval. rewrite Hlookup. simpl.
    iApply (imp_bind _ _ (λ v, ret (VXData l v)) with "[He]").
    iApply (imp_evals with "He").
    iIntros (vs) "HΦs".
    iDestruct ("Hjoin" $! vs with "HΦs") as "(%a & %Henc & HΦ)".
    iApply imp_ret; last iFrame.
    symmetry. unfold observe, observe_encode at 1. rewrite Henc.
    unfold observe_list, encode.encode, Encode_val.
    rewrite map_id. reflexivity.
  Qed.

  (** * ERecord : list fexpr → expr *)
  (** * ERecordUpdate : expr → list fexpr → expr *)
  (** * ERecordAccess : expr → field → expr *)
  (** * EBoolConj : expr → expr → expr *)
  (** * EBoolDisj : expr → expr → expr *)
  (** * EBoolNeg : expr → expr *)
  (** * EInt : Z → expr *)

  Lemma imp_EInt {ζ} η i :
    ⊢ imp^{ι} eval η (EInt i) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n, ⌜n = i⌝ }}.
  Proof.
    simpl_eval; by iApply imp_ret.
  Qed.

  (** * EMaxInt : expr *)
  (** * EMinInt : expr *)
  (** * EIntNeg : expr → expr *)
  (** * EIntAdd : expr → expr → expr *)

  Lemma imp_EIntAdd2 {ζ ζ1 ζ2} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ e, ζ1 e -∗ ζ e) ∧
    ▷ (∀ e, ζ2 e -∗ ζ e) ∧
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i + j)) -∗
    imp^{ι} eval η (EIntAdd e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_Par _ ζ1 _ ζ2 (as_int (eval η e1)) (as_int (eval η e2)) with "[H1] [H2]").
    - unfold as_int.
      iApply (imp_bind _ _ (λ v, val_as_int v) with "H1").
      iIntros (i) "HΦ1". simpl.
      iApply (imp_ret (repr i) i). unfold observe.
      instantiate (1 := Build_Observe _ _ _ repr).
      reflexivity.
      iExact "HΦ1".
    - unfold as_int.
      iApply (imp_bind _ _ (λ v, val_as_int v) with "H2").
      iIntros (i) "HΦ2". simpl.
      iApply (imp_ret (repr i) i). unfold observe.
      instantiate (1 := Build_Observe _ _ _ repr).
      reflexivity.
      iExact "HΦ2".
    - iSplit; last iSplit.
      { iIntros (e) "Hζ1 !>". rewrite /discontinue /=.
        iApply imp_throw.
        iApply ("Hjoin" with "Hζ1"). }
      { iIntros (e) "Hζ2 !>". rewrite /discontinue /=.
        iApply imp_throw.
        iApply ("Hjoin" with "Hζ2"). }
      iIntros (i j) "HΦ1 HΦ2 !>".
      iApply imp_ret. encode.
      iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_EIntAdd {ζ Φ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i + j)%Z) -∗
    imp^{ι} eval η (EIntAdd e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (imp_EIntAdd2 with "H1 H2").
    iSplit; last iSplit; auto.
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

  Local Instance observe_bool : Observe bool bool := { observe := id }.

  Lemma imp_EOpEq2 {Φ : bool → iProp Σ} {ζ ζ1 ζ2} η e1 e2 Φ1 Φ2 :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ1 ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ2 ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ e, ζ1 e -∗ ζ e) ∧
    ▷ (∀ e, ζ2 e -∗ ζ e) ∧
    ▷ (∀ v1 v2, Φ1 v1 -∗ Φ2 v2 -∗
              imp^{ι} eq_val v1 v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} eval η (EOpEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin". simpl_eval.
    iApply (imp_Par _ _ _ _ _ _
              (pfbind inject2 (λ '(v1, v2), 'b ← eq_val v1 v2;
                                            ret (VBool b)))
             with "H1 H2 [Hjoin]").
    iSplit; last iSplit.
    - iIntros (e) "Hζ1 !>". rewrite /discontinue /=.
      iApply (@imp_throw _ _ bool val exn).
      iApply ("Hjoin" with "Hζ1").
    - iIntros (e) "Hζ2 !>". rewrite /discontinue /=.
      iApply (@imp_throw _ _ bool val exn).
      iApply ("Hjoin" with "Hζ2").
    - iIntros (v1 v2) "HΦ1 HΦ2 !>".
      rewrite /continue /=.
      iApply (imp_bind _ _ (λ b, ret (VBool b)) with "[-]").
      iApply ("Hjoin" with "HΦ1 HΦ2").
      iIntros (b) "HΦ".
      iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpEq  {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ v1 v2,
         Φ1 v1 -∗ Φ2 v2 -∗
         imp^{ι} eq_val v1 v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} eval η (EOpEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (imp_EOpEq2 with "H1 H2"); auto.
  Qed.

  Lemma imp_EOpEq_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    imp^{ι} eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n, ⌜n = i⌝ }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ n, ⌜n = j⌝ }} -∗
    imp^{ι} eval η (EOpEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ b, ⌜b = (i =? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpEq with "[H1] [H2]").
    - iApply (basic_rules.ewp_mono with "H1").
      iIntros ([|]); [ | iIntros "$" ].
      iIntros "(%n & %Henc & ->) /=".
      iExists a. instantiate (1 := (λ a, ⌜ a = #i⌝)%I).
      auto.
    - iApply (basic_rules.ewp_mono with "H2").
      iIntros ([|]); [ | iIntros "$" ].
      iIntros "(%n & %Henc & ->) /=".
      iExists a. instantiate (1 := (λ a, ⌜ a = #j⌝)%I).
      auto.
    - iIntros "!>" (v1 v2) "-> ->".
      iApply imp_ret. rewrite eq_repr_repr. reflexivity. auto. auto.
      iPureIntro. reflexivity.
  Qed.

  (** * EOpNe : expr → expr → expr *)
  (** * EOpLt : expr → expr → expr *)
  (** * EOpLe : expr → expr → expr *)
  (** * EOpGt : expr → expr → expr *)
  (** * EOpGe : expr → expr → expr *)

  (** * ELet : list binding → expr → expr *)

  (* Intermediate lemma: using [eval_bindings] hypothesis *)
  Lemma imp_ELet_exn η bs e φ1 φ E Ψ :
    imp^{ι} eval_bindings η bs @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ δ, φ1 (O2Ret δ) -∗ imp^{ι} eval (δ ++ η) e @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι} eval η (ELet bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη E P /=". simpl_eval.
    iApply imp_bind'.
    iApply (imp_mono with "Hη").
    iIntros ([δ|v]) "H/=".
    - iApply ("P" with "H").
    - iApply ("E" with "H").
  Qed.

  Lemma imp_ELet {η bs e} (φ' : env -> iProp Σ) φ E Ψ :
    imp^{ι} eval_bindings η bs @ E <|Ψ|> {{ ensures v, φ' v }} -∗
    (∀ δ, φ' δ -∗ imp^{ι} eval (δ ++ η) e @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι} eval η (ELet bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hη P /=". simpl_eval.
    iApply imp_bind.
    iApply (imp_mono with "Hη").
    iIntros ([δ|v]) "H/="; last done.
    iApply ("P" with "H").
  Qed.

  (* Specialized [ELet] lemmas *)

  (* TODO: Have *_singleton *_cons lemmas about relevant expr constructs *)
  Corollary imp_ELet_singleton_total {η p e e'} (Φ : val -> iProp Σ) φ φ' E Ψ:
    imp^{ι} eval η e' @ E <|Ψ|> {{ ensures v, Φ v }} -∗
    (∀ v, Φ v -∗ ⌜pure_wp (irrefutably_extend η nil p v) (φ v) ⊥⌝) -∗
    (∀ v δ, Φ v -∗ ⌜φ v δ⌝ -∗
            imp^{ι} eval (δ ++ η) e @ E <|Ψ|> {{ φ' }}) -∗
    imp^{ι} eval η (ELet [ Binding p e' ] e) @ E <|Ψ|> {{ φ' }}.
  Proof.
    iIntros "He' HP He".
    iApply (imp_ELet (λ δ, imp^{ι}eval (δ ++ η) e @ E <|Ψ|> {{ φ' }})%I
      with "[He' HP He]").
    { iApply (imp_eval_bindings_singleton_total with "He' HP").
      iIntros (v δ) "HΦ Hφ".
      iApply ("He" with "HΦ Hφ"). }
    by iIntros (?) "HΦ".
  Qed.

  (* Special case of [let x = e' in e] *)
  Lemma imp_ELet_PVar_1 {η x e e'} (Φ : val -> iProp Σ) φ E Ψ:
    imp^{ι}eval η e' @ E <|Ψ|> {{ ensures v, Φ v }} -∗
    (∀ v, Φ v -∗ imp^{ι}eval ((x, v) :: η) e @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ELet [Binding (PVar x) e'] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_singleton_total with "H").
    iIntros (v) "_".
    iPureIntro. unfold irrefutably_extend. simpl_eval_pat.
    apply pure_wp_ret. instantiate (1 := λ v l, l = [(x, v)]).
    reflexivity.
    iIntros (v δ) "HΦ ->".
    by iApply "P".
  Qed.

  (* Alternative form *)
  Lemma imp_ELet_PVar_1_forward {η x e e' v} R φ E Ψ:
    imp^{ι}eval η e' @ E <|Ψ|> {{ λ v', ⌜v' = v⌝ ∗ R }} -∗
    (R -∗ imp^{ι}eval ((x, v) :: η) e @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ELet [ Binding (PVar x) e' ] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_PVar_1 with "H").
    iIntros (_v) "(-> & Hv)".
    iApply ("P" with "Hv").
  Qed.

  (* Special case of [let _ = e' in e] *)
  Lemma imp_ELet_PAny_1 {η e e'} R φ E Ψ:
    imp^{ι}eval η e' @ E <|Ψ|> {{ ensures _, R }} -∗
    (R -∗ imp^{ι}eval η e @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ELet [Binding PAny e'] e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_singleton_total with "H").
    iIntros (v) "_".
    iPureIntro. unfold irrefutably_extend. simpl_eval_pat.
    apply pure_wp_ret. instantiate (1 := λ v l, l = []).
    reflexivity.
    iIntros (v δ) "HΦ ->".
    by iApply "P".
  Qed.

  (** * ELetRec : list rec_binding → expr → expr *)

  Lemma imp_ELetRec η bs e φ E Ψ :
    let δ := eval_rec_bindings η bs in
    imp^{ι}eval (δ ++ η) e @ E <|Ψ|> {{ φ }} -∗
    imp^{ι}eval η (ELetRec bs e) @ E <|Ψ|> {{ φ }}.
  Proof.
    simpl_eval; auto.
  Qed.

  (** let rec expressions with one function. Here [a : A] is an auxiliary
  variable one can use to relate pre and postconditions, to be able to describe
  e.g. the state in which the function is called, rather than only depend on the
  variable *)
  Lemma imp_ELetRec_specced_1 {η f x e1 e2 φ E Ψ} {A : Type} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ imp^{ι}call vf v <|Ψ|> {{ φf a }}) -∗
       ∀ a v, R a v -∗ imp^{ι}eval ((x, v) :: (f, vf) :: η) e1 <|Ψ|> {{ φf a }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ imp^{ι}call vf v <|Ψ|> {{ φf a }}) -∗
      imp^{ι}eval ((f, vf) :: η) e2 @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "#He1 He2".
    iApply imp_ELetRec. simpl.
    iApply "He2".
    iLöb as "IH".
    iModIntro.
    iIntros (a v) "H".
    iApply imp_call_rec_1.
    iNext.
    iSpecialize ("He1" with "IH H").
    iApply (imp_mono with "He1").
    auto.
  Qed.

  Lemma imp_ELetRec_specced_ret_1 {η f x e1 e2 φ E Ψ} {A} (R : A → val → iProp Σ) φf :
    □(∀ vf,
     □(∀ a v, R a v -∗ imp^{ι}call vf v <|Ψ|> {{ ensures v', φf a v' }}) -∗
       ∀ a v, R a v -∗ imp^{ι}eval ((x, v) :: (f, vf) :: η) e1 <|Ψ|> {{ ensures v', φf a v' }}) -∗
    (∀ vf,
      □(∀ a v, R a v -∗ imp^{ι}call vf v <|Ψ|> {{ ensures v', φf a v' }}) -∗
      imp^{ι}eval ((f, vf) :: η) e2 @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ELetRec [RecBinding f (AnonFun x e1)] e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iApply imp_ELetRec_specced_1.
  Qed.

  (** * ELetModule : module → mexpr → expr → expr *)

  (** * ELetOpen : mexpr → expr → expr *)
  Lemma imp_ELetOpen η me e E ψ φ :
    imp^{ι}eval_mexpr η me @ E <|ψ|> {{ ensures m, ∃ δ, ⌜ m = VStruct δ ⌝ ∗
    imp^{ι}eval (δ ++ η) e @ E <|ψ|> {{ φ }} }} -∗
    imp^{ι}eval η (ELetOpen me e) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "Hme". simpl_eval.
    iApply imp_bind.
    rewrite /as_struct. iApply imp_bind.
    iApply (imp_mono with "Hme").
    iIntros ([|]) "Hδ"; [ simpl | done].
    iDestruct "Hδ" as "(%δ & -> & He)".
    iApply imp_widen. { apply pure_wp_ret; apply eq_refl. }
    by iIntros (?) "->".
  Qed.

  (** * ESeq : expr → expr → expr *)

  Lemma imp_ESeq_exn η e1 e2 φ1 φ E Ψ :
    imp^{ι}eval η e1 @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v1, φ1 (O2Ret v1) -∗ imp^{ι}eval η e2 @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι}eval η (ESeq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H M P /=". simpl_eval.
    iApply imp_bind'.
    iApply (imp_mono with "H").
    iIntros ([v|v]) "/= H1".
    - iApply ("P" with "H1").
    - iApply ("M" with "H1").
  Qed.

  Lemma imp_ESeq η e1 e2 φ E Ψ :
    imp^{ι}eval η e1 @ E <|Ψ|> {{ ensures _, imp^{ι}eval η e2 @ E <|Ψ|> {{ φ }} }} -∗
    imp^{ι}eval η (ESeq e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". simpl_eval. by iApply imp_bind.
  Qed.

  (** * EIfThen : expr → expr → expr *)

  Lemma imp_EIfThen_exn' η eb e1 φb φ E Ψ :
    imp^{ι} eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ imp^{ι} eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit))) -∗
    imp^{ι} eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply imp_bind'.
    iApply imp_bind'.
    iApply (imp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply imp_ret; auto.
  Qed.

  Lemma imp_EIfThen_exn η eb e1 φb φ E Ψ :
    imp^{ι}eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then imp^{ι}eval η e1 @ E <|Ψ|> {{ φ }}
           else φ (O2Ret VUnit)) -∗
    imp^{ι}eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply imp_bind'.
    iApply imp_bind'.
    iApply (imp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply imp_ret; auto.
  Qed.

  Lemma imp_EIfThen η eb e1 φ E Ψ :
    imp^{ι}eval η eb @ E <|Ψ|> {{ ensures v,
      (⌜v = VTrue ⌝ ∗ imp^{ι}eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ φ (O2Ret VUnit)) }} -∗
    imp^{ι}eval η (EIfThen eb e1) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (imp_EIfThen_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EIfThenElse : expr → expr → expr → expr *)

  Lemma imp_EIfThenElse_exn' η eb e1 e2 φb φ E Ψ :
    imp^{ι} eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      (⌜v = VTrue ⌝ ∗ imp^{ι} eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ imp^{ι} eval η e2 @ E <|Ψ|> {{ φ }})) -∗
    imp^{ι} eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P /=". simpl_eval.
    iApply imp_bind'.
    iApply imp_bind'.
    iApply (imp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as "[(-> & H) | (-> & H)] /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply imp_ret; auto.
  Qed.

  Lemma imp_EIfThenElse_exn η eb e1 e2 φb φ E Ψ :
    imp^{ι} eval η eb @ E <|Ψ|> {{ φb }} -∗
    (∀ v, φb (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φb (O2Ret v) -∗
      ∃ b, ⌜v = VBool b⌝ ∗
      if b then imp^{ι} eval η e1 @ E <|Ψ|> {{ φ }}
           else imp^{ι} eval η e2 @ E <|Ψ|> {{ φ }}) -∗
    imp^{ι} eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "Hb E P". simpl_eval.
    iApply imp_bind'.
    iApply imp_bind'.
    iApply (imp_mono with "Hb"). iIntros ([v|v]) "H /=". 2: by iApply "E".
    iDestruct ("P" with "H") as ([]) "(-> & H) /=";
      try assert (val_as_bool VTrue = ret true) as -> by reflexivity;
      try assert (val_as_bool VFalse = ret false) as -> by reflexivity;
      repeat iApply imp_ret; auto.
  Qed.

  Lemma imp_EIfThenElse η eb e1 e2 φ E Ψ :
    imp^{ι}eval η eb @ E <|Ψ|> {{ ensures v,
      (⌜v = VTrue ⌝ ∗ imp^{ι}eval η e1 @ E <|Ψ|> {{ φ }})
    ∨ (⌜v = VFalse⌝ ∗ imp^{ι}eval η e2 @ E <|Ψ|> {{ φ }}) }} -∗
    imp^{ι}eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H".
    iApply (imp_EIfThenElse_exn' with "H").
    by iIntros (?) "[]".
    by iIntros (v) "? //".
  Qed.

  (** * EMatch : expr → list branch → expr *)

  Lemma imp_EMatch η e bs Ψ E Φ :
    imp^{ι}deep_handler η e bs @ E <|Ψ|> {{ Φ }} -∗
    imp^{ι}eval η (EMatch e bs) @ E <|Ψ|> {{ Φ }}.
  Proof.
    by iIntros "H"; simpl_eval.
  Qed.

  (** * ERaise : expr → expr *)

  Lemma imp_ERaise η e φ E Ψ :
    imp^{ι} eval η e @ E <|Ψ|> {{ RET v => φ (O2Throw v) | EXN v => φ (O2Throw v)}} -∗
    imp^{ι} eval η (ERaise e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H". simpl_eval.
    iApply imp_bind'.
    iApply (imp_mono with "H").
    iIntros ([]) "/= H //".
    by iApply imp_throw.
  Qed.

  (** * EWhile : expr → expr → expr *)
  (** * EFor : var → expr → expr → expr → expr *)
  (** * EAssertFalse : expr *)

  (** * EAssert : expr → expr *)

  Lemma imp_EAssert_exn η e φ1 φ E Ψ :
    (φ (O2Ret #()))
     ∧
    (imp^{ι}eval η e @ E <|Ψ|> {{ φ1 }} ∗
     (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
     (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #())))
    ⊢ imp^{ι}eval η (EAssert e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply imp_choose.
    iNext. iSplit.
    - iApply imp_ret. iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "(H & E & P)".
      iApply imp_bind'.
      iApply imp_bind'.
      iApply (imp_mono with "H").
      iIntros ([v|v]) "H /=".
      * iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        repeat iApply imp_ret.
        iApply "H".
      * iApply ("E" with "H").
  Qed.

  Lemma imp_EAssert_exn_sep η e φ1 φ E Ψ :
    φ (O2Ret #()) ∗
    (φ (O2Ret #()) -∗ imp^{ι} eval η e @ E <|Ψ|> {{ φ1 }}) ∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) ∗
    (∀ v, φ1 (O2Ret v) -∗ ⌜v = VTrue⌝ ∗ φ (O2Ret #()))
    ⊢ imp^{ι} eval η (EAssert e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "(R & H & He & P) /=". simpl_eval.
    iApply imp_choose.
    iNext. iSplit. by iApply imp_ret.
    iSpecialize ("H" with "R").
    iApply imp_bind'.
    iApply imp_bind'.
    iApply (imp_mono with "H").
    iIntros ([v|v]) "H /=".
    - iDestruct ("P" with "H") as "(-> & H)".
        assert (val_as_bool VTrue = ret true) as -> by reflexivity.
        by repeat iApply imp_ret.
    - iApply ("He" with "H").
  Qed.

  Lemma imp_EAssert η e R E Ψ :
    R ∧ imp^{ι}eval η e @ E <|Ψ|> {{ ensures v, ⌜v = VTrue⌝ ∗ R }} -∗
    imp^{ι}eval η (EAssert e) @ E <|Ψ|> {{ ensures _, R }}.
  Proof.
    iIntros "H".
    iApply imp_EAssert_exn.
    iSplit.
    - iApply (bi.and_elim_l with "H").
    - iPoseProof (bi.and_elim_r with "H") as "H".
      iSplitL "H". iAssumption.
      iSplitL. by iIntros. iIntros (v) "$ //".
  Qed.

  Lemma imp_EAssert_sep η e R E Ψ :
    R ∗ (R -∗ imp^{ι}eval η e @ E <|Ψ|> {{ ensures v, ⌜v = VTrue⌝ ∗ R }}) -∗
    imp^{ι}eval η (EAssert e) @ E <|Ψ|> {{ ensures _, R }}.
  Proof.
    iIntros "(? & ?)".
    iApply imp_EAssert_exn_sep. iFrame. eauto.
  Qed.

  (** * ERef : expr → expr *)

  Lemma imp_ERef_exn η e φ1 φ E Ψ :
    imp^{ι} eval η e @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ1 (O2Ret v) -∗ ∀ l, l ↦ (V v) -∗ φ (O2Ret (VLoc l))) -∗
    imp^{ι} eval η (ERef e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P". simpl_eval.
    iApply imp_bind'.
    iApply (imp_mono with "H").
    iIntros ([v|v]) "H".
    - iApply imp_alloc. iNext. iIntros (l) "Hl".
      iApply imp_bind.
      iApply imp_ret.
      iApply imp_ret.
      iApply ("P" with "H"). auto.
    - iApply ("E" with "H").
  Qed.

  Lemma imp_ERef `{Encode A} η e (φ1 : A → iProp Σ) (φ : loc → iProp Σ) E Ψ :
    imp^{ι} eval η e @ E <|Ψ|> {{ ensures #a, φ1 a }} -∗
    (∀ (a : A) (l : loc), φ1 a -∗ l ↦ V #a -∗ φ l) -∗
    imp^{ι} eval η (ERef e) @ E <|Ψ|> {{ ensures #l, φ l }}.
  Proof.
    iIntros "H P".
    iApply (imp_ERef_exn with "H"); auto.
    iIntros (v) "(%v' & -> & Hv) %l Hl".
    iExists l. iSplitR; first (iPureIntro; encode).
    iApply ("P" with "Hv Hl").
  Qed.

  (** * ELoad : expr → expr *)

  Lemma imp_ELoad_exn η e φ1 φ E Ψ :
    imp^{ι} as_loc (eval η e) @ E <|Ψ|> {{ φ1 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l, φ1 (O2Ret l) -∗ ∃ q v, pointsto l q (V v) ∗ ▷(pointsto l q (V v) -∗ φ (O2Ret v))) -∗
    imp^{ι} eval η (ELoad e) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H E P /=". simpl_eval.
    iApply imp_bind'.
    iApply (imp_mono with "H").
    iIntros ([l|v]) "H1".
    - iSpecialize ("P" with "H1").
      iDestruct "P" as (q v) "(Hl & P)".
      iApply (imp_load with "Hl"). iNext. iIntros "Hl".
      iApply imp_ret.
      iApply ("P" with "Hl").
    - iApply ("E" with "H1").
  Qed.

  Lemma imp_ELoad η e (φ1 : loc → iProp Σ) φ E Ψ :
    imp^{ι} (eval η e) @ E <|Ψ|> {{ ensures #l, φ1 l }} -∗
    (∀ l, φ1 l -∗ ∃ q v, pointsto l q (V v) ∗ ▷(pointsto l q (V v) -∗ φ v)) -∗
    imp^{ι} eval η (ELoad e) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELoad_exn with "[H]"); auto.
    - iApply imp_bind. iApply (imp_mono with "H").
      iIntros ([|]); [ iIntros "Hl" | iIntros ([])].
      simpl. iDestruct "Hl" as "(%v & -> & Hφ1)".
      iApply imp_ret. instantiate (1 := (ensures v, φ1 v)%I). iApply "Hφ1".
    - iIntros (?) "[]".
    - iIntros (l) "Hφ1".
      iApply "P". iApply "Hφ1".
  Qed.

  Lemma imp_ELoad_simple η e (l : loc) q (v : val) E Ψ :
    imp^{ι} eval η e @ E <|Ψ|> {{ λ v, ⌜v = #l⌝ }} -∗
    pointsto l q (V v) -∗ imp^{ι} eval η (ELoad e) @ E <|Ψ|> {{ λ v', ⌜v' = v⌝ ∗ pointsto l q (V v) }}.
  Proof.
    iIntros "H Hl". iApply (imp_ELoad _ _ (λ l1, ⌜l = l1⌝%I) with "[H]").
    - iApply (imp_mono_ret with "H").
      iIntros (?) "(-> & _)". iExists l; done.
    - iIntros (? ->). iExists _, _; iFrame. auto.
  Qed.

  (** * EStore : expr → expr → expr *)

  Lemma imp_EStore_exn η e1 e2 φ1 φ2 φ E Ψ :
    imp^{ι} as_loc (eval η e1) @ E <|Ψ|> {{ φ1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ φ2 }} -∗
    (∀ v, φ1 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ v, φ2 (O2Throw v) -∗ φ (O2Throw v)) -∗
    (∀ l1 v2, φ1 (O2Ret l1) ∗ φ2 (O2Ret v2) -∗
      ∃ v1, l1 ↦ (V v1) ∗ ▷(l1 ↦ (V v2) -∗ φ (O2Ret VUnit))) -∗
    imp^{ι} eval η (EStore e1 e2) @ E <|Ψ|> {{ φ }}.
  Proof.
    iIntros "H1 H2 E1 E2 P /=". simpl_eval.
    iApply (imp_Par with "H1 H2 [E1] [E2]").
    - iIntros (e) "H1". iApply imp_throw. iApply ("E1" with "H1").
    - iIntros (e) "H2". iApply imp_throw. iApply ("E2" with "H2").
    - iIntros (l1 v2) "H1 H2".
      iSpecialize ("P" $! l1 v2 with "[$]").
      iDestruct "P" as (v1) "(Hl1 & P)".
      iApply (imp_store with "Hl1 [P]"). iNext; iIntros "Hl1".
      iApply imp_ret.
      iApply ("P" with "Hl1").
  Qed.

  Lemma imp_EStore `{Encode A} {η e1 e2} (φ1 : loc -d> iPropO Σ) (φ2 : A -d> iPropO Σ) φ E Ψ :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures #l, φ1 l }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ2 a }} -∗
    (∀ l a, φ1 l ∗ φ2 a -∗
            ∃ (a' : A), l ↦ (V #a') ∗ ▷ (l ↦ (V #a) -∗ φ VUnit)) -∗
    imp^{ι} eval η (EStore e1 e2) @ E <|Ψ|> {{ ensures v, φ v }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (imp_EStore_exn with "[H1] H2").
    - iApply imp_bind; iApply (imp_mono with "H1").
      iIntros ([|]); [ iIntros "H1 /=" | iIntros "[]" ].
      iDestruct "H1" as "(%v & -> & H1)".
      iApply imp_ret.
      instantiate (1 := (λ o, match o with | O2Ret l => φ1 l | _ => False end)%I).
      iApply "H1".
    - iIntros (? []).
    - auto.
    - simpl.
      iIntros (l v) "(Hφ1 & (%a & -> & Hφ2))".
      iCombine "Hφ1 Hφ2" as "H".
      iDestruct ("P" with "H") as "(%a' & Hl & Hnext)".
      iExists #a'; iFrame.
  Qed.

  (* Here, [l↦v] is threaded through [e2], as one is more likely to use
     ownership of [l] in [e2] than in [e1] (i.e. we rarely write things like
     [(!r := 1; r) := 2]) *)
  Lemma imp_EStore_simple `{Encode A} η e1 e2 (l : loc) (v : A) E Ψ :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ λ v, ⌜v = #l⌝ }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ λ v', ⌜v' = #v⌝ ∗ l ↦ (V #v) }} -∗
    imp^{ι} eval η (EStore e1 e2) @ E <|Ψ|> {{ λ v', ⌜v' = #()⌝ ∗ l ↦ (V #v) }}.
  Proof.
    iIntros "H1 H2".
    iApply (imp_EStore (λ l1, ⌜l = l1⌝%I) (λ v', ⌜v'=v⌝ ∗ l ↦ V #v)%I  with "[H1] [H2]").
    - iApply (imp_mono with "H1").
      iIntros ([|]); [ | iIntros "[]" ].
      iIntros "(-> & _)".
      iExists l; auto.
    - iApply (imp_mono with "H2").
      iIntros ([|]); [ | iIntros "[]" ].
      iIntros "(-> & Hl)".
      iExists v; auto.
    - iIntros (? ?) "(-> & -> & Hl)". iFrame.
      auto.
  Qed.

  (** * EPerform : expr -> expr *)

  Lemma imp_EPerform η e E ψ (φ1 : val -d> iPropO Σ) φ :
    imp^{ι}eval η e @ E <|ψ|> {{ ensures v, φ1 v }} -∗
    (∀ v, φ1 v -∗ imp^{ι}perform v @ E <|ψ|> {{ φ }} ) -∗
    imp^{ι}eval η (EPerform e) @ E <|ψ|> {{ φ }}.
  Proof.
    iIntros "He Hv".
    simpl_eval. iApply imp_bind.
    iApply (imp_mono with "He").
    iIntros ([|]) "Hφ1"; [ by iApply "Hv" | done ].
  Qed.

  (** * EContinue : expr -> expr -> expr *)

  Context {A : Type} `{Encode A}.

  Lemma imp_EContinue' η e1 e2 E ψ (φ1 : cont -d> iPropO Σ) (φ2 : val -d> iPropO Σ) ζ (Φ : A → iProp Σ) :
    imp^{ι} (eval η e1) @ E <|ψ|> {{ ensures #k, φ1 k }} -∗
    imp^{ι} eval η e2 @ E <|ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ (k : cont) v, φ1 k -∗ φ2 v -∗
                imp^{ι} stop CResume (k, O2Ret v) @ E <|ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    imp^{ι} eval η (EContinue e1 e2) @ E <|ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hk Hv Hmon".
    simpl_eval.
    iApply (imp_Par2 with "[Hk] [Hv] [Hmon]").
    { unfold as_cont. iApply imp_bind.
      iApply (imp_mono with "Hk").
      iIntros ([|]); last done.
      iIntros "(%v & -> & Hφ1)".
      iApply imp_ret. iExists a.
      instantiate (1 := observe_cont). iSplitR; first done.
      iApply "Hφ1". }
    { iApply (imp_mono with "Hv").
      iIntros ([|]); last done.
      iIntros "Hφ2". iExists a.
      instantiate (1 := observe_val). iSplitR; first done.
      iApply "Hφ2". }
    simpl; iIntros (k v) "Hφ1 Hφ2".
    iApply ("Hmon" with "Hφ1 Hφ2").
  Qed.

  Corollary imp_EContinue η e1 e2 E ψ (φ1 : cont -d> iPropO Σ) (φ2 : val -d> iPropO Σ) ζ (Φ : A → iProp Σ) :
    imp^{ι}(eval η e1) @ E <|ψ|> {{ ensures #k, φ1 k }} -∗
    imp^{ι}eval η e2 @ E <|ψ|> {{ ensures v2, φ2 v2 }} -∗
    (∀ k v, φ1 k -∗ φ2 v -∗
       ∃ sk, isCont k sk ∗
        (isShot k -∗
            ▷ imp^{ι}(sk (O2Ret v)) @ E <|ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }})) -∗
    imp^{ι}eval η (EContinue e1 e2) @ E <|ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H3".
    iApply (imp_EContinue' with "H1 H2").
    iIntros (??) "H1 H2".
    iSpecialize ("H3" with "H1 H2").
    iDestruct "H3" as (?) "(H1 & H2)".
    iApply (imp_resume with "H1").
    iIntros "H1".
    iSpecialize ("H2" with "H1"). iNext.
    by rewrite try2_inject2_right.
  Qed.

  Lemma imp_EFork' φ η e1 e2 E Ψ (φ1 φ2 : val -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    ▷ (∀ ι' v1 v2, valid_thread ι' φ -∗ φ1 v1 -∗ φ2 v2 -∗
                  imp^{ι'} call v1 v2 @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    simpl_eval.
    iApply (prove_imp_Par with "H1 H2").
    iIntros (v1 v2) "H1 H2"; simpl.
    iApply imp_fork.
    iIntros "!>" (ι') "#Hvalid".
    iSplitR ""; [ | ].
    iApply ("Hcall" with "Hvalid H1 H2").
    iExists _; iFrame "#"; iPureIntro; reflexivity.
  Qed.

  Lemma imp_EFork `{Encode A} P φ η e1 e2 E Ψ (φ_arg : A -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ_arg a }} -∗
    ▷ (∀ ι' a m, valid_thread ι' φ -∗ φ_arg a -∗
                 P a m -∗ imp^{ι'} m @ E <| ⊥ |> {{ λ o, □ φ o }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork' with "H1 H2").
    iIntros "!>" (ι' f v2) "Hvalid HSpec (%v & -> & H2)".
    rewrite iSpec_equation_1.
    iSpecialize ("HSpec" $! v).
    iApply ("Hcall" $! ι' v (call f #v) with "Hvalid H2 HSpec").
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is persistent *)
  Lemma imp_EFork_persistent' φ η e1 e2 E Ψ (φ1 φ2 : val -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    ▷ (∀ ι' v1 v2, φ1 v1 -∗ φ2 v2 -∗
                  imp^{ι'} call v1 v2 @ E <|⊥|> {{ λ _, □ φ }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', □ joinable ι' φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    simpl_eval.
    iApply (prove_imp_Par with "H1 H2").
    iIntros (v1 v2) "H1 H2"; simpl.
    iApply imp_fork.
    iIntros "!>" (ι') "#Hvalid".
    iSplitR ""; [ | ].
    iApply ("Hcall" with "H1 H2").
    iExists _; iFrame "#"; iSplit; auto.
  Qed.

  Lemma imp_EFork_persistent φ `{Encode A} P η e1 e2 E Ψ (φ_arg : A -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ_arg a }} -∗
    ▷ (∀ ι' a m, φ_arg a -∗
                   P a m -∗ imp^{ι'} m @ E <|⊥|> {{ λ _, □ φ }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', □ joinable ι' φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork_persistent' with "H1 H2").
    iIntros "!>" (ι' f v) "HSpec (%a & -> & H2)"; simpl.
    iApply ("Hcall" with "H2").
    rewrite iSpec_equation_1.
    iApply "HSpec".
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is a list of
  resources that other threads can recover when joining. *)
  Lemma imp_EFork_resourceful_list' φs η e1 e2 E Ψ (φ1 φ2 : val -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures v1, φ1 v1 }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures v2, φ2 v2 }} -∗
    ▷ (∀ ι' v1 v2, φ1 v1 -∗ φ2 v2 -∗
                  imp^{ι'} call v1 v2 @ E <| ⊥ |> {{ λ _, [∗ list] φ ∈ φs, φ }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', [∗ list] φ ∈ φs, joinable ι' φ }}.
  Proof.
    (* TODO reuse the proof from [stop_rules.v] instead of having this one, which is now redundant *)
    iIntros "H1 H2 Hcall".
    simpl_eval.
    iApply (prove_imp_Par with "H1 H2").

    iIntros (v1 v2) "H1 H2 /=".
    iApply imp_fork_resourceful.
    iIntros "!>" (ι') "Hjoinable /=". iFrame.
    iSplit; last (iPureIntro; reflexivity).
    iApply ("Hcall" with "H1 H2").
  Qed.

  Lemma imp_EFork_resourceful_list φs `{Encode A} P η e1 e2 E Ψ (φ_arg : A -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ_arg a }} -∗
    ▷ (∀ ι' a m, φ_arg a -∗
                 P a m -∗ imp^{ι'} m @ E <| ⊥ |> {{ λ _, [∗ list] φ ∈ φs, φ }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', [∗ list] φ ∈ φs, joinable ι' φ }}.
  Proof.
    (* TODO reuse the proof from [stop_rules.v] instead of having this one, which is now redundant *)
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork_resourceful_list' with "H1 H2").
    iIntros "!>" (ι' f v) "HSpec (%a & -> & H2)"; simpl.
    iApply ("Hcall" with "H2").
    rewrite iSpec_equation_1.
    iApply "HSpec".
  Qed.

  (* Specialization for one and two resources instead of a list of resources *)

  Local Lemma imp_EFork_one_resource φ `{Encode A} P η e1 e2 E Ψ (φ_arg : A -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ_arg a }} -∗
    ▷ (∀ ι' a m, φ_arg a -∗ P a m -∗ imp^{ι'} m @ E <| ⊥ |> {{ λ _, φ }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', joinable ι' φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (imp_mono with "[-]").
    iApply (imp_EFork_resourceful_list [φ] with "H1 H2 [H]").
    - iIntros "!> % % % H1 H2".
      iSpecialize ("H" with "H1 H2").
      iApply (imp_mono with "H").
      iIntros (_) "/= $".
    - iIntros ([|]) "// (% & -> & $ & ?) //".
  Qed.

  Local Lemma imp_EFork_two_resources φ1 φ2 `{Encode A} P η e1 e2 E Ψ (φ_arg : A -> iProp Σ) :
    imp^{ι} eval η e1 @ E <|Ψ|> {{ ensures f, iSpec τ[A] f P }} -∗
    imp^{ι} eval η e2 @ E <|Ψ|> {{ ensures #a, φ_arg a }} -∗
    ▷ (∀ ι' a m, φ_arg a -∗ P a m -∗ imp^{ι'} m @ E <|⊥|> {{ λ _, φ1 ∗ φ2 }}) -∗
    imp^{ι} eval η (EFork e1 e2) @ E <|Ψ|> {{ ensures #ι', joinable ι' φ1 ∗ joinable ι' φ2 }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (imp_mono with "[-]").
    iApply (imp_EFork_resourceful_list [φ1; φ2] with "H1 H2 [H]").
    - iIntros "!> % % % H1 H2".
      iSpecialize ("H" with "H1 H2").
      iApply (imp_mono with "H").
      iIntros (_) "/= ($ & $)".
    - iIntros ([|]) "// (% & -> & $ & $ & ?) //".
  Qed.

  Lemma imp_EJoin e η E Ψ φ Φ :
    imp^{ι} eval η e @ E <|Ψ|> {{ ensures #ι, valid_thread ι φ }} -∗
    ▷ (∀ o, □ φ o -∗ Φ o) -∗
    imp^{ι} eval η (EJoin e) @ E <|Ψ|> {{ Φ }}.
  Proof.
    iIntros "Hid Hjoined".
    simpl_eval.
    iApply imp_bind. unfold as_thread. iApply imp_bind.
    iApply (imp_mono with "Hid").
    iIntros ([ ι' |]); [ iIntros "Hvalid" | iIntros "[]" ].
    iDestruct "Hvalid" as "(% & -> & Hvalid)".
    iApply imp_ret.
    iApply (imp_join with "Hvalid Hjoined").
  Qed.

  (* The joinable rule for join is the same for persistent and resourceful posts *)
  Lemma imp_EJoin_joinable e η E Ψ φ Φ :
    ↑joinN ⊆ E →
    imp^{ι} eval η e @ E <|Ψ|> {{ ensures #ι', joinable ι' φ }} -∗
    ▷ (∀ o, ▷ φ -∗ Φ o) -∗
    imp^{ι} eval η (EJoin e) @ E <|Ψ|> {{ Φ }}.
  Proof.
    iIntros "%Hmask Hid Hjoined".
    simpl_eval.
    iApply imp_bind. unfold as_thread. iApply imp_bind.
    iApply (imp_mono with "Hid").
    iIntros ([ ι' |]); [ iIntros "Hjoinable" | iIntros "[]" ].
    iDestruct "Hjoinable" as "(% & -> & Hjoinable)".
    iApply imp_ret.
    iApply imp_fupd_post.
    iDestruct "Hjoinable" as "(%ψ & #Hvalid & Hcont)".
    iApply (imp_join with "[$]").
    iNext. iIntros "%o Hψ".
    iApply "Hjoined".
    iSpecialize ("Hcont" with "Hψ").
    iMod (fupd_mask_subseteq (↑joinN) Hmask) as "O".
    iMod "Hcont".
    iMod "O".
    done.
  Qed.

  (* TODO add a persistent predicate [thread_outcome ι o] so that [joinable] can
  talk about the outcome of the spawned thread. This is also needed when the
  spawned thread allocates and returns an address that is joined several times,
  e.g. by several threads, or even to prove safety of such programs:

  assert Domain.(let d = spawn ref in join d = join d)

  assert Domain.(let d = spawn Random.bool in join d = join d) *)

End imp_rules_expr.
