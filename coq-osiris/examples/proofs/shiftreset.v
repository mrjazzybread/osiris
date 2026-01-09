From stdpp Require Import telescopes.
From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_shiftreset.

(* Reasoning about delimited control via [shift/reset].

   Note: Sanity check example following [Hazel] [shift_reset] example and
         specification. *)

(* ========================================================================== *)
(** * Protocol. *)

(* ------------------------------------------------------------------------ *)
(** Shift Protocol. *)

Section shift_protocol.
  Context `{!osirisGS Σ}.

  Definition shift shift_eff h : val := VXData shift_eff [h].

  Definition is_shift (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) h : iProp Σ :=
    iSpec τ[cont] h (λ k m,
        ∀ ι,
        (∀ w, Q w -∗ EWP[ι] (resume k (O2Ret w)) <| Ψ |> {{ ensures v, Φ v }}) -∗
        ▷ EWP[ι] m <| Ψ |> {{ ensures v, Φ v }})%I.

  (* Note that this specification is different from in [Hazel]; there is
     no recursive reference within the specification itself. *)

  Definition SHIFT ℓ :
    (iEffO -d> (val -d> iPropO Σ) -d> iEffO) := λ Ψ Φ,
    (>> h Q >> !(shift ℓ h) {{ (is_shift Ψ Φ Q h) }};
      << w << ?(w) {{ Q ↑ w }} @ OS)%ieff.

  Lemma upcl_SHIFT ℓ Ψ Φ v Φ' :
    iEff_car (upcl OS (SHIFT ℓ Ψ Φ)) v Φ' ≡
      (∃ t Q,
          ⌜v = shift ℓ t ⌝ ∗ is_shift Ψ Φ Q t ∗
          (∀ w, Q ↑ w -∗ Φ' w))%I.
  Proof.
    transitivity (iEff_car (upcl OS (SHIFT ℓ Ψ Φ)) v Φ').
    - by iApply iEff_car_proper.
    - by rewrite /SHIFT (upcl_tele' [tele _ _] [tele _]).
  Qed.

End shift_protocol.

(* ------------------------------------------------------------------------ *)
(** Reasoning Rules. *)

Section reasoning_rules.
  Context `{!osirisGS Σ}.

  Definition env shift_eff := ("Shift", (VLoc shift_eff)) :: stdlib_env.

  (* Mapping of translated function declaration names *)
  Definition shift_f := (EAnonFun __fun0).
  Definition reset_f := (EAnonFun __fun2).

  Definition reset_spec ℓ : val → microvx → iProp Σ :=
    λ f m,
      (∀ (Ψ : iEff Σ) (Φ : val → iProp Σ),
          iSpec τ[unit] f (λ _ m, EWP m <|SHIFT ℓ Ψ Φ|> {{ ensures v, Φ v }}) -∗
          EWP m <|Ψ|> {{ ensures v, Φ v }})%I.

  Definition shift_spec ℓ : val → microvx → iProp Σ :=
    λ f m,
      (∀ (Ψ : iEff Σ) (Φ Q : val → iProp Σ),
          is_shift Ψ Φ Q f -∗
          EWP m <|SHIFT ℓ Ψ Φ|> {{ ensures v, Q v}})%I.

End reasoning_rules.

(* ------------------------------------------------------------------------ *)
(** Verification. *)

Section verification.
  Context `{!osirisGS Σ}.

  Lemma ewp_ensures_val {X} ι (Φ : val → iProp Σ) (m : micro val X) E Ψ :
    EWP[ι] m @ E <|Ψ|> {{ ensures #v, Φ v }} ⊣⊢ EWP[ι] m @ E <|Ψ|> {{ ensures v, Φ v }}.
  Proof.
    iStartProof; iSplit; iIntros "Hwp"; iApply (ewp_mono with "Hwp");
      (iIntros ([|]); [ | iIntros ([]) ]).
    - iIntros "(%v & -> & $)".
    - iIntros "HΦ". iExists a.
      iSplit; [ equality | iAssumption ].
  Qed.

  Lemma establish_shift_spec η (shift_eff : loc) :
    lookup_name η "Shift" = ret (VLoc shift_eff) →
    ⊢ EWP eval η (EAnonFun __fun0)
      {{ ensures v, □ iSpec τ[val] v (shift_spec shift_eff) }}.
  Proof.
    iIntros (Hlookup ι).
    iApply (ewp_EAnon_pers τ[val]); simpl.
    iIntros "!>" (f). rewrite /shift_spec.
    iIntros (Ψ Φ Q) "Hf %ι'".
    iApply ewp_please; iNext.
    iApply (ewp_EPerform _ _ _ _ (λ v, ⌜v = VXData shift_eff [f]⌝)%I).
    { simpl_eval. rewrite Hlookup /widen /try /=. iApply prove_ewp_Par.
      iApply ewp_ret. instantiate (1 := (λ v, ⌜v = f⌝)%I). equality.
      iApply ewp_ret. instantiate (1 := (λ v, ⌜v = []⌝)%I). equality.
      iIntros (?? -> ->) "/=".
      iApply ewp_ret. equality. }
    iIntros (? ->).
    iApply ewp_perform.
    rewrite /prot upcl_SHIFT. iFrame.
    iSplit; first equality.
    iIntros (o) "$".
  Qed.

  Lemma establish_reset_spec η (shift_eff : loc) :
    lookup_name η "Shift" = ret (VLoc shift_eff) →
    ⊢ EWP eval η (EAnonFun __fun2)
      {{ ensures v, □ iSpec τ[val] v (reset_spec shift_eff) }}.
  Proof.
    iIntros (Hlookup ι).
    iApply (ewp_EAnon_pers τ[val]); simpl.
    iIntros "!>" (f). rewrite /reset_spec.
    iIntros (Ψ Φ) "Hf %ι'".
    iApply ewp_please; iNext.

    iApply ewp_EMatch.

    iApply (ewp_deep_handler _ _ (SHIFT shift_eff Ψ Φ) (Φ ↑) with "[Hf]").
    { iApply (ewp_mono with "[-]").
      iApply (ewp_EApp τ[unit] with "[Hf]").
      simpl_eval. iApply ewp_ret. iApply "Hf".
      simpl_eval. iApply ewp_ret. instantiate (1 := (λ u, ⌜u = tt⌝)%I). equality; encode.
      simpl. iIntros (? -> m) "Hwp".
      iApply (ewp_mono with "Hwp").
      iIntros ([|]); [ | iIntros ([]) ]. simpl.
      iIntros "!> HΦ". iExists a. rewrite <- solve_encode_val. iSplit; [ equality | iExact "HΦ" ].
      iIntros ([|]); [ | iIntros ([]) ]. simpl.
      iIntros "(%v &-> & $)". }

    iLöb as "IH".
    iApply prove_deep_handler_spec; iSplit.

    (* Base case: we just return the value. *)
    { iIntros (?). iIntros "H !>"; destruct o; try done.
      next_branch.
      iIntros (? ->).
      iApply ewp_EPath. by iApply ewp_ret. }

    (* Handler case: an effect is being performed. *)
    iIntros (v k) "Hprot"; rewrite /prot.
    rewrite upcl_SHIFT.
    iDestruct "Hprot" as (g Q) "[-> [Hg Hk]]".
    rewrite /deep_handler_spec seal_eq.

    unfold is_shift.

    iModIntro.
    next_branch. iIntros (? []).
    next_branch. iIntros (? ->).
    iApply ewp_ensures_val.
    iApply (ewp_EApp τ[cont] with "[Hg] []").
    simpl_eval. iApply ewp_ret. iAssumption.
    simpl_eval. iApply ewp_ret. instantiate (1 := (λ v, ⌜v = k⌝)%I). iExists k; equality.
    iIntros (? -> m) "Hwp". rewrite /tapp.
    iApply ewp_ensures_val.
    iApply "Hwp".
    iIntros (v) "HQ".
    iSpecialize ("Hk" $! (O2Ret v) with "HQ").
    iApply "Hk". iNext.
    iApply "IH".
    tauto.
  Qed.

  Definition dummy_env := ("Effect", VStruct [("Deep", VStruct [])]) :: stdlib_env.

  Lemma module_proof :
    ⊢ EWP (eval_mexpr dummy_env __main)
      {{ ensures v, ∃ η, ⌜v = VStruct η⌝ ∧ ⌜lookup_name η "main" = ret #4⌝ }}.
  Proof.
    iIntros (ι).
    iApply ewp_module.
    iApply (ewp_sitems_cons _ _ _ (ieq ?[φ])).

    (* [open Effect] *)
    { iApply (ewp_sitem_open _ _ (ieq ?[φ3])).
      { simpl_eval_mexpr. iApply ewp_ret. equality. }
      iIntros (δ' ->). equality. }

    (* [open Effect.Deep] *)
    iIntros (? ->).
    iApply (ewp_sitems_cons _ _ _ (ieq ?[φ])); [ | iIntros (? ->)].
    { iApply (ewp_sitem_open _ _ (ieq ?[φ2]));
        [ | iIntros (? ->); equality ].
      simpl_eval_mexpr. iApply ewp_ret. equality. }

    (* [type _ Effect.t += Shift : t Effect.t] *)
    iApply ewp_sitems_extend.
    iIntros ([η δ]) "(%shift_eff & -> & Hshifteff)"; clear η δ.

    (* [let shift f = perform (Shift f)] *)
    iApply (ewp_sitems_let_singleton_var (λ v, □ iSpec τ[val] v (shift_spec shift_eff))%I).
    { iApply establish_shift_spec; auto. }
    iIntros ([η δ]) "(%shift & -> & #Hshift)". clear η δ.

    (* [let reset f = try f () with ...] *)
    iApply (ewp_sitems_let_singleton_var (λ v, □ iSpec τ[val] v (reset_spec shift_eff))%I).
    { iApply establish_reset_spec; auto. }
    iIntros ([η δ]) "(%reset & -> & #Hreset)". clear η δ.

    (* [let main = reset (fun _ -> ...)] *)
    iApply (ewp_sitems_let_singleton_var (λ v, ⌜v = #4⌝)%I with "[Hshift Hreset]").
    { (* Change the postcondition to [ensures #n, ⌜n = 4%Z⌝]. *)
      iApply (ewp_mono with "[-]"); last first.
      { instantiate (1 := (ensures #n, ⌜n = 4%Z⌝)%I).
        iIntros ([|]); [ | iIntros ([]) ].
        iIntros "(%v & -> & ->)". equality. }

      (* Prove that [reset (fun _ -> ...)] return [n = 4]. *)
      iApply (ewp_EApp τ[val] with "[Hreset] [Hshift]").
      { simpl_eval. iApply ewp_ret. iAssumption. }
      2: { simpl.
           iIntros (v) "Hv %m reset_spec".
           unfold reset_spec, tapp. iNext.
           iApply ("reset_spec" with "Hv"). }

      iApply ewp_ensures_val.
      iApply (ewp_EAnon τ[unit]).
      iIntros ([] ι').
      iApply (ewp_please); iNext.
      (* [fun _ -> ...] gets translated to [match anon with | _ -> ...] *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler).
      { simpl_eval. iApply ewp_ret. instantiate (1 := (ensures #v, ⌜v = tt⌝)%I).
        iExists tt; equality. }
      iApply prove_deep_handler_spec.
      iSplit; last first.
      { instantiate (1 := ⊥).
        iIntros (??); rewrite /prot upcl_bottom; iIntros ([]). }
      iIntros ([|]); [ | iIntros ([]) ].
      iIntros "(%u & -> & ->) !>".

      iApply deep_handle_cons; [ iPureIntro | iSplit ].
      {  ltac2:(specify_cpattern ()). pattern_match. apply eq_refl. }
      2: { iIntros ([]). }
      iIntros (? <-).

      (* Subgoal: [shift (fun k -> ...) + 3] returns [4]. *)
      iApply (ewp_EIntAdd'); clear ι.
      { (* Prove that [shift (fun k -> ...)] returns [1]? *)
        iApply (ewp_EApp τ[val]).
        { simpl_eval. iApply ewp_ret. iAssumption. }
        2: { iIntros (f) "Hf %m shift_spec".
             unfold shift_spec, tapp.
             iNext.
             iApply ("shift_spec" with "Hf"). }

        rewrite ewp_ensures_val.
        iApply (ewp_EAnon τ[cont]); simpl.

        iIntros (k ι) "Hresume".
        iApply ewp_please; iIntros "!> !>".
        (* Subgoal: [continue k 0 + 1] retuns [4]. *)
        iApply (ewp_EIntAdd' with "[Hresume]").
        { iApply ewp_EContinue'.
          { (* Evaluate [k]. *)
            simpl_eval. iApply ewp_ret.
            instantiate (1 := (λ v, ⌜v = k⌝)%I). iExists _; equality. }
          { (* Evalutate [0]. *)
            simpl_eval. iApply ewp_ret.
            instantiate (1 := (λ v, ⌜v = #0%Z⌝)%I). equality. }
          iIntros (? ? -> ->).
          iApply "Hresume".
          instantiate (1 := (λ v, ⌜v = 0%Z⌝)%I).
          iExists 0%Z; equality. }
        { (* Evaluate [1]. *)
          iApply (ewp_EInt with "[]").
          instantiate (1 := (λ n, ⌜n = 1%Z⌝)%I). iExists _; equality. }
        iIntros (n1 n2) "(-> & ->)". equality.
        (* The goal is now [(4 + 1) = 4]. *)
        admit. }
      { (* Evaluate [3]. *)
        iApply ewp_EInt.
        instantiate (1 := (λ n, ⌜n = 3⌝)%I). iExists _ ; equality. }

      iIntros (n1 n2) "(-> & ->)".
      (* The goal is now [(0 + 3) = 4]*)
      admit. }

    iIntros ([η δ]) "(%main & -> & %Hres)".

    iApply ewp_sitems_nil. simpl.
    iExists _. iSplit; first equality.
    iPureIntro.
    simpl. rewrite Hres. reflexivity.

  Admitted.

End verification.
