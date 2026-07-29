From osiris Require Import osiris.
From osiris.stdlib Require Import og_atomic.

(** * Specifications for the [Atomic] stdlib module.

    The [Atomic.Loc] operations are compiler primitives; Osiris
    translates them as eta-expanded closures over the corresponding
    Osiris instructions ([ECAS], [EFAA], ...), so their specifications
    are proved directly against those closures.

    For now only [Loc.compare_and_set] is specified, at inline-record
    values (the shape needed by clients that CAS a variant field, e.g.
    the concurrent union-find example). The remaining operations can be
    specified the same way when a client needs them. *)

Section atomic_proofs.

  Context `{!osirisGS Σ}.

  (* The logically-atomic specification of [Atomic.Loc.compare_and_set]
     at inline-record values.

     The caller provides, in a mask-changing fupd (typically opening an
     invariant), the points-to of the atomic location — which must hold
     an inline record — together with [isBlock] fractions for the
     current and expected blocks; the latter resolve the physical
     comparison performed by the CAS ([expected] must be a *mutable*
     block for the comparison to be defined). The caller learns the
     comparison's outcome when closing.

     Both the "expected" snapshot [seen] and the "new value" [v'] are
     generic over any [A] with an [Encode A] instance (not hardcoded to
     [val]): a client that already holds the *record* underlying its
     snapshot (e.g. from an earlier atomic read) or that just allocated
     a fresh record for the new value can instantiate [A := record]
     under the local [encode_record c] instance and pass records
     directly — no val/elem bridging needed, since [imp_EInline] and
     the atomic record-read rules already produce elem-domain
     postconditions. *)

  Definition compare_and_set_spec `{Encode A} (l : loc) (seen v' : A)
      (m : microvx) : iProp Σ :=
    ∀ (E2 : coPset) (Φ : bool → iProp Σ),
      ▷ (|={⊤,E2}=>
           ∃ c cs (r rs : record) dq1 dq2 t,
             ⌜#seen = VInline cs rs⌝ ∗
             ▷ l ↦ VInline c r ∗ ▷ isBlock r dq1 t ∗ ▷ isBlock rs dq2 Mut ∗
             ▷ (l ↦ (if locations.eqb r rs then #v' else VInline c r) -∗
                isBlock r dq1 t -∗ isBlock rs dq2 Mut -∗
                |={E2,⊤}=> Φ (locations.eqb r rs))) -∗
      imp m {{ Φ }}.

  Lemma imp_Loc_compare_and_set η :
    ⊢ imp (eval η (EAnonFun __Loc_fun5))
        {{ λ c, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] c compare_and_set_spec }}.
  Proof.
    iApply imp_EAnon_poly_pers.
    iIntros "!>" (A HencA). simpl.
    iIntros (l seen v').
    unfold compare_and_set_spec.
    iIntros (E2 Φ) "Hfupd".
    iApply imp_please; iNext.
    iApply (imp_cas_inline_atomic E2 ⊤ _ _ _ _
              (λ l0 : loc, ⌜l0 = l⌝)%I (λ s : val, ⌜s = #seen⌝)%I
              (λ w : val, ⌜w = #v'⌝)%I
              with "[] [] [] [Hfupd]").
    { imp_path. }
    { imp_path. }
    { imp_path. }
    iNext.
    iMod "Hfupd".
    iModIntro.
    iIntros (l0 s w) "-> -> ->".
    iDestruct "Hfupd" as (c cs r rs dq1 dq2 t) "(-> & Hl & Hr & Hrs & Hk)".
    iExists c, cs, r, rs, dq1, dq2, t.
    iFrame. done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Module-level specifications, in the style of [array_module_spec]. *)

  Definition atomic_loc_module_dom : gset var :=
    {[ "get"; "exchange"; "compare_and_set"; "fetch_and_add";
       "set"; "incr"; "decr" ]}.

  Definition atomic_loc_module_spec : env → iProp Σ :=
    (context [
         var_spec "compare_and_set"
           (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec)
      ] atomic_loc_module_dom)%I.

  Definition atomic_module_dom : gset var :=
    {[ "Loc"; "make"; "get"; "set"; "exchange"; "compare_and_set";
       "fetch_and_add"; "incr"; "decr" ]}.

  Definition atomic_module_spec : env → iProp Σ :=
    (context [
         var_spec "Loc" (λ δ : env, atomic_loc_module_spec δ)
      ] atomic_module_dom)%I.

  Global Instance atomic_spec_pers η : Persistent (atomic_module_spec η).
  Proof. apply _. Qed.

  (* The [Atomic] module satisfies its specification. The operations
     without a specification are admitted, as in [array.module_proof]. *)
  Lemma module_proof η :
    ⊢ imp (eval_mexpr η __main) {{ atomic_module_spec }}.
  Proof.
    iApply imp_module.
    iApply (imp_sitems_module atomic_loc_module_spec).
    { iApply imp_module.
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (get) "_".
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (exchange) "_".
      iApply (imp_sitems_external
                (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec)%I).
      { iApply imp_Loc_compare_and_set. }
      iIntros (cas) "#Hcas".
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (faa) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (set) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (incr) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (decr) "_".
      iApply imp_sitems_nil.
      iFrame "#". simpl. auto. }

    iIntros (δLoc) "#HLoc".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (make) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (get) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (set) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (exchange) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (cas) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (faa) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (incr) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (decr) "_".
    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Admitted.

  (* Resolving [Atomic.Loc.compare_and_set] through the module
     specification. This is the form clients use to discharge a
     top-level alias such as [let cas = Atomic.Loc.compare_and_set]. *)
  Lemma atomic_cas_path_spec η :
    in_env "Atomic" atomic_module_spec η -∗
    path_spec ["Atomic"; "Loc"; "compare_and_set"]
      (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec)%I η.
  Proof.
    iIntros "(%δA & %HA & #HAspec)".
    rewrite /atomic_module_spec /atomic_loc_module_spec /context /=.
    iDestruct "HAspec" as "(%HdomA & HLoc & _)".
    iDestruct "HLoc" as "(%δL & %HL & #HLspec)".
    iDestruct "HLspec" as "(%HdomL & Hcas & _)".
    iDestruct "Hcas" as "(%cas & %Hcas & #Hspec)".
    iExists cas.
    iSplit; last done.
    iPureIntro.
    simpl. rewrite HA /=.
    rewrite -!solve_encode_env /=.
    rewrite HL /=.
    rewrite -!solve_encode_env /=.
    exact Hcas.
  Qed.

End atomic_proofs.
