From osiris Require Import osiris.
From iris.proofmode Require Import ltac_tactics.

From osiris.test Require Import og_record_test.

Open Scope Z.

Class SimpleExpr (e : expr) := {}.
Global Hint Mode SimpleExpr ! : typeclass_instances.
Typeclasses Transparent deco.

Global Instance EPath_simple {p} : SimpleExpr (EPath p) := {}.

Global Instance EAdd_simple `{SimpleExpr e1, SimpleExpr e2} : SimpleExpr (EIntAdd e1 e2) := {}.
Global Instance EMul_simple `{SimpleExpr e1, SimpleExpr e2} : SimpleExpr (EIntMul e1 e2) := {}.
Global Instance ERecordAccess_simple `{SimpleExpr e1} {f} : SimpleExpr (ERecordAccess e1 f) := {}.

Section verification.

  Context `{!osirisGS Σ}.

  Definition length_spec r (m : microvx) : iProp Σ :=
    ∀ qp t (x y : Z),
      ▷ @ownRecord Σ _ τ[Z; Z] r qp t (x, y) -∗
      imp m {{ λ (i : Z), ⌜i = (x*x + y*y)%Z⌝ ∗ @ownRecord _ _ τ[Z; Z] r qp t (x, y) }}.

  Definition elength := EAnonFun __fun0.

  Lemma imp_length η :
    ⊢ imp (eval η elength) {{ λ length, □ iSpec τ[record] length length_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r qp t x y) "Hown".

    iApply imp_please; iNext.

    (* Goal: [(v.x * v.x) + (v.y * v.y)] *)
    imp_arith reading "Hown";
    (* All remaining subgoals are of the form [v.x] *)
    (iApply (imp_ERecordAccess with "Hown");
     [ split; simpl; lia | imp_path ]).
  Qed.

  Definition update_x_spec r x (m : microvx) : iProp Σ :=
    ∀ t (x0 y : Z),
      ▷ @ownRecord Σ _ τ[Z;Z] r 1 t (x0, y) -∗
      imp m {{ λ (_ : unit), @ownRecord Σ _ τ[Z;Z] r 1 t (x, y) }}.

  Definition eupdate_x := EAnonFun __fun2.

  Lemma imp_update_x η :
    ⊢ imp (eval η eupdate_x) {{ λ update_x, □ iSpec τ[record; Z] update_x update_x_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r x t x0 y) "Hown".
    iApply imp_please; iNext.
    iApply imp_mono_val; last first.

    iApply (imp_ERecordSet with "Hown"). split; simpl; lia.
    imp_path.
    imp_path. simpl.
    iIntros ([]) "(% & -> & $)".
  Qed.

  Lemma module_proof η :
    2 ≤ max_array_length →
    ⊢ imp (eval_mexpr η __main)
      {{ context
           [ var_spec "length" (λ length, iSpec τ[record] length length_spec);
             var_spec "update_x" (λ update, iSpec τ[record;Z] update update_x_spec) ]
           {[ "vec"; "length"; "update_x" ]} }}.
  Proof.
    intros Hmax_array.
    iApply imp_module.

    iApply (imp_sitems_let (A:=record)).
    { iApply (imp_ERecord (τ:=τ[Z; Z])).
      { simpl. lia. }
      iApply imp_evals_cons. imp_arith.
      iApply imp_evals_singleton. imp_arith. }

    iIntros (r) "(% & % & Hown & (-> & ->))".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_length. }

    iIntros (length) "#Hlength".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_update_x. }

    iIntros (update_x) "#Hupdate_x".
    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Qed.

End verification.

From osiris.logic Require Import big_opLZ.

Section encoded_fields.

  Context `{!osirisGS Σ}.

  Hypothesis Hmax : 2 ≤ max_array_length.

  Record point : Type := { x : Z; y : Z }.

  Definition ownPoint (r : record) (qp : Qp) (xs : point) : iProp Σ :=
    (∃ ls, isBlockLocs r ls ∗ r⤇{#qp} Mut ∗
          [∗ listZ] l;v ∈ ls; [ #xs.(x); #xs.(y)], l ↦{#qp} v)%I.

  Instance name' r p : fractional.Fractional (λ qp, ownPoint r qp p). admit. Admitted.

  Instance name r qp p : fractional.AsFractional (ownPoint r qp p) (λ qp, ownPoint r qp p) qp.
  Proof.
    constructor. reflexivity. apply _.
  Qed.

  Definition point_length_spec r (m : microvx) : iProp Σ :=
    ∀ qp (p : point),
      ▷ ownPoint r qp p -∗
      imp m {{ λ (i : Z), ⌜i = (p.(x) * p.(x) + p.(y) * p.(y))%Z⌝ ∗ ownPoint r qp p }}.

  Definition point_update_x_spec r x (m : microvx) : iProp Σ :=
    ∀ (p : point),
      ▷ ownPoint r 1 p -∗
      imp m {{ λ (_ : unit), ownPoint r 1 {| x := x; y:=p.(y) |} }}.


  Lemma ownRecord_ownPoint r qp (x y : Z) :
    ownRecord (τ:=τ[Z;Z]) r qp Mut (x, y) -∗
    ownPoint r qp {| x:=x; y:=y |}.
  Proof.
    iIntros "(% & Hblock & Htag & Hown)".
    iFrame.
  Qed.

  Lemma ownPoint_ownRecord r qp (x y : Z) :
    ownPoint r qp {| x:=x; y:=y |} -∗
    ownRecord (τ:=τ[Z;Z]) r qp Mut (x, y).
  Proof.
    iIntros "(% & Hblock & Htag & Hown)".
    iFrame.
  Qed.

  Lemma imp_point {η E Ψ ζ} e1 e2 (Φs : τ[Z;Z] -#> iProp Σ) :
    impure E (evals η [e1; e2]) Ψ ζ Φs -∗
    impure E (eval η (ERecord Mut [e1; e2])) Ψ ζ (λ r, ∃ x y, ownPoint r 1 {| x := x; y := y |} ∗ Φs x y)%I.
  Proof.
    iIntros "Hes".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecord with "Hes"). assumption. }
    iIntros (r) "(% & % & Hrecord & $)".
    iApply (ownRecord_ownPoint with "Hrecord").
  Qed.

  Lemma imp_point_x {η : env} {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}
    (r : record) (dq : Qp) (p : point) (e : expr) :
    ▷ ownPoint r dq p -∗
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ r' : record, ⌜r' = r⌝ }} -∗
    imp eval η (ERecordAccess e 0%Z) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ i : Z, ⌜i = x p⌝ ∗ ownPoint r dq p }}.
  Proof.
    iIntros "Hown He".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordAccess (τ:=τ[Z;Z]) _ 0 with "[Hown] He").
      split; simpl; lia.
      iApply (ownPoint_ownRecord with "Hown"). }
    iIntros (x) "(-> & $)". iPureIntro. reflexivity.
  Qed.

  Lemma imp_point_y {η : env} {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}
    (r : record) (dq : Qp) (p : point) (e : expr) :
    ▷ ownPoint r dq p -∗
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ r' : record, ⌜r' = r⌝ }} -∗
    imp eval η (ERecordAccess e 1%Z) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ i : Z, ⌜i = y p⌝ ∗ ownPoint r dq p }}.
  Proof.
    iIntros "Hown He".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordAccess (τ:=τ[Z;Z]) with "[Hown] He").
      split; simpl; lia.
      iApply (ownPoint_ownRecord with "Hown"). }
    iIntros (x) "(-> & $)". iPureIntro. reflexivity.
  Qed.

  Lemma point_update_x {η E Ψ ζ} (r : record) p e1 e2 (Φ : Z → iProp Σ) :
    ▷ ownPoint r 1 p -∗
    impure E (eval η e1) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 0 e2)) Ψ ζ (λ (_ : ()), ∃ x, Φ x ∗ ownPoint r 1 {| x:=x; y:=p.(y) |})%I.
  Proof.
    iIntros "Hown He1 He2".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordSet (τ:=τ[Z;Z]) with "[Hown] He1 [He2]").
      { split; simpl; lia. }
      iApply (ownPoint_ownRecord with "Hown").
      iApply "He2". }
    iIntros ([]) "(%x & $ & $)".
  Qed.

  Lemma imp_point_length η :
    ⊢ imp (eval η elength) {{ λ length, □ iSpec τ[record] length point_length_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r qp p) "Hown".

    iApply imp_please; iNext.

    (* Goal: [(v.x * v.x) + (v.y * v.y)] *)
    imp_arith reading "Hown".
    (* All remaining subgoals are of the form [v.x] *)
    - iApply (imp_point_x with "Hown"); imp_path.
    - iApply (imp_point_x with "Hown"); imp_path.
    - iApply (imp_point_y with "Hown"); imp_path.
    - iApply (imp_point_y with "Hown"); imp_path.
  Qed.

  Lemma imp_point_update_x η :
    ⊢ imp (eval η eupdate_x) {{ λ update_x, □ iSpec τ[record; Z] update_x point_update_x_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r x p) "Hown".
    iApply imp_please; iNext.

    iApply imp_mono_val; last first.
    { iApply (point_update_x with "Hown"). imp_path. imp_path. }
    iIntros ([]) "(% & -> & $)".
  Qed.


  Lemma point_module_proof η :
    2 ≤ max_array_length →
    ⊢ imp (eval_mexpr η __main)
      {{ context
           [ var_spec "length" (λ length, iSpec τ[record] length point_length_spec);
             var_spec "update_x" (λ update, iSpec τ[record;Z] update point_update_x_spec) ]
           {[ "vec"; "length"; "update_x" ]} }}.
  Proof.
    intros Hmax_array.
    iApply imp_module.

    iApply (imp_sitems_let (A:=record)).
    { iApply imp_point.
      iApply imp_evals_cons. imp_arith.
      iApply imp_evals_singleton. imp_arith. }

    iIntros (r) "(% & % & Hown & (-> & ->))".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_point_length. }

    iIntros (length) "#Hlength".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_point_update_x. }

    iIntros (update_x) "#Hupdate_x".
    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Qed.


End encoded_fields.
