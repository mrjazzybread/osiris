From osiris Require Import osiris.
From osiris.utils Require Import big_opLZ.


Require Import og_record_test.

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

  (* -------------------------------------------------------------------------- *)

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

From iris.bi.lib Require Import fractional.

Section encoded_fields.

  Context `{!osirisGS Σ}.

  Hypothesis Hmax : (2 ≤ max_array_length)%Z.

  Class RecordRepr (A : Type) (τ : types) (t : mut_tag) :=
    { repr_to_types : A → τ;
      types_to_repr : τ -#> A;
      repr_id : ∀ xs, (repr_to_types ∘ types_to_repr) xs = xs }.

  Record point : Type := { x : Z; y : Z }.

  Instance point_record : RecordRepr point τ[Z;Z] Mut :=
    { repr_to_types p := (p.(x), p.(y));
      types_to_repr := λ x y, {| x:=x; y:=y |};
      repr_id := λ '(x, y), eq_refl }.

  Definition ownRepr `{RecordRepr A τ t} (r : record) qp (a : A) : iProp Σ :=
    ownRecord (τ:=τ) r qp t (repr_to_types a).

  Instance ownRepr_fractional `{RecordRepr A τ t} r (a : A) : Fractional (λ qp, ownRepr r qp a) := _.

  Global Instance ownRepr_as_fractional `{RecordRepr A t} (r : record) q (a : A) :
    AsFractional (ownRepr r q a) (λ q, ownRepr r q a) q.
  Proof. constructor; done || apply _. Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma imp_record `{RecordRepr A τ t} {η E Ψ ζ} es (Φs : τ -#> iProp Σ) :
    (τ_length τ ≤ max_array_length)%Z →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ (λ r, ∃# (xs : τ), ownRepr r 1 (types_to_repr xs) ∗ Φs xs).
  Proof.
    iIntros (Hlength) "Hes".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecord with "Hes"). assumption. }
    iIntros (r).
    rewrite !bi_texist_equiv.
    iIntros "(%xs & Hr & HΦ)".
    iFrame. unfold ownRepr.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hr".
  Qed.

  Lemma imp_record_access `{RecordRepr A τ t} {η E Ψ ζ} f (r : record) (qp : Qp) (a : A) (e : expr) :
    valid_field f τ →
    ▷ ownRepr r qp a -∗
    impure E (eval η e) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ (λ (x : τ !!! f), ⌜x = repr_to_types a !!τ f⌝ ∗ ownRepr r qp a).
  Proof.
    iIntros (Hvalid) "Hown He".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordAccess with "Hown He"). assumption. }
    iIntros (x) "($ & $)".
  Qed.

  Lemma imp_record_update `{RecordRepr A τ t} {η E Ψ ζ} (r : record) f (a : A) e1 e2 Φ :
    valid_field f τ →
    ▷ ownRepr r 1 a -∗
    impure E (eval η e1) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ
      (λ _ : unit, ∃ (x : τ !!! f), Φ x ∗ ownRepr r 1 (types_to_repr (<[ f τ= x]> (repr_to_types a)))).
  Proof.
    iIntros (Hvf) "Hown He1 He2".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordSet with "Hown He1 He2"). exact Hvf. }
    iIntros (_) "(%x & HΦ & Hrecord)".
    iExists x. iFrame "HΦ".
    unfold ownRepr.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hrecord".
  Qed.

  (* -------------------------------------------------------------------------- *)

  Definition point_length_spec r (m : microvx) : iProp Σ :=
    ∀ qp (p : point),
      ▷ ownRepr r qp p -∗
      imp m {{ λ (i : Z), ⌜i = (p.(x) * p.(x) + p.(y) * p.(y))%Z⌝ ∗ ownRepr r qp p }}.

  Definition point_update_x_spec r x (m : microvx) : iProp Σ :=
    ∀ (p : point),
      ▷ ownRepr r 1 p -∗
      imp m {{ λ (_ : unit), ownRepr r 1 {| x := x; y:=p.(y) |} }}.

  Lemma imp_point_length η :
    ⊢ imp (eval η elength) {{ λ length, □ iSpec τ[record] length point_length_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r qp p) "Hown".

    iApply imp_please; iNext.

    (* Goal: [(v.x * v.x) + (v.y * v.y)] *)
    imp_arith reading "Hown".
    (* Subgoals of the form [v.x]: *)
    - iApply (imp_record_access with "Hown"). split; simpl; lia. imp_path.
    - iApply (imp_record_access with "Hown"). split; simpl; lia. imp_path.
    - iApply (imp_record_access with "Hown"). split; simpl; lia. imp_path.
    - iApply (imp_record_access with "Hown"). split; simpl; lia. imp_path.
  Qed.

  Lemma imp_point_update_x η :
    ⊢ imp (eval η eupdate_x) {{ λ update_x, □ iSpec τ[record; Z] update_x point_update_x_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r x p) "Hown".
    iApply imp_please; iNext.

    iApply (imp_wand with "[Hown]").
    { iApply (imp_record_update with "Hown"). split; simpl; lia. imp_path. imp_path. }
    simpl. unfold types_lookup_total. simpl.
    unfold tapp.
    iIntros ([]) "(% & -> & $)".
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma point_module_proof η :
    ⊢ imp (eval_mexpr η __main)
      {{ context
           [ var_spec "length" (λ length, iSpec τ[record] length point_length_spec);
             var_spec "update_x" (λ update, iSpec τ[record;Z] update point_update_x_spec) ]
           {[ "vec"; "length"; "update_x" ]} }}.
  Proof.
    iApply imp_module.

    iApply (imp_sitems_let (A:=record)).
    { iApply (imp_record (A:=point)). assumption.
      iApply imp_evals_cons. imp_arith.
      iApply imp_evals_singleton. imp_arith. }
    iIntros (r) "(%x & %y & Hown & (-> & ->))".
    unfold types_to_repr. simpl.

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
