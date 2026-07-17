From osiris Require Import osiris lang.
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
      ▷ ownBlock (τ:=τ[Z; Z]) r qp t (x, y) -∗
      imp m {{ λ (i : Z), ⌜i = (x*x + y*y)%Z⌝ ∗ ownBlock (τ:=τ[Z;Z]) r qp t (x, y) }}.

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
      ▷ ownBlock (τ:=τ[Z;Z]) r 1 t (x0, y) -∗
      imp m {{ λ (_ : unit), ownBlock (τ:=τ[Z;Z]) r 1 t (x, y) }}.

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

  (* Matching a record pattern against a record value:
     [match v with { x = a; y = b } -> a + b].
     The match reads the record's fields, so the pattern premise is the
     Iris judgement [icpattern] (see [ipattern_rules]); the sub-patterns
     are delegated to the pure [fpatterns] judgement. *)

  Lemma match_record_fields η r qp t (x y : Z) :
    ownBlock (τ:=τ[Z;Z]) r qp t (x, y) -∗
    imp eval (("v", VRecord r) :: η)
        (EMatch (EVar "v")
           [Branch (CVal (PRecord [(0%Z, PVar "a"); (1%Z, PVar "b")]))
                   (EIntAdd (EVar "a") (EVar "b"))])
        {{ λ i : Z, ⌜i = (x + y)%Z⌝ ∗ ownBlock (τ:=τ[Z;Z]) r qp t (x, y) }}.
  Proof.
    iIntros "Hown".
    iApply (imp_EMatch (A':=record) (λ r', ⌜r' = r⌝)%I with "[]").
    { iApply imp_wand. imp_path. iIntros (?) "-> //". }
    iIntros (r') "-> !>".
    next_branch.
    iApply (imp_wand with "[]").
    { imp_arith. }
    iIntros (i) "->". by iFrame.
  Qed.

  (* The same, on an inline record, through an alias pattern — the shape
     generated for [match v with Root ({ x = a; y = b } as w) -> ...]. *)

  Lemma match_inline_record_fields η r qp t (x y : Z) :
    ownBlock (τ:=τ[Z;Z]) r qp t (x, y) -∗
    imp eval (("v", VInline "Root" r) :: η)
        (EMatch (EVar "v")
           [Branch (CVal (PInline "Root"
                            (PAlias (PRecord [(0%Z, PVar "a"); (1%Z, PVar "b")]) "w")))
                   (EIntAdd (EVar "a") (EVar "b"))])
        {{ λ i : Z, ⌜i = (x + y)%Z⌝ ∗ ownBlock (τ:=τ[Z;Z]) r qp t (x, y) }}.
  Proof.
    iIntros "Hown".
    iApply (imp_EMatch (A':=val) (λ v, ⌜v = VInline "Root" r⌝)%I with "[]").
    { iApply imp_wand. imp_path. iIntros (?) "-> //". }
    iIntros (v) "-> !>".
    next_branch.
    iApply (imp_wand with "[]").
    { imp_arith. }
    iIntros (i) "->". by iFrame.
  Qed.

  (* A mixed pattern: a heap-free sub-pattern (a literal) next to a
     record pattern in the same tuple. [next_branch] lowers the
     literal to the pure engine mid-walk and processes the record with
     the Iris rules; the literal's no-match side surfaces as the pure
     refutation witness [1 = 1]. *)

  Lemma match_mixed_fields η r qp t (x y : Z) :
    ownBlock (τ:=τ[Z;Z]) r qp t (x, y) -∗
    imp eval (("v", VTuple ((#1%Z) :: VRecord r :: nil)) :: η)
        (EMatch (EVar "v")
           [Branch (CVal (PTuple [PInt 1; PRecord [(0%Z, PVar "a"); (1%Z, PVar "b")]]))
                   (EIntAdd (EVar "a") (EVar "b"))])
        {{ λ i : Z, ⌜i = (x + y)%Z⌝ ∗ ownBlock (τ:=τ[Z;Z]) r qp t (x, y) }}.
  Proof.
    iIntros "Hown".
    iApply (imp_EMatch (A':=val) (λ v, ⌜v = VTuple ((#1%Z) :: VRecord r :: nil)⌝)%I
             with "[]").
    { iApply imp_wand. imp_path. iIntros (?) "-> //". }
    iIntros (v) "-> !>".
    next_branch.
    { iApply (imp_wand with "[]").
      { imp_arith. }
      iIntros (i) "->". by iFrame. }
    reflexivity.
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

  Record point : Type := { x : Z; y : Z }.

  Instance point_record : RecordRepr point τ[Z;Z] Mut :=
    { repr_to_types p := (p.(x), p.(y));
      types_to_repr := λ x y, {| x:=x; y:=y |};
      repr_id := λ '(x, y), eq_refl }.

  (* -------------------------------------------------------------------------- *)

  Definition point_length_spec r (m : microvx) : iProp Σ :=
    ∀ qp (p : point),
      ▷ r ⤇{qp} p -∗
      imp m {{ λ (i : Z), ⌜i = (p.(x) * p.(x) + p.(y) * p.(y))%Z⌝ ∗ r ⤇{qp} p }}.

  Definition point_update_x_spec r x (m : microvx) : iProp Σ :=
    ∀ (p : point),
      ▷ r ⤇ p -∗
      imp m {{ λ (_ : unit), r ⤇ {| x := x; y:=p.(y) |} }}.

  Lemma imp_point_length η :
    ⊢ imp (eval η elength) {{ λ length, □ iSpec τ[record] length point_length_spec }}.
  Proof.
    iApply imp_EAnon_pers.
    iIntros "!>" (r qp p) "Hown".

    iApply imp_please; iNext.

    (* Goal: [(v.x * v.x) + (v.y * v.y)] *)
    imp_arith reading "Hown".
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
    { imp_record. }
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
