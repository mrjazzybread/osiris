From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.

Definition not_pure (s : string) : Prop := False.

From osiris.program_logic.pure Require Import
  judgements pure_rules pattern_rules call_rules.

(* This file defines contains reasoning rules about evaluation of expressions
  for pure judgements. *)

(* -------------------------------------------------------------------------- *)

(* EPath (x : path) *)

Lemma pure_eval_path `{Encode A} η π (ψ : A -> Prop) (ζ : exn -> Prop) :
  pure (lookup_path η π) ψ ⊥ ->
  pure (eval η (EPath π)) ψ ζ.
Proof.
  simpl_eval. apply pure_widen.
Qed.

(* -------------------------------------------------------------------------- *)

(**  *Anonymous functions. *)

(* EAnonFun (a : anonfun) *)

Lemma pure_eval_anonfun η a (φ : val -> Prop) ζ :
  φ (VClo η a) ->
  pure (eval η (EAnonFun a)) φ ζ.
Proof.
  intros Hclo.
  eapply pure_simp. simp.
  eapply pure_ret; eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Function application: [e1 e2]. *)

(* EApp (e1 e2 : expr) *)

Lemma pure_eval_app `{Encode A, Encode B, Encode C}
  η e1 e2
  (φ1 : A → Prop) (φ2 : B → Prop) (ψ : C → Prop)
  ζ :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ v1 v2, φ1 v1 → φ2 v2 → pure (call #v1 #v2) ψ ζ) →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros He1 He2 Hp. simpl_eval.
  eapply pure_Par;
    (do 2 (eapply pure_mono;
           [ done | | eapply pure_throw];
           intros ??);
     cbn; eauto ).
Qed.

(* Simple version : the expressions must evaluate to a singleton
   value. This lemma is useful for practical instances where
   the value postcondition is an evar for the [e1, e2] expressions. *)

Lemma pure_eval_app_simple `{Encode A, Encode B}
  η e1 e2
  (f : A) (arg : B) (ψ : A → Prop)
  ζ :
  pure (eval η e1) (singleton f) ζ →
  pure (eval η e2) (singleton arg) ζ →
  pure (call #f #arg) ψ ζ →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros; eapply pure_eval_app; eauto; by intros ??->->.
Qed.

Lemma pure_eval_app_seq `{Encode A, Encode B}
  η e1 e2
  (ψ : A → Prop)
  ζ :
  pure (eval η e1) (λ f : A,
    pure (eval η e2) (λ arg : B,
      pure (call #f #arg) ψ ζ) ζ) ⊥ →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros He1. simpl_eval. eapply pure_par_seq.
  eapply pure_ret_mono; first eapply He1; cbn; intros; try done.
  eapply pure_mono; first eapply H1; cbn; intros; try done.
  eapply pure_throw; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Evaluating tuples, or several expressions in parallel *)

(* TODO avoid [Forall2] just by showing nil and cons lemmas; offer tactic
  analogous to [pats]. *)

Lemma pure_evals_cons `{Encode A}
  η (hd : expr) tl (φ : list val -> Prop) ψ:
  pure (A := A) (eval η hd)
    (fun x =>
      pure (evals η tl) (fun v => φ (# x :: v)) ψ) ⊥  ->
  pure (evals η (hd :: tl)) φ ψ.
Proof.
  intros. simpl_evals.
  eapply pure_par_seq.
  eapply pure_ret_mono; try done.
  intros * ?.
  eapply pure_mono; first eapply H1; eauto.
  intros * ?. eapply pure_simp; first simp; eauto.
  cbn in H2; eapply pure_ret; eauto.
  cbn; f_equiv.
  intros; cbn. by apply pure_throw.
Qed.

Local Lemma pure_evals `{Encode A} η es φs ψ :
  Forall2 (λ e φ, pure (eval η e) φ ψ) es φs →
  pure (A := list A) (evals η es) (Forall2 id φs) ψ.
Proof.
  revert φs.
  induction es as [ | e es IHes]; intros φs' Hes.
  - simpl_evals. constructor; inv Hes; auto.
    eexists nil; encode.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (φ & φs & He & Hes & ->).
    simpl_evals.
    eapply pure_wp_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros v vs Hv Hvs. repeat constructor; eauto.
      red. returns_eauto.
      eexists _; split; encode.
    + intros exn []; repeat constructor; eauto.
Qed.

(* The following [_eq] versions should be simpler to use in cases we know the
  final values *)

Lemma pure_evals_eq η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (singleton v) ψ) es vs →
  pure_wp (evals η es) (singleton vs) ψ.
Proof.
  revert vs.
  induction es as [ | e es IHes]; intros vs' Hes; simpl_evals.
  - constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (v & vs & He & Hes & ->).
    eapply pure_wp_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros _ _ (?&->&->) ->. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.

Lemma prove_evals η es vs :
  Forall2 (fun e v => simp (eval η e) (ret v)) es vs ->
  simp (evals η es) (ret vs).
Proof.
  generalize vs. induction es; intros.
  - apply Forall2_nil_inv_l in H; rewrite H.
    by simpl_evals.
  - apply Forall2_cons_inv_l in H.
    destruct H as (v & vs' & Heval & H & ->).
    simpl_evals.
    eapply simp_par. apply Heval.
    apply IHes. apply H.
    unfold continue; apply SimpReflexive.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Tuple construction: [(e1, e2, ...)]. *)

(* ETuple (es : list expr) *)

Lemma pure_eval_tuple `{Encode A} η es a vs (ψ : A -> Prop)  :
  Forall2 (fun e v => simp (eval η e) (ret v)) es vs ->
  VTuple vs = #a ->
  ψ a ->
  pure (eval η (ETuple es)) ψ ⊥.
Proof.
  intros Hevals Henc Hψ.
  simpl_eval.
  eapply pure_simp.
  eapply prove_simp_bind.
  - apply prove_evals. apply Hevals.
  - apply SimpReflexive.
  - eapply pure_ret; eauto with encode.
Qed.

(* A special case at arity [2,3,4]. *)

(* LATER: Abstraction is broken; don't use [pure_wp] here. *)
Local Ltac solve_eval_tuple :=
   intros; simpl_eval;
  repeat (
    eapply pure_wpv_Par_left_conseq;
    eauto; intros ? (? & -> & ?));
  repeat apply pure_wp_ret; eauto with pure.

Lemma pure_eval_pair `{Encode A1, Encode A2}
  η e1 e2 (ψ : A1 * A2 → Prop) :
  pure (eval η e1)
    (λ a1 : A1, pure (eval η e2) (λ a2 : A2, ψ (a1, a2)) ⊥) ⊥ →
  pure (eval η (EPair e1 e2)) ψ ⊥.
Proof. solve_eval_tuple. Qed.

Lemma pure_eval_triple `{Encode A1, Encode A2, Encode A3}
  η e1 e2 e3 (ψ : A1 * A2 * A3 -> Prop) :
  pure (eval η e1) (λ a1 : A1,
      pure (eval η e2) (λ a2 : A2,
          pure (eval η e3) (λ a3 : A3,
              ψ (a1, a2, a3)) ⊥) ⊥) ⊥ ->
  pure (eval η (ETuple [e1; e2; e3])) ψ ⊥.
Proof. solve_eval_tuple. Qed.

Lemma pure_eval_quadruple `{Encode A1, Encode A2, Encode A3, Encode A4}
  (η : env) (e1 e2 e3 e4 : expr)
  (ψ : A1 * A2 * A3 * A4 → Prop) :
  pure (eval η e1) (λ a1 : A1,
      pure (eval η e2) (λ a2 : A2,
          pure (eval η e3) (λ a3 : A3,
              pure (eval η e4) (λ a4 : A4,
                  ψ (a1, a2, a3, a4)) ⊥) ⊥) ⊥) ⊥ ->
  pure (eval η (ETuple [e1; e2; e3; e4])) ψ ⊥.
Proof. solve_eval_tuple. Qed.

(* -------------------------------------------------------------------------- *)

(** *Data constructor application: [A (e)]. *)

(* EData (c : data) (e : list expr) *)

Lemma pure_eval_const `{Encode A}
  η c x (ψ : A -> Prop) ζ :
  VConstant c = #x ->
  ψ x ->
  pure (eval η (EConstant c)) ψ ζ.
Proof.
  intros.
  eapply pure_simp. simp.
  eauto using pure_ret with pure.
Qed.

Lemma pure_eval_data `{Encode Y} η c e y (ψ : Y -> Prop) ζ :
  pure (evals η e) (λ v', VData c v' = #y) ζ ->
  ψ y ->
  pure (eval η (EData c e)) ψ ζ.
Proof.
  intros He Hy.
  simpl_eval.
  eapply pure_bind.
  eapply pure_mono; eauto.
  intros ? ?. eapply pure_ret; eauto.
  (* LATER: Automate *)
  cbn in *; rewrite <-H0; repeat f_equiv.
  clear. induction a; cbn; try f_equiv; eauto.
Qed.

(* TODO RENAME *)
Lemma pure_eval_data' `{Encode Y} `{Encode A} η c e y (ψ : A -> Prop) ζ :
  pure (evals η e) (λ (v' : list Y), VData c (map encode.encode v') = #y) ζ ->
  ψ y ->
  pure (eval η (EData c e)) ψ ζ.
Proof.
  intros He Hy.
  simpl_eval.
  eapply pure_bind. eapply pure_mono; eauto.
  intros ? ?. eapply pure_ret. cbn in *.
  destruct a; cbn in *; returns_eauto; eauto with pure.
  done.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO *)
(** Record construction: [{ fs = es }]. *)
(* ERecord (fes : list fexpr) *)
(** Record update: [{ e with fs = es }]. *)
(* ERecordUpdate (e : expr) (fes : list fexpr) *)
(** Record access: [e.f]. *)
(* ERecordAccess (e : expr) (f : field) *)

(* -------------------------------------------------------------------------- *)

(** *Boolean conjunction, disjunction, and negation. *)
(* EBoolConj (e1 e2 : expr) TODO *)
(* EBoolDisj (e1 e2 : expr) TODO *)

(* Some special cases. *)

(* For [pure (as_bool _) φ ψ]. *)
Local Instance observe_bool : Observe bool bool :=
  {| observe := id |}.

Local Lemma pure_as_bool (m : microvx) (φ : bool → Prop) ψ :
  pure m φ ψ →
  pure (as_bool m) φ ψ.
Proof.
  intro H.
  eapply pure_bind; eauto.
  intros [] ?;
    with_strategy transparent [val_as_bool] cbn;
    eauto with pure.
Qed.

Local Lemma pure_bind_as_bool {A} {EncA: Encode A}
  (m : microvx) (φ : bool → Prop) (ψ : A → Prop)
  (k : bool → micro val exn) :
  pure m φ ⊥ →
  (∀ b : bool, φ b → pure (k b) ψ ⊥) →
  pure (bind (as_bool m) k) ψ ⊥.
Proof.
  intros Hm Hp. eapply pure_bind.
  eapply pure_as_bool; done.
  intros []; force_unfold val_as_bool; eauto with pure.
Qed.

(* EBoolNeg (e : expr) *)

Lemma pure_eval_negb η e (φ ψ : bool → Prop) :
  pure (eval η e) φ ⊥ →
  (∀ b, φ b → ψ (negb b)) →
  pure (eval η (EBoolNeg e)) ψ ⊥.
Proof.
  intros He Hp. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros b Hb; eapply pure_ret; eauto with pure.
Qed.

Lemma pure_eval_not η e (φ ψ : bool → Prop) :
  pure (eval η e) φ ⊥ →
  (∀ P, φ P → ψ (negb P)) →
  pure (eval η (EBoolNeg e)) ψ ⊥.
Proof.
  intros He Hp. simpl_eval.
  eapply pure_bind. by eapply pure_as_bool.
  intros. eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Integer literals. *)
(* EInt (i : Z) *)
(* EMaxInt TODO *)
(* EMinInt TODO *)

Lemma pure_eval_int η i (φ : _ -> Prop) ψ :
  φ i ->
  pure (eval η (EInt i)) φ ψ.
Proof.
  intros.
  eapply pure_simp. simp.
  eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Integer arithmetic. *)

(* Helper lemmas for arithmetic operations. *)

(* For [pure (as_int _) φ ψ]. *)
Global Instance observe_int : Observe int int :=
  {| observe := id |}.

Local Lemma pure_as_int m (φ : Z → Prop) ψ:
  pure m φ ψ →
  pure (as_int m)
    (λ i, ∃ z, i = repr z ∧ φ z) ψ.
Proof.
  intros Hm; eapply pure_bind; eauto.
  intros; eapply pure_ret; eauto.
Qed.

Lemma pure_par_as_int m1 m2 (φ1 φ2 φ : Z → Prop) k :
  pure m1 φ1 ⊥ →
  pure m2 φ2 ⊥ →
  (∀ z1 z2 : Z, φ1 z1 → φ2 z2 → pure (k (repr z1, repr z2)) φ ⊥) →
  pure (Par (as_int m1) (as_int m2) (pfbind inject2 k)) φ ⊥.
Proof.
  intros Hm1 Hm2 Hk.
  eapply pure_par_seq.
  do 2 (eapply pure_mono; first eapply pure_as_int; eauto;
        intros ? ?); try done.
  destruct H as (?&->&?); destruct H0 as (?&->&?).
  eapply pure_simp; [ simp | ]. eauto.
Qed.

(* If [z] is representable and [z ≠ 0] then the runtime check *)
(*   performed by [check_div_by_zero (repr z)] must succeed. *)

Lemma pure_wp_check_div_by_zero z :
  representable z →
  (z ≠ 0)%Z →
  pure_wp (check_div_by_zero (repr z)) (λ v, v = ()) ⊥.
Proof.
  intros.
  unfold check_div_by_zero.
  change int.zero with (repr 0).
  rewrite eq_repr_repr by representable.
  case_eq (z =? 0)%Z; [ rewrite Z.eqb_eq | rewrite Z.eqb_neq ]; intro.
  { tauto. }
  { by apply pure_wp_ret. }
Qed.

(* Primitive arithmetic operations. *)

(* TODO EIntNeg (e : expr) *)

(* EIntAdd (e1 e2 : expr) *)
Lemma pure_eval_add η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 + z2)) →
  pure (eval η (EIntAdd e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval.
  eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntSub (e1 e2 : expr) *)
Lemma pure_eval_sub η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 - z2)) →
  pure (eval η (EIntSub e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntMul (e1 e2 : expr) *)
Lemma pure_eval_mul η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥→
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 * z2)) →
  pure (eval η (EIntMul e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntDiv (e1 e2 : expr) *)
Lemma pure_eval_div η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → representable z2) →
  (∀ z2, φ2 z2 → z2 ≠ 0) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 ÷ z2)) →
  pure (eval η (EIntDiv e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_wp_bind.
  - eapply pure_wp_mono_ret.
    eapply pure_wp_check_div_by_zero; eauto.
    cbn; intros;subst.
    eapply pure_wp_ret.
    eexists _; split; eauto. encode.
Qed.

(* TODO EIntMod (e1 e2 : expr) *)

(* -------------------------------------------------------------------------- *)

(** Integer logical operations. *)

(* Helper lemma for primitive arithmetic operations. *)

Local Lemma pure_if_in_shift_range {E}
  z (m : micro val E) φ ψ :
  in_shift_range z →
  pure m φ ψ →
  pure (A := Z) (V := val) (E := E)
    (if_in_shift_range (repr z) m) φ ψ.
Proof.
  intros.
  unfold if_in_shift_range, in_shift_range_b.
  rewrite signed_repr by eauto using in_shift_range_representable.
  by rewrite in_shift_range_b_spec.
Qed.

(* Primitive logical operations on machine integers. *)

(* EIntLand (e1 e2 : expr) *)

Lemma pure_eval_land η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.land z1 z2)) →
  pure (eval η (EIntLand e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLor  (e1 e2 : expr) *)

Lemma pure_eval_lor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lor z1 z2)) →
  pure (eval η (EIntLor e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLxor (e1 e2 : expr) *)

Lemma pure_eval_lxor η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lxor z1 z2)) →
  pure (eval η (EIntLxor e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLnot (e : expr) *)

Lemma pure_eval_lnot η e1 (φ1 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  (∀ z1, φ1 z1 → φ (Z.lnot z1)) →
  pure (eval η (EIntLnot e1)) φ ⊥.
Proof.
  intros He1%pure_as_int Hp. simpl_eval.
  eapply pure_bind; eauto. intros ? (z & -> & Hz).
  eapply pure_ret; eauto with pure.
  cbn. by rewrite lnot_repr.
Qed.

(* EIntLsl  (e1 e2 : expr) *)

Lemma pure_eval_lsl η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftl z1 z2)) →
  pure (eval η (EIntLsl e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLsr  (e1 e2 : expr) *)

Lemma pure_eval_lsr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1, φ1 z1 → urepresentable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntLsr e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntAsr  (e1 e2 : expr) *)

Lemma pure_eval_asr η e1 e2 (φ1 φ2 φ : Z → Prop) :
  pure (eval η e1) φ1 ⊥ →
  pure (eval η e2) φ2 ⊥ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntAsr e1 e2)) φ ⊥.
Proof.
  intros. simpl_eval. eapply pure_par_as_int; eauto. intros.
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* -------------------------------------------------------------------------- *)

(** Floating-point literals. *)
(* TODO EFloat (f : float) *)

(** Character literals. *)
(* TODO EChar (c: char) *)

(** String literals. *)
(* TODO EString (s: string) *)

(* -------------------------------------------------------------------------- *)

(** Polymorphic comparison operators. *)

(* TODO EOpPhysEq (e1 e2 : expr) *)

(* Helper lemma for Boolean operations *)

Lemma pure_eval_comparison_operator `{Encode A}
  η e1 e2 (x1 x2 : Z) (f : val → val → micro bool exn) b a (φ : A → Prop) :
  pure (eval η e1) (singleton x1) ⊥ →
  pure (eval η e2) (singleton x2) ⊥ →
  f #x1 #x2 = ret b →
  #a = #b →
  φ a →
  pure (Par (eval η e1) (eval η e2)
          (pfbind inject2 (λ '(v1, v2), 'b ← f v1 v2; ret (VBool b)))) φ ⊥.
Proof.
  intros He1 He2 Ef Ea Ha.
  eapply pure_par_seq.
  do 2 (eapply pure_mono; eauto; try intros * ->;
   try contradiction).
  eapply pure_simp; [ simp | ].
  eapply pure_bind. setoid_rewrite Ef.
  eapply (pure_ret (fun b => #a = #b /\ φ a)); eauto.
  intros ? (?&?). eapply pure_ret; eauto.
Qed.

(* Boolean operations *)

(* EOpEq (e1 e2 : expr) *)

Lemma pure_eval_EOpEq η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpEq e1 e2)) (λ P, P <-> (x1 = x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpEq_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpEq e1 e2)) (λ (b : bool), b <-> (x1 = x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto. apply Zeq_spec.
Qed.

(* EOpNe (e1 e2 : expr) *)

Lemma pure_eval_EOpNe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpNe e1 e2)) (λ P, P <-> (x1 <> x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpNe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpNe e1 e2)) (λ (b : bool), b <-> (x1 <> x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto. apply Zne_spec.
Qed.

(* TODO EOpLt (e1 e2 : expr) *)

Lemma pure_eval_EOpLt η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLt e1 e2)) (λ P, P <-> (x1 < x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpLt_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLt e1 e2)) (λ (b : bool), b <-> (x1 < x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto. apply Zlt_spec.
Qed.

(* EOpLe (e1 e2 : expr) *)

Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ P, P <-> (x1 <= x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpLe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ (b : bool), b <-> (x1 <= x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto. apply Zle_spec.
Qed.

(* EOpGt (e1 e2 : expr) *)

Lemma pure_eval_EOpGt η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGt e1 e2)) (λ P, P <-> (x1 > x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpGt_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGt e1 e2)) (λ (b : bool), b <-> (x1 > x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto. rewrite Zlt_spec; lia.
Qed.

Lemma pure_eval_EOpGe η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGe e1 e2)) (λ P, P <-> (x1 >= x2)%Z) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  simpl. f_equal. f_equal. apply truth_eq_true. lia.
Qed.

Lemma pure_eval_EOpGe_bool η e1 e2 (x1 x2 : Z) :
  pure (eval η e1) (singleton x1) ⊥ ->
  pure (eval η e2) (singleton x2) ⊥ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGe e1 e2)) (λ (b : bool), b <-> (x1 >= x2)) ⊥.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto. rewrite Zle_spec; lia.
Qed.

(* -------------------------------------------------------------------------- *)

(** Non-recursive local definition: [let bs in e]. *)

(* ELet (bs : list binding) (e : expr) *)

Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop) :
  pure (eval η e1) φ1 ⊥ →
  (∀ a1, φ1 a1 → pure (eval ((x, #a1) :: η) e) ψ ⊥) →
  pure (eval η (ELet1Var x e1 e)) ψ ⊥.
Proof.
  intros He1 He.
  simpl_eval. eapply pure_simp; first simp.
  eapply pure_bind; eauto.
  intros. eapply pure_simp; first simp.
  by eapply He.
Qed.

Lemma pure_eval_let_simple `{Encode A1, Encode B} η x e1 e
  (a1 : A1) (ψ : B → Prop) :
  pure (eval η e1) (singleton a1) ⊥ →
  pure (eval ((x, #a1) :: η) e) ψ ⊥ →
  pure (eval η (ELet1Var x e1 e)) ψ ⊥.
Proof.
  intros He1 He2.
  eapply pure_eval_let; eauto.
  congruence.
Qed.

Lemma pure_eval_let_pair `{Encode A1, Encode A2} `{Encode X}
  p1 p2 e1 e2 η (ψ : X -> Prop) :
  pure (eval η e1) (λ '((v1, v2) : A1 * A2),
      pure (
          δ ← widen (irrefutably_extend [] p1 #v1);
          θ ← widen (irrefutably_extend δ p2 #v2);
          eval (θ ++ η) e2
        ) ψ ⊥) ⊥ ->
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ ⊥.
Proof. (* LATER: Clean up this proof. *)
  (* This proof is a long rewriting sequence, which makes some sense as it is *)
(*   not the standard method to prove a let binding, but rather a way to reduce the *)
(*   wp of a parallel pair to ordered wps of two binds with error handling *)
  intros He1.
  simpl_eval. apply pure_wp_Par_val_right.
  apply pure_wp_ret.
  apply (pure_wp_mono _ He1). clear He1.
  intros ? ([v1 v2] & -> & Hpure_wp).
  apply pure_wp_bind.
  apply pure_wp_bind.
  apply pure_wp_ret.
  unfold widen, irrefutably_extend in *.
  rewrite !try_try in *. simpl_extend.
  rewrite !bind_as_try, !try_try in *.
  apply pure_wp_try2.
  apply invert_pure_wp_try2 in Hpure_wp.
  apply (pure_wp_mono _ Hpure_wp); clear Hpure_wp.
  - intros δ Hpure_wp.
    unfold continue in *.
    unfold glue2 in *.
    repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *.
    apply invert_pure_wp_try2 in Hpure_wp.
    apply pure_wp_try2.
    apply (pure_wp_mono _ Hpure_wp); clear Hpure_wp.
    + intros θ Hpure_wp.
      unfold continue, glue2 in *.
      repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *.
      apply pure_wp_ret. eauto.
    + unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_wp_crash; eauto.
  - unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_wp_crash; eauto.
  - intros ? Hζ. unfold discontinue; simpl. by apply pure_wp_throw.
Qed.

(* -------------------------------------------------------------------------- *)

(** Recursive local definition: [let rbs in e]. *)
(* ELetRec (rbs : list rec_binding) (e : expr) *)

Lemma pure_letrec `{Encode X, Encode Y} {A} (WF_x : WellFounded X)
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : A -> X -> Y -> Prop) Ψ
  (P : A -> X -> Prop) (R : X -> X -> Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X) a,
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> P a y -> pure (call vf #y) (φf a y) Ψ) ->
      (P a x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf a x) Ψ)) ->
  (* Subogal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ a x, P a x -> pure (call vf #x) (φf a x) Ψ) ->
      pure (eval ((f, vf) :: η) e2) φ Ψ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ Ψ.
Proof.
  intros He1 He2.
  simpl_eval. apply He2; clear He2.
  intros a y HPy.
  eapply pure_rec_call; eauto.
Qed.

Lemma pure_letrec_simple `{Encode X, Encode Y} (WF_x : WellFounded X)
  (η : env) (f arg : var) e1 e2 (φ : val -> Prop) (φf : X -> Y -> Prop) Ψ
  (P : X -> Prop) (R : X -> X -> Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> P y -> pure (call vf #y) (φf y) Ψ) ->
      (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf x) Ψ)) ->
  (* Subogal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ x, P x -> pure (call vf #x) (φf x) Ψ) ->
      pure (eval ((f, vf) :: η) e2) φ Ψ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ Ψ.
Proof.
  intros He1 He2.
  simpl_eval. apply He2; clear He2.
  intros y HPy.
  eapply pure_rec_call; eauto.
Qed.

Lemma pure_rec_call_no_pre `{Encode X} `{Encode Y} `{WF_x: WellFounded X}
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : X -> Y -> Prop)
  (R : X -> X -> Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> pure (call vf #y) (φf y) ⊥) ->
      pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf x) ⊥) ->
  (* Subogal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ (x : X), pure (call vf #x) (φf x) ⊥) ->
      pure (eval ((f, vf) :: η) e2) φ ⊥) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ ⊥.
Proof.
  intros He1 He2.
  simpl_eval. apply He2. clear He2.
  intros y.
  eapply pure_rec_call with (P := fun _ => True); eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Local module definition: [let module M = me in e]. *)
(* TODO ELetModule (M : module) (me : mexpr) (e : expr) *)

(* Local [open] directive: [let open me in e]. *)
(* TODO ELetOpen (me : mexpr) (e : expr) *)

(* -------------------------------------------------------------------------- *)
(* Sequence: [e1; e2]. *)
(* ESeq (e1 e2 : expr) *)

(* Sequencing of pure computations. *)
Lemma pure_seq `{Encode A, Encode B} (φ : B -> Prop) ψ η e1 e2 :
  pure (eval η e1) (λ _ : A, pure (eval η e2) φ ψ) ψ →
  pure (eval η (ESeq e1 e2)) φ ψ.
Proof.
  simpl_eval.
  intros. eapply pure_bind.
  eapply pure_mono; try done.
  cbn; intros; eapply pure_mono; done.
Qed.

Lemma pure_eval_seq `{Encode A, Encode B}
  η e1 e2 (ψ : B -> Prop) :
  pure (eval η e1) (λ _ : A, True) ⊥ ->
  pure (eval η e2) ψ ⊥ ->
  pure (eval η (ESeq e1 e2)) ψ ⊥.
Proof.
  intros He1 He2.
  eapply (@pure_seq A _ B); by eapply pure_mono.
Qed.

Lemma pure_eval_seq_exn `{Encode A}
  η e1 e2 (Ψ : A -> Prop) ζ :
  pure (eval η e1) (λ _ : val, pure (eval η e2) Ψ ζ) ζ ->
  pure (eval η (ESeq e1 e2)) Ψ ζ.
Proof.
  intros; eapply pure_seq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Conditional: [if e then e1] and [if e then e1 else e2]. *)

(* TODO EIfThen (e e1 : expr) *)

Lemma pure_ifthenelse `{EncA: Encode A}
  η e e1 e2 φ (ψ : exn -> Prop) :
  pure (A := bool) (eval η e)
    (λ v : bool, pure (eval η (if v then e1 else e2)) φ ψ) ψ →
  pure (A := A) (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  intros He. simpl_eval.
  eapply pure_bind. eapply pure_as_bool; eauto.
  cbn; intros * H. destruct a; eauto.
Qed.

(* EIfThenElse (e e1 e2 : expr) *)

(* TODO fix inconsistent naming *)
Lemma pure_ifthenelse_bool `{EncA: Encode A}
  η e e1 e2 (φ : A -> _) φb ψ :
  pure (eval η e) φb ψ →
  (φb true  → pure (eval η e1) φ ψ) →
  (φb false → pure (eval η e2) φ ψ) →
  pure (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  simpl; intros Hb Ht Hf; simpl_eval.
  eapply pure_bind. apply pure_as_bool; eauto.
  intros [] ?; eauto with pure.
Qed.

Lemma pure_eval_ifthenelse `{EncA: Encode A}
  η e e1 e2 (P : Prop) (ψ : A → Prop) :
  pure (eval η e) (λ P', P' <-> P) ⊥ →
  (P → pure (eval η e1) ψ ⊥) →
  (~ P → pure (eval η e2) ψ ⊥) →
  pure (eval η (EIfThenElse e e1 e2)) ψ ⊥.
Proof.
  intros He He1 He2.
  eapply pure_ifthenelse.
  eapply pure_wp_mono; eauto.
  intros; returns_eauto.
  exists (truth P); cbn; split; auto.
  do 2 f_equiv; apply iff_truth; done.
  generalize (truth_elim P).
  destruct (truth P); eauto; intros; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Pattern matching: [match e with bs]. *)

(* [pure_match η v bs φ] is sugar for [pure (eval_match η v bs) ##φ ⊥].

  [eval_match] is used by [eval] when evaluating an [EMatch]. *)

(* LATER: Revisit the [pure_wp] use cases. (necessary due to [pattern].) *)

Definition pure_match `{Encode A}
  (η : env) (o : outcome3 val exn) bs (φ : A -> Prop) Ψ :=
  pure (deep_match_go η o bs) φ Ψ.

Arguments pure_match {A} {H} _ _ _ _.

(* Properties about [pure_match] *)

Lemma pure_eval_try_with_cons `{Encode A} η ex p e bs (φ : A -> Prop) ζ :
  pattern η p ex (λ η', pure (eval η' e) φ ζ) (pure (match_exn η ex bs) φ ζ) ->
  pure (match_exn η ex (Branch (CExc p) e :: bs)) φ ζ.
Proof.
  intros Hpat. simpl_match_exn.
  eapply pure_wp_try, pure_wp_mono; eauto.
Qed.

(* Currently unused *)

Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) Ψ :
  cpattern η p v (λ η', pure (eval η' e) φ Ψ) (pure_match η v bs φ Ψ) ->
  pure_match η v ((Branch p e) :: bs) φ Ψ.
Proof.
  unfold pure_match.
  intros; simpl_deep_match_go.
  apply pure_wp_try. eassumption.
Qed.

Lemma pure_match_cons `{Encode A} η v p e bs (φ : A -> Prop) ψ ζ :
  cpattern η p v (λ η', pure (eval η' e) φ ζ) ψ ->
  (ψ -> (pure_match η v bs φ ζ)) ->
  pure_match η v ((Branch p e) :: bs) φ ζ.
Proof.
  intros.
  apply pure_match_cons_unary.
  eapply pure_wp_mono; eauto.
Qed.

(* Not matching is an error. *)

Lemma pure_match_nil `{Encode A} η o (φ : A -> Prop) Ψ :
  False -> pure_match η o nil φ Ψ.
Proof. contradiction. Qed.

Lemma pure_match_single `{Encode A} η v p e (φ : A -> Prop) ψ ζ :
  cpattern η p v (λ η' : env, pure (eval η' e) φ ζ) ψ →
  (ψ -> False) ->
  pure_match η v [Branch p e] φ ζ.
Proof.
  intros.
  eapply pure_match_cons; eauto.
  tauto.
Qed.

(* EMatch (e : expr) (bs : list branch) *)

Lemma pure_eval_match `{Encode B} η e bs (a : val) (φ : B -> Prop) Ψ :
  pure (eval η e) (singleton a) ⊥ ->
  pure_match η (O3Ret a) bs φ Ψ ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros Heval Hmatch. simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ Heval); [ | intros _ [] ].
  intros ? (? & -> & ->).
  simpl_deep_match.
  apply (pure_wp_mono _ Hmatch); eauto.
Qed.

(* TODO Rename *)
Lemma pure_eval_match' `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) Ψ :
  pure (eval η e) φ' ⊥ ->
  (∀ (a : A), φ' a -> pure_match η (O3Ret #a) bs φ Ψ) ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros Heval Hmatch. simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ Heval). 2: intros _ [].
  intros ? (a & -> & Ha).
  simpl_deep_match.
  apply (pure_wp_mono _ (Hmatch _ Ha)); eauto.
Qed.

(* TODO Rename *)
Lemma pure_eval_match'_exn `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) ζ Ψ :
  pure (eval η e) φ' ζ ->
  (∀ (a : A), φ' a -> pure_match η (O3Ret #a) bs φ Ψ) ->
  (∀ (ex : exn), ζ ex -> pure_match η (O3Throw ex) bs φ Ψ) ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros He Hφ' Hζ.
  simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ He).
  - intros _v (a & -> & Ha).
    simpl_deep_match.
    by apply Hφ'.
  - intros ex Hex.
    simpl_deep_match.
    by apply Hζ.
Qed.

(* -------------------------------------------------------------------------- *)

(** Catching an exception: [try e with bs]. *)

(* ETryWith (e : expr) (bs : list branch) *)

Lemma pure_eval_trywith `{Encode A} η e bs (φ : A -> Prop) ζ ζ' :
  pure (eval η e) φ ζ ->
  (∀ ex, ζ ex -> pure (match_exn η ex bs) φ ζ') ->
  pure (eval η (ETryWith e bs)) φ ζ'.
Proof.
  intros Heval Htryw. simpl_eval.
  eapply pure_wp_try, pure_wp_mono; eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Raising an exception: [raise e]. *)
(* TODO ERaise (e : expr) *)

(* Performing an effect: [perform e]. *)
(* TODO EPerform (e : expr) *)

(* Continuing a continuation: [continue e1 e2]. *)
(* TODO EContinue (e1 : expr) (e2 : expr) *)

(* Discontinuing a continuation: [discontinue e1 e2]. *)
(* TODO EDiscontinue (e1 : expr) (e2 : expr) *)

(* Loop: [while e do body done]. *)
(* TODO EWhile (e body : expr) *)
(* Loop: [for x = e1 to e2 do e done]. *)
(* TODO EFor (x : var) (e1 e2 e : expr) *)

(* Fatal error: [assert false]. *)
(* We model OCaml's unreachable construct [.] in this way, too. *)
(* TODO EAssertFalse *)

(* -------------------------------------------------------------------------- *)

(** Runtime assertion: [assert(e)]. *)

(* EAssert (e : expr) *)

(* Runtime assertions. *)

Lemma pure_assert η e ψ :
  pure (eval η e) (singleton true) ψ →
  pure (eval η (EAssert e)) (singleton ()) ψ.
Proof.
  intros He. simpl_eval.
  apply pure_choose. eapply pure_ret; eauto.
  encode.
  eapply pure_bind. eapply pure_as_bool; eauto.
  intros _ ->. cbn.
  eapply pure_simp; [ simp | ].
  repeat econstructor. encode.
Qed.

Lemma pure_eval_assert_bool η e :
  pure (eval η e) (singleton true) ⊥ →
  pure (eval η (EAssert e)) (λ (_ : unit), True) ⊥.
Proof.
  intros He. eapply pure_mono.
  eapply pure_assert. all: done.
Qed.

Lemma pure_eval_assert_Prop η e :
  pure (eval η e) (λ P : Prop, P) ⊥ →
  pure (eval η (EAssert e)) (λ (_ : unit), True) ⊥.
Proof.
  intros He. eapply pure_mono.
  eapply pure_assert.
  eapply pure_wp_mono; first eapply He; eauto.
  all: try done.
  intros; returns_eauto; cbn; eauto.
  repeat econstructor. rewrite truth_true; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Reference allocation: [ref e]. *)
(* TODO ERef (e: expr) *)
(* Reference lookup: [!e]. *)
(* TODO ELoad (e: expr) *)
(* Reference assignment: [e1 := e2]. *)
(* TODO EStore (e1 e2: expr) *)

(* -------------------------------------------------------------------------- *)

(* - [φ] is the toplevel specification.
   - [φf] is the specification of the function [f]. *)

(* -------------------------------------------------------------------------- *)

(** Evaluating tuples, or several expressions in parallel *)

(* TODO avoid [Forall2] just by showing nil and cons lemmas; offer tactic
  analogous to [pats]. *)

(* FIXME *)
Lemma pure_evals_cons `{Encode A} η (hd : expr) tl (φ : list val -> Prop) :
  pure (A := A) (eval η hd)
    (fun x =>
      pure (evals η tl) (fun v => φ (# x :: v)) ⊥) ⊥ ->
  pure (evals η (hd :: tl)) φ ⊥.
Proof.
  intros. simpl_evals.
  eapply pure_par_seq.
  eapply pure_mono; try done.
  intros * ?.
  eapply pure_mono; first eapply H1; eauto.
  intros * ?. eapply pure_simp; first simp; eauto.
  cbn in H2; eapply pure_ret; eauto.
  cbn; f_equiv.
Qed.

Local Lemma pure_evals η es φs ψ :
  Forall2 (λ e φ, pure (eval η e) φ ψ) es φs →
  pure_wp (evals η es) (Forall2 id φs) ψ.
Proof.
  revert φs.
  induction es as [ | e es IHes]; intros φs' Hes.
  - simpl_evals. constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (φ & φs & He & Hes & ->).
    simpl_evals.
    eapply pure_wp_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros v vs Hv Hvs. repeat constructor; eauto.
      red. destruct Hv as (?&?&?); subst; done.
    + intros exn []; repeat constructor; eauto.
Qed.

(* The following [_eq] versions should be simpler to use in cases we know the
  final values *)

Lemma pure_evals_eq η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (singleton v) ψ) es vs →
  pure_wp (evals η es) (singleton vs) ψ.
Proof.
  revert vs.
  induction es as [ | e es IHes]; intros vs' Hes; simpl_evals.
  - constructor; inv Hes; auto.
  - apply Forall2_cons_inv_l in Hes. simpl.
    destruct Hes as (v & vs & He & Hes & ->).
    eapply pure_wp_Par_conseq.
    + apply He.
    + apply IHes, Hes.
    + intros _ _ (?&->&->) ->. repeat constructor; eauto.
    + intros exn []; repeat constructor; eauto.
Qed.

Lemma pure_evals_eq η es vs ψ :
  Forall2 (λ e v, pure (eval η e) (singleton v) ψ) es vs →
  pure (evals η es) (singleton vs) ψ.
Proof.
  apply pure_evals_eq.
Qed.

  (* -------------------------------------------------------------------------- *)
  (** Hoare reasoning rules *)

  (* Conditionals. *)

  Lemma pure_ifthenelse `{EncA: Encode A}
    η e e1 e2 φ (ψ : exn -> Prop) :
    pure (A := bool) (eval η e)
      (λ v : bool, pure (eval η (if v then e1 else e2)) φ ψ) ψ →
    pure (A := A) (eval η (EIfThenElse e e1 e2)) φ ψ.
  Proof.
    intros He. simpl_eval.
    eapply pure_wp_bind, pure_wp_bind, (pure_wp_mono _ He); auto.
    intros _v ([] & -> & H).
    all: eapply pure_wp_simp; [ simp | ];
    apply pure_wp_ret, H.
  Qed.

  (* TODO fix inconsistent naming *)
  Lemma pure_ifthenelse_bool `{EncA: Encode A}
    η e e1 e2 (φ : A -> _) φb ψ :
    pure (eval η e) φb ψ →
    (φb true  → pure (eval η e1) φ ψ) →
    (φb false → pure (eval η e2) φ ψ) →
    pure (eval η (EIfThenElse e e1 e2)) φ ψ.
  Proof.
    simpl.
    intros Hb Ht Hf.
    simpl_eval.
    eapply pure_wp_bind_conseq. apply pure_as_bool. apply Hb.
    intros [] ?; eauto with pure.
  Qed.

  Lemma pure_eval_ifthenelse `{EncA: Encode A}
    η e e1 e2 (P : Prop) (ψ : A → Prop) :
    pure (eval η e) (λ P', P' <-> P) ⊥ →
    (P → pure (eval η e1) ψ ⊥) →
    (~ P → pure (eval η e2) ψ ⊥) →
    pure (eval η (EIfThenElse e e1 e2)) ψ ⊥.
  Proof.
    intros He He1 He2.
    eapply pure_ifthenelse.
    eapply (pure_wp_mono_ret _ He).
    intros _v (_ & -> & ->%iff_encode). exists (truth P).
    rewrite encode_truth. split; auto.
    generalize (truth_elim P).
    destruct (truth P); eauto.
  Qed.

  Lemma pure_assert η e ψ :
    pure (eval η e) (singleton #true) ψ →
    pure (eval η (EAssert e)) (singleton #()) ψ.
  Proof.
    intros He. simpl_eval.
    apply pure_choose. eapply pure_ret; eauto.
    apply pure_wp_bind, pure_wp_bind.
    apply (pure_wp_mono _ He); auto.
    intros _ (?&->&->).
    eapply pure_wp_simp; [ simp | ];
    repeat econstructor.
  Qed.

  (* TODO: comment *)
  (* Primitive operations on Booleans. *)
  (* Local definitions. *)

  (* TODO only one or two bindings, for now *)

  (* TODO: lemmas starting with "_" are unused: remove? *)
  (* Helper lemma for Boolean operations *)

  Lemma pure_eval_comparison_operator `{Encode A}
    η e1 e2 (x1 x2 : Z) (f : val → val → micro bool exn) b a (φ : A → Prop) :
    pure (eval η e1) (singleton x1) ⊥ →
    pure (eval η e2) (singleton x2) ⊥ →
    f #x1 #x2 = ret b →
    #a = #b →
    φ a →
    pure (Par (eval η e1) (eval η e2) (pfbind inject2 (λ '(v1, v2), 'b ← f v1 v2; ret (VBool b)))) φ ⊥.
  Proof.
    intros He1 He2 Ef Ea Ha.
    eapply pure_wp_Par_conseq_ret; eauto.
    intros _ _ (_ & -> & ->) (_ & -> & ->).
    apply pure_wp_bind, pure_wp_ret, pure_wp_bind.
    rewrite Ef.
    apply pure_wp_ret, pure_wp_ret.
    eauto with pure.
  Qed.

  (* Boolean operations *)

  Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpLe e1 e2)) (λ P, P <-> (x1 <= x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite lt_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpLe_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpLe e1 e2)) (λ (b : bool), b <-> (x1 <= x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpLe; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  Lemma pure_eval_EOpLt η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpLt e1 e2)) (λ P, P <-> (x1 < x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite lt_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpLt_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpLt e1 e2)) (λ (b : bool), b <-> (x1 < x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpLt; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  Lemma pure_eval_EOpGt η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpGt e1 e2)) (λ P, P <-> (x1 > x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite lt_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpGt_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpGt e1 e2)) (λ (b : bool), b <-> (x1 > x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpGt; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  Lemma pure_eval_EOpGe η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpGe e1 e2)) (λ P, P <-> (x1 >= x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite lt_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpGe_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpGe e1 e2)) (λ (b : bool), b <-> (x1 >= x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpGe; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  Lemma pure_eval_EOpEq η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpEq e1 e2)) (λ P, P <-> (x1 = x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite eq_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpEq_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpEq e1 e2)) (λ (b : bool), b <-> (x1 = x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpEq; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  Lemma pure_eval_EOpNe η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpNe e1 e2)) (λ P, P <-> (x1 <> x2)%Z) ⊥.
  Proof.
    intros He1 He2 Hx1 Hx2. simpl_eval.
    eapply pure_eval_comparison_operator; eauto.
    rewrite eq_repr_repr; auto.
    simpl. f_equal. f_equal. apply truth_eq_true. lia.
  Qed.

  Lemma pure_eval_EOpNe_bool η e1 e2 (x1 x2 : Z) :
    pure (eval η e1) (singleton x1) ⊥ ->
    pure (eval η e2) (singleton x2) ⊥ ->
    (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
    representable x1 ->
    representable x2 ->
    pure (eval η (EOpNe e1 e2)) (λ (b : bool), b <-> (x1 <> x2)) ⊥.
  Proof.
    intros. eapply pure_wp_mono_ret. eapply pure_eval_EOpNe; eauto.
    intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth.
  Qed.

  (* Runtime assertions. *)

  Lemma pure_eval_assert_bool η e :
    pure (eval η e) (singleton true) ⊥ →
    pure (eval η (EAssert e)) (λ (_ : unit), True) ⊥.
  Proof.
    intros He.
    eapply pure_wp_mono_ret.
    eapply pure_assert.
    eapply pure_wp_mono_ret.
    eapply He.
    all:intros _ (V & -> & ->); repeat econstructor.
  Qed.

  Lemma pure_eval_assert_Prop η e :
    pure (eval η e) (λ P : Prop, P) ⊥ →
    pure (eval η (EAssert e)) (λ (_ : unit), True) ⊥.
  Proof.
    intros He.
    eapply pure_wp_mono_ret.
    eapply pure_assert.
    eapply pure_wp_mono_ret.
    eapply He.
    - intros _ (P & -> & HP).
      unfold encode, Encode_bool, Encode_Prop. rewrite truth_true; eauto.
      repeat econstructor.
    - intros _ (V & -> & ->); repeat econstructor.
  Qed.

  Lemma pure_eval_ret_concat `{Encode A}
    e δ η (ψ : A -> Prop) ζ :
    pure (eval (δ ++ η) e) ψ ζ ->
    pure (θ ← ret (δ ++ η);
          eval θ e) ψ ζ.
  Proof.
    tauto.
  Qed.

  Lemma pure_eval_const `{Encode A}
    η c x (ψ : A -> Prop) ζ :
    VConstant c = #x ->
    ψ x ->
    pure (eval η (EConstant c)) ψ ζ.
  Proof.
    intros.
    eapply pure_wp_simp. simp.
    eauto using pure_ret with pure.
  Qed.

End eval_rules.

Lemma pure_eval_data `{Encode Y} η c e y (ψ : Y -> Prop) ζ :
  pure (evals η e) (λ v', VData c v' = #y) ζ ->
  ψ y ->
  pure (eval η (EData c e)) ψ ζ.
Proof.
  intros He Hy.
  simpl_eval.
  eapply pure_wp_bind.
  eapply pure_wp_mono; eauto.
  intros ? ?; eapply pure_wp_noexn_weaken. eauto with pure.
Qed.

(* TODO Comment and clean up. *)
#[global] Instance PureJudgement_poly' {A A'} {EncA : Encode A} `{Encode A'}:
  @PureJudgement A EncA A' | 200 :=
  fun _ a Φ Ψ => pure_wp a (fun x => returns Φ #x) Ψ.

Lemma pure_eval_data' `{Encode Y} `{Encode A} η c e y (ψ : A -> Prop) ζ :
  pure (evals η e) (λ (v' : list Y), VData c (map encode.encode v') = #y) ζ ->
  ψ y ->
  pure (eval η (EData c e)) ψ ζ.
Proof.
  intros He Hy.
  simpl_eval.
  eapply pure_wp_bind.
  eapply pure_wp_mono; eauto.
  intros ? ?; eapply pure_wp_noexn_weaken.
  eapply pure_wp_ret. cbn in *.
  destruct a; cbn in *; returns_eauto; eauto with pure.
  { destruct v; inv H0.
    - inversion Ha_ensures; subst; eauto with pure.
    - inv H1. }
  { destruct v0; inv H0.
    inversion Ha_ensures; subst; eauto with pure.
    eexists _; split; eauto.
    inv H1. inv Ha_ensures.
    do 2 f_equiv. clear -H4.
    revert a v0 H4.
    induction a; intros; destruct v0; inv H4; eauto.
    cbn. f_equiv. eapply IHa; eauto. }
Qed.
