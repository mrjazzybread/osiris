From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval simplification.

From osiris.program_logic.pure Require Import wp notation total_rules.


Section ceval_rules.

  (** [CEval] evaluation *)

  Context {A} {EncA: Encode A}.

  Lemma pure_CEval {E η e k} (φ : A → Prop) (ψ : E → Prop) :
    pure (try2 (eval η e) k) φ ψ →
    pure (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros. eapply pure_wp_det_may_backward; eauto. repeat constructor.
    by intros m' ->%pure.invert_may_eval.
  Qed.

  Lemma pure_CEval_inject2 {η e φ ψ} :
    pure (A := A) (eval η e) φ ψ →
    pure (Stop CEval (η, e) inject2) φ ψ.
  Proof.
    intros He. eapply pure_CEval, pure_try2; try done;
    eauto using pure_ret, pure_throw.
  Qed.

End ceval_rules.

(* -------------------------------------------------------------------------- *)
(** *Evaluating data and data types*)
(* -------------------------------------------------------------------------- *)

(* Fun with data constructors: we can know the destructor as long as we
   have the signature of the algebraic datatype. *)

(* The type of a data constructor can be built from the list of
   constructor argument types. *)
Fixpoint data_constructor A (x : list Type) : Type :=
  match x with
    | nil => A
    | hd :: tl => hd -> data_constructor A tl
  end.

(* A signature for a constructor that builds type [A]. *)
Definition signature {A} : Type := sigT (data_constructor A).

(* Data types is a map from string (constructor name) to the type signatures
  of the constructors. *)
Class DataType (A : Type) :=
  { data_signature : gmap.gmap string (@signature A); }.

(* -------------------------------------------------------------------------- *)

(* TODO: Move *)

(* Utility *)

(** *Heterogeneous list *)

From Equations Require Import Equations.

Section hlist.
  Set Implicit Arguments.

  Inductive hlist (A : Type) (B : A -> Type) : list A -> Type :=
  | HNil : hlist B nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist B ls -> hlist B (x :: ls).
  Arguments HNil {A B}.
  Arguments HCons {A B x ls}.

  (* Append for heterogeneous lists. *)

  Equations happ (A B : list Type) :
    hlist (fun T : Type => T) A ->
    hlist (fun T : Type => T) B ->
    hlist (fun T : Type => T) (A ++ B) :=
  happ HNil m := m;
  happ (HCons a l1) m := HCons a (happ l1 m).

End hlist.

Arguments HNil {A B}.
Arguments HCons {A B x ls}.

(* -------------------------------------------------------------------------- *)

(* Construct a data type [A] given its signature, data constructor and arguments. *)

Equations build_constructor {A}
  (Σ : list Type)
  (constr : data_constructor A Σ)
  (data : hlist (fun T : Type => T) Σ)
  : A :=
  (* When there are no arguments left, the construction is immediate. *)
  @build_constructor _ nil constr HNil := constr;

  (* Peel off an argument of the signature and apply to the constructor. *)
  @build_constructor _ (τ :: tl) constr (HCons v vtl) :=
    (build_constructor (Σ := tl) (constr v) vtl).

(* TODO Comment *)

Fixpoint eval_data_aux {A X}
  (* FIXME: Change argument names *)
  (v : list expr)
  (η : env)
  (φ : A -> Prop) (ψ : exn -> Prop)
  (t : list Type)
  (constr : data_constructor A X)
  (acc_t : list Type)
  (acc : hlist (fun T : Type => T) acc_t)
  : Prop :=
  match v, t with
  | hd :: tl, hd_t :: tl_t =>
      ∃ (EncX : Encode hd_t) x,
      pure
        (eval η hd)
        (fun y : hd_t =>
          y = x /\
          @eval_data_aux _ _ tl η φ ψ
            tl_t
            constr
            (acc_t ++ [hd_t])
            (happ acc (HCons x HNil))) ⊥
  | nil, nil =>
      exists (eq_X : acc_t = X),
      φ (@build_constructor _ acc_t
           (eq_rect_r
              (fun X => data_constructor A X)
              constr eq_X) acc)
  | _ , _ => False
end.

Arguments eval_data_aux {A X} _ _ _ _ _ _ _ _.

(* Evaluate a list of expressions into a data type according to the signature. *)

Definition eval_data {A}
  (e : list expr) (η : env) (φ : A -> Prop) (ψ : exn -> Prop) (Σ : @eval_rules.signature A)
  := @eval_data_aux A _ e η φ ψ (projT1 Σ) (projT2 Σ) nil HNil.

(* -------------------------------------------------------------------------- *)

Lemma pure_eval_data_eq `{Encode A} a η c e (ψ : A -> Prop) ζ:
  pure_wp
    (evals η e)
    (λ x, # a = VData c x) ζ ->
  ψ a ->
  pure (eval η (EData c e)) ψ ζ.
Proof.
  intros Hwp Hψ.
  simpl_eval.
  eapply pure_wp_bind.
  eapply pure_wp_mono; eauto.
  intros l <-; apply pure_wp_ret. eauto with pure.
Qed.

Require Import Coq.Logic.EqdepFacts.

Lemma pure_eval_data {A} `{Encode A, DataType A} η
  c hd tl (φ : _ -> Prop) ψ
  (signature : sigT (data_constructor A)) :
  data_signature !! c = Some signature ->
  eval_data (hd :: tl) η φ ψ signature ->
  pure (A := A) (eval η (EData c (hd :: tl))) φ ψ.
Proof.
  intros Hsig Heval.
  simpl_eval.
  unfold eval_data in Heval.
  simp eval_data_aux in Heval.
  destruct signature as (t & constr); clear Hsig.

  (* Case analysis on the list type *)
  destruct t.
  { simpl in Heval. done. }

  revert constr Heval.
  induction t.

  { (* Base case *)
    intros constr Heval.
    destruct Heval as (?&?&?).
    eapply pure_wp_Par_val_left, pure_wp_mono; eauto.
    intros a' Hret; red in Hret; destruct Hret as (?&?&?&?).
    simpl in H4; subst.
    destruct tl; simp eval_data_aux in H4; cycle 1.
    { unfold eval_data_aux in H4; done. }

    cbn; simpl_evals; do 2 apply pure_wp_ret.
    cbn in *; destruct H4 as (?&?).
    simp happ in H2.

    simp build_constructor in H2.
    red; eexists _; split; eauto; unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq.

    (* TODO: Customize the instance for [Encode A]. *)
    (* VData c [#x0] = #(constr x0) *)
    admit. }

  (* Inductive case *)

  intros constr Heval.
  destruct Heval as (?&?&?).
  eapply pure_wp_Par_val_left, pure_wp_mono; eauto.
  intros a' Hret; red in Hret; destruct Hret as (?&?&?&?).
  simpl in H4. subst. destruct tl; simp eval_data_aux in H4.
  { by unfold eval_data_aux in H4. }

  cbn. simpl_evals.
  eapply pure_wp_mono.

Admitted.

(* -------------------------------------------------------------------------- *)
(** *Evaluating function calls *)
(* -------------------------------------------------------------------------- *)

(* A well-founded relation *)

Class WellFounded (A : Type) : Type :=
  { wf_relation : (A -> A -> Prop);
    wf_def : @well_founded A wf_relation }.

Arguments wf_relation {_ WF} : rename.
Arguments wf_def {_ WF} : rename.

Class WellFoundedRel (A : Type) (R : A -> A -> Prop) :=
  { wf_rel_def : @well_founded A R }.

Definition WellFoundedRel_WellFounded {A} (R : A -> A -> Prop)
  {wfr: WellFoundedRel R} : WellFounded A :=
  {| wf_relation := R; wf_def := wf_rel_def |}.

(* -------------------------------------------------------------------------- *)

Lemma pure_rec_call `{Encode X, Encode Y} (WF_x : WellFounded X)
  (η : env) (f : var) arg e (x : X) Ψ (P : X -> Prop) (φ : X -> Y -> Prop):
  P x ->
  (∀ vf x,
      (∀ (y : X), wf_relation (WF := WF_x) y x -> P y -> pure (call vf #y) (φ y) Ψ) ->
      (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e) (φ x) Ψ)) ->
  pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof.
  intros HPx Hrec.
  induction x as [x IH] using (well_founded_induction wf_def); intros.
  do 2 red.
  simpl. rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_ret_right.
  apply Hrec; [ intros y HR HPy | assumption ].
  apply IH; eauto.
Qed.

Lemma pure_rec_call_simple `{Encode X, Encode Y} (WF_x : WellFounded X)
  (η : env) (f : var) arg e (x : X) Ψ (φ : X -> Y -> Prop):
  (∀ vf x,
    (∀ (y : X), wf_relation (WF := WF_x) y x -> pure (call vf #y) (φ y) Ψ) ->
    (pure (eval ((arg, #x) :: (f, vf) :: η) e) (φ x) Ψ)) ->
  pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof. intros; eapply pure_rec_call with (P := fun _ => True); eauto. Qed.

Lemma pure_rec_call_measure `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M)
  (η : env) (f : var) arg e Ψ (φ : Y -> Prop):
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        pure (call vf #y) φ Ψ) ->
    (pure (eval ((arg, #y') :: (f, vf) :: η) e) φ Ψ)) ->
  forall (x : X),
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) φ Ψ.
Proof.
  intros Hrec x.
  remember (measure x). revert x Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_ret_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done.
Qed.

Lemma pure_rec_call_measure_gen `{Encode X, Encode Y} {M}
  (measure : X -> M) (WF_x : WellFounded M) x
  (η : env) (f : var) arg e Ψ (φ : X -> Y -> Prop):
  (∀ vf (y' : X),
    (∀ (y : X),
        wf_relation (WF := WF_x) (measure y) (measure y') ->
        pure (call vf #y) (φ y) Ψ) ->
    (pure (eval ((arg, #y') :: (f, vf) :: η) e) (φ y') Ψ)) ->
    pure (call (VCloRec η [RecBinding f (AnonFun arg e)] f) #x) (φ x) Ψ.
Proof.
  intros Hrec.
  remember (measure x). revert x Heqm.
  induction m as [mx IH] using (well_founded_induction wf_def); intros.
  simpl; rewrite String.eqb_refl.
  apply pure_wp_bind, pure_wp_ret. simpl.
  apply pure_CEval; rewrite try2_ret_right. subst.
  apply Hrec. intros; subst.
  specialize (IH _ H1). eapply IH; done.
Qed.

(* Tactics for reasoning about recursive calls. *)

Tactic Notation "recursion" constr(t) :=
  (eapply (pure_rec_call (X := t) _)).
Tactic Notation "recursion" "with" uconstr(R) :=
  (eapply (pure_rec_call_simple (WellFoundedRel_WellFounded R))).
Tactic Notation "recursion" uconstr(H) "with" uconstr(R) :=
  (eapply (pure_rec_call (WellFoundedRel_WellFounded R)) with (P := H)).
Tactic Notation "recursion" "{" "measure " uconstr(measure) "}" "∀" uconstr(g) :=
  (eapply (pure_rec_call_measure_gen measure _ g)).
Tactic Notation "recursion" "with" uconstr(R) "{" "measure " uconstr(measure) "}" :=
  (eapply (pure_rec_call_measure measure (WellFoundedRel_WellFounded R))).
Tactic Notation "recursion" "with" uconstr(R) "{" "measure " uconstr(measure) "}" "∀" uconstr(g) :=
  (eapply (pure_rec_call_measure_gen measure (WellFoundedRel_WellFounded R) g)).

(* -------------------------------------------------------------------------- *)

From osiris.program_logic.pure Require Import pattern_rules.

(* -------------------------------------------------------------------------- *)
(** *Evaluating pattern matches *)
(* -------------------------------------------------------------------------- *)

Section match_rules.

  (* [pure_match η v bs φ] is sugar for [pure (eval_match η v bs) ##φ ⊥].

    [eval_match] is used by [eval] when evaluating an [EMatch]. *)

  Definition pure_match `{Encode A} (η : env) bs (o : outcome3 val exn) (φ : A -> Prop) Ψ :=
    pure (deep_eval_match η bs o) φ Ψ.

  Arguments pure_match {A} {H} _ _ _ _.

  Lemma pure_eval_match `{Encode B} η e bs (a : val) (φ : B -> Prop) Ψ :
    total (eval η e) (λ x, x = a) ->
    pure_match η bs (O3Ret a) φ Ψ ->
    pure (eval η (EMatch e bs)) φ Ψ.
  Proof.
    intros Heval Hmatch. simpl_eval.
    apply pure_wp_handle.
    apply (pure_wp_mono _ Heval); [ | intros _ [] ].
    intros ? (? & -> & ->).
    simpl_install_deep_eval_match.
    apply (pure_wp_mono _ Hmatch); eauto with pure.
  Qed.

  Lemma pure_eval_match' `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) Ψ :
    total (eval η e) φ' ->
    (∀ (a : A), φ' a -> pure_match η bs (O3Ret #a) φ Ψ) ->
    pure (eval η (EMatch e bs)) φ Ψ.
  Proof.
    intros Heval Hmatch. simpl_eval.
    apply pure_wp_handle.
    apply (pure_wp_mono _ Heval). 2: intros _ [].
    intros ? (a & -> & Ha).
    simpl_install_deep_eval_match.
    apply (pure_wp_mono _ (Hmatch _ Ha)); eauto.
  Qed.

  Lemma pure_eval_match'_exn `{Encode A, Encode B} η e bs (φ : B -> Prop) (φ' : A -> Prop) ζ Ψ :
    pure (eval η e) φ' ζ ->
    (∀ (a : A), φ' a -> pure_match η bs (O3Ret #a) φ Ψ) ->
    (∀ (ex : exn), ζ ex -> pure_match η bs (O3Throw ex) φ Ψ) ->
    pure (eval η (EMatch e bs)) φ Ψ.
  Proof.
    intros He Hφ' Hζ.
    simpl_eval.
    apply pure_wp_handle.
    apply (pure_wp_mono _ He).
    - intros _v (a & -> & Ha).
      simpl_install_deep_eval_match.
      by apply Hφ'.
    - intros ex Hex.
      simpl_install_deep_eval_match.
      by apply Hζ.
  Qed.

  Lemma pure_eval_trywith `{Encode A} η e bs (φ : A -> Prop) ζ ζ' :
    pure (eval η e) φ ζ ->
    (∀ ex, ζ ex -> pure (eval_trywith η ex bs) φ ζ') ->
    pure (eval η (ETryWith e bs)) φ ζ'.
  Proof.
    intros Heval Htryw. simpl_eval.
    eapply pure_wp_try, pure_wp_mono; eauto with pure.
  Qed.

  Lemma pure_eval_try_with_cons `{Encode A} η ex p e bs (φ : A -> Prop) ζ :
    pattern η p ex (λ η', pure (eval η' e) φ ζ) (pure (eval_trywith η ex bs) φ ζ) ->
    pure (eval_trywith η ex (Branch (CExc p) e :: bs)) φ ζ.
  Proof.
    intros Hpat. simpl_eval_trywith.
    eapply pure_wp_try, pure_wp_mono; eauto.
    apply pattern_equals_pat; eauto.
    all: intros; eauto.
  Qed.

  (* Currently unused *)

  Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) Ψ :
    cpattern η p v (λ η', pure (eval η' e) φ Ψ) (pure_match η bs v φ Ψ) ->
    pure_match η ((Branch p e) :: bs) v φ Ψ.
  Proof.
    unfold pure_match.
    intros; simpl_deep_eval_match.
    apply pure_wp_try. by apply cpattern_equals_cpat.
  Qed.

  Lemma pure_match_cons `{Encode A} η v p e bs (φ : A -> Prop) ψ ζ :
    cpattern η p v (λ η', pure (eval η' e) φ ζ) ψ ->
    (ψ -> (pure_match η bs v φ ζ)) ->
    pure_match η ((Branch p e) :: bs) v φ ζ.
  Proof.
    intros.
    apply pure_match_cons_unary.
    apply cpattern_equals_cpat.
    eapply pure_wp_mono.
    by apply cpattern_equals_cpat.
    all: intros; eauto.
  Qed.

  (* Not matching is an error. *)

  Lemma pure_match_single `{Encode A} η v p e (φ : A -> Prop) ψ ζ :
    cpattern η p v (λ η' : env, pure (eval η' e) φ ζ) ψ →
    (ψ -> False) ->
    pure_match η [Branch p e] v φ ζ.
  Proof.
    intros.
    eapply pure_match_cons; eauto.
    tauto.
  Qed.

(* -------------------------------------------------------------------------- *)

End match_rules.


(* TODO Comment. *)

(* -------------------------------------------------------------------------- *)
(** *Evaluation of expressions *)
(* -------------------------------------------------------------------------- *)

Section eval_rules.

  Lemma pure_eval_path `{Encode A} η π (ψ : A -> Prop) (ζ : exn -> Prop) :
    total (lookup_path η π) ψ ->
    pure (eval η (EPath π)) ψ ζ.
  Proof. simpl_eval. Admitted.

  Lemma pure_eval_tuple `{Encode A, Encode B} η x tl (φ : B -> Prop) ψ v:
    pure (A := A)
      (eval η x)
      (fun v' : A =>
        pure_wp (evals η tl) (fun x => v = # v' :: x) ψ) ψ ->
    pure (A := B) (eval η (ETuple (x :: tl))) φ ψ.
  Proof. Admitted.

  Lemma pure_evals_cons `{Encode A} η (hd : expr) tl (φ : list val -> Prop) ψ :
    pure (A := A) (eval η hd)
      (fun x =>
        pure_wp (evals η tl) (fun v => φ (# x :: v)) ψ) ψ ->
    pure_wp (A := list val) (evals η (hd :: tl)) φ ψ.
  Proof. Admitted.

  (* -------------------------------------------------------------------------- *)

  (** Evaluating tuples, or several expressions in parallel *)

  (* Lemma pure_ifthenelse η e e1 e2 φ ψ : *)
  (*   pure (eval η e) (λ v, ∃ b : bool, v = #b ∧ pure (eval η (if b then e1 else e2)) φ ψ) ψ → *)
  (*   pure (eval η (EIfThenElse e e1 e2)) φ ψ. *)
  (* Proof. *)
  (*   simpl. *)
  (*   intros He. simpl_eval. *)
  (*   eapply pure_bind, pure_bind, (pure_mono _ He); auto. *)
  (*   intros _v ([] & -> & H); apply pure_ret, H. *)
  (* Qed. *)

  (* Lemma pure_assert η e ψ : *)
  (*   pure (eval η e) (λ v, v = #true) ψ → *)
  (*   pure (eval η (EAssert e)) (λ v, v = #()) ψ. *)
  (* Proof. *)
  (*   intros He. simpl_eval. *)
  (*   apply pure_choose. by apply pure_ret. *)
  (*   apply pure_bind, pure_bind. *)
  (*   apply (pure_mono _ He); auto. *)
  (*   intros _ ->. *)
  (*   repeat econstructor. *)
  (* Qed. *)

  (* Lemma pure_seq φ ψ η e1 e2 : *)
  (*   pure (eval η e1) (λ _, pure (eval η e2) φ ψ) ψ → *)
  (*   pure (eval η (ESeq e1 e2)) φ ψ. *)
  (* Proof. *)
  (*   simpl_eval. *)
  (*   eauto using pure_bind. *)
  (* Qed. *)

  (* (* If [z] is representable and [z ≠ 0] then the runtime check *)
  (*   performed by [check_div_by_zero (repr z)] must succeed. *) *)

  (* Lemma pure_check_div_by_zero z : *)
  (*   representable z → *)
  (*   (z ≠ 0)%Z → *)
  (*   pure (check_div_by_zero (repr z)) (λ v, v = ()) ⊥. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold check_div_by_zero. *)
  (*   change int.zero with (repr 0). *)
  (*   rewrite eq_repr_repr by representable. *)
  (*   case_eq (z =? 0)%Z; [ rewrite Z.eqb_eq | rewrite Z.eqb_neq ]; intro. *)
  (*   { tauto. } *)
  (*   { apply pure_val. } *)
  (* Qed. *)

  (* (* Helper lemma for primitive arithmetic operations. *) *)

  (* Lemma pure_if_in_shift_range {A E} z (m : micro A E) φ ψ : *)
  (*   in_shift_range z → *)
  (*   pure m φ ψ → *)
  (*   pure (if_in_shift_range (repr z) m) φ ψ. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold if_in_shift_range, in_shift_range_b. *)
  (*   rewrite signed_repr by eauto using in_shift_range_representable. *)
  (*   by rewrite in_shift_range_b_spec. *)
  (* Qed. *)

  (* TODO avoid [Forall2] just by showing nil and cons lemmas; offer tactic
    analogous to [pats]. *)

  Local Lemma pure_wp_evals η es φs ψ :
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

  Local Lemma pure_wp_evals_eq η es vs ψ :
    Forall2 (λ e v, pure (eval η e) (λ x, x = v) ψ) es vs →
    pure_wp (evals η es) (λ x, x = vs) ψ.
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

  (* -------------------------------------------------------------------------- *)

  Context {A} {EncA: Encode A}.

  (** Hoare reasoning rules *)

  Lemma pure_ifthenelse η e e1 e2 φ (ψ : exn -> Prop) :
    pure (A := bool) (eval η e)
      (λ v : bool, pure (eval η (if v then e1 else e2)) φ ψ) ψ →
    pure (A := A) (eval η (EIfThenElse e e1 e2)) φ ψ.
  Proof.
    simpl.
    intros He. simpl_eval.
    eapply pure_wp_bind, pure_wp_bind, (pure_wp_mono _ He); eauto.
    intros _v ([] & -> & H);
    apply pure_wp_ret, H.
  Qed.

  Lemma pure_assert η e ψ :
    pure (eval η e) (λ v, v = #true) ψ →
    pure (eval η (EAssert e)) (λ v, v = #()) ψ.
  Proof.
    intros He. simpl_eval.
    apply pure_choose. eapply pure_ret; eauto.
    apply pure_wp_bind, pure_wp_bind.
    apply (pure_wp_mono _ He); auto.
    intros _ (?&->&->); repeat econstructor.
  Qed.

  Definition pure_call2 `{Encode X} vf arg1 arg2 (φ : X -> Prop) Ψ :=
    pure (call vf arg1) (fun c => pure (call c arg2) (returns φ) Ψ) Ψ.

  (* Tuples. *)

  (* A special case at arity 2. *)

  (* TODO can we give a similar lemma at arity [n]? *)

  Lemma pure_eval_pair `{Encode A1, Encode A2} η e1 e2 (ψ : A1 * A2 → Prop) :
    total (eval η e1) (λ a1 : A1, total (eval η e2) (λ a2 : A2, ψ (a1, a2)))→
    total (eval η (EPair e1 e2)) ψ.
  Proof.
    intros. simpl_eval.
    eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
    eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
    repeat apply pure_wp_ret.
    eauto with pure.
  Qed.

  (* TODO: comment *)

  (* Lemma total_eval_int η i (ψ : Z -> Prop) : *)
  (*   ψ i -> *)
  (*   total (eval η (EInt i)) ψ. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply pure_wp_simp. simp_tactics.simp. *)
  (*   eapply total_ret; eauto. *)
  (* Qed. *)

  (* (* Function applications. *) *)

  (* Lemma pure_eval_anonfun `{Encode A, Encode A1} η v e (φ : A1 -> Prop) (ψ : val -> Prop) ζ : *)
  (*   (∀ (x : A), pure (eval ((v, #x) :: η) e) φ ζ) -> *)
  (*   (∀ (vf : val), (∀ (x : A), pure (call vf #x) φ ζ) -> ψ vf) -> *)
  (*   pure (eval η (EAnonFun (AnonFun v e))) ψ ζ. *)
  (* Proof. *)
  (*   intros Hcall Hcov. specialize (Hcov (VClo η (AnonFun v e))). *)
  (*   eapply pure_wp_simp; [ simp | eauto ]. *)
  (*   eapply pure_wp_ret. eexists. split. by encode. *)
  (*   apply Hcov. *)
  (*   intros. eapply pure_wp_simp; [ simp | apply Hcall ]. *)
  (* Qed. *)

  (* Lemma pure_eval_anonfun' `{Encode A, Encode A1} η a φ (ψ : val -> Prop) : *)
  (*   (∀ (x : A), φ (VClo η a) #x) -> *)
  (*   (∀ (vf : val), (∀ (x : A), φ vf #x) -> ψ vf) -> *)
  (*   total (eval η (EAnonFun a)) ψ. *)
  (* Proof. *)
  (*   intros Hcall Hcov. specialize (Hcov (VClo η a)). *)
  (*   eapply pure_wp_simp; [ simp | eauto ]. *)
  (*   eapply total_ret; first solve [encode]. *)
  (*   eauto. *)
  (* Qed. *)

  (* Lemma pure_eval_anonfunction `{Encode A, Encode A1} η bs (φ : A1 -> Prop) (ψ : val -> Prop) : *)
  (*   (∀ (x : A), *)
  (*       total *)
  (*         (deep_eval_match (("__osiris_anonymous_arg", #x) :: η) bs (O2Ret #x)) *)
  (*         φ) -> *)
  (*   (∀ (vf : val), (∀ (x : A), total (call vf #x) φ) -> ψ vf) -> *)
  (*   total (eval η (EAnonFun (AnonFunction bs))) ψ. *)
  (* Proof. *)
  (*   intros Hcall Hcov. *)
  (*   eapply pure_wp_simp; [ simp | eauto ]. *)
  (*   eapply total_ret; first solve [encode]. *)
  (*   apply Hcov. *)
  (*   intros. eapply pure_wp_simp; [ simp  |  ]. *)
  (*   specialize (Hcall x); generalize Hcall; by simpl_deep_eval_match. *)
  (* Qed. *)

  (* (* this sequentialized lemma create only one [pure] goal but assumes [e1] cannot *) *)
  (* (* throw exceptions *) *)
  (* Lemma pure_eval_app `{Encode A1, Encode A} η e1 e2 (ψ : A → Prop) ζ : *)
  (*   pure (eval η e1) *)
  (*     (λ f : val, *)
  (*         pure (eval η e2) *)
  (*           (λ arg : A1, *)
  (*               pure (call f #arg) ψ ζ) ⊥) ⊥ → *)
  (*   pure (eval η (EApp e1 e2)) ψ ζ. *)
  (* Proof. *)
  (*   intros He1. simpl_eval. *)
  (*   apply pure_wp_Par_vals_left. *)
  (*   eapply (pure_wp_mono_ret _ He1). intros ? (v & -> & He2). *)
  (*   eapply (pure_wp_mono _ He2); try done. *)
  (*   intros ? (a2 & -> & Hcall). apply Hcall. *)
  (* Qed. *)

  (* Lemma pure_eval_app_conseq `{Encode A, Encode B} η e1 e2 *)
  (*   (φ1 : val → Prop) (φ2 : A → Prop) (ψ : B → Prop) ζ *)
  (* : *)
  (*   pure (eval η e1) φ1 ζ → *)
  (*   pure (eval η e2) φ2 ζ → *)
  (*   (∀ v1 v2, φ1 v1 → φ2 v2 → pure (call v1 #v2) ψ ζ) → *)
  (*   pure (eval η (EApp e1 e2)) ψ ζ. *)
  (* Proof. *)
  (*   intros He1 He2 Hp. simpl_eval. *)
  (*   apply pure_par. *)
  (*   - eapply (pure_mono _ He1). 2: apply pure_throw. *)
  (*     intros ? (v1 & -> & Hv1). *)
  (*     eapply (pure_mono _ He2). 2: apply pure_throw. *)
  (*     intros ? (a & -> & Ha). apply Hp; eauto with encode. *)
  (*   - eapply (pure_mono _ He2). 2: apply pure_throw. *)
  (*     intros ? (v2 & -> & Hv2). *)
  (*     eapply (pure_mono _ He1). 2: apply pure_throw. *)
  (*     intros ? (a & -> & Ha). apply Hp; eauto with encode. *)
  (* Qed. *)


  (* Lemma pure_eval_app2 `{Encode A, Encode B, Encode C} η e1 e2 e3 vf *)
  (*   (arg1 : A) (arg2 : B) (ψ : C → Prop) ζ *)
  (*   : *)
  (*   total (eval η e1) (λ vf', vf' = vf) -> *)
  (*   total (eval η e2) (λ arg1', arg1' = arg1) -> *)
  (*   total (eval η e3) (λ arg2', arg2' = arg2) -> *)
  (*   pure_call2 vf #arg1 #arg2 ψ ζ -> *)
  (*   pure (eval η (EApp (EApp e1 e2) e3)) ψ ζ. *)
  (* Proof. *)
  (*   intros He1 He2 He3 Hcall. *)
  (*   eapply pure_simp; [ simp | eauto ]. *)
  (*   apply pure_Par_val_right. *)
  (*   apply (pure_mono_ret _ He3). intros ? (? & -> & ->). *)
  (*   apply pure_Par_vals_left. *)
  (*   apply (pure_mono_ret _ He1). intros ? (? & -> & <-). *)
  (*   apply (pure_mono_ret _ He2). intros ? (? & -> & ->). *)
  (*   unfold continue. simpl. *)
  (*   apply (pure_mono _ Hcall). auto. *)
  (*   intros ??; unfold discontinue; simpl; auto using pure_throw. *)
  (* Qed. *)

  (* Lemma pure_eval_app2_conseq `{Encode A, Encode B, Encode C} η e1 e2 e3 vf *)
  (*   (arg1 : A) (arg2 : B) (φ ψ : C → Prop) ζ *)
  (*   : *)
  (*   total (eval η e1) (λ vf', vf' = vf) -> *)
  (*   total (eval η e2) (λ arg1', arg1' = arg1) -> *)
  (*   total (eval η e3) (λ arg2', arg2' = arg2) -> *)
  (*   pure_call2 vf #arg1 #arg2 φ ζ -> *)
  (*   (∀ a, φ a → ψ a) → *)
  (*   wp (eval η (EApp (EApp e1 e2) e3)) ψ ζ. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply pure_eval_app2; eauto. *)
  (*   eapply pure_mono; first eassumption; last auto. *)
  (*   simpl; intros. *)
  (*   eapply total_consequence; eauto. *)
  (* Qed. *)

  (* Helper lemmas for arithmetic operations. *)

  (* Lemma pure_as_int m (φ : Z → Prop) : *)
  (*   total m φ → *)
  (*   total (as_int m) (λ i, ∃ z, i = repr z ∧ φ z). *)
  (* Proof. *)
  (*   intros Hm. apply pure_bind. *)
  (*   apply (pure_mono_ret _ Hm). intros ? (z & -> & Hz). *)
  (*   apply pure_ret. eauto. *)
  (* Qed. *)

  (* Lemma pure_enc_par_as_int m1 m2 (φ1 φ2 φ : Z → Prop) k : *)
  (*   pure m1 ##φ1 ⊥ → *)
  (*   pure m2 ##φ2 ⊥ → *)
  (*   (∀ z1 z2 : Z, φ1 z1 → φ2 z2 → pure (k (repr z1, repr z2)) ##φ ⊥) → *)
  (*   pure (Par (as_int m1) (as_int m2) (pfbind inject2 k)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros Hm1 Hm2 Hk. *)
  (*   unfold as_int. *)
  (*   eapply pure_Par_conseq. 1,2: eapply pure_as_int; eauto. 2: firstorder. *)
  (*   intros ? ? (z1 & -> & Hz1) (z2 & -> & Hz2). *)
  (*   eapply pure_simp; [ simp | ]. *)
  (*   by apply Hk. *)
  (* Qed. *)

  (* (* Primitive arithmetic operations. *) *)

  (* Lemma pure_eval_add η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 + z2)) → *)
  (*   pure (eval η (EIntAdd e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_sub η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 - z2)) → *)
  (*   pure (eval η (EIntSub e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_mul η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 * z2)) → *)
  (*   pure (eval η (EIntMul e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_div η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1, φ1 z1 → representable z1) → *)
  (*   (∀ z2, φ2 z2 → representable z2) → *)
  (*   (∀ z2, φ2 z2 → z2 ≠ 0) → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 ÷ z2)) → *)
  (*   pure (eval η (EIntDiv e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_bind, pure_mono_ret. *)
  (*   apply pure_check_div_by_zero; eauto. *)
  (*   intros [] _. *)
  (*   apply pure_ret. *)
  (*   eauto 10 with encode. *)
  (* Qed. *)

  (* (* Primitive logical operations on machine integers. *) *)

  (* Lemma pure_eval_lnot η e1 (φ1 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   (∀ z1, φ1 z1 → φ (Z.lnot z1)) → *)
  (*   pure (eval η (EIntLnot e1)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros He1%pure_as_int Hp. simpl_eval. *)
  (*   eapply pure_bind_conseq; eauto. intros ? (z & -> & Hz). *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_land η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.land z1 z2)) → *)
  (*   pure (eval η (EIntLand e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_lor η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lor z1 z2)) → *)
  (*   pure (eval η (EIntLor e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_lxor η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lxor z1 z2)) → *)
  (*   pure (eval η (EIntLxor e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_lsl η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1, φ1 z1 → representable z1) → *)
  (*   (∀ z2, φ2 z2 → in_shift_range z2) → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftl z1 z2)) → *)
  (*   pure (eval η (EIntLsl e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   apply pure_if_in_shift_range; auto. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_lsr η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1, φ1 z1 → urepresentable z1) → *)
  (*   (∀ z2, φ2 z2 → in_shift_range z2) → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) → *)
  (*   pure (eval η (EIntLsr e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   apply pure_if_in_shift_range; auto. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_asr η e1 e2 (φ1 φ2 φ : Z → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   pure (eval η e2) ##φ2 ⊥ → *)
  (*   (∀ z1, φ1 z1 → representable z1) → *)
  (*   (∀ z2, φ2 z2 → in_shift_range z2) → *)
  (*   (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) → *)
  (*   pure (eval η (EIntAsr e1 e2)) ##φ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval. eapply pure_enc_par_as_int; eauto. intros. *)
  (*   apply pure_if_in_shift_range; auto. *)
  (*   eapply pure_enc_ret; eauto with encode. *)
  (* Qed. *)

  (* (* Helper lemmas for operations on Booleans. *) *)

  (* Lemma pure_as_bool (m : microvx) (φ : bool → Prop) ψ : *)
  (*   pure m ##φ ψ → *)
  (*   pure (as_bool m) φ ψ. *)
  (* Proof. *)
  (*   intro H. *)
  (*   eapply pure_bind_conseq; eauto. *)
  (*   intros [] ([] & E & Hb); discriminate || rewrite E; with_strategy transparent [val_as_bool] by constructor. *)
  (* Qed. *)

  (* Lemma pure_enc_bind_as_bool {A} m (φ : bool → Prop) (ψ : A → Prop) (k : bool → micro A exn) : *)
  (*   pure m ##φ ⊥ → *)
  (*   (∀ b : bool, φ b → pure (k b) ψ ⊥) → *)
  (*   pure (bind (as_bool m) k) ψ ⊥. *)
  (* Proof. *)
  (*   intros Hm Hp. apply pure_bind, pure_as_bool. *)
  (*   apply (pure_mono_ret _ Hm). intros ? (b & -> & Hb). *)
  (*   destruct b; force_unfold val_as_bool; unfold encode_pred; eauto. *)
  (* Qed. *)

  (* (* Primitive operations on Booleans. *) *)

  (* Lemma pure_eval_negb η e (φ ψ : bool → Prop) : *)
  (*   pure (eval η e) ##φ ⊥ → *)
  (*   (∀ b, φ b → ψ (negb b)) → *)
  (*   pure (eval η (EBoolNeg e)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He Hp. simpl_eval. *)
  (*   eapply pure_enc_bind_as_bool; eauto. intros b Hb. apply pure_ret. eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_not η e (φ ψ : Prop → Prop) : *)
  (*   pure (eval η e) ##φ ⊥ → *)
  (*   (∀ P, φ P → ψ (¬P)) → *)
  (*   pure (eval η (EBoolNeg e)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He Hp. simpl_eval. *)
  (*   eapply pure_bind. *)
  (*   eapply pure_as_bool. *)
  (*   eapply pure_mono_ret. apply He. intros ? (P & -> & HP). *)
  (*   exists (truth P). split; auto. apply pure_ret. eexists. split; eauto with encode. *)
  (*   unfold encode, Encode_Prop. rewrite truth_neg. auto. *)
  (* Qed. *)

  (* (* Local definitions. *) *)

  (* (* TODO only one or two bindings, for now *) *)

  (* (* TODO: lemmas starting with "_" are unused: remove? *) *)

  (* Lemma pure_eval_let_pair `{Encode A1, Encode A2} `{Encode X} *)
  (*   p1 p2 e1 e2 η (ψ : X -> Prop) : *)
  (*   pure (eval η e1) ##(λ '((v1, v2) : A1 * A2), *)
  (*       pure ( *)
  (*           δ ← widen (irrefutably_extend [] p1 #v1); *)
  (*           θ ← widen (irrefutably_extend δ p2 #v2); *)
  (*           eval (θ ++ η) e2 *)
  (*         ) ##ψ ⊥) ⊥ -> *)
  (*   pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ##ψ ⊥. *)
  (* Proof. *)
  (*   (* This proof is a long rewriting sequence, which makes some sense as it is *) *)
  (* (*   not the standard method to prove a let binding, but rather a way to reduce the *) *)
  (* (*   wp of a parallel pair to ordered wps of two binds with error handling *) *)
  (*   intros He1. *)
  (*   simpl_eval. apply pure_Par_vals_left. *)
  (*   apply (pure_mono_ret _ He1). clear He1. *)
  (*   intros ? ([v1 v2] & -> & Hpure). apply pure_ret. *)
  (*   apply pure_bind. *)
  (*   apply pure_bind. *)
  (*   apply pure_ret. *)
  (*   unfold widen, irrefutably_extend in *. *)
  (*   rewrite !try_try in *. simpl_extend. *)
  (*   rewrite !bind_as_try, !try_try in *. *)
  (*   apply pure_try2. *)
  (*   apply invert_pure_try2 in Hpure. *)
  (*   apply (pure_mono _ Hpure); clear Hpure. *)
  (*   - intros δ Hpure. *)
  (*     unfold continue in *. *)
  (*     unfold glue2 in *. *)
  (*     repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *. *)
  (*     apply invert_pure_try2 in Hpure. *)
  (*     apply pure_try2. *)
  (*     apply (pure_mono _ Hpure); clear Hpure. *)
  (*     + intros θ Hpure. *)
  (*       unfold continue, glue2 in *. *)
  (*       repeat rewrite ?bind_as_try, ?try_try, ?try_ret in *. *)
  (*       apply pure_ret. eauto. *)
  (*     + unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_crash; eauto. *)
  (*   - unfold match_failure. rewrite try_crash. intros. edestruct @invert_pure_crash; eauto. *)
  (* Qed. *)

  (* Lemma pure_eval_let `{Encode A1, Encode B} η x e1 e *)
  (*   (φ1 : A1 → Prop) (ψ : B → Prop) : *)
  (*   pure (eval η e1) ##φ1 ⊥ → *)
  (*   (∀ a1, φ1 a1 → pure (eval ((x, #a1) :: η) e) ##ψ ⊥) → *)
  (*   pure (eval η (ELet1Var x e1 e)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He1 He. *)
  (*   simpl_eval. *)
  (*   eapply pure_Par_conseq_ret. *)
  (*   - eauto. *)
  (*   - eapply pure_simp. simp. apply pure_ret_eq. *)
  (*   - intros _v _η (a1 & -> & Ha1) ->. *)
  (*     apply pure_bind, pure_bind, pure_ret. *)
  (*     unfold irrefutably_extend. *)
  (*     apply pure_widen. *)
  (*     simpl_extend. *)
  (*     apply pure_try, pure_ret, pure_ret, He, Ha1. *)
  (* Qed. *)

  (* Lemma pure_eval_let' `{Encode A1, Encode B} η x e1 e *)
  (*   (a1 : A1) (ψ : B → Prop) : *)
  (*   pure (eval η e1) ##(λ x, x = a1) ⊥ → *)
  (*   pure (eval ((x, #a1) :: η) e) ##ψ ⊥ → *)
  (*   pure (eval η (ELet1Var x e1 e)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He1 He2. *)
  (*   eapply pure_eval_let; eauto. *)
  (*   congruence. *)
  (* Qed. *)

  (* (* Conditionals. *) *)

  (* (* TODO fix inconsistent naming *) *)
  (* Lemma pure_ifthenelse_bool η e e1 e2 φ φb ψ : *)
  (*   pure (eval η e) ##φb ψ → *)
  (*   (φb true  → pure (eval η e1) φ ψ) → *)
  (*   (φb false → pure (eval η e2) φ ψ) → *)
  (*   pure (eval η (EIfThenElse e e1 e2)) φ ψ. *)
  (* Proof. *)
  (*   simpl. *)
  (*   intros Hb Ht Hf. *)
  (*   simpl_eval. *)
  (*   eapply pure_bind_conseq. apply pure_as_bool. apply Hb. *)
  (*   intros []; auto. *)
  (* Qed. *)

  (* Lemma pure_eval_ifthenelse_bool `{Encode A} η e e1 e2 (φ : bool → Prop) (ψ : A → Prop) : *)
  (*   pure (eval η e) ##φ ⊥ → *)
  (*   (φ true  → pure (eval η e1) ##ψ ⊥) → *)
  (*   (φ false → pure (eval η e2) ##ψ ⊥) → *)
  (*   pure (eval η (EIfThenElse e e1 e2)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_ifthenelse_bool; eauto. *)
  (* Qed. *)

  (* Lemma pure_eval_ifthenelse `{Encode A} η e e1 e2 (P : Prop) (ψ : A → Prop) : *)
  (*   pure (eval η e) ##(λ P', P' <-> P) ⊥ → *)
  (*   (P → pure (eval η e1) ##ψ ⊥) → *)
  (*   (~ P → pure (eval η e2) ##ψ ⊥) → *)
  (*   pure (eval η (EIfThenElse e e1 e2)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He He1 He2. *)
  (*   eapply pure_ifthenelse. *)
  (*   eapply (pure_mono_ret _ He). *)
  (*   intros _v (_ & -> & ->%iff_encode). exists (truth P). *)
  (*   rewrite encode_truth. split; auto. *)
  (*   generalize (truth_elim P). *)
  (*   destruct (truth P); auto. *)
  (* Qed. *)

  (* (* Helper lemma for Boolean operations *) *)

  (* Lemma pure_eval_comparison_operator `{Encode A} η e1 e2 (x1 x2 : Z) (f : val → val → micro bool exn) b a (φ : A → Prop) : *)
  (*   pure (eval η e1) ##(λ x1' : Z, x1' = x1) ⊥ → *)
  (*   pure (eval η e2) ##(λ x2' : Z, x2' = x2) ⊥ → *)
  (*   f #x1 #x2 = ret b → *)
  (*   #a = #b → *)
  (*   φ a → *)
  (*   pure (Par (eval η e1) (eval η e2) (pfbind inject2 (λ '(v1, v2), 'b ← f v1 v2; ret (VBool b)))) ##φ ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Ef Ea Ha. *)
  (*   eapply pure_Par_conseq_ret; eauto. *)
  (*   intros _ _ (_ & -> & ->) (_ & -> & ->). *)
  (*   apply pure_bind, pure_ret, pure_bind. *)
  (*   rewrite Ef. *)
  (*   apply pure_ret, pure_ret. *)
  (*   eauto with encode. *)
  (* Qed. *)

  (* (* Boolean operations *) *)

  (* Lemma pure_eval_EOpLe η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpLe e1 e2)) ##(λ P, P <-> (x1 <= x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite lt_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpLe_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpLe e1 e2)) ##(λ (b : bool), b <-> (x1 <= x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpLe; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpLt η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpLt e1 e2)) ##(λ P, P <-> (x1 < x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite lt_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpLt_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpLt e1 e2)) ##(λ (b : bool), b <-> (x1 < x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpLt; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpGt η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpGt e1 e2)) ##(λ P, P <-> (x1 > x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite lt_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpGt_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpGt e1 e2)) ##(λ (b : bool), b <-> (x1 > x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpGt; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpGe η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpGe e1 e2)) ##(λ P, P <-> (x1 >= x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite lt_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpGe_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpGe e1 e2)) ##(λ (b : bool), b <-> (x1 >= x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpGe; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpEq η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpEq e1 e2)) ##(λ P, P <-> (x1 = x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite eq_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpEq_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpEq e1 e2)) ##(λ (b : bool), b <-> (x1 = x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpEq; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpNe η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpNe e1 e2)) ##(λ P, P <-> (x1 <> x2)%Z) ⊥. *)
  (* Proof. *)
  (*   intros He1 He2 Hx1 Hx2. simpl_eval. *)
  (*   eapply pure_eval_comparison_operator; eauto. *)
  (*   rewrite eq_repr_repr; auto. *)
  (*   simpl. f_equal. f_equal. apply truth_eq_true. lia. *)
  (* Qed. *)

  (* Lemma pure_eval_EOpNe_bool η e1 e2 (x1 x2 : Z) : *)
  (*   pure (eval η e1) ##(λ x1', x1' = x1) ⊥ -> *)
  (*   pure (eval η e2) ##(λ x2', x2' = x2) ⊥ -> *)
  (*   (* Representability hypotheses last for [x1] and [x2] evar initialisation *) *)
  (*   representable x1 -> *)
  (*   representable x2 -> *)
  (*   pure (eval η (EOpNe e1 e2)) ##(λ (b : bool), b <-> (x1 <> x2)) ⊥. *)
  (* Proof. *)
  (*   intros. eapply pure_mono_ret. eapply pure_eval_EOpNe; eauto. *)
  (*   intros _ (P & -> & HP). exists (truth P). by rewrite <-HP, encode_truth, Is_true_truth. *)
  (* Qed. *)

  (* (* Runtime assertions. *) *)

  (* Lemma pure_eval_assert_bool η e : *)
  (*   pure (eval η e) ##(λ b, b = true) ⊥ → *)
  (*   pure (eval η (EAssert e)) ##(λ (_ : unit), True) ⊥. *)
  (* Proof. *)
  (*   intros He. *)
  (*   eapply pure_mono_ret. *)
  (*   eapply pure_assert. *)
  (*   eapply pure_mono_ret. *)
  (*   eapply He. *)
  (*   - by intros _ (V & -> & ->). *)
  (*   - intros _ ->. eauto with encode. *)
  (* Qed. *)

  (* Lemma pure_eval_assert_Prop η e : *)
  (*   pure (eval η e) ##(λ P : Prop, P) ⊥ → *)
  (*   pure (eval η (EAssert e)) ##(λ (_ : unit), True) ⊥. *)
  (* Proof. *)
  (*   intros He. *)
  (*   eapply pure_mono_ret. *)
  (*   eapply pure_assert. *)
  (*   eapply pure_mono_ret. *)
  (*   eapply He. *)
  (*   - intros _ (P & -> & HP). *)
  (*     unfold encode, Encode_bool, Encode_Prop. by rewrite truth_true. *)
  (*   - intros _ ->. eauto with encode. *)
  (* Qed. *)

  (* (* Sequencing of pure computations. *) *)

  (* Lemma pure_eval_seq' `{Encode A} η e1 e2 (ψ : A -> Prop) : *)
  (*   pure (eval η e1) (λ _, True) ⊥ -> *)
  (*   pure (eval η e2) ##ψ ⊥ -> *)
  (*   pure (eval η (ESeq e1 e2)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He1 He2. *)
  (*   apply pure_seq. *)
  (*   apply (pure_mono_ret _ He1). intros _ _. *)
  (*   apply (pure_mono_ret _ He2). intuition. *)
  (* Qed. *)

  (* Lemma pure_eval_seq `{Encode A} `{Encode B} η e1 e2 (ψ : A -> Prop) : *)
  (*   pure (eval η e1) ##(λ _ : B, True) ⊥ -> *)
  (*   pure (eval η e2) ##ψ ⊥ -> *)
  (*   pure (eval η (ESeq e1 e2)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros He1 He2. *)
  (*   apply pure_seq. *)
  (*   apply (pure_mono_ret _ He1). intros _ _. *)
  (*   apply (pure_mono_ret _ He2). intuition. *)
  (* Qed. *)

  (* Lemma pure_eval_seq_exn `{Encode A} η e1 e2 (Ψ : A -> Prop) ζ : *)
  (*   pure (eval η e1) ##(λ _ : val, pure (eval η e2) ##Ψ ζ) ζ -> *)
  (*   pure (eval η (ESeq e1 e2)) ##Ψ ζ. *)
  (* Proof. *)
  (*   intros Hpure. apply pure_seq. *)
  (*   eapply (pure_mono _ Hpure); last auto. *)
  (*   by intros ? (? & ? & ?). *)
  (* Qed. *)

  (* Lemma pure_eval_mexpr_struct (η δ whatenv : env) items (ψ : val -> Prop) : *)
  (*   simp (eval_sitems (η, []) items) (ret (whatenv, δ)) -> *)
  (*   ψ (VStruct δ) -> *)
  (*   pure (eval_mexpr η (MStruct items)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros. simpl_eval_mexpr. *)
  (*   eapply pure_simp; [ simp | eauto using pure_ret with encode ]. *)
  (* Qed. *)

  (* Lemma pure_eval_mexpr_coerc η me c v (ψ : val -> Prop): *)
  (*   simp (eval_mexpr η me) (ret v) -> *)
  (*   pure (coerce c v) ##ψ ⊥ -> *)
  (*   pure (eval_mexpr η (MCoercion me c)) ##ψ ⊥. *)
  (* Proof. *)
  (*   intros Hme Hc. simpl_eval_mexpr. eapply pure_bind. *)
  (*   eapply pure_simp; eauto. *)
  (*   eapply pure_mono_ret. eapply pure_ret_eq. *)
  (*   intros _ ->. *)
  (*   rewrite pure_widen'. *)
  (*   apply Hc. *)
  (* Qed. *)

  (* Lemma pure_eval_ret_concat `{Encode A} e δ η (ψ : A -> Prop) ζ : *)
  (*   pure (eval (δ ++ η) e) ##ψ ζ -> *)
  (*   pure (θ ← ret (δ ++ η); *)
  (*         eval θ e) ##ψ ζ. *)
  (* Proof. *)
  (*   tauto. *)
  (* Qed. *)

  (* Lemma pure_eval_const `{Encode X} η c x (ψ : X -> Prop) ζ : *)
  (*   VConstant c = #x -> *)
  (*   ψ x -> *)
  (*   pure (eval η (EConstant c)) ψ ζ. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply pure_simp. simp. *)
  (*   eauto using pure_ret with pure. *)
  (* Qed. *)

  (* Lemma pure_eval_data `{Encode Y} η c e y (ψ : Y -> Prop) ζ : *)
  (*   pure (eval η e) (λ v', VData c v' = #y) ζ -> *)
  (*   ψ y -> *)
  (*   pure (eval η (EData c e)) ψ ζ. *)
  (* Proof. *)
  (*   intros He Hy. *)
  (*   simpl_eval. *)
  (*   eapply pure_bind. *)
  (* (*   eapply pure_consequence; eauto. *) *)
  (* (*   intros ? A. *) *)
  (* (*   eapply pure_noexn_weaken, pure_enc_ret; eauto; auto. *) *)
  (* (* Qed. *) *)
  (* Admitted. *)


End eval_rules.

(* TODO Clean up and comment *)
Ltac pure_eval_path :=
  eexists _, _;
  eapply pure_eval_path, total_ret_eq_and.
Ltac pure_data :=
  eapply pure_eval_data;
  first try done;
  repeat pure_eval_path; exists eq_refl.
Ltac pure_match :=
  eapply pure_match_cons; first solve_pattern; last intuition.
Ltac pure_path := by eapply pure_eval_path, total_ret.
Ltac eval_match :=
  eapply pure_eval_match; first pure_path.
Ltac match_signature hd :=
  eapply (@pure_evals_cons hd);
  eapply pure_eval_path; cbn -[evals];
  apply pure_wp_ret; eexists _; split; first done.
Ltac match_signatures l :=
  match l with
  | cons ?hd ?tl => match_signature hd;
                    match_signatures tl
  | nil => simpl_evals; apply pure_wp_ret; auto
  end.
Tactic Notation "build" "(" constr(x) ":" constr(l) ")":=
  apply (pure_eval_data_eq x); first match_signatures l.
