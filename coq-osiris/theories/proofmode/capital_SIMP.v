From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality simp.
From osiris.proofmode Require Import notations.

(* This file also defines the judgement [SIMP m φ], which asserts that the
   computation [m] is pure and eventually produces a result that satisfies
   the postcondition [φ]. This judgement and its reasoning rules for a
   simple Hoare logic (of total correctness) for pure computations. *)

(* This file offers lemmas and tactics that help work with [SIMP] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)

(* The judgement [SIMP m φ] asserts that the computation [m] can be simplified
   to [ret #x], where [x] is a (logical) value so that [φ x] holds. *)

(* Because the relation [simp] is inductively defined, this judgement implies
   that [m] terminates. This is a Hoare logic of total correctness. *)

Definition SIMP `{Encode X} (m : micro val) (φ : X → Prop) :=
  ∃ x, simp m (ret #x) ∧ φ x.

(* -------------------------------------------------------------------------- *)

(* Basic reasoning rules for [ret], [bind], [try]. *)

Lemma SIMP_ret `{Encode X} (φ : X → Prop) v x :
  v = #x →
  φ x →
  SIMP (ret v) φ.
Proof.
  unfold SIMP. intros. subst. eauto with simp.
Qed.

(* A reasoning rule for [try]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [Next],
   so the handler [g] is dead and no proof obligation bears on it. *)

Lemma SIMP_try X (_ : Encode X) Y (_ : Encode Y)
  m f g (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (try m f g) ψ.
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_try.
Qed.

(* This variant of the Bind rule has two premises. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind X (_ : Encode X) Y (_ : Encode Y)
  m f (φ : X → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ x, φ x → SIMP (f #x) ψ) →
  SIMP (bind m f) ψ.
Proof.
  rewrite bind_as_try. eauto using SIMP_try.
Qed.

(* This Iris-style variant of the Bind rule has just one premise. It is
   obtained by choosing the least precise φ in the above lemma. *)

(* This is [@bind val val]. *)

Lemma SIMP_bind_unary X (_ : Encode X) Y (_ : Encode Y)
  m f (φ : X -> Prop) (ψ : Y → Prop) :
  SIMP m ψ ->
  (forall x : Y, ψ x -> SIMP (f #x) φ) ->
  SIMP (bind m f) φ.
Proof.
  eauto using SIMP_bind.
Qed.

(* -------------------------------------------------------------------------- *)

(* This lemma allows simplifying a goal of the form [SIMP m φ] by first
   simplifying [m] into [m'], then reasoning about [m']. *)

Lemma SIMP_simp `{Encode X} m m' (φ : X → Prop) :
  simp m m' →
  SIMP m' φ →
  SIMP m φ.
Proof.
  unfold SIMP.
  intros ? (x & ? & ?).
  eauto with simp.
Qed.

(* The Consequence rule. *)

Lemma SIMP_covariant `{Encode X} m (φ ψ : X → Prop) :
  SIMP m φ →
  (∀ x, φ x → ψ x) →
  SIMP m ψ.
Proof.
  intros (x & Hm & Hx) ?. exists x. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [bind] composed with [as_bool]. *)

Lemma simp_as_bool (x : bool) (m : micro val) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  destruct x; eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_bool Y (_ : Encode Y)
  m (f : bool → micro val) (φ : bool → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : bool), φ x → SIMP (f x) ψ) →
  SIMP (bind (as_bool m) f) ψ.
  (* This is [@bind bool val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_bool.
Qed.

(* [bind] composed with [as_int]. *)

Lemma simp_as_int (x : Z) (m : micro val) :
  simp m (ret #x) →
  simp (as_int m) (ret (repr x)).
Proof.
  eauto using prove_simp_bind with simp.
Qed.

Lemma SIMP_bind_as_int Y (_ : Encode Y)
  m (f : int → micro val) (φ : Z → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : Z), φ x → SIMP (f (repr x)) ψ) →
  SIMP (bind (as_int m) f) ψ.
  (* This is [@bind int val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  exists y; eauto using prove_simp_bind, simp_as_int.
Qed.

(* TODO add similar lemmas for [as_loc] and possibly others *)

(* -------------------------------------------------------------------------- *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma SIMP_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [SIMP_covariant] and [SIMP_call]. *)

Lemma SIMP_call_covariant `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  (∀ y, φ y → ψ y) →
  SIMP (call v1 v'2) ψ.
Proof.
  eauto using SIMP_covariant, SIMP_call.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma SIMP_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) :
  SIMP (acall η a v2) φ ->
  SIMP (call (VClo η a) v2) φ.
Proof.
  tauto.
Qed.

Lemma SIMP_enter_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  SIMP (
    let δ := eval_rec_bindings η rbs in
    let η := concat δ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ ->
  SIMP (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma SIMP_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  SIMP (
    let δ := eval_rec_bindings η rbs in
    let η := concat δ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ =
  SIMP (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma invert_SIMP_crash `{Encode Y} (φ : Y -> Prop) :
  SIMP Crash φ -> False.
Proof.
  intros (? & Hsimp & _).
  by apply simp_crash_ret in Hsimp.
Qed.

Lemma invert_SIMP_call `{Encode Y} f v (φ : Y -> Prop) : 
  SIMP (call f v) φ ->
  (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g. 
Proof.
  intros Hcall.
  unfold call in Hcall.
  destruct f; simpl in Hcall;
    ((exfalso; by eapply invert_SIMP_crash) || eauto).
Qed.

(* Replace the first occurence of a var in an environment *)

Fixpoint replace_env_binding η name val {struct η} :=
  match η with
  | EnvNil => EnvNil
  | EnvCons name0 val0 η0 =>
      if (name =? name0)%string then EnvCons name val η0 else
        EnvCons name0 val0 (replace_env_binding η0 name val)
  end.

Lemma lookup_rec_bindings_cases rbs g :
  lookup_rec_bindings rbs g = missing_variable g \/ exists a, lookup_rec_bindings rbs g = ret a.
Proof.
  induction rbs as [|[f a] ? IH]; first auto.
  simpl. destruct (g =? f)%string; eauto.
Qed.

Lemma in_bindings_in_eval_bindings rbs fname η :
  (∃ afun, lookup_rec_bindings rbs fname = ret afun) ->
  exists vf, lookup_name (eval_rec_bindings η rbs) fname = ret vf.
Proof.
  intros [afun Hlkp].
  unfold eval_rec_bindings. generalize rbs at 1.
  induction rbs as [|[??] rbs IHrbs]; first discriminate; intros.
  simpl in *. destruct (fname =? f)%string; eauto.
Qed.

Lemma replace_env_idempotent η fname vf :
  lookup_name η fname = ret vf -> replace_env_binding η fname vf = η.
Proof.
  intros Hlkp.
  induction η as [|fname' ? η IHη]; first discriminate.
  simpl in *. destruct (fname =? fname')%string eqn:name_eq.
  { apply String.eqb_eq in name_eq as ->. injection Hlkp as ->. reflexivity. }
  by rewrite IHη.
Qed.

Lemma replace_env_binding_concat1 η1 η2 fname v :
  (exists vf, lookup_name η1 fname = ret vf) ->
  replace_env_binding (concat η1 η2) fname v = concat (replace_env_binding η1 fname v) η2.
Proof.
  intros [vf Hlkp].
  induction η1 as [|fname' ? η1 IHη1]; first discriminate.
  simpl in *. destruct (fname =? fname')%string eqn:name_eq; first reflexivity.
  by rewrite IHη1.
Qed.

Lemma eval_bindings_produces_eq η rbs rbs' fname :
  lookup_name (eval_rec_bindings η rbs) fname = ret (VCloRec η rbs' fname) -> rbs = rbs'.
Proof.
  unfold eval_rec_bindings. generalize rbs at 2; intros rbs''.
  induction rbs'' as [|[??] ??]; first discriminate; simpl.
  by destruct (_ =? _)%string; [injection 1|].
Qed.

Lemma lookup_eval_bindings_aux rbs η fname afun :
  lookup_rec_bindings rbs fname = ret afun ->
  exists rbs', lookup_name (eval_rec_bindings η rbs) fname = ret (VCloRec η rbs' fname).
Proof.
  intros Hlkp. unfold eval_rec_bindings. generalize rbs at 1.
  induction rbs as [|[fname' ?] rbs IHrbs]; first discriminate; intros.
  simpl in *. destruct (fname =? fname')%string eqn:name_eq.
  { apply String.eqb_eq in name_eq as ->. eauto. }
  eauto.
Qed.

Corollary lookup_eval_bindings rbs η fname afun :
  lookup_rec_bindings rbs fname = ret afun ->
  lookup_name (eval_rec_bindings η rbs) fname = ret (VCloRec η rbs fname).
Proof.  
  intros Hlkp. eapply lookup_eval_bindings_aux in Hlkp as [rbs' Hlkp].
  replace rbs' with rbs in Hlkp by (eapply eval_bindings_produces_eq; eauto).
  apply Hlkp.
Qed.

Lemma replace_binding_idempotent η rbs fname afun :
  lookup_rec_bindings rbs fname = ret afun ->
  (replace_env_binding
     (concat (eval_rec_bindings η rbs) η)
     fname
     (VCloRec η rbs fname) =
     concat (eval_rec_bindings η rbs) η).
Proof.
  intros Hlkp.
  apply lookup_eval_bindings with (η:=η) in Hlkp.
  rewrite replace_env_binding_concat1 by eauto.
  rewrite replace_env_idempotent by eauto.
  done.
Qed.

Lemma SIMP_Eval `{Encode X} η e k ko (φ : X -> Prop) :
  SIMP (try (eval η e) k ko) φ ->
  SIMP (Stop CEval (η, e) k ko) φ.
Proof.
  intros.
  by eapply SIMP_simp; first apply SimpEval.
Qed.

Lemma SIMP_EvalRetNext `{Encode X} η e (φ : X -> Prop) :
  SIMP (eval η e) φ ->
  SIMP (Stop CEval (η, e) ret (fun _ => Next)) φ.
Proof.
  intros.
  by eapply SIMP_simp; [apply advance_SimpEvalRetNext; apply SimpReflexive|].
Qed.

(* Todo: write comment *)

Lemma SIMP_rec_call `{Encode X} `{Encode Y}
  (η : env) (rbs : rec_bindings) (fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          SIMP (call vf #v'') (φ v'')) ->
      SIMP (let δ := concat (eval_rec_bindings η rbs) η in
            let η := replace_env_binding δ fname vf in
            'afun ← lookup_rec_bindings rbs fname ;
            let 'AnonFun x e := afun in
            let η0 := EnvCons x #v' η in
            eval η0 e
        ) (φ v')) ->
  SIMP (call (VCloRec η rbs fname) #v) (φ v).
Proof.
  intros Hwf HP Hrec. 
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply SIMP_enter_call_VCloRec; simpl in *.
  destruct (lookup_rec_bindings_cases rbs fname) as [Hlkp|[afun Hlkp]].
  { rewrite Hlkp in *; simpl in *.
    eapply Hrec with (vf:=VInt int.zero); eauto. }
  { specialize (Hrec (VCloRec η rbs fname) v HP).
    rewrite Hlkp in *; simpl in *.
    erewrite replace_binding_idempotent in Hrec by apply Hlkp.
    unfold acall; destruct afun; apply SIMP_EvalRetNext.
    eapply Hrec; auto.
    intros. rewrite Hlkp. by apply IH. }
Qed.

Notation "fname 'to' afun" :=
  (RecBinding fname afun) (at level 50).

Notation "'RecBind' x" := (RecBiCons x RecBiNil) (at level 70). 

Notation "'RecBinds' x ; y ; .. ; z" :=
  (RecBiCons x (RecBiCons y .. (RecBiCons z RecBiNil) ..))
    (at level 60,
      format "'RecBinds'  x ;  '/' y ; '/' .. ; '/' z").

Lemma SIMP_rec_call_unary `{Encode X} `{Encode Y}
  (η : env) afun (fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          SIMP (call vf #v'') (φ v'')) -> 
      SIMP (let 'AnonFun x e := afun in
            eval (EnvCons x #v' (EnvCons fname vf η)) e) (φ v')) ->
  SIMP (call (VCloRec η (RecBind fname to afun) fname) #v) (φ v).
Proof.
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply SIMP_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct afun; apply SIMP_EvalRetNext.
  eapply Hrec; auto.
Qed.

Lemma SIMP_rec_call_binary_mutual `{Encode X} `{Encode Y}
  (η : env) (afun agun : anonfun) (gname fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          SIMP (call vf #v'') (φ v'')) -> 
      SIMP (let 'AnonFun x e := afun in
            eval (x ~> #v';
                  fname ~> vf;
                  gname ~> (VCloRec η (RecBinds fname to afun; gname to agun) gname);
                  η) e) (φ v')) ->
  SIMP (call (VCloRec η (RecBinds fname to afun; gname to agun) fname) #v) (φ v).
Proof.
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply SIMP_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct afun; apply SIMP_EvalRetNext.
  eapply Hrec; auto.
Qed.

Lemma SIMP_rec_call_binary_mutual_aliasing `{Encode X} `{Encode Y}
  (η : env) ef eg farg garg (gname fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          SIMP (call vf #v'') (φ v'')) -> 
      SIMP (eval ((if (fname =? gname)%string then garg else farg) ~> #v';
                  gname ~>
                    if (fname =? gname)%string
                    then vf
                    else (VCloRec
                            η
                            (RecBinds
                               gname to (AnonFun garg eg);
                             fname to (AnonFun farg ef))
                            gname);
                  fname ~> vf;
                  η) (if (fname =? gname)%string then eg else ef)) (φ v')) ->
  SIMP (call (VCloRec η (RecBinds gname to (AnonFun garg eg); fname to (AnonFun farg ef)) fname) #v) (φ v).
Proof.
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply SIMP_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct (fname =? gname)%string eqn:name_eq; apply SIMP_EvalRetNext.
  { apply String.eqb_eq in name_eq as ->. eapply Hrec; eauto. }
  eapply Hrec; eauto.
Qed.

Lemma SIMP_rec_call_binary_mutual2 `{Encode X} `{Encode Y}
  (η : env) ef farg agun (gname fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (fname =? gname)%string = false ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          SIMP (call vf #v'') (φ v'')) -> 
      SIMP (eval (farg ~> #v';
                  gname ~>
                    (VCloRec η (RecBinds gname to agun; fname to (AnonFun farg ef)) gname);
                  fname ~> vf;
                  η) ef) (φ v')) ->
  SIMP (call (VCloRec η (RecBinds gname to agun; fname to (AnonFun farg ef)) fname) #v) (φ v).
Proof.
  intros Hwf HP Hname Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply SIMP_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; rewrite Hname; apply SIMP_EvalRetNext.
  eapply Hrec; eauto.
Qed.

Definition nested_SIMP `{Encode X} vf arg1 arg2 (φ : X -> Prop) :=
  SIMP (call vf arg1) (fun c =>
                         SIMP (call c arg2) φ).

Lemma SIMP_nested_rec_call `{Encode A} `{Encode B} `{Encode C}
  (η : env) farg farg2 ef ef2 (fname : var) (v1 : A) (v2 : B)
  (P : A -> B -> Prop) (φ : A -> B -> C -> Prop) (R : (A * B) -> (A * B) -> Prop) :
  let vclo := (VCloRec η (RecBind fname to (AnonFun farg ef)) fname) in
  well_founded R ->
  P v1 v2 ->
  let η1 := (farg ~> #v1; fname ~> vclo; η) in
  eval η1 ef = ret (VClo η1 (AnonFun farg2 ef2)) ->
  (forall (vf : val) v1' v2',
      P v1' v2' ->
      (forall v1'' v2'',
          let η1' := (farg ~> #v1''; fname ~> vclo; η) in
          eval η1' ef = ret (VClo η1' (AnonFun farg2 ef2)) ->
          P v1'' v2'' ->
          R (v1'', v2'') (v1', v2') ->
          nested_SIMP vf #v1'' #v2'' (φ v1'' v2'')) ->
      let δ := (farg2 ~> #v2'; farg ~> #v1'; fname ~> vf; η) in
      SIMP (eval δ ef2) (φ v1' v2')) ->
  nested_SIMP vclo #v1 #v2 (φ v1 v2).
Proof.
  cbn zeta.
  intros Hwf HP Heval Hrec.
  remember (v1, v2) as p eqn:Hpeq.
  replace v1 with (p.1) in * by (rewrite Hpeq; reflexivity).
  replace v2 with (p.2) in * by (rewrite Hpeq; reflexivity).
  clear v1 v2 Hpeq.
  induction p as [p IH] using (well_founded_induction Hwf); intros.
  destruct p as [v1 v2]; simpl in *.
  apply SIMP_enter_call_VCloRec; simpl; rewrite String.eqb_refl; simpl.
  
  unfold acall; apply SIMP_EvalRetNext.
  rewrite Heval. eapply SIMP_ret; first solve [encode].
  apply SIMP_enter_call_VClo; simpl; apply SIMP_EvalRetNext.
  eapply Hrec; auto; intros.
  apply (IH (v1'', v2'')); auto.
Qed.






  
(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* TODO reduce just beta-redexes in the goal (possibly under ∀ and →) *)

Ltac beta :=
  cbn beta.

Goal (λ (x : bool), negb x = ((λ (x : bool), x) false)) true.
Proof.
  beta. reflexivity.
Qed.

(* [SIMP_ret] expects a goal of the form [SIMP (ret v) φ]. It applies
   the lemma [SIMP_ret], solves the subgoal [v = #x], and leaves just
   the subgoal [φ x], which it simplifies. *)

Ltac SIMP_ret :=
  simple eapply SIMP_ret; [ solve [ encode ] | beta ].

(* [SIMP_simp] expects a goal of the form [SIMP m φ]. It simplifies
   [m] into [m'], if possible, and leaves the goal [SIMP m' φ]. *)

Ltac SIMP_simp :=
  simple eapply SIMP_simp; [ simp_really |].

(* SIMP0 leaves zero subgoal. *)
(* SIMP1 leaves one subgoal, which may have an arbitrary shape. *)

Ltac SIMP0 :=
  try SIMP_simp;
  first [

    SIMP_ret; [
      (* goal: [φ x] *)
      SIMP_close
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* goal: [SIMP (call #x) φ] *)
      SIMP_close
    ]

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* goal: [∀ x, φ x → φ' x] *)
    | SIMP_close
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_bind        ; [ SIMP0 | beta; intros; SIMP0 ]
  | simple eapply SIMP_try         ; [ SIMP0 | beta; intros; SIMP0 ]

  | SIMP_close

  ]

with SIMP1 :=
  try SIMP_simp;
  first [

    SIMP_ret (* residual goal: [φ x] *)

  | simple eapply SIMP_call_covariant; [
      (* goal: [v = #x] *)
      solve [encode]
      (* goal: [SIMP (call #x) φ] *)
    | solve [eauto with SIMP_specs]
      (* residual goal: [∀ x, φ x → φ' x] *)
    | beta
    ]

  | simple eapply SIMP_call; [
      (* goal: [v = #x] *)
      solve [encode]
    | (* residual goal: [SIMP (call #x) φ] *)
      idtac
    ]

  | simple eapply SIMP_bind_as_bool; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind_as_int ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_bind        ; [ SIMP0 | (* residual goal *) beta ]
  | simple eapply SIMP_try         ; [ SIMP0 | (* residual goal *) beta ]

  | idtac (* residual goal *)

  ]

with SIMP_close :=
  solve [ eauto with SIMP_specs representable ].

Ltac SIMP1_call_step :=
  first [
    eapply SIMP_enter_call_VClo
  | eapply SIMP_enter_call_VCloRec
  ].

Ltac SIMP_enter :=
  SIMP1_call_step;
  SIMP1.

Ltac SIMP_continue :=
  lazymatch goal with
  | |- SIMP ?m _ =>
      unfold_breakpoint m;
      SIMP1
  | _ =>
      fail "[SIMP_continue] expects a goal of the form [SIMP _ _]"
  end.

Ltac SIMP_specify x φ :=
  lazymatch goal with
  | |- SIMP (bind (ret_dconcat ?δ _) _) _ =>
      (* is this reduction too strong? *)
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

(* It is debatable in which order the two premises of the lemma [SIMP_call]
   should be attacked. The premise [v'2 = #x] may seem easy to solve (this
   is the job of the tactic [encode]) so one may wish to solve it first.
   This offers the advantage of instantiating [x] immediately, so [x] is
   known when we try to prove that the call is permitted -- which may
   involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g., the
   type of an empty list), and we have used [Hint Mode] in encode.v to
   forbid this. So, it can also be preferable to first solve the premise
   [SIMP (call v1 #x) φ]. Doing so can allow us to instantiate these types
   in a correct way.

   One might wish to try both approaches in sequence, but waiting until
   [encode] fails is very slow (several seconds).

   One might also wish to do a bit of both: that is, first apply some lemma
   [L] to the subgoal [SIMP (call v1 #x) φ], then solve [v'2 = #x], then
   attack the proof obligations created by applying the lemma [L]. *)

Create HintDb SIMP_specs.

(* TODO may be unused *)
Ltac SIMP_call :=
  first [
    simple eapply SIMP_call; [ solve [encode] | solve [eauto with SIMP_specs] ]
  | simple eapply SIMP_covariant; [
      simple eapply SIMP_call; [ solve [encode] | eauto with SIMP_specs ]
    | cbn ]
  ].

Ltac SIMP_enter_and_abstract :=
  lazymatch goal with |- SIMP (call ?v _) _ =>
    (* First, expand [call] away. *)
    SIMP1_call_step;
    normalize;
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.
