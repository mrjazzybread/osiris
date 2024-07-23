From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import equality.
From osiris.proofmode Require Import simp_eval notations.

(* Because the relation [pure_wp] is inductively defined, the [pure] judgement
   implies that [m] terminates. This forms a Hoare logic of total correctness
   for pure computations. *)

(* This file offers lemmas and tactics that help work with [pure] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)

Lemma pure_prove_bind_bind `{Encode A} `{Encode X} {E} m (a : A)
  (f : A -> _) (g : val -> _) (φ : X -> Prop) :
  simp ('c ← m;
        f c) (ret #a) ->
  pure (g #a) φ ->
  pure (X := E) ('v1 ← m;
        'v2 ← f v1;
        g v2) φ.
Proof.
  (* TODO should we really have [simp] as hypothesis? *)
  eintros Hfm%pure_simp_ret Hga.
  apply invert_pure_wp_bind in Hfm.
  eapply pure_wp_bind_compat; eauto. simpl.
  intros a' Ha'.
  eapply pure_wp_bind_compat; eauto. simpl.
  intros _v (_a & -> & ->).
  eapply pure_wp_mono; eauto.
Qed.

Lemma pure_bind_bind `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  pure ('x ← m;
        f x) ψ ->
  (forall y, ψ y -> pure (g #y) φ) ->
  pure ('v1 ← m;
        v2 ← f v1;
        g v2) φ.
Proof.
  intros Hm Hga.
  apply invert_pure_wp_bind in Hm.
  eapply pure_wp_bind_compat; eauto. simpl.
  intros v Hv.
  eapply pure_wp_bind_compat; eauto. simpl.
  intros _ (y & -> & Hy).
  eapply pure_wp_mono_ret.
  - apply Hga, Hy.
  - intros _ (x & -> & Hx). eauto.
Qed.

Lemma pure_bind_binary `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  pure m (fun x => pure (f x) ψ) ->
  (forall y, ψ y -> pure (g #y) φ) ->
  pure ('x ← m;
        y ← f x;
        g y) φ.
Proof.
  intros.
  eapply pure_bind_bind; last done.
  eapply pure_bind; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [pure_bind_as_bool] is already in [simp_eval.v] but it is useful there *)

(* [bind] composed with [as_int]. *)

Lemma pure_bind_as_int `{Encode Y}
  m (f : int → microvx) (φ : Z → Prop) (ψ : Y → Prop) :
  pure m φ →
  (∀ (x : Z), φ x → pure (f (repr x)) ψ) →
  pure (bind (as_int m) f) ψ.
  (* This is [@bind int val]. *)
Proof.
  intros Hm%pure_as_int Hf.
  eapply pure_wp_bind_compat; eauto.
  intros _ (i & -> & Hi).
  eapply (pure_wp_mono_ret _ (Hf i Hi)); auto.
Qed.

(* [bind] composed with [as_loc]. *)

Lemma pure_bind_as_loc `{Encode Y}
  m (f : loc → microvx) (φ : loc → Prop) (ψ : Y → Prop) :
  pure m φ →
  (∀ (x : loc), φ x → pure (f x) ψ) →
  pure (bind (as_loc m) f) ψ.
  (* This is [@bind loc val]. *)
Proof.
  intros Hm Hf.
  apply pure_wp_bind.
  eapply pure_wp_bind_compat; eauto.
  intros _ (l & -> & Hl). apply pure_wp_ret, Hf, Hl.
Qed.

(* [bind] composed with [as_struct]. *)

Lemma pure_bind_as_struct Y (_ : Encode Y)
  m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) :
  pure m (λ y : val, (exists y', y = VStruct y' /\ φ y)) →
  (∀ (x : env), φ (VStruct x) → pure (f x) ψ) →
  pure (bind (as_struct m) f) ψ.
  (* This is [@bind env val]. *)
Proof.
  intros Hm Hf.
  apply pure_wp_bind.
  eapply pure_wp_bind_compat; eauto.
  intros _ (_ & -> & (env & -> & Henv)).
  apply pure_wp_ret, Hf, Henv.
Qed.

(* [bind] composed with [as_record]. *)

Lemma pure_bind_as_record Y (_ : Encode Y)
  m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) :
  pure m (λ y : val, exists y', y = VRecord y' /\ φ y) →
  (∀ (x : env), φ (VRecord x) → pure (f x) ψ) →
  pure (bind (as_record m) f) ψ.
  (* This is also [@bind env val]. *)
Proof.
  (* same exact proof script *)
  intros Hm Hf.
  apply pure_wp_bind.
  eapply pure_wp_bind_compat; eauto.
  intros _ (_ & -> & (env & -> & Henv)).
  apply pure_wp_ret, Hf, Henv.
Qed.

(* TODO add similar lemmas for other constructs *)

(* -------------------------------------------------------------------------- *)

(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

Lemma pure_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ →
  pure (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

(* This lemma combines [pure_consequence] and [pure_call]. *)

Lemma pure_call_consequence `{Encode X} `{Encode Y}
  (φ ψ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  pure (call v1 #x) φ →
  (∀ y, φ y → ψ y) →
  pure (call v1 v'2) ψ.
Proof.
  eauto using pure_consequence, pure_call.
Qed.

(* The following two lemmas paraphrase the definition of [call] in eval.v.
   When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
   a concrete closure (as opposed to a rigid metavariable), they step into
   the call. *)

Lemma pure_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) :
  pure (acall η a v2) φ ->
  pure (call (VClo η a) v2) φ.
Proof.
  tauto.
Qed.

Lemma pure_enter_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  pure (
    let δ := eval_rec_bindings η rbs in
    let η := δ ++ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ ->
  pure (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma pure_call_VCloRec `{Encode Y} η rbs g v2 (φ : Y → Prop) :
  pure (
    let δ := eval_rec_bindings η rbs in
    let η := δ ++ η in
    a ← lookup_rec_bindings rbs g ;
    acall η a v2
  ) φ =
  pure (call (VCloRec η rbs g) v2) φ.
Proof.
  tauto.
Qed.

Lemma invert_pure_crash `{Encode Y} {X} (φ : Y -> Prop) :
  pure (X := X) Crash φ -> False.
Proof.
  apply invert_pure_wp_crash.
Qed.

Lemma invert_pure_call `{Encode Y} f v (φ : Y -> Prop) :
  pure (call f v) φ ->
  (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g.
Proof.
  intros Hcall.
  unfold call in Hcall.
  destruct f; simpl in Hcall;
    ((exfalso; by eapply invert_pure_crash) || eauto).
Qed.

(* Replace the first occurence of a var in an environment *)

Fixpoint replace_env_binding η (name : var) (x : val) {struct η} :=
  match η with
  | [] => []
  | (name0, val0) :: η0 =>
      if (name =? name0)%string then (name, x) :: η0 else
        (name0, val0) :: (replace_env_binding η0 name x)
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
  induction η as [| [fname' ?] η IHη]; first discriminate.
  simpl in *. destruct (fname =? fname')%string eqn:name_eq.
  { apply String.eqb_eq in name_eq as ->. injection Hlkp as ->. reflexivity. }
  by rewrite IHη.
Qed.

Lemma replace_env_binding_concat1 η1 η2 fname v :
  (exists vf, lookup_name η1 fname = ret vf) ->
  replace_env_binding (η1 ++ η2) fname v = (replace_env_binding η1 fname v) ++ η2.
Proof.
  intros [vf Hlkp].
  induction η1 as [| [fname' ?] η1 IHη1]; first discriminate.
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
     ((eval_rec_bindings η rbs) ++ η)
     fname
     (VCloRec η rbs fname) =
     (eval_rec_bindings η rbs) ++ η).
Proof.
  intros Hlkp.
  apply lookup_eval_bindings with (η:=η) in Hlkp.
  rewrite replace_env_binding_concat1 by eauto.
  rewrite replace_env_idempotent by eauto.
  done.
Qed.

Lemma replace_binding η rbs fname afun :
  lookup_rec_bindings rbs fname = ret afun ->
  replace_env_binding (eval_rec_bindings η rbs) fname (VCloRec η rbs fname) =
    eval_rec_bindings η rbs.
Proof.
  intros Hlkp.
  apply lookup_eval_bindings with (η:=η) in Hlkp.
  rewrite replace_env_idempotent; auto.
Qed.

(* Todo: write comment *)

Lemma pure_rec_call `{Encode X} `{Encode Y}
  (η : env) (rbs : list rec_binding) (fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          pure (call vf #v'') (φ v'')) ->
      pure ('afun ← lookup_rec_bindings rbs fname ;
            let δ := replace_env_binding (eval_rec_bindings η rbs) fname vf in
            let 'AnonFun x e := afun in
            eval ((x, #v') :: δ ++ η) e
        ) (φ v')) ->
  pure (call (VCloRec η rbs fname) #v) (φ v).
Proof.
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply pure_enter_call_VCloRec; simpl in *.
  destruct (lookup_rec_bindings_cases rbs fname) as [Hlkp|[afun Hlkp]].
  { rewrite Hlkp in *; simpl in *.
    eapply Hrec with (vf:=VInt int.zero); eauto. }
  { specialize (Hrec (VCloRec η rbs fname) v HP).
    erewrite replace_binding in Hrec by eauto.
    simpl in *; rewrite !Hlkp in *; simpl in *.
    unfold acall; destruct afun; apply pure_EvalRetThrow.
    eapply Hrec; auto. }
Qed.

Notation "fname 'to' afun" :=
  (RecBinding fname afun) (at level 50).

Lemma pure_rec_call_unary `{Encode X} `{Encode Y}
  (η : env) afun (fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          pure (call vf #v'') (φ v'')) ->
      pure (let 'AnonFun x e := afun in
            eval ((x, #v') :: (fname, vf) :: η) e) (φ v')) ->
  pure (call (VCloRec η [RecBinding fname afun] fname) #v) (φ v).
Proof.
(*   intros Hwf HP Hrec. *)
(*   eapply pure_rec_call. *)
(*   { apply Hwf. } *)
(*   { apply HP. } *)
(*   simpl; rewrite String.eqb_refl. apply Hrec. *)
(* Qed. *)
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply pure_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct afun; apply pure_EvalRetThrow.
  eapply Hrec; auto.
Qed.

Lemma pure_rec_call_binary_mutual `{Encode X} `{Encode Y}
  (η : env) (afun agun : anonfun) (gname fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          pure (call vf #v'') (φ v'')) ->
      pure (let 'AnonFun x e := afun in
            eval (x ~> #v';
                  fname ~> vf;
                  gname ~> (VCloRec η [RecBinding fname afun; RecBinding gname agun] gname);
                  η) e) (φ v')) ->
  pure (call (VCloRec η [RecBinding fname afun; RecBinding gname agun] fname) #v) (φ v).
Proof.
(*   intros Hwf HP Hrec. *)
(*   eapply pure_rec_call. *)
(*   { apply Hwf. } *)
(*   { apply HP. } *)
(*   simpl; rewrite String.eqb_refl. apply Hrec. *)
(* Qed. *)
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply pure_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct afun; apply pure_EvalRetThrow.
  eapply Hrec; auto.
Qed.

Lemma pure_rec_call_binary_mutual_aliasing `{Encode X} `{Encode Y}
  (η : env) ef eg farg garg (gname fname : var) (v : X)
  (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) :
  well_founded R ->
  P v ->
  (forall (vf : val) v',
      P v' ->
      (forall v'',
          P v'' ->
          R v'' v' ->
          pure (call vf #v'') (φ v'')) ->
      pure (eval ((if (fname =? gname)%string then garg else farg) ~> #v';
                  gname ~>
                    if (fname =? gname)%string
                    then vf
                    else (VCloRec
                            η
                            [RecBinding gname (AnonFun garg eg);
                             RecBinding fname (AnonFun farg ef)]
                            gname);
                  fname ~>
                    if (fname =? gname)%string
                    then (VCloRec η
                            [RecBinding gname (AnonFun garg eg);
                             RecBinding fname (AnonFun farg ef)]
                            fname)
                    else vf;
                  η) (if (fname =? gname)%string then eg else ef)) (φ v')) ->
  pure (call (VCloRec η [RecBinding gname (AnonFun garg eg);
                         RecBinding fname (AnonFun farg ef)] fname) #v) (φ v).
Proof.
(*   intros Hwf HP Hrec. *)
(*   eapply pure_rec_call. *)
(*   { apply Hwf. } *)
(*   { apply HP. } *)
(*   simpl; destruct (fname =? gname)%string eqn:name_eq; simpl. *)
(*   { apply String.eqb_eq in name_eq. rewrite name_eq in *. apply Hrec. } *)
(*   rewrite String.eqb_refl. apply Hrec. *)
(* Qed. *)
  intros Hwf HP Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply pure_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; destruct (fname =? gname)%string eqn:name_eq; apply pure_EvalRetThrow.
  { apply String.eqb_eq in name_eq as ->. eapply Hrec; eauto. }
  eapply Hrec; eauto.
Qed.

Lemma pure_rec_call_binary_mutual2 `{Encode X} `{Encode Y}
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
          pure (call vf #v'') (φ v'')) ->
      pure (eval (farg ~> #v';
                  gname ~>
                    (VCloRec η [RecBinding gname agun;
                                RecBinding fname (AnonFun farg ef)] gname);
                  fname ~> vf;
                  η) ef) (φ v')) ->
  pure (call (VCloRec η [RecBinding gname agun;
                         RecBinding fname (AnonFun farg ef)] fname) #v) (φ v).
Proof.
(*   intros Hwf HP Hname Hrec. *)
(*   eapply pure_rec_call. *)
(*   { apply Hwf. } *)
(*   { apply HP. } *)
(*   simpl. rewrite Hname. rewrite String.eqb_refl. simpl. *)
(*   apply Hrec. *)
  (* Qed. *)
  intros Hwf HP Hname Hrec.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  apply pure_enter_call_VCloRec; simpl; rewrite String.eqb_refl.
  unfold acall; rewrite Hname; apply pure_EvalRetThrow.
  eapply Hrec; eauto.
Qed.

Definition pure_call2 `{Encode X} vf arg1 arg2 (φ : X -> Prop) :=
  pure (call vf arg1) (fun c =>
                         pure (call c arg2) φ).

Lemma pure_nested_rec_call `{Encode A} `{Encode B} `{Encode C}
  (η : env) farg farg2 ef ef2 (fname : var) (v1 : A) (v2 : B)
  (P : A -> B -> Prop) (φ : A -> B -> C -> Prop) (R : (A * B) -> (A * B) -> Prop) :
  let vclo := (VCloRec η [RecBinding fname (AnonFun farg ef)] fname) in
  well_founded R ->
  P v1 v2 ->
  let η1 := (farg ~> #v1; fname ~> vclo; η) in
  pure (eval η1 ef) (λ v, v = (VClo η1 (AnonFun farg2 ef2))) ->
  (forall (vf : val) v1' v2',
      P v1' v2' ->
      (forall v1'' v2'',
          let η1' := (farg ~> #v1''; fname ~> vclo; η) in
          eval η1' ef = ret (VClo η1' (AnonFun farg2 ef2)) ->
          P v1'' v2'' ->
          R (v1'', v2'') (v1', v2') ->
          pure_call2 vf #v1'' #v2'' (φ v1'' v2'')) ->
      let δ := (farg2 ~> #v2'; farg ~> #v1'; fname ~> vf; η) in
      pure (eval δ ef2) (φ v1' v2')) ->
  pure_call2 vclo #v1 #v2 (φ v1 v2).
Proof.
  cbn zeta.
  intros Hwf HP Heval Hrec.
  remember (v1, v2) as p eqn:Hpeq.
  replace v1 with (p.1) in * by (rewrite Hpeq; reflexivity).
  replace v2 with (p.2) in * by (rewrite Hpeq; reflexivity).
  clear v1 v2 Hpeq.
  induction p as [p IH] using (well_founded_induction Hwf); intros.
  destruct p as [v1 v2]; simpl in *.
  apply pure_enter_call_VCloRec; simpl; rewrite String.eqb_refl; simpl.

  unfold acall; apply pure_EvalRetThrow.
  eapply pure_consequence. apply Heval. intros vf ->.
  apply pure_enter_call_VClo; simpl; apply pure_EvalRetThrow.
  eapply Hrec; auto; intros.
  apply (IH (v1'', v2'')); eauto. simpl.
  rewrite H2.
  eapply pure_ret; [ solve [encode] | reflexivity].
Qed.

Lemma pure_nested_call `{Encode A} `{Encode B} `{Encode C}
  (η : env) rbs (fname : var) (v1 : A) (v2 : B) x y e1 e2
  (P : A -> B -> Prop) (φ : A -> B -> C -> Prop) (R : (A * B) -> (A * B) -> Prop) :
  let δ := eval_rec_bindings η rbs in
  lookup_rec_bindings rbs fname = ret (AnonFun x e1) ->
  (let η0 := (x ~> #v1; δ ++ η) in
   eval η0 e1 = ret (VClo η0 (AnonFun y e2))) ->
  well_founded R ->
  P v1 v2 ->
  (forall vf v1' v2',
      P v1' v2' ->
      (forall v1'' v2'',
          (let η0 := (x ~> #v1''; δ ++ η) in
           eval η0 e1 = ret (VClo η0 (AnonFun y e2))) ->
          P v1'' v2'' ->
          R (v1'', v2'') (v1', v2') ->
          pure_call2 vf #v1'' #v2'' (φ v1'' v2'')) ->
      let δ := replace_env_binding δ fname vf in
      pure (eval (y ~> #v2'; x ~> #v1'; δ ++ η) e2) (φ v1' v2')) ->
  pure_call2 (VCloRec η rbs fname) #v1 #v2 (φ v1 v2).
Proof.
  cbn zeta.
  intros Hlkp Heval Hwf HP Hrec.
  remember (v1, v2) as p eqn:Hpeq.
  replace v1 with (p.1) in * by (rewrite Hpeq; reflexivity).
  replace v2 with (p.2) in * by (rewrite Hpeq; reflexivity).
  clear v1 v2 Hpeq.
  induction p as [p IH] using (well_founded_induction Hwf); intros.
  destruct p as [v1 v2]; simpl in *.
  apply pure_enter_call_VCloRec; rewrite Hlkp; simpl.
  apply pure_EvalRetThrow. rewrite Heval.
  eapply pure_ret; first solve [encode].
  apply pure_enter_call_VClo; apply pure_EvalRetThrow.
  rewrite <- (replace_binding _ _ _ _ Hlkp).
  eapply Hrec; auto; intros.
  apply (IH (v1'', v2'')); auto.
Qed.
