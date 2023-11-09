Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_merge.
Local Opaque app. (* Prevent undesired simplification. *)


Notation "'<(' f ')>'" := (VCloRec _ _ f) (only printing).
Notation "'<' f '>'" := (VClo _ f) (only printing).
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (EnvCons x _ (.. (EnvCons z _ EnvNil) ..))
 (only printing).


Fixpoint encode_list `{Encode A} (t : list A) : val :=
  match t with
  | nil => VConstant "[]"
  | cons x l => VData "::" <v #x, (encode_list l) v>
  end.

Local Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (l : list A),
    encode_list l = #l.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_list_is_encode : encode.


Lemma solve_encode_nil `{Encode A} (l : list A) :
  nil = l ->
  VConstant "[]" = #l.
Proof.
  intros. subst l. eauto.
Qed.

Lemma solve_encode_cons `{Encode A} (l : list A) x l1 vx vl1 :
  cons x l1 = l ->
  vx = #x ->
  vl1 = #l1 ->
  VData "::" <v vx, vl1 v> = #l.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve solve_encode_nil solve_encode_cons : encode.

Definition merge_spec (merge : val) : Prop :=
  ∀ A `(_ : Encode A) (l1 l2 : list Z),
    Forall (fun n => representable n) l1 ->
    Forall (fun n => representable n) l2 ->
    Sorted (Z.le) l1 ->
    Sorted (Z.le) l2 ->
    SIMP
      (call merge #(l1, l2))
      (λ l, Sorted (Z.le) l /\ Permutation (l1 ++ l2) l).

Ltac fixme :=
  unfold EMkTuple; unfold PMkTuple; simpl.

Lemma SIMP_match `{Encode X} η e bs (φ : X -> Prop):
  SIMP ( 'v ← eval η e; eval_match η v bs) (φ) ->
  SIMP (eval η (EMatch e bs)) (φ).
Proof.
  intros (x&H1&H2).
  eapply SIMP_simp. { apply SimpReflexive. }
  eexists x; auto.
Qed.

Ltac SimpRet :=
  (apply SimpParRetLeft || apply SimpParRetRight).

Lemma Sorted_Hd_cmp A x (l : list A) (cmp : A -> A -> Prop) `{Transitive A cmp}:
  Sorted cmp l -> HdRel cmp x l <-> Forall (cmp x) l.
Proof.
  split; intros.
  { induction l; first done.
    destruct l; first (constructor; by inversion H1).
    apply Forall_cons; split; first by inversion H1.
    apply IHl; [ by inversion H0 | apply HdRel_cons].
    eapply H; first by inversion H1.
    inversion H0; subst. by inversion H5. }
  { induction l; first done.
    apply HdRel_cons.
    by inversion H1. }
Qed.

Lemma Zle_Transitive : Transitive Z.le.
Proof.
  unfold Transitive. intros.
  eauto using Z.le_trans.
Qed.
Local Hint Resolve Zle_Transitive : core.

Definition is_env_with_spec name (spec : val -> Prop) :=
  fun v =>
    match v with
    | VStruct env =>
        match (lookup_name env name) with
        | ret v' => spec v'
        | _ => False
        end
    | _ => False
    end.

Lemma Merge__spec:
  let η := EnvCons "Stdlib" Stdlib Stdlib_env in
  SIMP (eval_mexpr η __main)
       (is_env_with_spec "merge" merge_spec).
Proof.
  intros.
  eapply SIMP_simp; [eapply advance_simp_bind_bind; eapply advance_SimpBind ;simp_close |].
  simpl.
  (* Because we don't use the spec once we prove it, we can omit the use of SIMP_specify *)
  SIMP_continue.
  fixme.
  generalize η; clear η; intro η.
  unfold merge_spec.
  induction l1 as [|h1 t1]; intros.
  { rewrite app_nil_l.
    SIMP1. repeat SIMP_continue. auto. }
  induction l2 as [|h2 t2].
  { rewrite app_nil_r.
    SIMP1; repeat SIMP_continue. auto. }
  specialize (IHt1 (h2::t2)).
  inversion H0; inversion H1; inversion H2; inversion H3; subst.
  destruct IHt1 as (h1l2&IH1&?&?); auto.
  destruct IHt2 as (l1t2&IH2&?&?); auto.
  SIMP1. SIMP_continue. SIMP_continue.
  destruct (lt _) eqn:branch; simpl.
  { unfold __exp1. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpRet.
    repeat (eapply advance_SimpBind; simpl; first SimpRet).
    eapply advance_SimpBind; simpl.
    (* Use induction hypothesis *)
    eapply prove_simp_try. { apply IH2. }
    all: try apply SimpReflexive; simpl.
    SIMP_ret.
    split.
    { (* Goal: Sorted (h2 :: l1t2) *)
      apply Sorted_cons; first assumption.
      apply Sorted_Hd_cmp; try auto.
      (* Goal: Forall (le h2) l1t2 *)
      rewrite <- H9; apply Forall_app.
      split; apply Sorted_Hd_cmp; auto.
      constructor.
      rewrite lt_repr_repr in branch; only 2-3: auto.
      apply Z.ltb_lt in branch.
      by apply Z.lt_le_incl. }
    { (* (h1 :: t1) ++ h2 :: t2 =p h2 :: l1t2 *)
      rewrite Permutation_app_comm.
      rewrite <- app_comm_cons.
      apply Permutation_skip.
      by rewrite Permutation_app_comm. }}

  { unfold __exp0. fixme.
    (* Advance to call merge *)
    eapply SIMP_simp.
    simp_eval. eapply advance_SimpBind.
    apply advance_simp_eval. cbn [eval'].
    eapply advance_SimpBind. cbn [evals].
    eapply advance_SimpBind. simpl.
    repeat (rewrite eval_eval'; simpl).
    SimpRet.
    repeat (eapply advance_SimpBind; simpl; first SimpRet).
    eapply advance_SimpBind; simpl.

    (* Use Induction hypothesis *)
    eapply prove_simp_try.  { apply IH1. }
    all: try apply SimpReflexive. simpl.
    SIMP_ret.
    split.
    { (* Goal: Sorted le (h1 :: h1l2) *)
      apply Sorted_cons; first assumption.
      apply Sorted_Hd_cmp; try auto.
      (* Goal: Forall (le h1) h1l2 *)
      rewrite <- H5; apply Forall_app.
      split; apply Sorted_Hd_cmp; auto.
      apply HdRel_cons.
      (* Goal: h1 <= h2 *)
      rewrite lt_repr_repr in branch; only 2-3: auto.
      by apply Z.ltb_ge in branch. }
    { (* (h1  :: t1) ++ h2 :: t2 =p h1 :: h1l2 *)
      rewrite <- app_comm_cons.
      by apply Permutation_skip. }}
Qed.
