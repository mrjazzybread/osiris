From Stdlib Require Import Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_bst.

Open Scope Z.

(* -------------------------------------------------------------------------- *)

(* Boilerplate: reflect the algebraic data type ['a bst]. *)

Inductive tree (A : Type) : Type :=
| Leaf: tree A
| Node: tree A → A → tree A → tree A.

Arguments Leaf {A}.
Arguments Node {A} t1 x t2.

(* Provide a well-founded ordering for wf induction on trees. *)

Fixpoint tree_size {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node t1 _ t2 => 1 + (tree_size t1) + (tree_size t2)
  end.

Definition tlt {A} (t1 t2 : tree A) :=
  (tree_size t1 < tree_size t2)%nat.

#[local] Program Instance tree_wf {A} : WellFounded (tree A) :=
  {| wf_relation := tlt |}.
Next Obligation. intros; unfold tlt; apply wf_inverse_image, lt_wf. Qed.

(* -------------------------------------------------------------------------- *)

(* Boilerplate: fix the encoding scheme for trees. *)

Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      VData "Node" [encode_tree t1; #x; encode_tree t2]
  end.

Local Instance Encode_tree `{Encode A} : Encode (tree A) :=
  { encode := encode_tree }.

Lemma encode_tree_is_encode `{Encode A} :
  ∀ (t : tree A),
  encode_tree t = #t.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_tree_is_encode : encode.

Lemma solve_encode_Leaf `{Encode A} (t : tree A) :
  Leaf = t →
  VConstant "Leaf" = #t.
Proof.
  intros. subst. eauto.
Qed.

Lemma solve_encode_Node `{Encode A} t1 x t2 (t : tree A) vt1 vx vt2 :
  Node t1 x t2 = t →
  vt1 = #t1 →
  vx = #x →
  vt2 = #t2 →
  VData "Node" [vt1; vx; vt2] = #t.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve solve_encode_Leaf solve_encode_Node : encode.


(* -------------------------------------------------------------------------- *)

(* Boilerplate: provide pattern matching lemmas for trees. *)

Definition pLeaf := PConstant "Leaf".

Definition pNode (p1 p2 p3 : syntax.pat) :=
  PData "Node" $ [p1; p2; p3].

Ltac pats :=
  repeat first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons; [ eauto | simpl; intros ]
    ].

Lemma pat_pLeaf `{Encode A} η δ v (t : tree A) (φ : env -> Prop) :
  v = #t →
  (t = Leaf -> φ δ) ->
  pattern η δ pLeaf v φ (t <> Leaf).
Proof.
    intros; subst.
  destruct t.
  { eapply pattern_exn_mono.
    { eapply pat_PData_eq; pats. }
    destruct 1. }
  { eapply pattern_exn_mono.
    { eapply pat_PData_neq; auto. }
    congruence. }
Qed.

Ltac pat_pLeaf :=
  eapply pat_pLeaf; first solve [encode].

Lemma pat_pNode `{Encode A} (η δ : env) (v : val) (t : tree A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : tree A -> Prop) (ψ2 : A -> Prop) (ψ3 : tree A -> Prop)
  :
  v = #t ->
  (∀ (t1 : tree A) (a : A) (t2 : tree A),
      t = Node t1 a t2 →
      pattern η δ p1 #t1
        (λ δ', pattern η δ' p2 #a
            (λ δ', pattern η δ' p3 #t2 φ (ψ3 t2))
            (ψ2 a))
        (ψ1 t1)) ->
  pattern η δ (pNode p1 p2 p3) v φ
    (t = Leaf \/ (exists t1 a t2, t = Node t1 a t2 /\ (ψ1 t1 \/ ψ2 a \/ ψ3 t2))).
Proof.
  intros -> Hcov.
  destruct t; eapply pattern_exn_mono.
  { eapply pat_PData_neq; eauto. }
  { auto. }
  { eapply pat_PData_eq; pats ; eauto. }
  { clear; right; do 3 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNode :=
  eapply pat_pNode; first solve [encode].

Ltac pattern_hook ::=
  first [pat_pLeaf | pat_pNode].


(* -------------------------------------------------------------------------- *)

(* Binary Search Trees *)

Inductive ForallTree {A} (P : A -> Prop) : tree A -> Prop :=
| Forall_Leaf : ForallTree P Leaf
| Forall_Node :
  ∀ l r x,
    ForallTree P l ->
    ForallTree P r ->
    P x ->
    ForallTree P (Node l x r).

Inductive bst : tree Z -> Prop :=
| bst_Leaf : bst Leaf
| bst_Node :
  ∀ l r x,
    bst l ->
    bst r ->
    representable x ->
    ForallTree (fun y => x <? y) l ->
    ForallTree (fun y => ~ (x <? y)) l ->
    bst (Node l x r).


(* -------------------------------------------------------------------------- *)

(* Specifications *)

Fixpoint lookup (x : Z) (t : tree Z) :=
  match t with
  | Leaf => false
  | Node t1 a t2 =>
      if (x <? a) then lookup x t1 else
      if (a <? x) then lookup x t2 else
        x =? a
  end.

Definition insert_spec '((y, t) : (Z * tree Z)) (m : microvx) :=
  bst t ->
  representable y ->
  pure m
    (λ (t' : tree Z),
      ∀ x, lookup x t' = Z.eqb x y || lookup x t) ⊥.

Definition member_spec '((x, t) : (Z * tree Z)) (m : microvx) :=
  bst t ->
  representable x ->
  pure m
    (λ (b : bool), b = lookup x t) ⊥.

(* -------------------------------------------------------------------------- *)

Section Proofs.

Variable η : env.

Lemma insert_mkspec insert (x : Z) (t : tree Z) :
  (lookup_name η "v" = ret #t) ->
  (lookup_name η "x" = ret #x) ->
  (lookup_name η "insert" = ret insert) ->
  bst t ->
  representable x ->
  Spec τ[Z * tree Z] insert
    (λ (x0 : Z * tree Z) (m : microvx),
      tlt x0.2 (x, t).2 →
      insert_spec x0 m) ->
  η ⊢ₚ { EMatch (EPath ["v"]) __branches4
           ensures λ t' : tree Z, ∀ x0 : Z, lookup x0 t' = (x0 =? x) || lookup x0 t }.
Proof.
  intros Hv Hx Hinsert Ht Hrepr IH.
  eapply @pure_eval_match with (A := tree Z).
  { apply pure_eval_path. simpl; rewrite Hv. pure_ret. }
  pure_match.
  - (* Case: [v] matches [Leaf] *)
    apply pure_eval_data.
    eapply (@pure_evals_cons (tree Z)). pure_const.
    eapply (@pure_evals_cons Z).
    apply pure_eval_path. simpl lookup_path; rewrite Hx. pure_ret.
    eapply (@pure_evals_cons (tree Z)). pure_const.
    eapply pure_evals_nil.
    eexists. split; [ encode | ].
    intro z; cbn.
    destruct (z <? x) eqn:Hlt'; first lia.
    destruct (x <? z) eqn:Hlt; first lia.
    by rewrite orb_false_r.
  - (* Case: [v] matches [Node (l, y, r)] *)
    eapply pure_eval_ifthenelse.
    { (* Evaluate the condition [x < y] *)
      inversion Ht; subst.
      eapply pure_eval_EOpLt; try pure_path.
      eapply pure_eval_path. simpl; rewrite Hx; pure_ret.
      assumption. assumption. }

    (* Case: [z < a] *)
    { intros Hlt.
      (* Evalute the recursive call under the data construction. *)
      apply pure_eval_data.
      eapply (@pure_evals_cons (tree Z)).
      eapply (pure_EApp τ[(Z * tree Z)]).
      { eapply pure_eval_path. simpl. rewrite Hinsert. pure_ret. }
      apply pure_eval_pair.
      { eapply pure_eval_path. simpl lookup_path. rewrite Hx. pure_ret.
        pure_path. apply eq_refl. }
      intros [??] Heqp m Hm; fold evals; simpl in Hm.
      apply pair_equal_spec in Heqp as [-> ->].
      eapply pure_ret_mono.
      { apply Hm.
        - red. cbn. lia.
        - by inv Ht.
        - assumption. }
      intros t' Ht'; simpl in Ht'.

      eapply (@pure_evals_cons Z). pure_path.
      eapply (@pure_evals_cons (tree Z)). pure_path.
      eapply pure_evals_nil.

      exists (Node t' a t2); split; try done.
      cbn; setoid_rewrite Ht'; intros x.
      destruct (x <? a) eqn:Hla; first done.
      destruct (a <? x) eqn:Hlt'; try lia.
      assert (x =? z = false) as Heqf by lia. by rewrite Heqf. }

    (* Case: [¬ (z < a)] *)
    { intros Hge.
      eapply pure_eval_ifthenelse.
      { inversion Ht; subst.
        eapply pure_eval_EOpGt; try pure_path.
        eapply pure_eval_path. simpl. rewrite Hx. pure_ret.
        assumption. assumption. }

      (* Subcase: [ ¬ (x < a)] *)
      { intros Hgt.
        apply pure_eval_data.
        eapply (@pure_evals_cons (tree Z)). pure_path.
        eapply (@pure_evals_cons Z). pure_path.
        eapply (@pure_evals_cons (tree Z)).
        eapply (pure_EApp τ[(Z * tree Z)%type]).
        { eapply pure_eval_path. simpl. rewrite Hinsert. pure_ret. }
        { eapply pure_eval_pair.
          { eapply pure_eval_path. simpl. rewrite Hx. pure_ret.
            pure_path. apply eq_refl. } }
        intros [??] Heqp m Hm; simpl in Hm.
        apply pair_equal_spec in Heqp as [-> ->].
        eapply pure_ret_mono.
        { apply Hm.
          - red; cbn; lia.
          - inv Ht; done.
          - assumption. }
        intros t' Ht'; simpl in Ht'.
        apply pure_evals_nil.

        exists (Node t1 a t'); split; try done.
        cbn in *; setoid_rewrite Ht'; clear Ht'; intros x.
        destruct (x <? a) eqn:Hla.
        { assert (x =? z = false) as Heqf by lia.
          rewrite Heqf; done. }
        destruct (a <? x) eqn:Hlx; try lia; done. }

      (* Subcase: [¬ (x > a)] . *)
      intros. simpl in Hge, H. assert (x = a) by lia. subst.
      pure_data. intros x. cbn.
      destruct (x <? a) eqn:Hla.
      { assert (x =? a = false) by lia; rewrite H0; done. }
      destruct (a <? x) eqn : Hla'; try lia.
      assert (x =? a = false) by lia; rewrite H0; done. }
Qed.

Lemma member_mkspec member (x : Z) (t : tree Z) :
  (lookup_name η "v" = ret #t) ->
  (lookup_name η "x" = ret #x) ->
  (lookup_name η "member" = ret member) ->
  bst t ->
  representable x ->
  Spec τ[Z * tree Z] member
    (λ (x0 : Z * tree Z) (m : microvx),
      tlt x0.2 (x, t).2 → member_spec x0 m) ->
  η ⊢ₚ { EMatch (EPath ["v"]) __branches11
           ensures λ b : bool, b = lookup x t }.
Proof.
  intros Hv Hx Hmember Ht Hrepr IH.
  eapply pure_eval_match.
  { eapply pure_eval_path. simpl. rewrite Hv. pure_ret. }
  pure_match.
  (* The case when [v] is a [Leaf] is trivial. *)
  pure_data.

  (* Now we prove that case where [v] is some [Node (l, y, r)] *)
  rename a into y.
  eapply pure_eval_ifthenelse.
  { inversion Ht; subst.
    eapply pure_eval_EOpLt; try pure_path.
    eapply pure_eval_path. simpl. rewrite Hx. pure_ret.
    assumption. assumption. }

  (* Case: [x < y] *)
  { intros Hlt.
    eapply (pure_EApp τ[(Z * tree Z)%type]).
    { eapply pure_eval_path. simpl. rewrite Hmember. pure_ret. }
    { eapply pure_eval_pair.
      eapply pure_eval_path. simpl. rewrite Hx. pure_ret.
      pure_path. apply eq_refl. }
    intros [??] Heqp m Hm; simpl in Hm.
    apply pair_equal_spec in Heqp as [-> ->].
    eapply pure_ret_mono.
    { eapply Hm; cbn.
      - red; cbn; lia.
      - inv Ht; done.
      - assumption. }
    intros ? ->. cbn.
    destruct (z <? y) eqn:Hla; first done; lia. }

  { (* Case: [¬ (x < y)] *)
    intros Hge.
    eapply pure_eval_ifthenelse.
    { inversion Ht; subst.
      eapply pure_eval_EOpGt; try pure_path.
      apply pure_eval_path. simpl. rewrite Hx. pure_ret.
      assumption. assumption. }

    (* Subcase: [x > y] *)
    { intros Hgt.
      eapply (pure_EApp τ[(Z * tree Z)]).
      { eapply pure_eval_path. simpl. rewrite Hmember. pure_ret. }
      { eapply pure_eval_pair.
        eapply pure_eval_path. simpl. rewrite Hx. pure_ret.
        pure_path. apply eq_refl. }
      intros [??] Heqp m Hm.
      apply pair_equal_spec in Heqp as [-> ->].
      eapply pure_ret_mono.
      { eapply Hm; cbn.
        - red; cbn; lia.
        - inv Ht; done.
        - assumption. }
      intros ? ->. cbn.
      assert (z <? y = false) by lia; rewrite H.
      assert (y <? z = true) by lia; rewrite H0. done. }

    (* Subcase : [¬ (x > a)] *)
    { intros Hle. pure_const. simpl in Hge, Hle.
      assert (x = y) as -> by lia.
      cbn. rewrite Z.ltb_irrefl.
      by rewrite Z.eqb_refl. } }
Qed.

End Proofs.

(* -------------------------------------------------------------------------- *)


Lemma Module__spec :
  eval_module stdlib_env __main (λ _, True).
Proof.
  apply module_struct.
  eapply (@structs_letrec τ[(Z * tree Z)]) with
    (P := insert_spec).
  { repeat eexists. }
  { instantiate (1 := λ a b, tlt (snd a) (snd b)).
    apply wf_inverse_image.
    apply tree_wf. }
  { simpl; fold eval; unfold insert_spec at 2.
    intros insert [x t] IH Ht Hrepr.
    apply pure_please_eval.
    eapply @pure_eval_match with (A := (Z * tree Z)%type).
    { pure_path. eapply solve_encode_tuple2; try encode. }
    pure_match.
    eapply insert_mkspec; auto. }

  intros insert Hinsert.
  eapply (@structs_letrec τ[(Z * tree Z)]) with
    (P := member_spec).
  { repeat eexists. }
  { instantiate (1 := λ a b, tlt (snd a) (snd b)).
    apply wf_inverse_image.
    apply tree_wf. }
  { simpl; fold eval; unfold member_spec at 2.
    intros member [x t] IH Ht Hrepr.
    apply pure_please_eval.
    eapply @pure_eval_match with (A := (Z * tree Z)%type).
    { pure_path. eapply solve_encode_tuple2; try encode. }
    pure_match.
    eapply member_mkspec; auto. }

  intros member Hmember.
  finished_struct.

  done.
Qed.
