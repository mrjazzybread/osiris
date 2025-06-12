Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_bst.

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

Definition insert_spec insert :=
  ∀ (y : Z) (t : tree Z),
    bst t ->
    representable y ->
    pure
      (call insert #(y, t))
      (λ (t' : tree Z),
        ∀ x, lookup x t' = Z.eqb x y || lookup x t) ⊥.

Definition member_spec member :=
  ∀ (x : Z) (t : tree Z),
    bst t ->
    representable x ->
    pure
      (call member #(x, t))
      (λ (b : bool), b = lookup x t) ⊥.

(* -------------------------------------------------------------------------- *)

(* Proof *)

Lemma Insert_spec :
  insert_spec
    (VCloRec stdlib_env
       [RecBinding
          "insert"
          (AnonFunction __branches5)]
       "insert").
Proof.
  unfold insert_spec.
  intros z t Hbst Hrep.

  (* We need to massage the postcondition so we can generalize the argument for *)
(*     the recursive call. *)
  change
    (λ t' : tree Z,
       ∀ x : Z,
        lookup x t' = (Z.eqb x z || lookup x t))
    with
    ((λ '(z', t'') (t' : tree Z),
       ∀ x : Z,
        lookup x t' = (Z.eqb x z' || lookup x t'')) (z, t)).

  (* Recursion, with decreasing depth of tree. Generalize the hypothesis *)
(*     that the tree is a bst. *)
  recursion { measure snd }
    ∀ (z, t)
    gen (fun x => bst x.2 /\ representable x.1); first done.

  clear z t Hbst Hrep; intros insert [z t] IH [Hbst Hrep] ;
    simpl in *; fold eval.

  (* Match to destruct the argument tuple *)
  eapply pure_eval_match. { pure_path. }

  (* Match on [v] *)
  pure_match.
  eapply pure_eval_match. { pure_path. }

  pure_match.

  (* Case: [v] matches [Leaf] *)
  { pure_data. cbn. intro.
    destruct (x <? z) eqn:Hlt; first lia.
    destruct (z <? x) eqn:Hlt'; first lia.
    by rewrite orb_false_r. }

  (* If-then-else *)
  eapply pure_eval_ifthenelse.
  { inversion Hbst; subst.
    eapply pure_eval_EOpLt; try pure_path.
    all: done. }

  (* z < a *)
  { intros Hlt. apply pure_eval_data.
    eapply (@pure_evals_cons (tree Z)).
    eapply (@pure_eval_app (Z * tree Z)).
    { pure_path. }
    { eapply (pure_eval_pair _ _ _ (fun '(x,y) => x = z /\ y = t1)).
      pure_path. pure_path. }
    intros ? [] -> [-> ->].
    eapply pure_ret_mono.
    { eapply IH; cbn.
      - red; cbn; lia.
      - inv Hbst; done. }

    intros.
    eapply (@pure_evals_cons Z). pure_path.
    eapply (@pure_evals_cons (tree Z)). pure_path.
    eapply pure_evals_nil.

    exists (Node a0 a t2); split; try done.
    cbn in *; setoid_rewrite H; intros.
    destruct (x <? a) eqn:Hla; first done.
    destruct (a <? x) eqn:Hlt'; try lia.
    assert (x =? z = false) by lia. rewrite H0; done. }

  (* not (z < a) *)
  intros Hlt.

  eapply pure_eval_ifthenelse.
  { inversion Hbst; subst.
    eapply pure_eval_EOpGt; try pure_path.
    all: done. }

  (* z > a *)
  { intros Hgt.
    apply pure_eval_data.
    eapply (@pure_evals_cons (tree Z)). pure_path.
    eapply (@pure_evals_cons Z). pure_path.
    eapply (@pure_evals_cons (tree Z)).
    eapply (@pure_eval_app (Z * tree Z)).
    { pure_path. }
    { eapply (pure_eval_pair _ _ _ (fun '(x,y) => x = z /\ y = t2)).
      pure_path. pure_path. }
    intros ? [] -> [-> ->].
    eapply pure_ret_mono.
    { eapply IH; cbn.
      - red; cbn; lia.
      - inv Hbst; done. }

    intros; eapply pure_evals_nil.

    exists (Node t1 a a0); split; try done.
    cbn in *; setoid_rewrite H; clear H; intros.
    destruct (x <? a) eqn:Hla.
    { assert (x =? z = false) by lia. rewrite H; done. }
    destruct (a <? x) eqn:Hlx; try lia; done. }

  (* Last branch. *)
  intros. assert (z = a) by lia. subst.
  pure_data. intros. cbn.
  destruct (x <? a) eqn:Hla.
  { assert (x =? a = false) by lia; rewrite H0; done. }
  destruct (a <? x) eqn : Hla'; try lia.
  assert (x =? a = false) by lia; rewrite H0; done.
Qed.

Lemma Member_spec insert :
  insert_spec insert ->
  member_spec
    (VCloRec
       ("insert" ~> insert; stdlib_env)
       [RecBinding "member" (AnonFunction __branches12)]
       "member").
Proof.
  unfold member_spec.
  intros Hinsert z t Hbst Hrep.

  (* We need to massage the postcondition so we can generalize the argument for *)
(*     the recursive call. *)
  change
    (λ (b : bool), b = lookup z t) with
    ((λ '(z', t'') (b : bool), b = lookup z' t'') (z, t)).

  (* Recursion, with decreasing depth of tree. Generalize the hypothesis
     that the tree is a bst. *)
  recursion { measure snd }
    ∀ (z, t)
    gen (fun x => bst x.2 /\ representable x.1);
    first done.

  clear z t Hbst Hrep; intros member [z t] IH [Hbst Hrep];
    simpl in *; fold eval.

  (* Match to destruct the argument tuple *)
  eapply pure_eval_match. { pure_path. }

  (* Match on [v] *)
  pure_match.
  eapply pure_eval_match. { pure_path. }

  pure_match; first pure_data.

  (* If-then-else *)
  eapply pure_eval_ifthenelse.
  { inversion Hbst; subst.
    eapply pure_eval_EOpLt; try pure_path.
    all: done. }

  (* z < a *)
  { intros Hlt.
    eapply (@pure_eval_app (Z * tree Z)).
    { pure_path. }
    { eapply (pure_eval_pair _ _ _ (fun '(x,y) => x = z /\ y = t1)).
      pure_path. pure_path. }
    intros ? [] -> [-> ->].
    eapply pure_ret_mono.
    { eapply IH; cbn.
      - red; cbn; lia.
      - inv Hbst; done. }
    intros ? ->. cbn. destruct (z <? a) eqn:Hla; first done; lia. }

  (* not (z < a) *)
  intros Hlt.

  eapply pure_eval_ifthenelse.
  { inversion Hbst; subst.
    eapply pure_eval_EOpGt; try pure_path.
    all: done. }

  (* z > a *)
  { intros Hgt.
    eapply (@pure_eval_app (Z * tree Z)).
    { pure_path. }
    { eapply (pure_eval_pair _ _ _ (fun '(x,y) => x = z /\ y = t2)).
      pure_path. pure_path. }
    intros ? [] -> [-> ->].
    eapply pure_ret_mono.
    { eapply IH; cbn.
      - red; cbn; lia.
      - inv Hbst; done. }

    intros ? ->. cbn.
    assert (z <? a = false) by lia; rewrite H.
    assert (a <? z = true) by lia; rewrite H0. done. }

  (* not z > a *)
  { intros Hgt. pure_data. cbn.
    assert (z <? a = false /\ a <? z = false /\ z =? a = true) by lia.
    destruct H as (->&->&->); tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

Lemma BstSpec :
  toplevel __main
    (env_has_pspecs [("insert", insert_spec); ("member", member_spec)]).
Proof.
  apply module_struct.
  next_item.
  { apply Insert_spec. }
  intros [??] (insert & Hinsert & -> & ->).
  next_item with member_spec.
  { eapply Member_spec. done. }
  intros [??] (lookup & Hlookup & -> & ->).
  finished_struct.
  simpl. repeat split; auto.
Qed.
