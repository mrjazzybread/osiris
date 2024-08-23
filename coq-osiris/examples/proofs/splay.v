Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_splay.

(* -------------------------------------------------------------------------- *)

(* WIP *)

Local Ltac unpack :=
  repeat (lazymatch goal with [ h: _ ∧ _ |- _ ] => destruct h end).

(* Notation "'<closure>'" := (VCloRec _ _ _) (only printing). *)
(* Notation "'<closure>'" := (VClo _ _) (only printing). *)
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (cons x _ (.. (cons z _ nil) ..))
 (only printing).

(* -------------------------------------------------------------------------- *)

(* Boilerplate: reflect the algebraic data type ['a tree]. *)

Local Transparent encode.

Inductive tree (A : Type) : Type :=
| Leaf: tree A
| Node: tree A → A → tree A → tree A.

Arguments Leaf {A}.
Arguments Node {A} t1 x t2.

Fixpoint tree_depth {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node t1 _ t2 => 1 + (tree_depth t1) + (tree_depth t2)
  end.

Definition tlt {A} (t1 t2 : tree A) :=
  (tree_depth t1 < tree_depth t2)%nat.

Lemma tlt_wf {A} :
  well_founded (@tlt A).
Proof.
  unfold tlt. eapply wf_inverse_image. eapply lt_wf.
Qed.

Lemma zlookup_wf {A B C} :
  well_founded (
      fun (t1 t2 : tree A * B * C) =>
        @tlt A
          (match t1 with
           | (tree1,_,_) => tree1
           end)
          (match t2 with
           | (tree2,_,_) => tree2
           end)).
Proof.
  apply wf_inverse_image. apply tlt_wf.
Qed.

Local Hint Extern 1 (tree_depth _ < tree_depth _)%nat => (simpl; lia) : pure_specs.

Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      VData "Node" (VTuple3 (encode_tree t1) #x (encode_tree t2))
  end.

Local Instance Encode_tree `{Encode A} : Encode (tree A) :=
  { encode := encode_tree }.

Local Instance CRel3Node `{Encode A} :
  CRel3 (tree A) "Node" Node := {}.

Local Instance CRel1Some `{Encode A} :
  CRel1 (option A) "Some" Some := {}.

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
  VData "Node" (VTuple3 vt1 vx vt2) = #t.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve solve_encode_Leaf solve_encode_Node : encode.

Definition pLeaf := PConstant "Leaf".

Lemma pat_pLeaf `{Encode A} η v (t : tree A) (φ : env -> Prop) :
  v = #t →
  (t = Leaf -> φ η) ->
  pattern η pLeaf v φ (t <> Leaf).
Proof.
  intros; subst.
  destruct t.
  { eapply pat_consequence_psi.
    { eapply pat_PData_eq; pat_PTuple; pats. }
    destruct 1. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; auto. }
    congruence. }
Qed.

Ltac pat_pLeaf :=
  eapply pat_pLeaf; first solve [encode].

Definition pNode (p1 p2 p3 : syntax.pat) :=
  PData "Node" (PTuple [p1; p2; p3]).

Lemma pat_pNode `{Encode A} (η : env) (v : val) (t : tree A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : tree A -> Prop) (ψ2 : A -> Prop) (ψ3 : tree A -> Prop)
  :
  v = #t ->
  (∀ (t1 : tree A) (a : A) (t2 : tree A),
      t = Node t1 a t2 →
      pattern η p1 #t1
        (λ η', pattern η' p2 #a
            (λ η', pattern η' p3 #t2 φ (ψ3 t2))
            (ψ2 a))
        (ψ1 t1)) ->
  pattern η (pNode p1 p2 p3) v φ
    (t = Leaf \/ (exists t1 a t2, t = Node t1 a t2 /\ (ψ1 t1 \/ ψ2 a \/ ψ3 t2))).
Proof.
  intros -> Hcov.
  destruct t; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { auto. }
  { eapply pat_PData_eq; pat_PTuple; pats; eauto. }
  { clear; right; do 3 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNode :=
  eapply pat_pNode; first solve [encode].

(* -------------------------------------------------------------------------- *)

(* Boilerplate: reflect the algebraic data type ['a zipper]. *)

Inductive zipper (A : Type) : Type :=
| Root  : zipper A
| NodeL : zipper A → A → tree A → zipper A
| NodeR : tree A → A → zipper A → zipper A.

Arguments Root  {A}.
Arguments NodeL {A} z1 x t2.
Arguments NodeR {A} t1 x z2.

Fixpoint encode_zipper `{Encode A} (z : zipper A) : val :=
  match z with
  | Root =>
      VConstant "Root"
  | NodeL z1 x t2 =>
      VData "NodeL" (VTuple3 (encode_zipper z1) #x #t2)
  | NodeR t1 x z2 =>
      VData "NodeR" (VTuple3 #t1 #x (encode_zipper z2))
  end.

Local Instance Encode_zipper `{Encode A} : Encode (zipper A) :=
  { encode := encode_zipper }.

Local Instance CRel3NodeL `{Encode A} :
  CRel3 (zipper A) "NodeL" NodeL := {}.

Global Instance CRel3NodeR `{Encode A} :
  CRel3 (zipper A) "NodeR" NodeR := {}.

Lemma encode_zipper_is_encode `{Encode A} :
  ∀ (z : zipper A),
  encode_zipper z = #z.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_zipper_is_encode : encode.

Lemma solve_encode_Root `{Encode A} (z : zipper A) :
  Root = z →
  VConstant "Root" = #z.
Proof.
  intros. subst. eauto.
Qed.

Lemma solve_encode_NodeL `{Encode A} z1 x t2 (z : zipper A) vz1 vx vt2 :
  NodeL z1 x t2 = z →
  vz1 = #z1 →
  vx = #x →
  vt2 = #t2 →
  VData "NodeL" (VTuple3 vz1 vx vt2) = #z.
Proof.
  intros. subst. eauto.
Qed.

Lemma solve_encode_NodeR `{Encode A} t1 x z2 (z : zipper A) vt1 vx vz2 :
  NodeR t1 x z2 = z →
  vt1 = #t1 →
  vx = #x →
  vz2 = #z2 →
  VData "NodeR" (VTuple3 vt1 vx vz2) = #z.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve
  solve_encode_Root solve_encode_NodeL solve_encode_NodeR
  : encode.

Definition pRoot := PConstant "Root".

Lemma pat_pRoot `{Encode A} η v (z : zipper A) (φ : env -> Prop) :
  v = #z →
  (z = Root -> φ η) ->
  pattern η pRoot v φ (z <> Root).
Proof.
  intros; subst.
  destruct z.
  { eapply pat_consequence_psi.
    { eapply pat_PData_eq; pat_PTuple; pats. }
    destruct 1. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; auto. }
    congruence. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; auto. }
    congruence. }
Qed.

Ltac pat_pRoot :=
  eapply pat_pRoot; first solve [encode].

Definition pNodeL (p1 p2 p3 : syntax.pat) :=
  PData "NodeL" (PTuple [p1; p2; p3]).

Lemma pat_pNodeL `{Encode A} (η : env) (v : val) (z : zipper A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : zipper A -> Prop) (ψ2 : A -> Prop) (ψ3 : tree A -> Prop)
  :
  v = #z ->
  (∀ (z' : zipper A) (a : A) (t : tree A),
      z = NodeL z' a t →
      pattern η p1 #z' (λ η', pattern η' p2 #a (λ η', pattern η' p3 #t φ (ψ3 t)) (ψ2 a)) (ψ1 z')) ->
  pattern η (pNodeL p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeR a1 a2 a3) \/
                                 (exists z' a t, z = NodeL z' a t /\ (ψ1 z' \/ ψ2 a \/ ψ3 t))).
Proof.
  intros -> Hcov.
  destruct z; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { auto. }
  { eapply pat_PData_eq; pat_PTuple; pats; eauto. }
  { clear; do 2 right; do 3 eexists; split; [ reflexivity | tauto ]. }
  { eapply pat_PData_neq; eauto. }
  { right; left; eauto. }
Qed.

Ltac pat_pNodeL :=
  eapply pat_pNodeL; first solve [encode].

Definition pNodeR (p1 p2 p3 : syntax.pat) :=
  PData "NodeR" (PTuple [p1; p2; p3]).

Lemma pat_pNodeR `{Encode A} (η : env) (v : val) (z : zipper A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : tree A -> Prop) (ψ2 : A -> Prop) (ψ3 : zipper A -> Prop)
  :
  v = #z ->
  (∀ (t : tree A) (a : A) (z' : zipper A),
      z = NodeR t a z' →
      pattern η p1 #t (λ η', pattern η' p2 #a (λ η', pattern η' p3 #z' φ (ψ3 z')) (ψ2 a)) (ψ1 t)) ->
  pattern η (pNodeR p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeL a1 a2 a3) \/
                                 (exists t a z', z = NodeR t a z' /\ (ψ1 t \/ ψ2 a \/ ψ3 z'))).
Proof.
  intros -> Hcov.
  destruct z; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { auto. }
  { eapply pat_PData_neq; eauto. }
  { right; left; eauto. }
  { eapply pat_PData_eq; pat_PTuple; pats. }
  { clear; right; right; do 3 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNodeR :=
  eapply pat_pNodeR; first solve [encode].

Local Opaque encode.

(* -------------------------------------------------------------------------- *)

(* The depth of a zipper. *)

Fixpoint zipper_depth {A} (z : zipper A) : nat :=
  match z with
  | Root =>
      0
  | NodeL z1 x t2 =>
      1 + zipper_depth z1
  | NodeR t1 x z2 =>
      1 + zipper_depth z2
  end.

Definition zlt {A} (z1 z2 : zipper A) :=
  (zipper_depth z1 < zipper_depth z2)%nat.

Lemma zlt_wf {A} :
  well_founded (@zlt A).
Proof.
  unfold zlt. eapply wf_inverse_image. eapply lt_wf.
Qed.

Lemma splay_wf {A B C D} :
  well_founded (
      fun (t1 t2 : B * C * D * zipper A) =>
        @zlt A
          (match t1 with
           | (_,_,_,ctx1) => ctx1
           end)
          (match t2 with
           | (_,_,_,ctx2) => ctx2
           end)).
Proof.
  apply wf_inverse_image. apply zlt_wf.
Qed.

Local Hint Extern 1 (zipper_depth _ < zipper_depth _)%nat => (simpl; lia) : pure_specs.

(* -------------------------------------------------------------------------- *)

(* Filling a zipper with a tree. *)

Fixpoint fill {A} (z : zipper A) (t : tree A) :=
  match z with
  | Root =>
      t
  | NodeL z1 x t2 =>
      fill z1 (Node t x t2)
  | NodeR t1 x z2 =>
      fill z2 (Node t1 x t)
  end.

(* -------------------------------------------------------------------------- *)

(* The fringe of a tree. *)

Fixpoint fringe {A} (t : tree A) : list A :=
  match t with
  | Leaf =>
      []
  | Node l x r =>
      fringe l ++ [x] ++ fringe r
  end.

(* The left and right fringes of a zipper. *)

Fixpoint lfringe {A} (z : zipper A) : list A :=
  match z with
  | Root =>
      []
  | NodeL z1 x t2 =>
      lfringe z1
  | NodeR t1 x z2 =>
      lfringe z2 ++ fringe t1 ++ [x]
  end.

Fixpoint rfringe {A} (z : zipper A) : list A :=
  match z with
  | Root =>
      []
  | NodeL z1 x t2 =>
      [x] ++ fringe t2 ++ rfringe z1
  | NodeR t1 x z2 =>
      rfringe z2
  end.

(* The fringe of [fill z t] can be characterized as follows. *)

Lemma fringe_fill {A} : ∀ (z : zipper A) (t : tree A),
  fringe (fill z t) = lfringe z ++ fringe t ++ rfringe z.
Proof.
  induction z; simpl; intros.
  + rewrite app_nil_r. eauto.
  + rewrite IHz. simpl. rewrite <- !app_assoc. eauto.
  + rewrite IHz. simpl. rewrite <- !app_assoc. eauto.
Qed.

(* This tactic proves an equality between two fringes. *)

#[export] Hint Rewrite @fringe_fill @app_nil_l @app_nil_r @app_assoc : fringe.

Local Ltac prove_same_fringe :=
  rewrite -> ?fringe_fill;
  simpl fringe ;
  simpl lfringe ;
  simpl rfringe ;
  rewrite ?app_nil_l ;
  rewrite ?app_nil_r ;
  repeat (rewrite <- ?app_comm_cons ;
          rewrite <- ?app_assoc) ;
  eauto.

(* -------------------------------------------------------------------------- *)

(* The binary-search-tree property. *)

(* Quite strikingly, the binary-search-tree (BST) property can be defined
   not as a property of a tree, but as a property of its fringe: a tree is
   a BST if and only if its fringe is sorted. *)

(* This definition makes it extremely easy to recognize that rotations
   preserve the BST property: in fact, they preserve the fringe of the
   tree. The function [splay], for instance, does not even require that
   the tree be a BST; it simply promises to preserve its fringe. *)

Section BST.

Context {A : Type}.
Context (lt : A → A → Prop).
Context {Tlt : Transitive lt}.

(* A tree is a BST if and only if its fringe is sorted. *)

Definition bst (t : tree A) :=
  Sorted lt (fringe t).

Notation "xs '≺' ys" := (pairwise lt xs ys) (at level 80).

(* The following lemmas provide an alternative characterization of binary
   search trees. If the predicate [bst t] was inductively defined, then
   these two statements would correspond the two constructors (and their
   inversion principle). *)

Lemma bst_Leaf_iff :
  bst Leaf ↔ True.
Proof.
  unfold bst. simpl fringe. rewrite Sorted_empty_iff. auto.
Qed.

Lemma cons_is_app x (l1 : list A) : x :: l1 = [x] ++ l1. Proof. auto. Qed.

Lemma bst_Node_iff l x r :
  bst (Node l x r) ↔
  bst l ∧ bst r ∧ fringe l ≺ [x] ∧ [x] ≺ fringe r.
Proof.
  unfold bst. simpl fringe.
  repeat (first [ rewrite Sorted_app_iff
                | rewrite Sorted_singleton_iff
                | rewrite cons_is_app; rewrite Sorted_app_iff
                | rewrite pairwise_app_right_iff]).
  pose proof (@pairwise_transitive_singleton _ lt _ (fringe l) x (fringe r)).
  tauto.
Qed.

End BST.

Ltac destruct_bst_Node :=
  lazymatch goal with h: bst _ (Node _ _ _) |- _ =>
    rewrite bst_Node_iff in h; try typeclasses eauto;
    destruct h as (?&?&?&?)
  end.

(* -------------------------------------------------------------------------- *)

Open Scope Z.

(* TODO move these lemmas *)
Lemma ltb_true (n m : Z) :
  n < m →
  (n <? m) = true.
Proof.
  intros. rewrite Z.ltb_lt. assumption.
Qed.

Lemma ltb_false (n m : Z) :
  m ≤ n →
  (n <? m) = false.
Proof.
  intros. rewrite Z.ltb_ge. lia.
Qed.

Ltac pattern_hook ::=
  first
    [ pat_pRoot; intros
    | pat_pNodeL; intros
    | pat_pNodeR; intros
    | pat_pLeaf; intros
    | pat_pNode; intros
    ].

(* Specification for each function *)
Definition splay_spec :=
  fun splay =>
    ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
    pure
      (call splay #(l, x, r, ctx))
      ##(λ t', fringe t' = fringe (fill ctx (Node l x r))) ⊥.

Definition splay_leaf_spec :=
  fun (splay_leaf : val) =>
    ∀ A `(_ : Encode A) (ctx : zipper A),
    pure
      (call splay_leaf #ctx)
      ##(λ t', fringe t' = fringe (fill ctx Leaf)) ⊥.

Definition zlookup_spec :=
  fun (zlookup : val) =>
    ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      pure
        (call zlookup #(t, x, ctx))
        ##(λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)) ⊥.

(* -------------------------------------------------------------------------- *)

(* Specification of [splay]. *)

Section splay_proofs.

(* Top-level environment of [splay]. *)

Lemma Splay_spec :
  splay_spec
    (VCloRec stdlib_env [RecBinding "splay" (AnonFunction __branches1)] "splay").
Proof.
  unfold splay_spec.
  intros A H ctx l x r.
  (* TODO: Add the following pattern into pure_rec_call *)
  remember (l, x, r, ctx) as t.
  rewrite (surjective_pairing t) in Heqt.
  rewrite (surjective_pairing t.1) in Heqt.
  rewrite (surjective_pairing t.1.1) in Heqt.
  apply pair_eq in Heqt as [Heqt <-].
  apply pair_eq in Heqt as [Heqt <-].
  apply pair_eq in Heqt as [<- <-].

  change
    (λ t' : tree A, fringe t' = fringe (fill t.2 (Node t.1.1.1 t.1.1.2 t.1.2)))
    with
    ((fun t t' => fringe t' = fringe (fill t.2 (Node t.1.1.1 t.1.1.2 t.1.2))) t).

  eapply pure_rec_call with (P := fun a x => a = x). apply splay_wf. reflexivity.
  intros splay [[[l x] r] ctx] IH a ->; simpl.

  (* Match to destruct the argument tuple *)
  eapply pure_eval_match. { pure_path. reflexivity. }
  pure_match.

  (* Match on [ctx] *)
  eapply pure_eval_match. { pure_path. reflexivity. }
  pure_match; abstract_env. (* Was very slow, now just slow *)

  (* Case: [ctx] matches [Root] *)
  { pure_data.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeL (Root, y, ry)] *)
  { pure_data.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeL (NodeL (up, z, rz), y, ry)] *)
  { eapply pure_eval_app. pure_path.
    eapply pure_eval_quadruple. pure_path. pure_path. pure_data. pure_path.
    pure_call.
    { specialize (IH (l, x, Node r a (Node t0 a0 t1), z'0)).
      eapply IH; unfold zlt; subst; auto with arith. }
    simpl; intros ? ->.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeL (NodeR (lz, z, up), y, ry)] *)
  { eapply pure_eval_app. pure_path.
    eapply pure_eval_quadruple. pure_data. pure_path. pure_data. pure_path.
    pure_call.
    { specialize (IH (Node t1 a0 l, x, Node r a t0, z'0)).
      eapply IH; unfold zlt; subst; auto with arith. }
    intros ? ->.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, Root)] *)
  { pure_data.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, NodeL (up, z, rz))] *)
  { eapply pure_eval_app.
    pure_path.
    eapply pure_eval_quadruple. pure_data. pure_path. pure_data. pure_path.
    pure_call.
    { specialize (IH (Node t0 a l, x, Node r a0 t1, z'0)).
      eapply IH; unfold zlt; subst; auto with arith. }
    intros ? ->.
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, NodeR (lz, z, up))] *)
  { eapply pure_eval_app. pure_path.
    eapply pure_eval_quadruple. pure_data. pure_path. pure_path. pure_path.
    pure_call.
    { specialize (IH (Node (Node t1 a0 t0) a l, x, r, z'0)).
      eapply IH; unfold zlt; subst; auto with arith. }
    intros ? ->.
    prove_same_fringe. }
Qed.


Lemma Splay_leaf_spec splay :
  splay_spec splay ->
  splay_leaf_spec
    (VClo ("splay" ~> splay; stdlib_env) __fun4).
Proof.
  unfold splay_leaf_spec.
  intros Hsplay A H ctx.
  pure_enter.
  (* Match on [ctx] *)
  eapply pure_eval_match. { pure_path; reflexivity. }
  pure_match.

  (* Case: [ctx] matches [Root] *)
  { pure_const. reflexivity. }

  (* Case: [ctx] matches [NodeL (up, x, r)] *)
  { eapply pure_eval_app. pure_path. (* What does [pure_path] do? *)
    eapply pure_eval_quadruple.
    eapply pure_eval_const.
    apply (@solve_encode_Leaf A); reflexivity. (* Todo: weird *)
    pure_path. pure_path. pure_path.
    unfold splay_spec in Hsplay.
    specialize (Hsplay _ _ z' Leaf a t).
    apply Hsplay. }

  (* Case: [ctx] matches [NodeR (l, x, up)] *)
  { eapply pure_eval_app. pure_path. eapply pure_eval_quadruple.
    pure_path. pure_path. eapply pure_eval_const.
    apply (@solve_encode_Leaf A). reflexivity.
    pure_path.
    specialize (Hsplay _ _ z' t a Leaf).
    apply Hsplay. }
Qed.

Lemma Zlookup_spec splay splay_leaf :
  splay_leaf_spec splay_leaf ->
  splay_spec splay ->
  zlookup_spec
    (VCloRec ("splay_leaf" ~> splay_leaf;
              "splay" ~> splay;
              stdlib_env)
       [RecBinding "zlookup" (AnonFunction __branches11)]
       "zlookup").
Proof.
  unfold zlookup_spec.
  intros Hsplay_leaf Hsplay A H le ? Hcompare t x ctx Hbst.
  remember (t, x, ctx) as tup eqn:Heqtup.
  rewrite (surjective_pairing tup) in Heqtup.
  rewrite (surjective_pairing tup.1) in Heqtup.
  apply pair_eq in Heqtup as [Heqtup <-].
  apply pair_eq in Heqtup as [<- <-].
  match goal with
  | |- pure _ ##?φ _ =>
      let h := fresh in
      set (h := φ);
      pattern tup in h;
      subst h
  end.

  eapply pure_rec_call with (a := tup) (x := tup) (P := fun a x => a = x /\ _ x.1.1).
  { apply zlookup_wf. }
  { split; [ reflexivity | exact Hbst ]. }
  clear Hbst tup.
  intros zlookup [[t x] ctx] IH ? [-> Hpre]. simpl in *. fold eval.

  (* Match on tuple argument *)
  eapply pure_eval_match. { pure_path. reflexivity. }
  pure_match.
  (* Match on [t] *)
  eapply pure_eval_match. { pure_path. reflexivity. }
  pure_match.

  (* Case: [t] matches [Leaf] *)
  { eapply pure_eval_pair. pure_const.
    eapply pure_eval_app. pure_path. pure_path.
    pure_call.
    split; [ intros | auto]; apply not_elem_of_nil. }

  (* Case: [t] matches [Node (l, y, r)] *)
  { destruct_bst_Node.
    eapply pure_eval_let.
    { (* Evaluate rhs of [let c = ..] *)
      eapply pure_eval_app2.
      { pure_path; reflexivity. }
      { pure_path; reflexivity. }
      { pure_path; reflexivity. }
      apply Hcompare. }
    (* Evaluate continuation expression after let *)
    intros c (? & Hlt & Heq & Hgt).
    eapply pure_eval_ifthenelse.
    { (* Evalute comparison operation *)
      eapply pure_eval_EOpLt.
      { pure_path. reflexivity. }
      { eapply pure_eval_int. reflexivity. }
      { assumption. }
      { representable. } }

    { (* Case: [c < 0] *)
      intro Clt0.
      eapply pure_eval_app. pure_path.
      eapply pure_eval_triple. pure_path. pure_path. pure_data.
      pure_call.
      { eapply IH with (y := (t1, x, NodeL ctx a t2));
          unfold tlt, tree_depth; auto with arith. }
      intros [oy t'] [??]; simpl in *.
      split; [ | assumption ].
      - apply bst_member_left; representable. }

    { (* Case: [c >= 0] *)
      intros Cge0.
      eapply pure_eval_ifthenelse.
      { (* Evaluate second comparison operation *)
        eapply pure_eval_EOpGt.
        { pure_path. reflexivity. }
        { eapply pure_eval_int. reflexivity. }
        { assumption. }
        { representable. } }

      { (* Subcase: [c > 0] *)
        intros Cgt0.
        eapply pure_eval_app. pure_path.
        eapply pure_eval_triple. pure_path. pure_path. pure_data.
        pure_call.
        { eapply IH with (y := (t2, x, NodeR t1 a ctx)).
          { unfold tlt, tree_depth; lia. }
          { split; [ reflexivity | auto ]. } }
        intros [oy t'] [??]; simpl in *.
        split.
        - apply bst_member_right; representable.
          apply Hgt; apply Z.gt_lt; auto.
        - assumption. }

      { (* Subcase: [c <= 0] *)
        intros Cle0.
        (* Deduce [c = 0] *)
        eapply pure_eval_pair. pure_data.
        eapply pure_eval_app. pure_path.
        eapply pure_eval_quadruple. pure_path. pure_path. pure_path. pure_path.
        pure_call.
        intros. split; [ split | ].
        - apply Heq. lia.
        - apply elem_of_app; right; apply elem_of_cons; left; reflexivity.
        - assumption. } } }
Qed.

Lemma Splay__spec:
  toplevel __main
    (env_has_pspecs [("splay", splay_spec);
                            ("splay_leaf", splay_leaf_spec);
                            ("zlookup", zlookup_spec)]).
Proof.
  apply module_struct.
  next_item.
  { apply Splay_spec. }
  intros [??] (splay & Hsplay & -> & ->).
  next_item with splay_leaf_spec.
  { pure_simp.
    apply Splay_leaf_spec; assumption. }
  intros [??] (splay_leaf & Hsplay_leaf & -> & ->).
  next_item.
  { apply Zlookup_spec; assumption. }
  intros [??] (zlookup & Hzlookup & -> & ->).
  next_item.
  { pure_simp. apply eq_refl. }
  intros [??] (lookup & Hlookup & -> & ->).
  finished_struct.
  simpl. repeat split; auto.
Qed.

End splay_proofs.
