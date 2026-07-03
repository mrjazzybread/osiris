From osiris.utils Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.

From osiris.examples Require Import og_splay.

(* The algebraic data types of ['a tree] and ['a zipper]. *)

Inductive tree (A : Type) : Type :=
| Leaf: tree A
| Node: tree A → A → tree A → tree A.
Arguments Leaf {A}.
Arguments Node {A} t1 x t2.

Inductive zipper (A : Type) : Type :=
| Root  : zipper A
| NodeL : zipper A → A → tree A → zipper A
| NodeR : tree A → A → zipper A → zipper A.
Arguments Root  {A}.
Arguments NodeL {A} z1 x t2.
Arguments NodeR {A} t1 x z2.

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

(* -------------------------------------------------------------------------- *)

(* Well-foundedness *)

From Stdlib Require Import Wellfounded.Inverse_Image.

(* The size of a tree. *)

Fixpoint tree_size {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node t1 _ t2 => 1 + (tree_size t1) + (tree_size t2)
  end.

(* Well-founded relation on tree size. *)

Definition tlt {A} (t1 t2 : tree A) :=
  (tree_size t1 < tree_size t2)%nat.

#[local] Program Instance tree_wf {A} : WellFounded (tree A) :=
  {| wf_relation := tlt |}.
Next Obligation. intros; unfold tlt; apply wf_inverse_image, lt_wf. Qed.

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

(* Well-founded relation on zipper depth. *)

Definition zlt {A} (z1 z2 : zipper A) :=
  (zipper_depth z1 < zipper_depth z2)%nat.

#[local] Program Instance zipper_wf {A} : WellFounded (zipper A) :=
  {| wf_relation := zlt |}.
Next Obligation. constructor; unfold zlt; apply wf_inverse_image, lt_wf. Qed.

(* -------------------------------------------------------------------------- *)

Section encode.
Local Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      VData "Node" [encode_tree t1; #x; encode_tree t2]
  end.

#[global] Instance Encode_tree `{Encode A} : Encode (tree A) :=
  { encode' := encode_tree }.

Global Instance data_node `{Encode A} : Data "Node" τ[tree A; A; tree A] (tree A) :=
  { ctor_apply := λ '(t1, (x, t2)), Node t1 x t2;
    ctor_encode := λ '(t1, (x, t2)), eq_refl }.

Local Fixpoint encode_zipper `{Encode A} (z : zipper A) : val :=
  let (c, l) :=
    (match z with
    | Root =>
        ("Root", nil)
    | NodeL z1 x t2 =>
        ("NodeL", [encode_zipper z1; #x; #t2])
    | NodeR t1 x z2 =>
        ("NodeR", [ #t1; #x; encode_zipper z2])
    end)
  in
  VData c l.

Definition zipper_tag `{Encode A} (z : zipper A) : string :=
  match z with
  | Root =>
      "Root"
  | NodeL z1 x t2 =>
      "NodeL"
  | NodeR t1 x z2 =>
      "NodeR"
  end.

Definition zipper_data `{Encode A} (z : zipper A) : list val :=
  match z with
  | Root =>
      nil
  | NodeL z1 x t2 =>
      [encode_zipper z1; #x; #t2]
  | NodeR t1 x z2 =>
      [ #t1; #x; encode_zipper z2]
  end.

Lemma unfold_encode_zipper `{Encode A} (z : zipper A) :
  encode_zipper z = VData (zipper_tag z) (zipper_data z).
Proof.
  induction z; eauto.
Qed.

Definition tree_tag `{Encode A} (z : tree A) : string :=
  match z with
  | Node _ _ _ =>
      "Node"
  | Leaf =>
      "Leaf"
  end.

Definition tree_data `{Encode A} (z : tree A) : list val :=
  match z with
  | Leaf => nil
  | Node z1 x t2 => [ #z1; #x; #t2]
  end.

Lemma unfold_encode_tree `{Encode A} (t : tree A) :
  encode_tree t = VData (tree_tag t) (tree_data t).
Proof.
  induction t; eauto.
Qed.

#[global] Instance Encode_zipper `{Encode A} : Encode (zipper A) :=
  { encode' := encode_zipper }.

Global Instance data_nodeL `{Encode A} : Data "NodeL" τ[zipper A; A; tree A] (zipper A) :=
  { ctor_apply := λ '(t1, (x, t2)), NodeL t1 x t2;
    ctor_encode := λ '(t1, (x, t2)), eq_refl }.

Global Instance data_nodeR `{Encode A} : Data "NodeR" τ[tree A; A; zipper A] (zipper A) :=
  { ctor_apply := λ '(t1, (x, t2)), NodeR t1 x t2;
    ctor_encode := λ '(t1, (x, t2)), eq_refl }.

End encode.

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

  Context {A : Type} (lt : A → A → Prop) {Tlt : Transitive lt}.

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


(* -------------------------------------------------------------------------- *)

(** *Specification *)

Definition splay_spec :=
  fun splay =>
    ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
    pure
      (call splay #(l, (x, (r, ctx))))
      (λ t', fringe t' = fringe (fill ctx (Node l x r))) (⊥ : void → Prop).

Definition splay_leaf_spec :=
  fun (splay_leaf : val) =>
    ∀ A `(_ : Encode A) (ctx : zipper A),
    pure
      (call splay_leaf #ctx)
      (λ t', fringe t' = fringe (fill ctx Leaf)) (⊥ : void → Prop).

Definition zlookup_spec :=
  fun (zlookup : val) =>
    ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      pure
        (call zlookup #(t, (x, ctx)))
        (λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)) (⊥ : void → Prop).

(* -------------------------------------------------------------------------- *)

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

Section splay_proofs.

(* -------------------------------------------------------------------------- *)

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
  VData "NodeL" [vz1; vx; vt2] = #z.
Proof.
  intros. subst. eauto.
Qed.

Lemma solve_encode_NodeR `{Encode A} t1 x z2 (z : zipper A) vt1 vx vz2 :
  NodeR t1 x z2 = z →
  vt1 = #t1 →
  vx = #x →
  vz2 = #z2 →
  VData "NodeR" [vt1; vx; vz2] = #z.
Proof.
  intros. subst. eauto.
Qed.

Local Hint Resolve
  solve_encode_Root solve_encode_NodeL solve_encode_NodeR
  : encode.


(* -------------------------------------------------------------------------- *)

Ltac pats :=
  repeat first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons; [ eauto | simpl; intros ]
    ].

Definition pLeaf := PConstant "Leaf".

Lemma pat_pLeaf `{Encode A} η δ v (t : tree A) (φ : env -> Prop) :
  v = #t →
  (t = Leaf -> φ δ) ->
  pattern η δ pLeaf v φ (t <> Leaf).
Proof.
  intros; subst.
  destruct t.
  { eapply pattern_exn_mono.
    { eapply pat_PData_eq; pats; eauto. }
    destruct 1. }
  { eapply pattern_exn_mono.
    { eapply pat_PData_neq.
      - (* This goal should be solvable by "encode." *)
        erewrite solve_encode_Node; eauto.
      - eauto. }
    congruence. }
Qed.

Ltac pat_pLeaf :=
  eapply pat_pLeaf; first solve [encode].

Definition pNode (p1 p2 p3 : syntax.pat) :=
  PData "Node" [p1; p2; p3].

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
  { eapply pat_PData_neq.
    - (* This goal should be solvable with "encode." *)
      erewrite solve_encode_Leaf; eauto.
    - auto. }
  { auto. }
  { eapply pat_PData_eq; pats ; eauto. }
  { clear; right; do 3 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNode :=
  eapply pat_pNode; first solve [encode].

Definition pRoot := PConstant "Root".

Lemma pat_pRoot `{Encode A} η δ v (z : zipper A) (φ : env -> Prop) :
  v = #z →
  (z = Root -> φ δ) ->
  pattern η δ pRoot v φ (z <> Root).
Proof.
  intros; subst.
  destruct z.
  { eapply pattern_exn_mono.
    { eapply pat_PData_eq; pats; encode. }
    destruct 1. }
  { eapply pattern_exn_mono.
    { eapply pat_PData_neq; auto.
      - erewrite solve_encode_NodeL; eauto.
      - auto. }
    congruence. }
  { eapply pattern_exn_mono.
    { eapply pat_PData_neq.
      - erewrite solve_encode_NodeR; eauto.
      - auto. }
    congruence. }
Qed.

Ltac pat_pRoot :=
  eapply pat_pRoot; first solve [encode].

Definition pNodeL (p1 p2 p3 : syntax.pat) :=
  PData "NodeL" [p1; p2; p3].

Lemma pat_pNodeL `{Encode A} (η δ : env) (v : val) (z : zipper A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : zipper A -> Prop) (ψ2 : A -> Prop) (ψ3 : tree A -> Prop)
  :
  v = #z ->
  (∀ (z' : zipper A) (a : A) (t : tree A),
      z = NodeL z' a t →
      pattern η δ p1 #z' (λ δ', pattern η δ' p2 #a (λ δ', pattern η δ' p3 #t φ (ψ3 t)) (ψ2 a)) (ψ1 z')) ->
  pattern η δ (pNodeL p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeR a1 a2 a3) \/
                                 (exists z' a t, z = NodeL z' a t /\ (ψ1 z' \/ ψ2 a \/ ψ3 t))).
Proof.
  intros -> Hcov.
  destruct z; eapply pattern_exn_mono.
  { eapply pat_PData_neq.
    - erewrite solve_encode_Root; eauto.
    - auto. }
  { auto. }
  { eapply pat_PData_eq; pats; eauto. }
  { clear; do 2 right; do 3 eexists; split; [ reflexivity | tauto ]. }
  { eapply pat_PData_neq.
    - erewrite solve_encode_NodeR; eauto.
    - auto. }
  { right; left; eauto. }
Qed.

Ltac pat_pNodeL :=
  eapply pat_pNodeL; first solve [encode].

Definition pNodeR (p1 p2 p3 : syntax.pat) :=
  PData "NodeR" [p1; p2; p3].

Lemma pat_pNodeR `{Encode A} (η δ : env) (v : val) (z : zipper A)
  (p1 p2 p3 : syntax.pat) (φ : env -> Prop)
  (ψ1 : tree A -> Prop) (ψ2 : A -> Prop) (ψ3 : zipper A -> Prop)
  :
  v = #z ->
  (∀ (t : tree A) (a : A) (z' : zipper A),
      z = NodeR t a z' →
      pattern η δ p1 #t (λ δ', pattern η δ' p2 #a (λ δ', pattern η δ' p3 #z' φ (ψ3 z')) (ψ2 a)) (ψ1 t)) ->
  pattern η δ (pNodeR p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeL a1 a2 a3) \/
                                 (exists t a z', z = NodeR t a z' /\ (ψ1 t \/ ψ2 a \/ ψ3 z'))).
Proof.
  intros -> Hcov.
  destruct z; eapply pattern_exn_mono.
  { eapply pat_PData_neq.
    - erewrite solve_encode_Root; eauto.
    - auto. }
  { auto. }
  { eapply pat_PData_neq.
    - erewrite solve_encode_NodeL; eauto.
    - auto. }
  { right; left; eauto. }
  { eapply pat_PData_eq; pats; eauto. }
  { clear; right; right; do 3 eexists; split; [ reflexivity | tauto ]. }
Qed.

Ltac pat_pNodeR :=
  eapply pat_pNodeR; first solve [encode].

Ltac pattern_hook ::=
  first
    [ pat_pRoot
    | pat_pNodeL
    | pat_pNodeR
    | pat_pLeaf
    | pat_pNode
    ].


(* -------------------------------------------------------------------------- *)

Lemma invert_singleton {A} (a b : A) :
  wp.singleton a b ->
  a = b.
Proof. rewrite /singleton. by intros ->. Qed.

Lemma Splay_spec :
  splay_spec
    (VCloRec stdlib_env [RecBinding "splay" (AnonFunction __branches1)] "splay").
Proof.
  intros A H ctx l x r.

  (* We need to massage the postcondition so we can generalize the argument for
    the recursive call. *)
  change (λ t', fringe t' = fringe (fill ctx (Node l x r))) with
    ((λ '(l, (x, (r, ctx))) t', fringe t' = fringe (fill ctx (Node l x r)))
         (l, (x, (r, ctx)))).

  (* Recursion, with decreasing depth of zipper. *)
  recursion { measure (fun p => snd (snd (snd p))) } ∀ (l, (x, (r, ctx))).
  clear l x r ctx; intros splay [l [x [r ctx]]] IH.

  (* Match to destruct the argument tuple *)
  eapply pure_eval_match. { pure_path. }
  (* Match on [ctx] *)
  pure_match.
  eapply pure_eval_match. { pure_path. }

  pure_match. (* Very slow. *)

  (* Case: [ctx] matches [Root] *)
  { pure_data.
    intros ??? (<- & <- & <-). reflexivity. }

  (* Case: [ctx] matches [NodeL (Root, y, ry)] *)
  { pure_data.
    - pure_data. intros ??? (<- & <- & <-). apply eq_refl.
    - intros ??? (<- & <- & <-).
      prove_same_fringe. }

  (* Case: [ctx] matches [NodeL (NodeL (up, z, rz), y, ry)] *)
  { eapply pure_eval_app.
    - pure_path.
    - pure_tuple.
      + pure_data.
        * pure_data.
          intros ??? (<- & <- & <-). apply eq_refl.
        * intros ??? (<- & <- & <-). apply eq_refl.
      + intros ???? (<- & <- & <- & <-).
        (* FIXME *)
        instantiate (1:=data_node). instantiate (1:=data_node).
        apply eq_refl.
    - intros ? args -> <-.
      eapply pure_ret_mono.
      { eapply IH; cbn; unfold zlt; subst; auto with arith. }
      simpl; intros ? ->.
      prove_same_fringe. }

  (* Case: [ctx] matches [NodeL (NodeR (lz, z, up), y, ry)] *)
  { eapply pure_eval_app.
    - pure_path.
    - pure_tuple.
      + pure_data.
        instantiate (1:=data_node). (* FIXME *)
        intros ??? (<- & <- & <-). apply eq_refl.
      + pure_data. instantiate (1:=data_node). (* FIXME *)
        intros ??? (<- & <- & <-). apply eq_refl.
      + simpl. intros ???? (<- & <- & <- & <-).
        apply eq_refl.
    - intros ? args -> <-.
      eapply pure_ret_mono.
      { eapply IH; cbn; unfold zlt; subst; auto with arith. }
      simpl; intros ? ->.
      prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, Root)] *)
  { pure_data. pure_data. intros ??? (<- & <- & <-); apply eq_refl.
    intros ??? (<- & <- & <-).
    prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, NodeL (up, z, rz))] *)
  { eapply pure_eval_app.
    - pure_path.
    - pure_tuple.
      pure_data. instantiate (1:=data_node).
      intros ??? (<- & <- & <-). apply eq_refl.
      pure_data. instantiate (1:=data_node).
      intros ??? (<- & <- & <-). apply eq_refl.
      intros ???? (<- & <- & <- & <-). apply eq_refl.
    - intros ?? -> <-.
      eapply pure_ret_mono.
      { eapply IH; cbn; unfold zlt; subst; auto with arith. }
      intros ? ->.
      prove_same_fringe. }

  (* Case: [ctx] matches [NodeR (ly, y, NodeR (lz, z, up))] *)
  { eapply pure_eval_app.
    - pure_path.
    - pure_tuple.
      pure_data.
      { pure_data. instantiate (1:=data_node).
        intros ??? (<- & <- & <-). apply eq_refl. }
      instantiate (1:=data_node).
      intros ??? (<- & <- & <-). apply eq_refl.
      intros ???? (<- & <- & <- & <-). apply eq_refl.
    - intros ?? -> <-.
      eapply pure_ret_mono.
      { eapply IH; cbn; unfold zlt; subst; auto with arith. }
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
  { eapply pure_eval_app. pure_path.
    pure_tuple.
    eapply pure_eval_const.
    apply (@solve_encode_Leaf A); reflexivity. apply eq_refl. (* Todo: weird *)
    intros ???? (<- & <- & <- & <-). apply eq_refl.

    intros ? ? -> <-.
    unfold splay_spec in Hsplay.
    specialize (Hsplay _ _ z' Leaf a t).
    apply Hsplay. }

  (* Case: [ctx] matches [NodeR (l, x, up)] *)
  { eapply pure_eval_app. pure_path.
    pure_tuple.
    eapply pure_eval_const.
    apply (@solve_encode_Leaf A); reflexivity. apply eq_refl.
    intros ???? (<- & <- & <- & <-). apply eq_refl.
    intros ? ? -> <-.
    specialize (Hsplay A _ x1 x x0 Leaf).
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

  change
    (λ '(oy, t'),
       member le x (fringe t) oy ∧ fringe t' = fringe (fill ctx t)) with
    ((λ '(t, (x, ctx)) '(oy, t'),
       member le x (fringe t) oy ∧ fringe t' = fringe (fill ctx t))
       (t, (x, ctx))).

  recursion { measure fst } ∀ (t, (x, ctx)) gen (fun x => bst (strict le) x.1);
   first done.

  clear x ctx; intros zlookup [t' [x ctx]] IH.
  simpl in *. clear Hbst; intros Hbst.

  (* Match on tuple argument *)
  eapply pure_eval_match. { pure_path. }
  pure_match.
  (* Match on [t] *)
  eapply pure_eval_match. { pure_path. }
  pure_match.

  (* Case: [t] matches [Leaf] *)
  { pure_tuple. pure_const. apply eq_refl.
    eapply pure_eval_app. pure_path.
    pure_path.
    intros ? ? <- <-.
    apply (Hsplay_leaf A H ctx).
    intros ? a2 (<- & ->).
    split.
    - repeat intro; by eapply not_elem_of_nil.
    - auto. }

  (* Case: [t] matches [Node (l, y, r)] *)
  { destruct_bst_Node.

    eapply pure_eval_let1var.
    { (* Evaluate rhs of [let c = ..] *)
      eapply pure_eval_app.
      { eapply pure_eval_app.
        { pure_path. }
        { pure_path. }
        intros ? ? <- <-.
        eapply Hcompare. }
      pure_path.
      intros ? ? Hcall ->.
      eapply Hcall. }
    (* Evaluate continuation expression after let *)
    intros c (? & Hlt & Heq & Hgt).
    eapply pure_eval_ifthenelse.
    { (* Evalute comparison operation *)
      eapply pure_eval_EOpLt.
      { pure_path. }
      { eapply pure_eval_int. reflexivity. }
      { assumption. }
      { representable. } }

    { (* Case: [c < 0] *)
      intro Clt0.
      eapply pure_eval_app. { pure_path. }
      pure_tuple.
      change (encode' ctx) with #ctx.
      pure_data. instantiate (1:=data_nodeL).
      intros ??? (<- & <- & <-). apply eq_refl.
      intros ??? (<- & <- & <-). apply eq_refl.
      intros ? ? -> <-.
      eapply pure_ret_mono.
      { eapply IH with (y := (t1, (x, NodeL ctx a t2)));
          unfold tlt, tree_size; auto with arith. }
      intros [oy t'] [??]; simpl in *.
      split; [ | assumption ].
      apply bst_member_left; representable.
      apply Hlt. lia. }

    { (* Case: [c >= 0] *)
      intros Cge0.
      eapply pure_eval_ifthenelse.
      { (* Evaluate second comparison operation *)
        eapply pure_eval_EOpGt.
        { pure_path. }
        { eapply pure_eval_int. reflexivity. }
        { assumption. }
        { representable. } }

      { (* Subcase: [c > 0] *)
        intros Cgt0.
        eapply pure_eval_app. { pure_path. }
        change (encode' ctx) with #ctx.
        pure_tuple. pure_data.
        instantiate (1:=data_nodeR).
        intros ??? (<- & <- & <-). apply eq_refl.
        intros ??? (<- & <- & <-). apply eq_refl.
        intros ? ? -> <-.
        eapply pure_ret_mono.
        { eapply IH with (y := (t2, (x, NodeR t1 a ctx))).
          { cbn; unfold tlt. cbn. lia. }
          { auto. } }
        intros [oy t'] [??]; simpl in *.
        split.
        - apply bst_member_right; representable.
          apply Hgt; apply Z.gt_lt; lia.
        - assumption. }

      { (* Subcase: [c <= 0] *)
        intros Cle0.
        (* Deduce [c = 0] *)
        pure_tuple. pure_data. intros ? <-. apply eq_refl.
        eapply pure_eval_app. { pure_path. }
        change (encode' ctx) with #ctx.
        pure_tuple. intros ???? (<- & <- & <- & <-).
        apply eq_refl.
        intros ? ? <- <-.
        apply Hsplay. intros ?? (<- & <-).
        simpl in Cge0, Cle0 |- *.
        split; first split.
        - apply Heq. lia.
        - apply elem_of_app; right; apply elem_of_cons; left; reflexivity.
        - reflexivity. } } }
Qed.

Lemma Splay__spec:
  toplevel __main
    (pure_context [var_spec "splay" splay_spec;
                   var_spec "splay_leaf" splay_leaf_spec;
                   var_spec "zlookup" zlookup_spec] {["lookup";"splay";"splay_leaf";"zlookup"]}).
Proof.
  apply module_struct.
  next_item.
  { apply Splay_spec. }
  intros [??] (splay & Hsplay & -> & ->).
  next_item with splay_leaf_spec.
  { rewrite <- fold_pre_eval. simpl. pure_ret. simpl. rewrite <- solve_encode_val. eauto.
    apply Splay_leaf_spec; assumption. }
  intros [??] (splay_leaf & Hsplay_leaf & -> & ->).
  next_item.
  { apply Zlookup_spec; assumption. }
  intros [??] (zlookup & Hzlookup & -> & ->).
  next_item.
  { rewrite <- fold_pre_eval. simpl. pure_ret. }
  intros [??] (lookup & Hlookup & -> & ->).
  finished_struct.
  simpl.
  split; first auto.
  repeat (constructor;
  first try (eexists; split; [ rewrite <- solve_encode_val | ]; eauto)).
  constructor.
Qed.

End splay_proofs.
