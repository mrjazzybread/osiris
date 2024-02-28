Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_splay.

(* -------------------------------------------------------------------------- *)

(* WIP *)

Local Ltac unpack :=
  repeat lazymatch goal with h: _ ∧ _ |- _ => destruct h end.

(* Notation "'<closure>'" := (VCloRec _ _ _) (only printing). *)
(* Notation "'<closure>'" := (VClo _ _) (only printing). *)
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (cons x _ (.. (cons z _ nil) ..))
 (only printing).

(* -------------------------------------------------------------------------- *)

(* Boilerplate: reflect the algebraic data type ['a tree]. *)

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
  pat η pLeaf v φ (t <> Leaf).
Proof.
  intros; subst.
  destruct t.
  { eapply pat_consequence_psi.
    { eapply pat_PData_eq; eapply pat_PTuple.
      pats. }
    tauto. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; done. }
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
      pat η p1 #t1
        (λ η', pat η' p2 #a
            (λ η', pat η' p3 #t2 φ (ψ3 t2))
            (ψ2 a))
        (ψ1 t1)) ->
  pat η (pNode p1 p2 p3) v φ
    (t = Leaf \/ (exists t1 a t2, t = Node t1 a t2 /\ (ψ1 t1 \/ ψ2 a \/ ψ3 t2))).
Proof.
  intros; subst.
  destruct t; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { tauto. }
  { eapply pat_PData_eq; eapply pat_PTuple.
    pats; subst; eauto. }
  { clear; right; do 3 eexists; split; [reflexivity | tauto]. }
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
  pat η pRoot v φ (z <> Root).
Proof.
  intros; subst.
  destruct z.
  { eapply pat_consequence_psi.
    { eapply pat_PData_eq; eapply pat_PTuple.
      pats. }
    tauto. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; done. }
    congruence. }
  { eapply pat_consequence_psi.
    { eapply pat_PData_neq; done. }
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
      pat η p1 #z' (λ η', pat η' p2 #a (λ η', pat η' p3 #t φ (ψ3 t)) (ψ2 a)) (ψ1 z')) ->
  pat η (pNodeL p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeR a1 a2 a3) \/
                                 (exists z' a t, z = NodeL z' a t /\ (ψ1 z' \/ ψ2 a \/ ψ3 t))).
Proof.
  intros; subst.
  destruct z; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { tauto. }
  { eapply pat_PData_eq; eapply pat_PTuple.
    pats; subst; eauto. }
  { clear; do 2 right; do 3 eexists; split; [reflexivity | tauto]. }
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
      pat η p1 #t (λ η', pat η' p2 #a (λ η', pat η' p3 #z' φ (ψ3 z')) (ψ2 a)) (ψ1 t)) ->
  pat η (pNodeR p1 p2 p3) v φ (z = Root \/
                                 (exists a1 a2 a3, z = NodeL a1 a2 a3) \/
                                 (exists t a z', z = NodeR t a z' /\ (ψ1 t \/ ψ2 a \/ ψ3 z'))).
Proof.
  intros; subst.
  destruct z; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { tauto. }
  { eapply pat_PData_neq; eauto. }
  { right; left; eauto. }
  { eapply pat_PData_eq; eapply pat_PTuple.
    pats. }
  { clear; right; right; do 3 eexists; split; [ reflexivity | tauto]. }
Qed.

Ltac pat_pNodeR :=
  eapply pat_pNodeR; first solve [encode].

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
  unfold bst. simpl fringe. rewrite Sorted_empty_iff. tauto.
Qed.

Lemma cons_is_app x (l1 : list A) : x :: l1 = [x] ++ l1. Proof. tauto. Qed.

Lemma bst_Node_iff l x r :
  bst (Node l x r) ↔
  bst l ∧ bst r ∧ fringe l ≺ [x] ∧ [x] ≺ fringe r.
Proof.
  unfold bst. simpl fringe.
  repeat first [ rewrite Sorted_app_iff
               | rewrite Sorted_singleton_iff
               | rewrite cons_is_app; rewrite Sorted_app_iff
               | rewrite pairwise_app_right_iff].
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

Lemma pat_consequence_phi η p v (φ φ' : env -> Prop) ψ :
  (∀ η, φ' η -> φ η) ->
  pat η p v φ' ψ ->
  pat η p v φ ψ.
Proof.
  intros.
  eapply pat_consequence; eauto.
Qed.

Opaque encode.

Lemma pure_eval_quadruple `{Encode A1, Encode A2, Encode A3, Encode A4} (η : env) (e1 e2 e3 e4 : expr)
  (ψ : A1 * A2 * A3 * A4 → Prop) :
  pure (eval η e1) (λ a1 : A1,
        pure (eval η e2) (λ a2 : A2,
              pure (eval η e3) (λ a3 : A3,
                    pure (eval η e4) (λ a4 : A4,
                          ψ (a1, a2, a3, a4))))) ->
  pure (eval η (ETuple [e1; e2; e3; e4])) ψ.
Proof.
  intros.
  repeat (let h := fresh in destruct_pure h).
  eapply pure_simp; [ simp | ].
  by pure_ret.
Qed.

Ltac pattern_hook ::=
  first
    [ pat_pRoot; intros
    | pat_pNodeL; intros
    | pat_pNodeR; intros
    | pat_pLeaf; intros
    | pat_pNode; intros
    ].
(* -------------------------------------------------------------------------- *)
(* Specification structures. *)

(* Given a name which corresponds to the declaration, there is some pspec *)
Class decl_spec (name : var) := { Decl_spec : pspec }.

(* Smart constructor *)
Definition val_spec (name : var) `{decl_spec name} (v : val) : Prop :=
  @Decl_spec name _ v.

(* Lifting specification over declaration to a specification over an environment:
    i.e. the declaration can be found the environment and satisfies the
    specification. *)
Definition spec (name : var) `{decl_spec name} (η : env) : Prop :=
  let val_spec := @Decl_spec name _ in
  pure (lookup_name η name) val_spec.

(* -------------------------------------------------------------------------- *)
(* Specification of [splay]. *)

(* Names for the functions we would like to specify *)
Definition SPLAY := "splay".
Definition SPLAY_LEAF := "splay_leaf".
Definition ZLOOKUP := "zlookup".

(* Specification for each function *)
Definition splay_spec :=
  fun splay =>
    ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
    pure
      (call splay #(l, x, r, ctx))
      (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Definition splay_leaf_spec :=
  fun (splay_leaf : val) =>
    ∀ A `(_ : Encode A) (ctx : zipper A),
    pure
      (call splay_leaf #ctx)
      (λ t', fringe t' = fringe (fill ctx Leaf)).

Definition zlookup_spec :=
  fun (zlookup : val) =>
    ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      pure
        (call zlookup #(t, x, ctx))
        (λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)).

#[local] Instance splay_decl_spec : decl_spec SPLAY :=
  {| Decl_spec := splay_spec |}.

#[local] Instance splay_leaf_decl_spec : decl_spec SPLAY_LEAF :=
  {| Decl_spec := splay_leaf_spec |}.

#[local] Instance zlookup_decl_spec : decl_spec ZLOOKUP :=
  {| Decl_spec := zlookup_spec |}.

(* -------------------------------------------------------------------------- *)

(* Top-level environment of [splay]. *)

Definition stdlib_env := ("Stdlib", Stdlib) :: Stdlib_env.

(* Ltac programming to compute the environment from [mexpr]'s. *)

(* Instantiates an evar and tries to apply the aggressive [simp_really] resolution
   spitting out a [micro] monad if it succeeds. *)
Ltac try_reduce_with_simp A E m :=
  let e := fresh "e" in
  let H := fresh "H" in
  evar (e : micro A E);
  assert (H:simp m ?e) by simp_really;
  clear H;
  exact e.

(* Given a module definition that has been evaluated, return the environment that
 is built from the evaluated module. *)
Ltac extract_env module_def :=
  let m := fresh "m" in
  let l := fresh "l" in
  pose module_def as m;
  unfold module_def in m;
  match goal with
  | m := ret (VStruct ?x) |- _ => pose x as l
  end; clear m; cbn in *; exact l.

(* We can extract the environment programmatically. *)
Definition splay_module_env' :=
  (ltac:(try_reduce_with_simp val void (eval_mexpr stdlib_env __main))).
(* A more sane approach would be to state some well-formedness conditions *)

(* Extracted environment *)
Definition splay_module_env : env :=
  ltac:(extract_env splay_module_env').

(* -------------------------------------------------------------------------- *)

(* Util functions for specs *)
Ltac start_proof := unfold spec; cbn; pure1; red.

(* If a specification holds for an environment, we know that there exists some
   declaration in the environment that satisfies the specification. *)
(* TODO fp: It seems to me that this lemma goes too far.
        It essentially expands away the judgement
        [pure (lookup_name η name) val_spec]
        but we should we able to exploit this judgement
        without expanding it. *)
Lemma invert_spec :
  forall x `{decl_spec x} env,
    spec x env ->
    ∃ v, lookup_name env x = ret v /\ val_spec x v.
Proof.
  intros x Spec env; revert x Spec.
  induction env.
  intros * Hspec. red in Hspec; cbn in Hspec.
  - unfold lookup_name in Hspec.
    destruct Hspec as (?&Hspec&?).
    with_strategy transparent [missing_variable_or_field]
      unfold missing_variable_or_field in Hspec.
    clarify_simp.
  - intros * Hspec. red in Hspec.
    unfold lookup_name in *. destruct a.
    destruct (x =? v)%string.
    + destruct Hspec as (?&?&Hspec). clarify_simp.
      eexists; split; eauto.
    + fold lookup_name in *. eapply IHenv; eauto.
Qed.

(* Apply the specification of a function *)
Ltac apply_spec SPEC :=
  let H := fresh "H" in
  let vspec := fresh "vspec" in
  let Hlu := fresh "Hlu" in
  pose proof (invert_spec _ _ SPEC) as H;
  destruct H as (?&Hlu&vspec);
  inversion Hlu; subst;
  try solve [eapply vspec];
  try (eapply pure_consequence ; first eapply vspec).

(* -------------------------------------------------------------------------- *)
(* Specification of [splay]. *)
Section splay_proofs.

  Notation splay_spec x := (spec x splay_module_env).

  Lemma Splay_spec : splay_spec SPLAY.
  Proof.
    start_proof.

    repeat intro.
    (* TODO: Add the following pattern into pure_rec_call *)
    remember (l, x, r, ctx) as t.
    replace ctx with t.2 by (rewrite Heqt; reflexivity).
    replace l with (t.1.1.1) by (rewrite Heqt; reflexivity).
    replace x with (t.1.1.2) by (rewrite Heqt; reflexivity).
    replace r with (t.1.2) by (rewrite Heqt; reflexivity).
    pure_rec t (fun _ : (tree A * A * tree A * zipper A) => True) (@splay_wf A).

    clear l ctx x r.
    destruct t as [[[l x] r] ctx]; simpl; rename vf into splay.

    (* Match to destruct the argument tuple *)
    eapply pure_eval_match. { pure_path. reflexivity. }
    unfold __branches1; pure_match.

    (* Match on [ctx] *)
    eapply pure_eval_match. { pure_path. reflexivity. }
    unfold __branches0; pure_match. (* Was very slow, now just slow *)

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
      { eapply IH; unfold zlt; subst; auto with arith. }
      simpl; intros ? ->.
      prove_same_fringe. }

    (* Case: [ctx] matches [NodeL (NodeR (lz, z, up), y, ry)] *)
    { eapply pure_eval_app. pure_path.
      eapply pure_eval_quadruple. pure_data. pure_path. pure_data. pure_path.
      pure_call.
      { eapply IH; unfold zlt; subst; auto with arith. }
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
      { eapply IH; unfold zlt; subst; auto with arith. }
      intros ? ->.
      prove_same_fringe. }

    (* Case: [ctx] matches [NodeR (ly, y, NodeR (lz, z, up))] *)
    { eapply pure_eval_app. pure_path.
      eapply pure_eval_quadruple. pure_data. pure_path. pure_path. pure_path.
      pure_call.
      { eapply IH; unfold zlt; subst; auto with arith. }
      intros ? ->.
      prove_same_fringe. }
  Qed.

  Lemma Splay_leaf_spec : splay_spec SPLAY_LEAF.
  Proof.
    start_proof.

    repeat intro.
    pure_call_VClo.
    (* Match on [ctx] *)
    eapply pure_eval_match. { pure_path; reflexivity. }
    unfold __branches3; pure_match.

    (* Case: [ctx] matches [Root] *)
    { pure_const. by subst. }

    (* Case: [ctx] matches [NodeL (up, x, r)] *)
    { eapply pure_eval_app. pure_path. (* What does [pure_path] do? *)
      eapply pure_eval_quadruple.
      eapply pure_eval_const.
      apply (@solve_encode_Leaf A); first done. (* Todo: weird *)
      repeat pure_path.
      apply_spec Splay_spec. }

    (* Case: [ctx] matches [NodeR (l, x, up)] *)
    { eapply pure_eval_app. pure_path. eapply pure_eval_quadruple.
      pure_path. pure_path. eapply pure_eval_const.
      apply (@solve_encode_Leaf A). reflexivity.
      pure_path.
      apply_spec Splay_spec. }
  Qed.

  Lemma Zlookup_spec : splay_spec ZLOOKUP.
  Proof.
    start_proof.
    intros ????.
    intros Hcompare ??? Hbst.
    remember (t, x, ctx) as tup eqn:Heqtup.
    replace ctx with (tup.2) by (rewrite Heqtup; reflexivity).
    replace x with (tup.1.2) by (rewrite Heqtup; reflexivity).
    replace t with (tup.1.1) in Hbst |- * by (rewrite Heqtup; reflexivity).
    pure_rec tup (λ (t : tree A * A * zipper A),
        match t with
        | (t, _, _) => bst (strict le) t
        end) (@zlookup_wf A).
    repeat (destruct tup as [tup ?]); simpl in *.
    (* Match on tuple argument *)
    eapply pure_eval_match. { pure_path. reflexivity. }
    unfold __branches11; pure_match.
    (* Match on [t] *)
    eapply pure_eval_match. { pure_path. reflexivity. }
    unfold __branches10; pure_match.

    (* Case: [t] matches [Leaf] *)
    { eapply pure_eval_pair. pure_const.
      eapply pure_eval_app. do 2 pure_path.
      apply_spec Splay_leaf_spec.
      split; [ intros | done]; apply not_elem_of_nil. }

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
      intros c (?&Hlt&Heq&Hgt).
      unfold __exp9.
      eapply pure_eval_ifthenelse.
      { (* Evalute comparison operation *)
        eapply pure_eval_EOpLt.
        { pure_path. reflexivity. }
        { eapply pure_eval_int. reflexivity. }
        { assumption. }
        { representable. } }

      { (* Case: [c < 0] *)
        intro Clt0. unfold __exp5.
        eapply pure_eval_app. pure_path.
        eapply pure_eval_triple. pure_path. pure_path. pure_data.
        pure_call.
        { eapply IH; unfold tlt, tree_depth; auto with arith. }
        intros [oy t'] [??]; simpl in *.
        split.
        - rewrite bst_member_left; representable.
        - assumption. }

      { (* Case: [c >= 0] *)
        intros Cge0. unfold __exp8.
        eapply pure_eval_ifthenelse.
        { (* Evaluate second comparison operation *)
          eapply pure_eval_EOpGt.
          { pure_path. reflexivity. }
          { eapply pure_eval_int. reflexivity. }
          { assumption. }
          { representable. } }

        { (* Subcase: [c > 0] *)
          intros Cgt0. unfold __exp6.
          eapply pure_eval_app. pure_path.
          eapply pure_eval_triple. pure_path. pure_path. pure_data.
          pure_call.
          { eapply IH; [ auto | unfold tlt, tree_depth; lia ]. }
          intros [oy t'] [??]; simpl in *.
          split.
          - rewrite bst_member_right; representable.
            by apply Hgt; apply Z.gt_lt.
          - assumption. }

        { (* Subcase: [c <= 0] *)
          intros Cle0. unfold __exp7.
          (* Deduce [c = 0] *)
          assert (equivalent le a a0) by (apply Heq; lia).
          eapply pure_eval_pair. pure_data.
          eapply pure_eval_app. pure_path.
          eapply pure_eval_quadruple. do 4 pure_path.
          apply_spec Splay_spec.
          intros. split; first split.
          - assumption.
          - apply elem_of_app; right; apply elem_of_cons; by left.
          - assumption. } } }
  Qed.

  Lemma Splay__spec:
    let η := ("Stdlib", Stdlib) :: Stdlib_env in
    pure (eval_mexpr η __main)
      (is_module_with_pspecs [(SPLAY, splay.splay_spec);
                              (SPLAY_LEAF, splay.splay_leaf_spec);
                              (ZLOOKUP, splay.zlookup_spec)]).
  Proof.
    intros; pure1; simpl.
    split; last split; red.
    { apply_spec Splay_spec. }
    { apply_spec Splay_leaf_spec. }
    { apply_spec Zlookup_spec. }
  Qed.

End splay_proofs.
