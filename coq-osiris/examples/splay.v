Require Import Coq.Wellfounded.Inverse_Image.
From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_splay.
Local Opaque app. (* Prevent undesired simplification. *)
  (* TODO clash between ++ in fringes and ++ in paths *)

(* -------------------------------------------------------------------------- *)

(* WIP *)

Local Ltac unpack :=
  repeat lazymatch goal with h: _ ∧ _ |- _ => destruct h end.

Notation "'<closure>'" := (VCloRec _ _ _) (only printing).
Notation "'<closure>'" := (VClo _ _) (only printing).
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
  rewrite <- ?app_assoc ;
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

Lemma bst_Node_iff l x r :
  bst (Node l x r) ↔
  bst l ∧ bst r ∧ fringe l ≺ [x] ∧ [x] ≺ fringe r.
Proof.
  unfold bst. simpl fringe.
  rewrite !Sorted_app_iff !Sorted_singleton_iff pairwise_app_right_iff.
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

(* Specification of [splay]. *)

Definition splay_spec (splay : val) : Prop :=
  ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
  pure
    (call splay #(l, x, r, ctx))
    (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Definition splay_leaf_spec (splay_leaf : val) : Prop :=
  ∀ A `(_ : Encode A) (ctx : zipper A),
  pure
    (call splay_leaf #ctx)
    (λ t', fringe t' = fringe (fill ctx Leaf)).

Definition zlookup_spec (zlookup : val) : Prop :=
  ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
  compare_spec Stdlib__compare le →
  ∀ (t : tree A) (x : A) (ctx : zipper A),
  bst (strict le) t →
  pure
    (call zlookup #(t, x, ctx))
    (λ '(oy, t'),
      member le x (fringe t) oy ∧
      fringe t' = fringe (fill ctx t)
    ).

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

Local Ltac fixme :=
  with_strategy transparent [app] simpl (MkPathRev _); pure1.

Lemma Splay__spec:
  let η := ("Stdlib", Stdlib) :: Stdlib_env in
  pure (eval_mexpr η __main)
       (λ (_ : val), True). (* TODO missing postcondition *)
Proof.
  intros.
  pure1.
  pure_specify "splay" splay_spec.
  (* Subgoal: prove that [splay] satisfies its specification. *)
  { generalize η; clear η; intro η. (* optional *)
    unfold splay_spec. intros ??.
    intros.
    (* TODO: Add the following pattern into pure_rec_call *)
    (* remember (l, x, r, ctx) as t. *)
    (* replace ctx with t.2 by (rewrite Heqt; reflexivity). *)
    (* replace l with (t.1.1.1) by (rewrite Heqt; reflexivity). *)
    (* replace x with (t.1.1.2) by (rewrite Heqt; reflexivity). *)
    (* replace r with (t.1.2) by (rewrite Heqt; reflexivity). *)
    (* pure_rec t (fun _ : (tree A * A * tree A * zipper A) => True) (@splay_wf A). *)
    (* do 3 destruct t as [t ?]. *)
    eapply pure_rec_call with
      (v:=(l, x, r, ctx))
      (P:=fun _ => True)
      (φ:= fun tuple =>
             match tuple with
             | (l, x, r, ctx) =>
                 (fun t' => fringe t' = fringe (fill ctx (Node l x r))) end).
    { apply splay_wf. }
    { done. }
    clear l x r ctx.
    intros splay [[[l x] r] ctx] _ IH.
    unfold zlt in IH.
    (* Perform case analysis over the zipper [ctx]. *)
    destruct ctx as [| ctx y ry | ly y ctx ]; pure1.
    (* Case: [Root]. *)
    {
      (* Establish the postcondition. *)
      prove_same_fringe. }
    (* Case: [NodeL]. *)
    { (* Perform case analysis on the second level of the zipper. *)
      destruct ctx as [| up z rz | lz z up ];
      pure1.
      (* Subcase: [Root]. *)
      { (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeL]. *)
      { (* Apply the induction hypothesis. *)
        pure1. intros t' Ht'.
        (* Establish the postcondition. *)
        rewrite Ht'. prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      { (* Apply the induction hypothesis. *)
        pure1. intros t' Ht'.
        (* Establish the postcondition. *)
        rewrite Ht'.
        prove_same_fringe. }
    }
    (* Case: [NodeR]. *)
    { (* Perform case analysis on the second level of the zipper. *)
      destruct ctx as [| up z rz | lz z up ]; pure1.
      (* Subcase: [Root]. *)
      {
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeL]. *)
      {
        (* Apply the induction hypothesis. *)
        pure1. intros t' Ht'.
        (* Establish the postcondition. *)
        rewrite Ht'.
        prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      {
        (* Apply the induction hypothesis. *)
        pure1. intros t' Ht'.
        (* Establish the postcondition. *)
        rewrite Ht'.
        prove_same_fringe. }
    }
  }
  intros splay Hsplay. pure_continue.

  pure_specify "splay_leaf" splay_leaf_spec.
  (* Subgoal: prove that [splay_leaf] satisfies its specification. *)
  { unfold splay_leaf_spec. intros.
    (* This helps Coq recognize the encoding of [Leaf] at type [A]. *)
    (* Without this, the tactic [encode] fails to solve [Leaf = #?t]. TODO *)
    pose proof (@solve_encode_Leaf A _).
    (* Step into the function. *)
    pure_enter. fixme.
    (* Perform case analysis over the zipper [ctx]. *)
    destruct ctx as [| up x r | r x up ]; pure1.
    (* Case: [Root]. *)
    { prove_same_fringe. }
    (* Case: [NodeL]. *)
    { pure0. }
    (* Case: [NodeR]. *)
    { pure0. }
  }
  intros splay_leaf Hsplay_leaf. pure_continue.

  pure_specify "zlookup" zlookup_spec.
  (* Subgoal: prove that [zlookup] satisfies its specification. *)
  { unfold zlookup_spec. do 4 intro.
    intros Hcompare ??? Hbst.
    eapply pure_rec_call_unary with
      (v:=(t,x,ctx))
      (P:=fun '(t, _, _) => bst (strict le) t)
      (φ:=fun tuple =>
            match tuple with
            | (t, x, ctx) =>
                λ '(oy, t'),
                member le x (fringe t) oy ∧ fringe t' = fringe (fill ctx t)
            end).
    { apply zlookup_wf. }
    { apply Hbst. }
    clear dependent t x ctx.
    intros vf [[t x] ctx] Hbst IH.
    (* Reason by induction on the tree [t]. *)
    destruct t as [|l y r]; pure1.
    (* Case: [Leaf]. *)
    { intros t' Ht'. pure1.
      (* Establish the postcondition: *)
      split.
      - simpl member. intros. rewrite elem_of_nil. tauto. (* TODO use [set_solver]? *)
      - assumption. }
    (* Case: [Node]. *)
    { (* The call [compare x y] is curried. *)
      intros v Hv.
      eapply pure_bind. (* TODO try to automate this *)
      { eapply Hv. }
      clear v Hv.
      intros c Hc. cbn in Hc.
      (* The call [compare x y] is now complete. *)
      destruct_bst_Node.
      pure_continue.
      rewrite lt_repr_repr; [ | representable | representable].
      assert (c < 0 ∨ 0 < c ∨ c = 0) as [|[|]] by lia.
      (* Case: [c < 0], that is, [x < y]. *)
      { rewrite ltb_true; [ | lia ].
        pure1. eapply pure_consequence.
        { eapply IH; eauto.
          { unfold tlt. simpl; lia. }}
        intros [ox t'] (? & ?); simpl.
        (* Establish the postcondition: *)
        split.
        - rewrite bst_member_left; representable.
        - assumption. }
      (* Case: [c > 0], that is, [x > y]. *)
      { rewrite ltb_false; try lia.
        pure1.
        rewrite lt_repr_repr; representable.
        rewrite ltb_true; try lia.
        pure1. eapply pure_consequence.
        { eapply IH; first assumption.
          { unfold tlt. simpl; lia. }}
        intros [b t'] (? & ?); simpl.
        (* Establish the postcondition: *)
        split.
        - rewrite bst_member_right; representable.
        - assumption. }
      (* Subcase: [c = 0], so [x] and [y] are equivalent with respect to
         the preorder [le]. *)
      { rewrite ltb_false; try lia.
        pure1.
        rewrite lt_repr_repr; representable.
        rewrite ltb_false; try lia.
        pure1.
        intros t' Ht'. pure1.
        (* Establish the postcondition: *)
        assert (equivalent le x y) by tauto.
        split; [ split |]; simpl.
        - assumption.
        - rewrite !elem_of_app elem_of_list_singleton. tauto.
        - assumption. }
    }
  }
  intros zlookup zlookup_spec. pure_continue. pure_continue.

  (* Conclude. *)
  tauto.

Time Qed.
