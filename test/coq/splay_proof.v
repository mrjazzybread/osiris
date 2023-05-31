Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Sorting.Sorted.
From osiris Require Import osiris.
From osiris.semantics Require Export evalprime.
From osiris.proofmode Require Export proofmode. (* TODO *)
From osiris.libs Require Import Stdlib.
From test Require Import splay.

(* -------------------------------------------------------------------------- *)

(* WIP *)

Ltac SIMP_specify x φ :=
  lazymatch goal with
  | |- SIMP (bind (dconcatenating ?δ _) _) _ =>
      let o := eval cbn in (lookup_name δ x) in
      lazymatch o with ret ?v =>
        let h := fresh in
        assert (φ v) as h; [| revert h; generalize v ]
      end
  end.

Lemma SIMP_simp_bind X Y (_ : Encode Y)
   m f (x : X) (ψ : Y → Prop) :
  simp m (ret x) →
  SIMP (f x) ψ →
  SIMP (bind m f) ψ.
  (* This is [@bind X val]. *)
Proof.
  intros Hm Hf.
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_bind.
Qed.

Lemma SIMP_covariant `{Encode X} m (φ ψ : X → Prop) :
  SIMP m φ →
  (∀ x, φ x → ψ x) →
  SIMP m ψ.
Proof.
  intros (x & Hm & Hx) ?. exists x. eauto.
Qed.

Lemma SIMP_call_up_to_eq `{Encode X} (φ : X → Prop) v1 v2 v'2 :
  SIMP (call v1 v2) φ →
  v2 = v'2 →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

Lemma SIMP_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = encode x →
  SIMP (call v1 (encode x)) φ →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

Arguments String.eqb !s1 !s2 : simpl nomatch. (* TODO *)

Notation "'<closure>'" := (VCloRec _ _ _) (only printing).
Notation "'<closure>'" := (VClo _ _) (only printing).
Notation "'Environment'  'composed'  'of'  [ x ; .. ; z ]" :=
  (EnvCons x _ (.. (EnvCons z _ EnvNil) ..))
 (only printing).

(* WIP *)

Create HintDb SIMP_specs.

Ltac SIMP_call :=
  eapply SIMP_covariant; [
    notypeclasses refine (@SIMP_call _ _ _ _ _ _ _ _ _ _);
      [ encode | eauto with SIMP_specs ]
  | cbn
  ].

(* -------------------------------------------------------------------------- *)

(* Boilerplate: reflect the algebraic data type ['a tree]. *)

Inductive tree (A : Type) : Type :=
| Leaf: tree A
| Node: tree A → A → tree A → tree A.

Arguments Leaf {A}.
Arguments Node {A} t1 x t2.

Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      let vs :=
        VCons (encode_tree t1) $
        VCons (encode x) $
        VCons (encode_tree t2) $
        VNil
      in
      VData "Node" (VTuple vs)
  end.

Local Instance Encode_tree `{Encode A} : Encode (tree A) :=
  { encode := encode_tree }.

Lemma encode_tree_is_encode `{Encode A} :
  ∀ (t : tree A),
  encode_tree t = encode t.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_tree_is_encode : encode.

Lemma solve_encode_Leaf `{Encode A} t :
  Leaf = t →
  VConstant "Leaf" = encode t.
Proof.
  intros. subst. eauto.
Qed.

Lemma solve_encode_Node `{Encode A} t1 x t2 t et1 ex et2 :
  Node t1 x t2 = t →
  et1 = encode t1 →
  ex = encode x →
  et2 = encode t2 →
  VData "Node" (VTuple $
    VCons et1 $
    VCons ex $
    VCons et2 $
    VNil
  ) = encode t.
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
      let vs :=
        VCons (encode_zipper z1) $
        VCons (encode x) $
        VCons (encode_tree t2) $
        VNil
      in
      VData "NodeL" (VTuple vs)
  | NodeR t1 x z2 =>
      let vs :=
        VCons (encode_tree t1) $
        VCons (encode x) $
        VCons (encode_zipper z2) $
        VNil
      in
      VData "NodeR" (VTuple vs)
  end.

Local Instance Encode_zipper `{Encode A} : Encode (zipper A) :=
  { encode := encode_zipper }.

Lemma encode_zipper_is_encode `{Encode A} :
  ∀ (z : zipper A),
  encode_zipper z = encode z.
Proof.
  eauto.
Qed.

Local Hint Resolve encode_zipper_is_encode : encode.

(* -------------------------------------------------------------------------- *)

(* The depth of a zipper. *)

Fixpoint depth {A} (z : zipper A) : nat :=
  match z with
  | Root =>
      0
  | NodeL z1 x t2 =>
      1 + depth z1
  | NodeR t1 x z2 =>
      1 + depth z2
  end.

Definition zlt {A} (z1 z2 : zipper A) :=
  depth z1 < depth z2.

Lemma zlt_wf {A} :
  well_founded (@zlt A).
Proof.
  unfold zlt. eapply wf_inverse_image. eapply lt_wf.
Qed.

Local Hint Extern 1 (depth _ < depth _) => (simpl; lia) : SIMP_specs.

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

(* An opaque list singleton. *)

Local Definition sing {A} (x : A) : list A :=
  [x].

Local Opaque sing.

(* The fringe of a tree. *)

Fixpoint fringe {A} (t : tree A) : list A :=
  match t with
  | Leaf =>
      []
  | Node l x r =>
      fringe l ++ sing x ++ fringe r
  end.

(* The left and right fringes of a zipper. *)

Fixpoint lfringe {A} (z : zipper A) : list A :=
  match z with
  | Root =>
      []
  | NodeL z1 x t2 =>
      lfringe z1
  | NodeR t1 x z2 =>
      lfringe z2 ++ fringe t1 ++ sing x
  end.

Fixpoint rfringe {A} (z : zipper A) : list A :=
  match z with
  | Root =>
      []
  | NodeL z1 x t2 =>
      sing x ++ fringe t2 ++ rfringe z1
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

Local Ltac prove_same_fringe :=
  repeat rewrite fringe_fill in *;
  simpl fringe in *;
  repeat rewrite <- app_assoc in *;
  eauto.

(* -------------------------------------------------------------------------- *)

(* Properties of sorted lists. *)

(* TODO not year clear which results are useful in this section *)
Section Sortedness.

Context {A : Type}.
Context {lt : A → A → Prop}.
Context {Slt : StrictOrder lt}.
Notation "x '<' y" := (lt x y).

Definition lllt (xs ys : list A) :=
  Forall (λ x, Forall (λ y, x < y) ys) xs.

Notation "xs '≺' ys" := (lllt xs ys) (at level 80).

Lemma Sorted_empty :
  Sorted lt [].
Proof.
  econstructor.
Qed.

Lemma Sorted_singleton (x : A) :
  Sorted lt [x].
Proof.
  econstructor.
  + eauto using Sorted_empty.
  + econstructor.
Qed.

Lemma lllt_Singleton_left x ys :
  [x] ≺ ys ↔
  Forall (λ y, x < y) ys.
Proof.
  unfold lllt. rewrite Forall_singleton. tauto.
Qed.

Lemma lllt_Singleton_right xs y :
  xs ≺ [y] ↔
  Forall (λ x, x < y) xs.
Proof.
  unfold lllt. split; intro.
  + eapply Forall_impl; [ eauto |].
    intro. simpl. rewrite Forall_singleton. tauto.
  + eapply Forall_impl; [ eauto |].
    intro. simpl. rewrite Forall_singleton. tauto.
Qed.

Lemma Sorted_append (xs ys : list A) :
  Sorted lt (xs ++ ys) ↔
  Sorted lt xs ∧ Sorted lt ys ∧ xs ≺ ys.
Proof.
Admitted.

Lemma cons_is_append x (ys : list A) :
  x :: ys = [x] ++ ys.
Proof.
  reflexivity.
Qed.

Lemma Sorted_cons x (ys : list A) :
  Sorted lt (x :: ys) ↔
  Sorted lt ys ∧ [x] ≺ ys.
Proof.
  change (x :: ys) with ([x] ++ ys).
  rewrite Sorted_append.
  generalize (Sorted_singleton x).
  tauto.
Qed.

End Sortedness.

(* Notation "xs '≺' ys" := (lllt xs ys) (at level 80). TODO *)

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
Context {lt : A → A → Prop}.

Definition bst (t : tree A) :=
  Sorted lt (fringe t).

End BST.

(* -------------------------------------------------------------------------- *)

(* WIP *)

Global Instance Encode_tuple4
  `{Encode A}
  `{Encode B}
  `{Encode C}
  `{Encode D}
  : Encode (A * B * C * D)
  | 0 (* TODO higher priority than the rule for binary tuples *)
  :=
  { encode := λ '(a, b, c, d),
      VTuple (
        VCons (encode a) $
        VCons (encode b) $
        VCons (encode c) $
        VCons (encode d) $
        VNil
      )
  }.

Lemma solve_encode_tuple4
  `{Encode A}
  `{Encode B}
  `{Encode C}
  `{Encode D}
  (a : A) (b : B) (c : C) (d : D)
  ea eb ec ed
  t :
  (a, b, c, d) = t →
  ea = encode a →
  eb = encode b →
  ec = encode c →
  ed = encode d →
  VTuple (
    VCons ea $
    VCons eb $
    VCons ec $
    VCons ed $
    VNil
  ) = encode t.
Proof.
  intros. subst. eauto.
Qed.

(* The lemma [solve_encode_tuple4] has 22 arguments. *)

(* We cannot let [eapply] apply this lemma, as Coq would again make
   incorrect choices of the types A, B, C, D. *)

Global Hint Extern 1 (_ = _) =>
  notypeclasses refine (@solve_encode_tuple4
    _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _
    _ _ _ _ _ _
  )
  : encode.

(* -------------------------------------------------------------------------- *)

(* Specification of [splay]. *)

Definition splay_spec (splay : val) : Prop :=
  ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
  SIMP
    (call splay (encode (l, x, r, ctx)))
    (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Axiom skip : False. (* TODO *)

Lemma Splay__spec:
  let η := EnvCons "Stdlib" Stdlib EnvNil in
  SIMP (eval_mexpr η Splay) (λ (_ : val), True).
Proof.
  intros.
  SIMP.

  SIMP_specify "splay" splay_spec.
  (* Subgoal: prove that [splay] satisfies its specification. *)
  { generalize η; clear η; intro η.
    unfold splay_spec. intros ??.
    (* Reason by well-founded induction on the depth of the zipper [ctx]. *)
    induction ctx as [ctx IH] using (well_founded_induction zlt_wf);
    unfold zlt in IH.
    intros.
    (* Enter the closure. *)
    SIMP_enter. SIMP_continue.
    (* Optional: abstract away the closure; make it an abstract value [c]. *)
    match goal with |- context[VCloRec ?η ?rbs ?f] =>
      revert IH; generalize (VCloRec η rbs f); intros c IH
    end.
    (* Perform case analysis over the zipper [ctx]. *)
    destruct ctx as [| ctx y ry | ly y ctx ]; SIMP.
    (* Case: [Root]. *)
    { SIMP_continue.
      (* Establish the postcondition. *)
      prove_same_fringe. }
    (* Case: [NodeL]. *)
    { (* Perform case analysis on the second level of the zipper. *)
      destruct ctx as [| up z rz | lz z up ];
      SIMP; SIMP_continue.
      (* Subcase: [Root]. *)
      { (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeL]. *)
      { (* Apply the induction hypothesis. *)
        SIMP_call; intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      { (* Apply the induction hypothesis. *)
        SIMP_call; intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
    }
    (* Case: [NodeR]. *)
    { (* Perform case analysis on the second level of the zipper. *)
      destruct ctx as [| up z rz | lz z up ]; SIMP.
      (* Subcase: [Root]. *)
      { SIMP_continue.
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeL]. *)
      { SIMP_continue.
        (* Apply the induction hypothesis. *)
        SIMP_call; intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      { SIMP_continue.
        (* Apply the induction hypothesis. *)
        SIMP_call; intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
    }
  }
  intros splay Hsplay. SIMP_continue.

  exfalso. apply skip.
Time Qed.
