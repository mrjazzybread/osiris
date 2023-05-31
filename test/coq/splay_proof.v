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

(* It is debatable in which order the two premises of the lemma
   [SIMP_call] should be listed. The premise [v'2 = #x] may seem easy
   to solve (this is the job of the tactic [encode]) so one may wish
   to solve it first. This offers the advantage of instantiating [x]
   immediately, so [x] is known when we try to prove that the call is
   permitted -- which may involve proving that a precondition holds.

   However, solving [v'2 = #x] can involve guessing some types (e.g.,
   the type of an empty list), and we have used [Hint Mode] in
   encode.v to forbid this. So, it can also be preferable to first
   solve the premise [SIMP (call v1 #x) φ]. Doing so can allow us to
   instantiate these types in a correct way.

   One might wish to try both approaches, but waiting until [encode]
   fails is very slow (several seconds). *)

Lemma SIMP_call `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  v'2 = #x →
  SIMP (call v1 #x) φ →
  SIMP (call v1 v'2) φ.
Proof.
  intros. subst. eauto.
Qed.

Lemma SIMP_call_reversed `{Encode X} `{Encode Y}
  (φ : Y → Prop) v1 v'2 (x : X) :
  SIMP (call v1 #x) φ →
  v'2 = #x →
  SIMP (call v1 v'2) φ.
Proof.
  eauto using SIMP_call.
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
  first [
    eapply SIMP_call; [ solve [encode] | solve [eauto with SIMP_specs] ]
  | eapply SIMP_covariant; [
      eapply SIMP_call; [ solve [encode] | eauto with SIMP_specs ]
    | cbn ]
  ].

Ltac SIMP_call_reversed :=
  eapply SIMP_covariant; [
    eapply SIMP_call_reversed; [ eauto with SIMP_specs | encode ]
  | cbn
  ].

Ltac SIMP_use H :=
  eapply SIMP_covariant; [
    eapply SIMP_call_reversed; [ eapply H | encode ]
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

Lemma simp_as_bool (x : bool) (m : free val) :
  simp m (ret #x) →
  simp (as_bool m) (ret x).
Proof.
  intros. unfold as_bool.
  eapply prove_simp_bind.
  + eauto.
  + destruct x; simpl; eauto with simp.
Qed.

Lemma SIMP_bind_as_bool Y (_ : Encode Y)
  m (f : bool → free val) (φ : bool → Prop) (ψ : Y → Prop) :
  SIMP m φ →
  (∀ (x : bool), φ x → SIMP (f x) ψ) →
  SIMP (bind (as_bool m) f) ψ.
  (* This is [@bind bool val]. *)
Proof.
  intros (x & ? & Hx) Hf.
  specialize (Hf x Hx).
  destruct Hf as (y & ? & ?).
  eexists; split; eauto using prove_simp_bind, simp_as_bool.
Qed.

(* -------------------------------------------------------------------------- *)

(* Specification of [splay]. *)

Definition splay_spec (splay : val) : Prop :=
  ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
  SIMP
    (call splay #(l, x, r, ctx))
    (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Definition splay_leaf_spec (splay_leaf : val) : Prop :=
  ∀ A `(_ : Encode A) (ctx : zipper A),
  SIMP
    (call splay_leaf #ctx)
    (λ t', fringe t' = fringe (fill ctx Leaf)).

Definition zlookup_spec (zlookup : val) : Prop :=
  ∀ A `(_ : Encode A) (lt : A → A → Prop) `(_ : StrictOrder A)
    (t : tree A) (x : A) (ctx : zipper A),
  SIMP
    (call zlookup #(t, x, ctx))
    (λ '((b, t') : bool * tree A), fringe t' = fringe (fill ctx t)).
    (* TODO incomplete spec *)

Axiom skip : False. (* TODO *)
Ltac skip := exfalso; apply skip.

Lemma Splay__spec:
  let η := EnvCons "Stdlib" Stdlib EnvNil in
  SIMP (eval_mexpr η Splay)
       (λ (_ : val), True). (* TODO missing postcondition *)
Proof.
  intros.
  SIMP.

  SIMP_specify "splay" splay_spec.
  (* Subgoal: prove that [splay] satisfies its specification. *)
  { generalize η; clear η; intro η. (* optional *)
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
        SIMP_call. intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      { (* Apply the induction hypothesis. *)
        SIMP_call. intros t' Ht'.
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
        SIMP_call. intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
      (* Subcase: [NodeR]. *)
      { SIMP_continue.
        (* Apply the induction hypothesis. *)
        SIMP_call. intros t' Ht'.
        (* Establish the postcondition. *)
        prove_same_fringe. }
    }
  }
  intros splay Hsplay. SIMP_continue.

  SIMP_specify "splay_leaf" splay_leaf_spec.
  (* Subgoal: prove that [splay_leaf] satisfies its specification. *)
  { unfold splay_leaf_spec. intros.
    (* This helps Coq recognize the encoding of [Leaf] at type [A]. *)
    (* Without this, the tactic [encode] fails to solve [Leaf = #?t]. TODO *)
    pose proof (@solve_encode_Leaf A _).
    (* Step into the function. *)
    SIMP_enter. SIMP_continue.
    (* Perform case analysis over the zipper [ctx]. *)
    destruct ctx as [| up x r | r x up ]; SIMP; SIMP_continue.
    (* Case: [Root]. *)
    { prove_same_fringe. }
    (* Case: [NodeL]. *)
    { SIMP_call. }
    (* Case: [NodeR]. *)
    { SIMP_call. }
  }
  intros splay_leaf Hsplay_leaf. SIMP_continue.

  SIMP_specify "zlookup" zlookup_spec.
  (* Subgoal: prove that [zlookup] satisfies its specification. *)
  { unfold zlookup_spec. intros ?????.
    (* TODO cheat and assuming that [Stdlib.(<)] decides [lt] on [A]. *)
    assert (
      forall (x y : A),
      SIMP ('v ← call Stdlib__lt #x; call v #y)
           (λ (b : bool), if b then lt x y else ¬ lt x y)
    ) as lt_spec by skip.
    (* TODO cheat and assuming that [Stdlib.(<)] decides [lt] on [A]. *)
    assert (
      forall (x y : A),
      SIMP ('v ← call Stdlib__gt #x; call v #y)
           (λ (b : bool), if b then ¬ lt y x else lt y x)
    ) as gt_spec by skip.
    (* Reason by induction on the tree [t]. *)
    induction t as [| l IHl y r IHr ];
    intros;
    SIMP_enter; SIMP_continue; SIMP_continue.
    (* Case: [Leaf]. *)
    { (* TODO clean up *)
      SIMP_bind; [ SIMP_call | cbn ]. intros t' Ht'.
      SIMP. cbn.
      assumption. }
    (* Case: [Node]. *)
    { (* Examine the comparison [x < y]. Reason by cases on its outcome. *)
      eapply SIMP_bind_as_bool.
      { SIMP. eapply lt_spec. }
      cbn. intros [|] Hlt; SIMP.
      (* Subcase: [x < y]. *)
      { SIMP_call. intros [b t'] ?.
        assumption. }
      (* Examine the comparison [x > y]. Reason by cases on its outcome. *)
      eapply SIMP_bind_as_bool.
      { SIMP. eapply gt_spec. }
      cbn. intros [|] Hgt; SIMP.
      (* Subcase: [x > y]. *)
      { SIMP_call. intros [b t'] ?.
        assumption. }
      (* Subcase: neither comparison succeeded, so [x = y]. *)
      { eapply SIMP_bind.
        { SIMP_call. }
        cbn. intros t' Ht'.
        SIMP. cbn.
        assumption. }
    }
  }
  intros zlookup zlookup_spec. SIMP_continue.

  (* Conclude. *)
  tauto.

Time Qed.
