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

Definition proj_tlt {A B} (p1 : B * tree A) (p2 : B * tree A) :=
  tlt p1.2 p2.2.

Lemma proj_tlt_wf {A B} :
  well_founded (@proj_tlt A B).
Proof.
  unfold proj_tlt. eapply wf_inverse_image. eapply tlt_wf.
Qed.

Local Hint Extern 1 (tree_depth _ < tree_depth _)%nat => (simpl; lia) : pure_specs.


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

Lemma pat_pLeaf `{Encode A} η v (t : tree A) (φ : env -> Prop) :
  v = #t →
  (t = Leaf -> φ η) ->
  pattern η pLeaf v φ (t <> Leaf).
Proof.
  intros; destruct t; subst.
Admitted.

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
  intros; destruct t; subst.
Admitted.

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

Class Ord A : Type :=
  {
    lt : A -> A -> bool;
  }.

Inductive bst `{Ord A} : tree A -> Prop :=
| bst_Leaf : bst Leaf
| bst_Node :
  ∀ l r x,
    bst l ->
    bst r ->
    ForallTree (fun y => lt x y) l ->
    ForallTree (fun y => ~ (lt x y)) l ->
    bst (Node l x r).


(* -------------------------------------------------------------------------- *)

(* Specifications *)


Class Eq A : Type :=
  {
    eqb : A -> A -> bool;
  }.

Fixpoint lookup `{Ord A, Eq A} (x : A) (t : tree A) :=
  match t with
  | Leaf => false
  | Node t1 a t2 =>
      if (lt x a) then lookup x t1 else
      if (lt a x) then lookup x t2 else
        eqb x a
  end.

Definition insert_spec `{Encode A, Ord A, Eq A} insert :=
  ∀ (y : A) (t : tree A),
    bst t ->
    pure_call2 insert #y #t (λ (t' : tree A),
        ∀ x, lookup x t' = if eqb x y then true else lookup x t) ⊥.

Definition member_spec `{Encode A, Ord A, Eq A} member :=
  ∀ (x : A) (t : tree A),
    bst t ->
    pure_call2 member #x #t (λ (b : bool), b = lookup x t) ⊥.

Local Instance Ord_Z : Ord Z := { lt x y := (x <? y)%Z }.
Local Instance Eq_z : Eq Z := { eqb x y := Z.eqb x y }.


(* -------------------------------------------------------------------------- *)

(* Proof *)

(* [env_has_pspecs : list (var * (val -> Prop)) -> env -> Prop] states that
   a given environment certain values, with names and specifications
   given in an association list. *)


Lemma ModuleSpec :
  eval_module stdlib_env __main
    (env_has_pspecs [("insert", insert_spec); ("member", member_spec)]).
Proof. Admitted.
