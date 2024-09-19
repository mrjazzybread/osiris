From osiris.logic Require Import orders sorting.
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

Require Import Coq.Wellfounded.Inverse_Image.

(* The depth of a tree. *)

Fixpoint tree_depth {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node t1 _ t2 => 1 + (tree_depth t1) + (tree_depth t2)
  end.

(* Well-founded relation on tree depth. *)

Definition tlt {A} (t1 t2 : tree A) :=
  (tree_depth t1 < tree_depth t2)%nat.

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

(* Fun with data constructors: we can know the destructor as long as we
   have the signature of the algebraic datatype. *)

(* The type of a data constructor can be built from the list of
   constructor argument types. *)
Fixpoint data_constructor A (x : list Type) : Type :=
  match x with
    | nil => A
    | hd :: tl => hd -> data_constructor A tl
  end.

(* Data types is a map from string (constructor name) to the type signatures
  of the constructors. *)
Class DataType (A : Type) :=
  { data_signature : gmap string { x & data_constructor A x }; }.

(* -------------------------------------------------------------------------- *)

(* Datatype instance for [tree] *)

(* LATER: Can this be generated during translation? *)

Definition Leaf_ {A} : sigT (data_constructor (tree A)) :=
  existT [] Leaf.

Definition Node_ {A} : sigT (data_constructor (tree A)) :=
  existT [tree A; A; tree A] Node.

#[global] Instance tree_datatype `{Encode A} : DataType (tree A) :=
  { data_signature :=
      <["Leaf" := Leaf_ (A := A) ]>
        (<["Node" := Node_ (A := A) ]> ∅) }.

(* -------------------------------------------------------------------------- *)

(* Encodings *)

Local Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      VData "Node" [encode_tree t1; #x; encode_tree t2]
  end.

#[global] Instance Encode_tree `{Encode A} : Encode (tree A) :=
  { encode := encode_tree }.

Local Fixpoint encode_zipper `{Encode A} (z : zipper A) : val :=
  match z with
  | Root =>
      VConstant "Root"
  | NodeL z1 x t2 =>
      VData "NodeL" [encode_zipper z1; #x; #t2]
  | NodeR t1 x z2 =>
      VData "NodeR" [ #t1; #x; encode_zipper z2]
  end.

#[global] Instance Encode_zipper `{Encode A} : Encode (zipper A) :=
  { encode := encode_zipper }.

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

End BST.

(* -------------------------------------------------------------------------- *)

(** *Specification *)

Definition splay_spec :=
  fun splay =>
    ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
    total
      (call splay #(l, x, r, ctx))
      (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Definition splay_leaf_spec :=
  fun (splay_leaf : val) =>
    ∀ A `(_ : Encode A) (ctx : zipper A),
    total
      (call splay_leaf #ctx)
      (λ t', fringe t' = fringe (fill ctx Leaf)).

Definition zlookup_spec :=
  fun (zlookup : val) =>
    ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      total
        (call zlookup #(t, x, ctx))
        (λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)).

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

(* -------------------------------------------------------------------------- *)

Section splay_proofs.

(* Top-level environment of [splay]. *)

Set Implicit Arguments.

Inductive hlist (A : Type) (B : A -> Type) : list A -> Type :=
| HNil : hlist B nil
| HCons : forall (x : A) (ls : list A), B x -> hlist B ls -> hlist B (x :: ls).

(* declare a bit more implicit arguments than the one automatically detected by Implicit Arguments *)
Arguments HNil {A B}.
Arguments HCons {A B x ls}.

From Equations Require Import Equations.

Equations app (A B : list Type) :
  hlist (fun T : Type => T) A ->
  hlist (fun T : Type => T) B ->
  hlist (fun T : Type => T) (A ++ B) :=
app HNil m := m;
app (HCons a l1) m := HCons a (app l1 m).

Definition build_constructor {A}
  (x : list Type)
  (constr : data_constructor A x)
  (a : hlist (fun T : Type => T) x)
  : A.
Proof.
  induction x; eauto.
  cbn in *. inv a.
  specialize (constr X).
  exact (IHx constr X0).
Defined.

Fixpoint build_data {A X} η
  (φ : A -> Prop) ψ
  (v : list expr)
  (t : list Type)
  (constr : data_constructor A X)
  (acc_t : list Type)
  (acc : hlist (fun T : Type => T) acc_t)
  : Prop :=
  match v, t with
  | hd :: tl, hd_t :: tl_t =>
      ∃ (EncX : Encode hd_t) x,
      pure
        (eval η hd)
        (fun y : hd_t =>
          y = x /\
          @build_data _ _ η φ ψ tl
            tl_t
            constr
            (acc_t ++ [hd_t])
            (app acc (HCons x HNil))) ψ
  | nil, nil =>
      exists (eq_X : acc_t = X),
      φ (@build_constructor _ acc_t
           (eq_rect_r
              (fun X => data_constructor A X)
              constr eq_X) acc)
  | _ , _ => False
end.

Lemma pure_eval_data {A} `{Encode A, DataType A} η
  c hd tl (φ : _ -> Prop) ψ
  (signature : sigT (data_constructor A)) :
  data_signature !! c = Some signature ->
  @build_data _ _ η φ ψ
    (hd :: tl)
    (projT1 signature)
    (projT2 signature)
    nil HNil ->
  pure (A := A) (eval η (EData c (hd :: tl))) φ ψ.
Proof. Admitted.

Lemma total_ret_eq_and `{Encode A} {X : Type} (a : A) (ψ : Prop):
  ψ →
  total (E := X) (ret #a) (λ a', a' = a /\ ψ).
Proof.
  intros. eapply total_mono. apply total_ret_eq.
  cbn. intros; by subst.
Qed.

Ltac pure_eval_path :=
  eexists _, _; eapply pure_eval_path; eapply total_ret_eq_and.

Lemma Splay_spec :
  splay_spec
    (VCloRec stdlib_env [RecBinding "splay" (AnonFunction __branches1)] "splay").
Proof.
  intros A H ctx l x r.

  (* We need to massage the postcondition so we can generalize the argument for the
     recursive call. *)
  change (λ t', fringe t' = fringe (fill ctx (Node l x r))) with
    ((λ '(l, x, r, ctx) t', fringe t' = fringe (fill ctx (Node l x r))) (l, x, r, ctx)).

  (* Recursion, with decreasing depth of zipper. *)
  recursion { measure snd } ∀ (l, x, r, ctx).

  clear l x r ctx; intros splay [[[l x] r] ctx] IH.

  (* Match to destruct the argument tuple *)
  eval_match; pure_match.

  (* Match on [ctx] *)
  eval_match.

  destruct ctx eqn: Hctx. (* FIXME: Generate custom match cases like before *)
  { (* Case: [ctx] matches [Root] *)
    pure_match.
    eapply pure_eval_data; first try done.
    repeat pure_eval_path.
    exists eq_refl. prove_same_fringe. }

Admitted.

Lemma Splay_leaf_spec splay :
  splay_spec splay ->
  splay_leaf_spec
    (VClo ("splay" ~> splay; stdlib_env) __fun4).
Proof.
  unfold splay_leaf_spec.
Admitted.

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
    ((λ '(t, x, ctx) '(oy, t'),
       member le x (fringe t) oy ∧ fringe t' = fringe (fill ctx t))
       (t, x, ctx)).

  recursion { measure (fun x => fst (fst x)) } ∀ (t, x, ctx).

  clear Hbst t x ctx; intros zlookup [[t x] ctx] IH.
  simpl in *. fold eval.

  (* Match on tuple argument *)
  eapply pure_eval_match. { pure_path. }
  pure_match.
  (* Match on [t] *)
  eapply pure_eval_match. { pure_path. }
  pure_match.

  (* Case: [t] matches [Leaf] *)
Admitted.

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
Admitted.

End splay_proofs.

