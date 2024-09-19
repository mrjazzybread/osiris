From osiris.logic Require Import orders sorting.
From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_splay.

(* The algebraic data type ['a tree]. *)

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

(* The algebraic data type ['a zipper]. *)

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

(* Well-formedness *)

Require Import Coq.Wellfounded.Inverse_Image.

#[local]
  Program Canonical Structure tree_wf {A} : WellFounded (tree A) :=
  {| wf_relation := (fun t1 t2 => tree_depth t1 < tree_depth t2)%nat |}.
Next Obligation.
  intros; eapply wf_inverse_image; eapply lt_wf.
Qed.

(* -------------------------------------------------------------------------- *)
Section encodings.

(* Encodings *)
Local Fixpoint encode_tree `{Encode A} (t : tree A) : val :=
  match t with
  | Leaf =>
      VConstant "Leaf"
  | Node t1 x t2 =>
      VData "Node" [encode_tree t1; #x; encode_tree t2]
  end.

Class Decode (A : Type) `{Encode A} :=
  { decode : val → option A;
    decode_encode : forall x, decode (encode.encode x) = Some x}.

#[global] Instance Encode_tree `{Encode A} : Encode (tree A).
Proof. constructor; eapply encode_tree. Defined.

Local Fixpoint decode_tree `{Decode A} val : option (tree A) :=
  match val with
  | VConstant s => if (s =? "Leaf")%string then Some Leaf else None
  | VData s [x;y;z] =>
      if (s =? "Node")%string then
        match decode_tree x, decode y, decode_tree z with
        | Some x, Some y, Some z => Some (Node x y z)
        | _, _, _ => None
        end
      else None
  | _ => None
  end.

Lemma decode_encode_tree `{Decode A}
  : forall (x : tree A), decode_tree (encode_tree x) = Some x.
Proof.
  intros. induction x; cbn. econstructor.
  rewrite IHx1 IHx2.
  by rewrite decode_encode.
Defined.

#[global] Program Instance Decode_tree `{Decode A} : Decode (tree A) :=
  { decode := decode_tree }.
Next Obligation.
  intros. induction x; cbn. econstructor.
  rewrite IHx1 IHx2.
  by rewrite decode_encode.
Qed.

Local Fixpoint encode_zipper `{Encode A} (z : zipper A) : val :=
  match z with
  | Root =>
      VConstant "Root"
  | NodeL z1 x t2 =>
      VData "NodeL" [encode_zipper z1; #x; #t2]
  | NodeR t1 x z2 =>
      VData "NodeR" [ #t1; #x; encode_zipper z2]
  end.

#[global] Instance Encode_zipper `{Encode A} : Encode (zipper A).
Proof. constructor; eapply encode_zipper. Defined.

End encodings.

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
    ∀ A `(_ : Decode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      total
        (call zlookup #(t, x, ctx))
        (λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)).

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

(* Well-founded relation on zipper depth. *)

Definition zlt {A} (z1 z2 : zipper A) :=
  (zipper_depth z1 < zipper_depth z2)%nat.

#[local] Instance zlt_WF {A} : WellFoundedRel (@zipper A) zlt.
  constructor; unfold zlt; apply wf_inverse_image, lt_wf.
Qed.

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

(* TODO: Move *)
Ltac pure_match :=
  eapply pure_match_cons; first solve_pattern; last intuition.
Ltac pure_path := by eapply pure_eval_path, total_ret.
Ltac eval_match :=
  eapply pure_eval_match; first pure_path.

Lemma pure_eval_data_eq `{Encode Y} `{Decode Y}
  η c e (ψ : Y -> Prop) ζ y:
  pure_wp
    (evals η e)
    (λ v', match (decode (VData c v')) with
            | Some v => y = v
            | None => False
            end) ζ ->
  ψ y ->
  pure (eval η (EData c e)) ψ ζ.
Proof. Admitted.


Lemma pure_eval_data `{Encode Y} `{Decode Y}
  η c e (ψ : Y -> Prop) ζ :
  pure_wp
    (evals η e)
    (λ v', match (decode (VData c v')) with
            | Some v => ψ v
            | None => False
            end) ζ ->
  pure (eval η (EData c e)) ψ ζ.
Proof. Admitted.

Lemma pure_eval_tuple `{Encode A, Encode B} η x tl (φ : B -> Prop) ψ v:
  pure (A := A)
    (eval η x)
    (fun v' : A =>
       pure_wp (evals η tl) (fun x => v = # v' :: x) ψ) ψ ->
  pure (A := B) (eval η (ETuple (x :: tl))) φ ψ.
Proof.
Admitted.

Lemma pure_evals_cons `{Encode A} η (hd : expr) tl (φ : list val -> Prop) ψ :
  pure (A := A) (eval η hd)
    (fun x =>
       pure_wp (evals η tl) (fun v => φ (# x :: v)) ψ) ψ ->
  pure_wp (A := list val) (evals η (hd :: tl)) φ ψ.
Proof. Admitted.

Section splay_proofs.

(* Top-level environment of [splay]. *)

Lemma Splay_spec :
  splay_spec
    (VCloRec stdlib_env [RecBinding "splay" (AnonFunction __branches1)] "splay").
Proof.
  intros A H ctx l x r.
  change (λ t', fringe t' = fringe (fill ctx (Node l x r))) with
    ((λ '(l, x, r, ctx) t', fringe t' = fringe (fill ctx (Node l x r))) (l, x, r, ctx)).

  recursion with zlt { measure snd } ∀ (l, x, r, ctx).

  intros splay [[[l' x'] r'] ctx'] IH.

  (* Match to destruct the argument tuple *)
  eval_match. pure_match.

  (* Match on [ctx] *)
  eval_match.

  destruct ctx' eqn: Hctx'; pure_match. (* Note: No longer slow ! *)
  { (* Case: [ctx] matches [Root] *)

    eapply (@pure_eval_data_eq (tree A) _ _ Decode_tree).
    { eapply (@pure_evals_cons (tree A)).
      eapply pure_eval_path; cbn -[evals].
      apply pure_wp_ret; eexists l'; split; first done.

      eapply (@pure_evals_cons A).
      eapply pure_eval_path; cbn -[evals].
      apply pure_wp_ret; eexists x'; split; first done.

      eapply (@pure_evals_cons (tree A)).
      eapply pure_eval_path; cbn -[evals].
      apply pure_wp_ret; eexists r'; split; first done.

      simpl_evals.
      apply pure_wp_ret.
      rewrite !decode_encode_tree decode_encode; reflexivity. }

    cbn.
    prove_same_fringe. }

  {
    (* destruct z eqn: Hz. *)
    (* pure_match. *)
    admit.
    (* Case: [ctx] matches [NodeL (Root, y, ry)] *)
    (* { pure_data. *)
    (*   prove_same_fringe. } *)

    (* (* Case: [ctx] matches [NodeL (NodeL (up, z, rz), y, ry)] *) *)
    (* { eapply pure_eval_app. pure_path. *)
    (*   eapply pure_eval_quadruple. pure_path. pure_path. pure_data. pure_path. *)
    (*   pure_call. *)
    (*   { eapply IH; unfold zlt; subst; auto with arith. } *)
    (*   simpl; intros ? ->. *)
    (*   prove_same_fringe. } *)

    (* (* Case: [ctx] matches [NodeL (NodeR (lz, z, up), y, ry)] *) *)
    (* { eapply pure_eval_app. pure_path. *)
    (*   eapply pure_eval_quadruple. pure_data. pure_path. pure_data. pure_path. *)
    (*   pure_call. *)
    (*   { eapply IH; unfold zlt; subst; auto with arith. } *)
    (*   intros ? ->. *)
    (*   prove_same_fringe. } } *) }

  { admit. }
  (* (* Case: [ctx] matches [NodeR (ly, y, Root)] *) *)
  (* { pure_data. *)
  (*   prove_same_fringe. } *)

  (* (* Case: [ctx] matches [NodeR (ly, y, NodeL (up, z, rz))] *) *)
  (* { eapply pure_eval_app. *)
  (*   pure_path. *)
  (*   eapply pure_eval_quadruple. pure_data. pure_path. pure_data. pure_path. *)
  (*   pure_call. *)
  (*   { eapply IH; unfold zlt; subst; auto with arith. } *)
  (*   intros ? ->. *)
  (*   prove_same_fringe. } *)

  (* (* Case: [ctx] matches [NodeR (ly, y, NodeR (lz, z, up))] *) *)
  (* { eapply pure_eval_app. pure_path. *)
  (*   eapply pure_eval_quadruple. pure_data. pure_path. pure_path. pure_path. *)
  (*   pure_call. *)
  (*   { eapply IH; unfold zlt; subst; auto with arith. } *)
  (*   intros ? ->. *)
  (*   prove_same_fringe. } *)
Admitted.


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

  eapply pure_rec_call with (x := tup) (P := fun x => bst (strict le) x.1.1).
  { apply zlookup_wf. }
  { exact Hbst. }
  clear Hbst tup.
  intros zlookup [[t x] ctx] IH Hpre. simpl in *. fold eval.

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
          { auto. } }
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

