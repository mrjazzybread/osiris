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


(* -------------------------------------------------------------------------- *)

(* Boilerplate: provide pattern matching lemmas for trees. *)

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

Ltac pattern_hook ::=
  first
    [ pat_pLeaf; intros
    | pat_pNode; intros
    ].

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
        ∀ x, lookup x t' = if eqb x y then true else lookup x t).

Definition member_spec `{Encode A, Ord A, Eq A} member :=
  ∀ (x : A) (t : tree A),
    bst t ->
    pure_call2 member #x #t (λ (b : bool), b = lookup x t).

Local Instance Ord_Z : Ord Z := { lt x y := (x <? y)%Z }.
Local Instance Eq_z : Eq Z := { eqb x y := Z.eqb x y }.


(* -------------------------------------------------------------------------- *)

(* Proof *)

(* The [toplevel] relation takes a module expression, and asserts
   that after evaluating it in the environment comprising of the
   standard library, we learn some postcondition on the environment
   contained in the resulting module structure. *)

(* [env_has_pspecs : list (var * (val -> Prop)) -> env -> Prop] states that
   a given environment certain values, with names and specifications
   given in an association list. *)

Lemma ModuleSpec :
  toplevel __main
    (env_has_pspecs [("insert", insert_spec); ("member", member_spec)]).
Proof.
  (* Evaluating a [MStruct] boils down to evaluating the structure items one by one. *)
  apply module_struct.

  (* Applying [structs_cons] introduces a cut, allowing structure items
     to be individually specified and abstracted as we go through them. *)
  eapply structs_cons.
  { (* Facing a standard [let rec], we use the following lemma
       to specify the resulting value. *)
    eapply struct_letrec_single with (spec := (@insert_spec Z _ _ _)).
    unfold insert_spec.

    intros.

    (* Goal: show that calling [insert] satifies its postcondition.
       We want to proceed by well-founded induction over the arguments.
       We first need to modify the shape of the goal so that Coq can
       properly link the arguments to the postcondition. *)

    match goal with
    | |- pure_call2 _ _ _ ?φ =>
        change φ with
        ((fun '(y, t) =>
            fun t' =>
              ∀ x, lookup x t' = (if eqb x y then true else lookup x t))
           (y, t))
    end.

    (* We can now apply our lemma for recursive calls with two arguments.
       Note that we need to state the relation between the initial
       arguments and the precondition through the relation [P]. *)
    eapply pure_rec_call2 with
      (P := fun '(x1, t1) '(x2, t2) =>
              x1 = x2 /\ t1 = t2 /\ bst t2).
    (* Subgoal: the relation we use for induction is well-founded. *)
    { apply proj_tlt_wf. }
    (* Subgoal: the precondition is met of the initial arguments. *)
    { auto. }

    (* The [pure_rec_call2] lemma then steps into the function body,
       abstracting away the initial arguments.
       This makes us do a little bookeeping before we can proceed. *)
    clear dependent t y.
    intros insert x t IH [??] (-> & -> & Htree).

    (* FIXME: Hoare rule for evaluating anonfuns [pure_eval_anonfun] is broken. *)
    pure_simp.
    pure_enter.

    (* [insert] is defined by using the [function] keyword, which is
       translated as [fun x -> match x with ...] This results in the
       addition of  "__osiris_anonymous_arg" to the environment. *)
    eapply pure_eval_match. { pure_path. reflexivity. }
    (* The [pure_match] tactic creates one subgoal per branch of
       the pattern match. It uses the information gained by pattern
       matching to rewrite the term being matched on, and to prove
       that the match is exhaustive. *)
    pure_match.

    (* First Branch. *)
    { (* When evaluating a constructor, [pure_data] can deal with "simple"
         arguments that are either also constructors or variables. *)
      pure_data.
      (* Goal: show that the postcondition holds when [t = Leaf]. *)
      intros y. simpl.
      (* TODO: tactic that does three cases: y < x, y > x, and y = x. *)
      destruct (y <? x)%Z eqn:Hlt.
      { destruct (y =? x)%Z eqn:Heq; lia. }
      destruct (x <? y)%Z eqn:Hgt.
      { destruct (y =? x)%Z eqn:Heq; lia. }
      destruct (y =? x)%Z eqn:Heq; lia. }

    (* Second Branch. *)
    { (* When faced with an [if .. then .. else], we have a choice of
         two lemmas to apply depending on if we want the resulting
         information to be in bool or Prop. *)
      eapply pure_eval_ifthenelse.
      { (* The [_ < _] operator is translated to less-than on
           machine integers. Note that this requires us to prove
           representability. *)
        eapply pure_eval_EOpLt.
        - pure_path; reflexivity.
        - pure_path; reflexivity.
        - admit.
        - admit. }
      (* We now have two subgoals: one for [then], and one for [else]. *)
      { intros Hlt; simpl in Hlt.

        (* Here [pure_data] does not work because one of the arguments
           is a function call. We thus need to resort to a lemma
           specialized to 3-argument constructors.  *)
        eapply pure_eval_data3; eapply pure_eval_triple.
        (* We are now faced with a recursive call. We use the following
           lemma to insert a cut. Note that the lemma is specialized to
           function calls wit two arguments. *)
        eapply pure_eval_app2_conseq; try (pure_path; reflexivity).
        { (* We can now use our induction hypothesis, specialized to
             our new arguments. *)
          eapply IH with (a := (x, t1)).
          { (* Subgoal: show that the well-founded measure decreases. *)
            unfold proj_tlt, tlt. simpl. lia. }
          { (* Subgoal: show the precondition holds on these arguments. *)
            repeat split. by inversion Htree. } }

        (* We are now post-cut, we learn that recursive call produced
           a value satisfying the functions postcondition. *)
        intros t' Htree'; simpl in Htree'.
        (* Evaluate the two remaining arguments of the constructor. *)
        pure_path. pure_path.
        (* Show that the value produced from the constructor applied
           to its arguments is well reflected by a Node.
           TODO: We would like to hide such subgoals. *)
        split; [ encode | ].

        (* Goal: show that the postcondition holds in this branch of the [if]. *)
        intros y; simpl.
        destruct (y <? a)%Z eqn:Hlty.
        { by rewrite Htree'. }
        destruct (a <? y)%Z eqn:Hgty.
        { assert ((y =? x)%Z = false) as -> by lia.
          reflexivity. }
        assert ((y =? a)%Z = true) as -> by lia.
        by destruct (y =? x)%Z. }

      (* Other branch of the [if]. *)
      { intros Hge; simpl in Hge.
        (* We proceed identically to the first branch. *)
        eapply pure_eval_ifthenelse.
        { eapply pure_eval_EOpGt.
          - pure_path. reflexivity.
          - pure_path. reflexivity.
          - admit.
          - admit. }

        { (* First branch of the second [if]. *)
          intros Hgt; simpl in Hgt.
          (* Again, we cannot use [pure_data], now because of the
             argument of the constructor instead of the first. *)
          eapply pure_eval_data3; eapply pure_eval_triple.
          pure_path. pure_path.
          eapply pure_eval_app2_conseq; try (pure_path; reflexivity).
          { (* Apply the induction hypothesis. *)
            eapply IH with (a := (x, t2)).
            { unfold proj_tlt, tlt; simpl; lia. }
            { repeat split; by inversion Htree. } }
          intros t' Htree'; simpl in Htree'.
          split; [ encode | ].
          (* Show the postcondition. *)
          intros y; simpl.
          destruct (y <? a)%Z eqn:Hlty.
          { assert ((y =? x)%Z = false) as -> by lia.
            reflexivity. }
          destruct (a <? y)%Z eqn:Hgty.
          { by rewrite Htree'. }
          assert ((y =? a)%Z = true) as -> by lia.
          by destruct (y =? x)%Z. }

        (* Second branch of the second [if]. *)
        { intros Hle; simpl in Hle.
          assert (x = a) as -> by lia; clear Hge Hle.
          pure_data.
          (* Show the postcondition. *)
          intros y; simpl.
          destruct (y <? a)%Z eqn:Hlt.
          { assert ((y =? a)%Z = false) as -> by lia.
            reflexivity. }
          destruct (a <? y)%Z eqn:Hgt.
          { assert ((y =? a)%Z = false) as -> by lia.
            reflexivity. }
          assert ((y =? a)%Z = true) as -> by lia.
          reflexivity. } } } }

  (* We have now finished proving that [insert] satisfies its spec.
     We proceed by abstracting away its implementation, and
     elaborating the current environment with the abstracted value. *)
  intros [??] (insert & Hinsert & -> & ->).


  eapply structs_cons.
  { (* Proceed with [let rec member = ...] *)
    eapply struct_letrec_single with (spec := member_spec).
    unfold member_spec.
    intros x t Ht.

    (* Again, we wish to proceed by induction over the arguments,
       and we have to change the shape of the goal for the
       [pure_rec_call2] lemma to be correctly applied. *)
    match goal with
    | |- pure_call2 _ _ _ ?φ =>
        change φ with ((fun '(x, t) b => b = lookup x t) (x, t))
    end.
    (* The precondition is that the second argument is a BST. *)
    eapply pure_rec_call2 with (P := fun '(x1, t1) '(x2, t2) =>
                                       x1 = x2 /\ t1 = t2 /\ bst t2).
    { apply proj_tlt_wf. }
    { repeat split; assumption. }
    clear dependent x t.
    intros member x t IH [??] (-> & -> & Ht).

    pure_simp.
    pure_enter.
    eapply pure_eval_match. { pure_path; reflexivity. }
    pure_match.

    (* First branch of the match. *)
    { pure_data; reflexivity. }

    (* Second branch of the match. *)
    { (* Here we use the boolean version of the ifthenelse lemma
         because we want to manipulate the retuned boolean value. *)
      eapply pure_eval_ifthenelse_bool.
      { (* Comparison operators also have boolean versions. *)
        eapply pure_eval_EOpLt_bool.
        - pure_path; reflexivity.
        - pure_path; reflexivity.
        - admit.
        - admit. }

      (* First branch of the first [if]. *)
      { intros Hlt; simpl in Hlt.
        eapply pure_eval_app2_conseq; try (pure_path; reflexivity).
        { (*Apply the induction hypothesis. *)
          eapply IH with (a := (x, t1)).
          { (* Subgoal: the measure is decreasing on the arguments. *)
            unfold proj_tlt, tlt; simpl; lia. }
          { (* Subgoal: show the arguments satisfy the precondition. *)
            repeat split; by inversion Ht. } }
        intros b ->; simpl.
        (* Goal: show the postcondition holds. *)
        assert ((x <? a)%Z = true) as -> by lia.
        reflexivity. }

      (* Second branch of the first [if]. *)
      { intros Hge; simpl in Hge.
        eapply pure_eval_ifthenelse_bool.
        { eapply pure_eval_EOpGt_bool.
          - pure_path; reflexivity.
          - pure_path; reflexivity.
          - admit.
          - admit. }

        (* First branch of the second [if]. *)
        { intros Hlt; simpl in Hlt.
          eapply pure_eval_app2_conseq; try (pure_path; reflexivity).
          { (* Apply the induction hypothesis. *)
            eapply IH with (a := (x, t2)).
            { (* Subgoal: show the measure is decreasing on the arguments. *)
              unfold proj_tlt, tlt; simpl; lia. }
            { (* Subgoal: show the arguments satify the precondition. *)
              repeat split; by inversion Ht. } }
          intros b ->; simpl.
          assert ((x <? a)%Z = false) as -> by lia.
          assert ((a <? x)%Z = true) as -> by lia.
          reflexivity. }

        (* Second branch of the second [if]. *)
        { intros Hle; simpl in Hle.
          pure_data.
          simpl.
          assert ((x <? a)%Z = false) as -> by lia.
          assert ((a <? x)%Z = false) as -> by lia.
          lia. } } } }

  (* Abstracting away the implementation of [member]. Courtesy of
     [struct_letrec_single], which shapes the cut created by
     [structs_cons].  *)
  intros [??] (member & Hmember & -> & ->).

  (* We have now traversed the whole module, all that remains is
     to show the module specification.*)
  apply structs_nil.
  simpl. auto.
Admitted.
