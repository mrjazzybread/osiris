From osiris Require Import osiris.
From osiris.semantics Require Export evalprime.
From osiris.proofmode Require Export proofmode. (* TODO *)
From osiris.libs Require Import Stdlib.
From test Require Import splay.

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

Lemma encode_tree_is_encode `{Encode A} :
  ∀ (xs : tree A),
  encode_tree xs = encode xs.
Proof.
  reflexivity.
Qed.

Local Hint Extern 1 (_ = _) =>
  repeat rewrite encode_tree_is_encode : encode.

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

(* -------------------------------------------------------------------------- *)

(* WIP *)

Instance Encode_tuple4
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

(* -------------------------------------------------------------------------- *)

(* Specification of [splay]. *)

Definition splay_spec (splay : val) : Prop :=
  ∀ `{Encode A} (l : tree A) (x : A) (r : tree A) (ctx : zipper A),
  SIMP
    (call splay (encode (l, x, r, ctx)))
    (λ (t' : tree A), True).

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

Lemma Splay__spec:
  let η := EnvCons "Stdlib" Stdlib EnvNil in
  SIMP (eval_mexpr η Splay) (λ (_ : val), True).
Proof.
  intros.
  SIMP.
  SIMP_specify "splay" splay_spec.
  (* Subgoal: prove that [splay] satisfies its specification. *)
  { unfold splay_spec. intros.
    SIMP_enter. SIMP_continue.
    (* Perform case analysis on the zipper [ctx]. *)
    destruct ctx as [| ctx y ry | ly y ctx ]; SIMP.
    (* Case: [Root]. *)
    { SIMP_continue.
      (* For now, the postcondition is True. *)
      tauto. }
    (* Case: [NodeL]. *)
    { (* Perform case analysis on the second level of the zipper. *)
      destruct ctx as [| lz z up | up z rz ]; SIMP; SIMP_continue.
      (* Subcase: [Root]. *)
      { (* For now, the postcondition is True. *)
        tauto. }
      (* Subcase: [NodeL]. *)
      { admit. }
      (* Subcase: [NodeR]. *)
      { admit. }
    }
    (* Case: [NodeR]. *)
    { destruct ctx; admit.
    }
  }
  intros splay Hsplay. (* SIMP_continue. *)
Abort.
