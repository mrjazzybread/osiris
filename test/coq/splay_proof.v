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
  SIMP_specify "splay" (λ (splay : val), True).
Abort.
