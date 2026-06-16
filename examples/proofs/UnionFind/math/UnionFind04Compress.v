From osiris Require Import osiris.
From stdpp Require Import relations propset.
Require Import UnionFind01Data.

(* -------------------------------------------------------------------------- *)

(* We consider what happens when one performs one step of path compression:
   given an edge from [x] to [y] and a path from [y] to [z], we replace the
   edge from [x] to [y] with an edge from [x] to [z]. *)

(* This is a scoped-down port: it covers only what UnionFind.v's [Mem_compress]
   needs (the definition of [compress] and the lemmas that don't depend on the
   [F x y]/[path F y z] hypotheses). The rest of the original file
   (is_dsf_compress, compress_preserves_is_repr[_direct['], _is_equiv,
   _dsf_per, _descendants_of_roots, _paths_*, the "weak" variants,
   compress_R_compress_agree, compress_compress) characterizes how [compress]
   interacts with a *specific* edge [x -> y] and the path beyond it; that's
   needed for [find_spec_inductive]'s iterated-compression argument
   (UnionFind05IteratedCompression.v), which belongs to the deferred
   function-specification phase, not the Mem/Inv layer. *)

Section PathCompression.

Variable V : Type.
Variable EqV : EqDecision V.
Variable CountableV : Countable V.
Variable F : relation V.
Variable x z : V.

(* Path compression is performed as follows: every edge out of [x] is
   removed, and a new edge from [x] to [z] is installed. *)

Definition compress : relation V :=
  fun a b => (F a b /\ a <> x) \/ (a = x /\ b = z).

(* We have a new edge from [x] to [z]. *)

Lemma compress_x_z:
  compress x z.
Proof. right. split; reflexivity. Qed.

(* Every existing edge whose source is not [x] is preserved. *)

Lemma compress_preserves_other_edges:
  forall v w,
  F v w ->
  v <> x ->
  compress v w.
Proof. intros v w HF Hneq. left. split; assumption. Qed.

(* Every root other than [x] remains a root. *)

Lemma compress_preserves_roots_other_than_x:
  forall r,
  r <> x ->
  is_root V F r ->
  is_root V compress r.
Proof.
  intros r Hneq Hroot w Hcomp.
  destruct Hcomp as [[HF _] | [Heq _]].
  - eapply Hroot; eauto.
  - apply Hneq. exact Heq.
Qed.

Lemma compress_preserves_roots_converse:
  forall r,
  is_root V compress r ->
  is_root V F r.
Proof.
  intros r Hroot w HF.
  destruct (decide (r = x)) as [-> | Hneq].
  - eapply Hroot. right. split; reflexivity.
  - eapply Hroot. left. split; [exact HF | exact Hneq].
Qed.

End PathCompression.
