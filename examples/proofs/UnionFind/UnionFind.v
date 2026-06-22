From osiris Require Import osiris.
From osiris.examples Require Import og_UnionFindBasic.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link UnionFind04Compress
  UnionFind06Join UnionFind05IteratedCompression UnionFind07Reachable.

From Stdlib Require Import FunctionalExtensionality.

(* An object in the Union Find data structure is represented by an
   heap_lang location. *)
Notation elem := loc.

Record link `{Encode A} : Type := { parent : elem }.
Record root `{Encode A} : Type := { rank : Z; value : A }.

(* The logical type of the content of a vertex. *)
Inductive content `{Encode A} :=
| Root : record -> content
| Link : record -> content.

Local Instance val_of_content `{Encode A} : Encode (@content A _) :=
  { encode' := λ c, match c with
                    | Root r => VData "Root" [ #r ]
                    | Link r => VData "Link" [ #r ]
                    end }.

Local Instance root_data `{Encode A} : Data "Root" τ[record] (@content A _) :=
  { ctor_apply := λ r, Root r;
    ctor_encode := λ r, eq_refl }.

Local Instance link_data `{Encode A} : Data "Link" τ[record] (@content A _) :=
  { ctor_apply := λ r, Link r;
    ctor_encode := λ r, eq_refl }.

(* [root]/[link] are mutable OCaml records, so at the heap level a vertex's
   content (Root/Link) only stores a [record], i.e. a pointer to a *separate*
   heap block holding the record's own fields (rank/value, or parent). The
   [RecordRepr] class (in record_rules.v) lets us reason about that second
   block using the named [root]/[link] types instead of raw [types] tuples. *)

Instance root_record : RecordRepr (root (A:=val)) τ[Z; val] Mut :=
  { repr_to_types rt := (rt.(rank), rt.(value));
    types_to_repr := λ k v, {| rank := k; value := v |};
    repr_id := λ '(k, v), eq_refl }.

Instance link_record : RecordRepr (link (A:=val)) τ[elem] Mut :=
  { repr_to_types lk := lk.(parent);
    types_to_repr := λ y, {| parent := y |};
    repr_id := λ y, eq_refl }.

Section UnionFind.

Context `{!osirisGS Σ}.

Implicit Types x y r : elem.
Implicit Types v : val.
Implicit Types D : gset elem.  (* domain *)
Implicit Types F : elem -> elem -> Prop.      (* edges *)
Implicit Types R : elem -> elem.     (* functional view of [is_repr F] *)
Implicit Types V : elem -> val.      (* data stored at the roots *)

(* -------------------------------------------------------------------------- *)

(* [fcupdate f P b] coincides with [f] everywhere, except that it maps every
   point satisfying the (decidable) predicate [P] to [b]. *)

Definition fcupdate {A B : Type} (f : A -> B) (P : A -> Prop)
    `{!forall a, Decision (P a)} (b : B) : A -> B :=
  fun a => if decide (P a) then b else f a.

(* The predicate [Inv ...] relates the mathematical graph encoded by [D/F] and
   the view that is exposed to the client, which is encoded by [D/R/V].
   In short,
   1. [D/F] form a disjoint set forest, as per [is_dsf];
   2. [R] is included in [is_repr F],
      which means that [R x = y] implies [is_repr F x y],
      or in other words, [R] agrees with [F];
   3. [V] agrees with [R]. *)

(* We drop the rank component [K] and the time-credit/potential bookkeeping
   ([Phi]/[TC]/[TR]) that the original (CFML) development carried for its
   amortized-complexity analysis; this port is not redoing that analysis. *)

Record Inv D F R V : Prop := {
  Inv_dsf  : is_dsf elem _ _ D F;
  Inv_incl : fun_in_rel elem R (is_repr elem F);
  Inv_data : forall x, V x = V (R x)
}.

Local Hint Resolve Inv_dsf Inv_incl Inv_data : core.

(* -------------------------------------------------------------------------- *)

(* [ownRepr r qp a] (from record_rules.v) owns the fields of the record
   block pointed to by [r], viewed through the named record type [A] (here
   [root] or [link]) rather than as a raw [types] tuple. *)

(* The *logical* content of a vertex, as exposed to [Mem]/[Inv] — i.e. with
   the rank dropped and the record-pointer indirection hidden. [pointsto_M]
   below is what relates this logical view back to the actual two-level
   heap representation (vertex location -> content -> record block). *)

Inductive lcontent :=
| LRoot : val -> lcontent
| LLink : elem -> lcontent.

(* The predicate [Mem ...] relates the mathematical graph encoded by [D/F/V]
   and the memory encoded by the finite map [LM]. In short,
    1. [LM]'s domain is exactly [D] (in particular, no entries outside [D] —
       this is what lets us derive that a freshly-allocated vertex is not in
       [D] from the fact that it cannot already have an [LM] entry);
    2. the links in [LM] coincide with the links in [F];
    3. the data stored at a root in [LM] agrees with [V]. (We don't track the
       rank's value at all, having dropped the complexity analysis it was
       for; the actual rank field stored in memory is existentially
       quantified away in [pointsto_M] below.) *)

Definition Mem D F V (LM : gmap elem lcontent) : Prop :=
  dom LM = D /\
  forall x, x ∈ D ->
    match LM !! x with
    | Some (LLink y) => F x y
    | Some (LRoot v) => is_root elem F x /\ v = V x
    | None => False
    end.

(* [rec_repr lr lc] owns the record block at [lr] backing a vertex whose
   logical content is [lc]. A root's rank is not tracked, so it stays
   existential; a link stores its parent directly. *)

Definition rec_repr (lr : record) (lc : lcontent) : iProp Σ :=
  match lc with
  | LRoot v => ∃ k : Z, ownRepr lr 1 ({| rank := k; value := v |} : root (A:=val))
  | LLink y => ownRepr lr 1 ({| parent := y |} : link (A:=val))
  end.

(* The content *value* stored in [x]'s ref cell: a [Root]/[Link] tag wrapping
   the pointer [lr] to [x]'s record block. *)

Definition content_of (lr : record) (lc : lcontent) : @content val _ :=
  match lc with LRoot _ => Root lr | LLink _ => Link lr end.

(* [pointsto_M ρ LM] asserts ownership of the whole two-level heap: for each
   vertex [x], its content cell [x ↦ #(content_of (ρ x) lc)] and the record
   block [ρ x] it points to. Crucially the record-location map [ρ] is *exposed*
   rather than existentially hidden per entry. Since [find] only ever mutates
   record *fields* (never a content cell, and never reallocating a record),
   [ρ] is an invariant of [find]: it comes back verbatim from the recursive
   call, so [x]'s own record is recoverable by name afterwards. This is what
   lets [find] recurse on the *whole* structure — no framing of [x]'s
   resources out of the recursion, and no reachable-set restriction. *)

Definition pointsto_M (ρ : elem -> record) (LM : gmap elem lcontent) : iProp Σ :=
  ([∗ map] x ↦ lc ∈ LM, x ↦ #(content_of (ρ x) lc) ∗ rec_repr (ρ x) lc)%I.

(* [UF D R V] is the representation predicate. It is an abstract predicate:
   the client uses this predicate, but does not know how it is defined. It
   quantifies existentially over [F/LM], which therefore are not exposed to
   the client. *)

Definition UF D R V : iProp Σ :=
  (∃ F ρ LM,
  ⌜ Inv D F R V ⌝ ∗
  ⌜ Mem D F V LM ⌝ ∗
  pointsto_M ρ LM)%I.

(* -------------------------------------------------------------------------- *)

(* The functions [V] and [R] are compatible with [R]. In other words, every
   member of an equivalence class must have the same image through [V] (see
   [Inv_data]) and through [R]. For this reason, when we wish to update one of
   these functions, we must update it not just at one point, but at a whole
   equivalence class. *)

(* The function [update1 R f x b] coincides with the function [f] everywhere,
   except on the equivalence class of [x], whose elements are mapped to [b]. *)

Definition update1 {B : Type} (f : elem -> B) R x (b : B) :=
  fcupdate f (fun z => R z = R x) b.

(* The function [update2 R f x y b] coincides with the function [f] everywhere,
   except on the equivalence classes of [x] and [y], whose elements are mapped
   to [b]. *)

Definition update2 {B : Type} (f : elem -> B) R x y (b : B) :=
  fcupdate f (fun z => R z = R x \/ R z = R y) b.

Lemma update2_V_self :
  ∀ D F R V x,
    Inv D F R V →
    update2 V R x x (V x) = V.
Proof.
  intros. unfold update2. unfold fcupdate.
  extensionality a. case_decide; last reflexivity.
  pose proof H.(Inv_data D F R V) as HeqR.
  rewrite (HeqR x) (HeqR a).
  destruct H0; by rewrite H0.
Qed.

Lemma update2_R_self :
  ∀ R x,
    R x = x →
    update2 R R x x x = R.
Proof.
  intros R x HeqR. unfold update2. unfold fcupdate.
  extensionality a. case_decide; last reflexivity.
  rewrite -HeqR.
  destruct H; by rewrite H.
Qed.

Lemma update2_root :
  ∀ (B : Type) (f : elem → B) R x y b,
    idempotent elem R →
    update2 f R (R x) (R y) b = update2 f R x y b.
Proof.
  intros B f R x y b Hidem.
  unfold update2, fcupdate.
  extensionality a.
  rewrite !Hidem.
  case_decide; reflexivity.
Qed.

Lemma update2_sym :
  ∀ B (f : elem → B) R x y b,
    update2 f R x y b = update2 f R y x b.
Proof.
  intros B F R x y b.
  unfold update2, fcupdate.
  extensionality a.
  case_decide; case_decide; tauto.
Qed.

(* When [x] and [y] are already in the same equivalence class ([R x = R y]),
   updating both their classes to [R x] (the "diagonal" case, as opposed to
   [update2_R_self]'s [x = y]) is a no-op on [R]/[V]. This is what [union]'s
   fast path (testing [x == y] physically after [find]-ing both) needs: when
   the test succeeds, no actual merge happened, so the invariant carries
   over unchanged. *)

Lemma update2_R_diag :
  ∀ R x y, R x = R y → update2 R R x y (R x) = R.
Proof.
  intros R x y Heq.
  unfold update2, fcupdate.
  extensionality a.
  case_decide as Hcase; [|reflexivity].
  destruct Hcase as [Hax|Hay].
  - symmetry; exact Hax.
  - rewrite Heq. symmetry; exact Hay.
Qed.

Lemma update2_V_diag :
  ∀ D F R V x y,
    Inv D F R V → R x = R y → update2 V R x y (V (R x)) = V.
Proof.
  intros D F R V x y HI Heq.
  pose proof (Inv_data _ _ _ _ HI) as HVeq.
  unfold update2, fcupdate.
  extensionality a.
  case_decide as Hcase; [|reflexivity].
  rewrite (HVeq a).
  destruct Hcase as [Hax|Hay].
  - rewrite Hax. reflexivity.
  - rewrite Hay Heq. reflexivity.
Qed.

Lemma Inv_update2_diag :
  ∀ D F R V x y,
    Inv D F R V → R x = R y →
    Inv D F (update2 R R x y (R x)) (update2 V R x y (V (R x))).
Proof.
  intros D F R V x y HI Heq.
  rewrite (update2_R_diag R x y Heq).
  rewrite (update2_V_diag D F R V x y HI Heq).
  exact HI.
Qed.

(* TODO: the algebraic lemmas about [update1]/[update2] (update2_V_self,
   update2_R_self, update2_root, update2_sym in the original) are only used
   by the OCaml function specs (link_spec/union_spec), which we're deferring.
   They also need function extensionality (their statements are equalities
   of functions, not pointwise equalities) — fine to import
   [Coq.Logic.FunctionalExtensionality] for that when we get there, since
   it's a much milder axiom than the classical-logic gap we left open in
   UnionFind01Data; just flagging it for when this comes back up. *)

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Inv]. *)

(* If [x] is in the domain and [r] is its representative, then [r] is in the
   domain and [r] is its own representative. *)

Lemma Inv_root : forall D F R V x r,
  Inv D F R V ->
  x ∈ D ->
  r = R x ->
  r ∈ D /\ R r = r.
Proof.
  intros D F R V x r [Hdsf Hincl Hdata] Hx ->.
  split.
  - eapply sticky_R; eauto.
  - eapply idempotent_R; eauto.
Qed.

(* The invariant is preserved when a new element [r] is created and the
   function [V] is updated at [r] in an arbitrary manner. *)

Lemma Inv_make : forall D R F V D' V' r v,
  Inv D F R V ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  V' = update1 V R r v ->
  Inv D' F R V'.
Proof.
  intros D R F V D' V' r v [Hdsf Hincl Hdata] Hr -> ->.
  constructor.
  - apply is_dsf_create. exact Hdsf.
  - exact Hincl.
  - intros x0. unfold update1, fcupdate.
    assert (Hidem : R (R x0) = R x0) by (eapply idempotent_R; eauto).
    rewrite Hidem.
    destruct (decide (R x0 = R r)) as [Heq | Hneq].
    + reflexivity.
    + apply Hdata.
Qed.

(* The invariant is preserved by updating [V] at one equivalence class. *)

Lemma Inv_update1 : forall D F R V x v,
  Inv D F R V ->
  Inv D F R (update1 V R x v).
Proof.
  intros D F R V x v [Hdsf Hincl Hdata].
  constructor; [exact Hdsf | exact Hincl | ].
  intros x0. unfold update1, fcupdate.
  assert (Hidem : R (R x0) = R x0) by (eapply idempotent_R; eauto).
  rewrite Hidem.
  destruct (decide (R x0 = R x)) as [Heq | Hneq].
  - reflexivity.
  - apply Hdata.
Qed.

(* The invariant is preserved by a [link] operation. *)

(* The hypothesis is that the invariant holds and [x] and [y] are distinct
   roots in the domain. The conclusion is that the invariant holds again,
   with [x]'s equivalence class folded into [y]'s (so [y] becomes the new
   representative).

   The original picked whichever of [x]/[y] becomes the new representative
   based on rank (new_repr_by_rank/link_by_rank_F/K/R), to keep the trees
   balanced for its complexity bound. We drop that: here [y] is *always*
   the side that wins, and the (deferred) function spec for [link]/[union]
   is responsible for calling this with [x]/[y] in whichever order the
   actual rank comparison picked — the math doesn't care which. We also drop
   the potential ([Phi]) conclusion, and the [Inv_link] Ltac helper that
   existed to discharge the rank-equations side goals (not needed once
   there's no rank to compute). *)

(* [Inv_link]'s own [R'] is stated via [link_R] (the math-side construction:
   redirect every element of [x]'s class to [y]), but [union]'s spec states
   its postcondition via [update2 R R x y (R y)] (mapping *both* [x]'s and
   [y]'s classes to [y]'s value, matching [union]/[link]'s general shape).
   They agree pointwise given [y] is already its own representative — that's
   what this lemma packages, so [union_proof] can equate the two. *)

Lemma link_R_eq_update2 :
  forall R x y, R y = y -> forall t, UnionFind03Link.link_R elem _ x y R t = update2 R R x y y t.
Proof.
  intros R x y Hy t. unfold UnionFind03Link.link_R, update2, fcupdate.
  destruct (decide (R t = R x)) as [H1|H1].
  - destruct (decide (R t = R x \/ R t = R y)) as [_|Hc]; [reflexivity|exfalso; apply Hc; left; exact H1].
  - destruct (decide (R t = R x \/ R t = R y)) as [[H2|H2]|H3].
    + congruence.
    + rewrite H2. exact Hy.
    + reflexivity.
Qed.

Lemma Inv_link: forall D R F V F' V' x y,
  Inv D F R V ->
  x ≠ y ->
  x ∈ D ->
  y ∈ D ->
  R x = x ->
  R y = y ->
  F' = UnionFind03Link.link elem F x y ->
  V' = update2 V R x y (V y) ->
  Inv D F' (UnionFind03Link.link_R elem _ x y R) V'.
Proof.
  intros D R F V F' V' x y [Hdsf Hincl Hdata] Hneq Hx Hy HRx HRy -> ->.
  assert (Hrootx : is_root elem F x) by (eapply R_self_is_root; eauto).
  assert (Hrooty : is_root elem F y) by (eapply R_self_is_root; eauto).
  constructor.
  - eapply is_dsf_link; eauto.
  - eapply link_R_link_agree; eauto.
  - intros w.
    unfold update2, fcupdate, link_R.
    assert (Hidem : forall t, R (R t) = R t) by (intros t; eapply idempotent_R; eauto).
    destruct (decide (R w = R x)) as [Hwx | Hwx].
    + destruct (decide (R w = R x \/ R w = R y)) as [_|Hc].
      * destruct (decide (R y = R x \/ R y = R y)); reflexivity.
      * exfalso; apply Hc; left; exact Hwx.
    + rewrite (Hidem w).
      destruct (decide (R w = R x \/ R w = R y)) as [_|_]; [reflexivity | apply Hdata].
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Mem]. *)

(* If [x] is in the domain and is a root, then [M] maps [x] to [Root]
   with rank [K x] and data [V x]. *)

Lemma Mem_root : forall D R F M V x,
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  R x = x ->
  M !! x = Some (LRoot (V x)).
Proof.
  intros D R F M V x HInv [Hdom HM] Dx Rxx.
  specialize (HM x Dx).
  destruct (M !! x) as [[w | y] | ] eqn:Heq.
  - f_equal. f_equal. destruct HM as [_ Hv]. congruence.
  - exfalso. assert (Hrootx : is_root elem F x) by (eapply R_self_is_root; eauto).
    eapply Hrootx; eauto.
  - exfalso. exact HM.
Qed.

(* Conversely, if [M] maps [x] to [LRoot], then [x] is a root whose data is
   as predicted by [M]. (We don't track a rank value at all anymore.) *)

Lemma Mem_root_inv : forall D F M V x vx,
  Mem D F V M ->
  x ∈ D ->
  M !! x = Some (LRoot vx) ->
  is_root elem F x /\ vx = V x.
Proof.
  intros D F M V x vx [Hdom HM] Dx HE.
  specialize (HM x Dx). rewrite HE in HM. exact HM.
Qed.

(* [Mem] is preserved when a new element [r] is created and the function
   [V] is updated at [r] in an arbitrary manner. (The original also
   inserted rank 0 at [r]; since we don't track rank, there's nothing to
   record there beyond [LRoot v].) *)

Lemma Mem_make : forall D R F D' r M V v,
  Inv D F R V ->
  Mem D F V M ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  Mem D' F (update1 V R r v) (<[r:=LRoot v]>M).
Proof.
  intros D R F D' r M V v HInv [Hdom HM] Hr ->.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros x Hx.
    apply elem_of_union in Hx. destruct Hx as [Hx | Hx%elem_of_singleton].
    + assert (Hxr : x <> r) by set_solver.
      rewrite lookup_insert_ne; [|exact (not_eq_sym Hxr)].
      specialize (HM x Hx).
      destruct (M !! x) as [[v0|y]|] eqn:Heq; [|exact HM|exact HM].
      split; [tauto|].
      unfold update1, fcupdate. destruct (decide (R x = R r)) as [Heqr|Hner].
      * exfalso. assert (HRr : R r = r) by (eapply R_is_identity_outside_D; eauto).
        destruct HInv as [Hdsf Hincl _].
        assert (Hxd : R x ∈ D) by (eapply sticky_R; eauto).
        rewrite Heqr HRr in Hxd. set_solver.
      * tauto.
    + subst x. rewrite lookup_insert_eq. split.
      * eapply only_roots_outside_D; eauto.
      * unfold update1, fcupdate.
        destruct (decide (R r = R r)) as [_|Hc]; [reflexivity|exfalso; apply Hc; reflexivity].
Qed.

(* [Mem] is preserved by installing a link from a root [x] to a root [y].
   (The original had a separate [Mem_link_incr] for the case where [x] and
   [y] have equal rank, which also increments [y]'s rank; since we don't
   track rank, that's just this same lemma — the rank field still gets
   incremented in memory, but [Mem] doesn't care what value ends up there.) *)

Lemma Mem_link : forall D F R M V V' x y,
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  x = R x ->
  y = R y ->
  V' = update2 V R x y (V y) ->
  Mem D (UnionFind03Link.link elem F x y) V' (<[x:=LLink y]>M).
Proof.
  intros D F R M V V' x y HInv [Hdom HM] Hx Hxr Hyr ->.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a Da.
    specialize (HM a Da).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply link_appears.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[w|y']|] eqn:Heq; [|apply link_previous; exact HM | exact HM].
      destruct HM as [Hroota Hva].
      split.
      * apply is_root_link; [exact Hroota | congruence].
      * assert (Hra : R a = a) by (eapply is_root_R_self; eauto).
        unfold update2, fcupdate.
        destruct (decide (R a = R x \/ R a = R y)) as [Hin|Hout].
        -- rewrite Hra in Hin. destruct Hin as [Hin|Hin].
           ++ exfalso. apply Hne. congruence.
           ++ congruence.
        -- congruence.
Qed.

(* [Mem] is preserved by installing a direct link from [x] to [y] during
   path compression. *)

Lemma Mem_compress : forall D F M V x y,
  Mem D F V M ->
  x ∈ D ->
  Mem D (compress elem F x y) V (<[x:=LLink y]>M).
Proof.
  intros D F M V x y [Hdom HM] Dx.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a Da.
    specialize (HM a Da).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply compress_x_z.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[w|y']|] eqn:Heq;
        [|apply compress_preserves_other_edges; [exact HM | congruence] | exact HM].
      destruct HM as [Hroota Hva]. split; [|exact Hva].
      apply compress_preserves_roots_other_than_x; [congruence | exact Hroota].
Qed.

(* [Mem] is preserved when [V] is updated at one equivalence class and [M]
   is updated at the representative element. *)

Lemma Mem_update1 : forall D R F M V r x v,
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  r = R x ->
  Mem D F (update1 V R x v) (<[r := LRoot v]>M).
Proof.
  intros D R F M V r x v HInv [Hdom HM] Hx ->.
  assert (Hrr : R x ∈ D /\ R (R x) = R x) by (apply (Inv_root _ _ _ _ _ _ HInv Hx eq_refl)).
  destruct Hrr as [Hrd Hrr].
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a Da.
    specialize (HM a Da).
    destruct (decide (R x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. split.
      * eapply R_self_is_root; eauto.
      * unfold update1, fcupdate.
        rewrite Hrr. destruct (decide (R x = R x)) as [_|Hc]; [reflexivity|exfalso; apply Hc; reflexivity].
    + rewrite lookup_insert_ne; [|exact Hne].
      destruct (M !! a) as [[v0|y]|] eqn:Heq; [|exact HM|exact HM].
      destruct HM as [Hroota Hva]. split; [exact Hroota|].
      unfold update1, fcupdate. destruct (decide (R a = R x)) as [Heqr|_]; [|exact Hva].
      exfalso. apply Hne. assert (HRa : R a = a) by (eapply is_root_R_self; eauto). congruence.
Qed.

(* A vertex with no [LM] entry is, by [Mem]'s domain equation, not in [D]. *)

Lemma Mem_not_elem_of_dom : forall D F V M x,
  Mem D F V M ->
  M !! x = None ->
  x ∉ D.
Proof.
  intros D F V M x [Hdom _] Heq.
  rewrite -Hdom. eapply not_elem_of_dom_2. exact Heq.
Qed.

(* If [pointsto_M LM] and [x ↦ v] are both owned, [x] cannot already be an
   [LM] entry (otherwise we'd own [x] twice). Combined with [Mem]'s domain
   equation, this is how we show a freshly-allocated vertex is not in [D]. *)

Lemma pointsto_M_fresh : forall ρ (LM : gmap elem lcontent) x v,
  pointsto_M ρ LM -∗ x ↦ v -∗ ⌜LM !! x = None⌝.
Proof.
  iIntros (ρ LM x v) "HM Hx".
  destruct (LM !! x) as [lc|] eqn:Heq; [|done].
  iExFalso.
  iDestruct (big_sepM_lookup with "HM") as "[Hx' _]"; [exact Heq|].
  iCombine "Hx Hx'" gives %Hbad.
  destruct Hbad as [Hbad _]. exfalso; eapply dfrac_full_exclusive; exact Hbad.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [make]. *)

(* [record]/[ERecord] operations need the records they build to fit within
   [max_array_length] (records are heap blocks, like arrays); since our
   records only ever have 1 or 2 fields, this is a mild assumption. *)

Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

(* The function call [make v] requires [UF D R V]. It returns a new element
   [x], that is, [x] is not in [D]. It updates the data structure to
   [UF D' R V'], where:
   1. [D'] is [D] extended with [x];
   2. [R'] is [R];
   3. [V'] is [V] extended with a mapping of [x] to [v].
   (The original additionally required/tracked O(1) time credits; we don't,
   having dropped the complexity analysis.) *)

Definition make_spec : val → microvx → iProp Σ :=
  λ v m,
    (∀ D R V,
       UF D R V -∗
       imp m {{ λ (x : elem), UF (D ∪ {[x]}) R (update1 V R x v) ∗ ⌜x ∉ D /\ R x = x⌝ }})%I.

Definition make := EAnonFun __fun1.

Lemma imp_make η :
  ⊢ imp (eval η make) {{ λ c, □ iSpec τ[val] c make_spec }}.
Proof.
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  iIntros (D R V) "HUF".
  iApply imp_please; iNext.
  imp_match val.
  iApply (imp_wand with "[]").
  { iApply (imp_ERef2 (A:=@content val _)
              (λ c, ∃ rr, ⌜c = Root rr⌝ ∗ ownRepr rr 1 ({|rank:=0;value:=v|}:root(A:=val)))%I).
    imp_data.
    { (* Construct root record. *)
      iApply (imp_record (τ:=τ[_;_])).
      - rewrite /τ_length /=. lia.
      - iApply imp_evals_cons.
        + imp_int.
        + iApply imp_evals_singleton. imp_path. }
    simpl. iIntros (r) "(% & % & Hown & (-> & ->))".
    by iFrame "Hown". }
  iIntros (x) "(%a & (%rr & -> & Hown) & Hx)".
  iDestruct "HUF" as (F ρ LM) "(%HInv & %HMem & HptM)".
  iDestruct (pointsto_M_fresh with "HptM Hx") as %HxLM.
  assert (HxD : x ∉ D) by (eapply Mem_not_elem_of_dom; eauto).
  iSplitR "".
  - (* extend [ρ] at the fresh vertex [x] with its just-allocated record [rr]. *)
    iExists F, (fun z => if decide (z = x) then rr else ρ z), (<[x:=LRoot v]>LM).
    iSplit; [iPureIntro; eapply Inv_make; eauto|].
    iSplit; [iPureIntro; eapply Mem_make; eauto|].
    rewrite /pointsto_M big_sepM_insert; [|exact HxLM].
    iSplitL "Hown Hx".
    + rewrite decide_True; [|reflexivity]. unfold content_of, rec_repr. iFrame.
    + iApply (big_sepM_mono with "HptM"). iIntros (z lc Hz) "He".
      rewrite decide_False; [done|]. intros ->. rewrite Hz in HxLM. discriminate.
  - iPureIntro. split; [exact HxD|].
    eapply R_is_identity_outside_D; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about the representation predicate and about [pointsto_M].
   (These are part of the old, not-yet-ported function-specification
   machinery below — they still reference the single-level [content]/
   [val_of_content] encoding, not our two-level [lcontent]/[pointsto_M].) *)


(* [pointsto_M] depends on [ρ] only through the vertices in [LM]'s domain, so
   two record-location maps that agree there yield the same predicate. (Used by
   [make] to extend [ρ] at the fresh vertex without disturbing the rest.) *)

Lemma pointsto_M_proper ρ1 ρ2 LM :
  (forall x lc, LM !! x = Some lc -> ρ1 x = ρ2 x) ->
  pointsto_M ρ1 LM ⊣⊢ pointsto_M ρ2 LM.
Proof.
  intros Hag. apply big_sepM_proper. intros x lc Hx. rewrite (Hag x lc Hx). done.
Qed.

(* [pointsto_M_acc] gives access to a single vertex [x]'s content cell and its
   record block [ρ x], plus a wand to put the record back — possibly with an
   updated field, for path compression — and recover [pointsto_M] at the
   updated map. The record location [ρ x] is named (not existential), so the
   wand reinstalls *that* record: this is what makes [find]'s in-place
   [link.parent <- z] go through unchanged after the recursive call. *)

Lemma pointsto_M_acc ρ LM x lc :
  LM !! x = Some lc ->
  pointsto_M ρ LM -∗
    x ↦ #(content_of (ρ x) lc) ∗ rec_repr (ρ x) lc ∗
    (∀ lc', x ↦ #(content_of (ρ x) lc') -∗ rec_repr (ρ x) lc' -∗ pointsto_M ρ (<[x:=lc']> LM)).
Proof.
  intros HLM. iIntros "HM". unfold pointsto_M.
  iDestruct (big_sepM_delete _ LM x lc HLM with "HM") as "[[Hx Hrec] HM]".
  iFrame "Hx Hrec". iIntros (lc') "Hx Hrec".
  unfold pointsto_M. rewrite -insert_delete_eq big_sepM_insert; [|apply lookup_delete_eq]. iFrame.
Qed.

(* The read-only variant: read [x]'s cell/record, then put both back unchanged. *)

Lemma pointsto_M_acc_same ρ LM x lc :
  LM !! x = Some lc ->
  pointsto_M ρ LM -∗
    x ↦ #(content_of (ρ x) lc) ∗ rec_repr (ρ x) lc ∗
    (x ↦ #(content_of (ρ x) lc) -∗ rec_repr (ρ x) lc -∗ pointsto_M ρ LM).
Proof.
  intros HLM. iIntros "HM".
  iDestruct (pointsto_M_acc _ _ _ _ HLM with "HM") as "(Hx & Hrec & HM)".
  iFrame "Hx Hrec". iIntros "Hx Hrec".
  iSpecialize ("HM" $! lc with "Hx Hrec"). by rewrite insert_id.
Qed.

(* The two-location variant of [pointsto_M_acc]: gives access to two
   *distinct* vertices [x]/[y] at once, with a wand to put both back
   (possibly updated). Needed for scrutinees like [!x, !y] that read both
   sides before deciding what to write (e.g. [union]'s [match !x, !y with
   Root _, Root _ -> ... end]), where extracting one location at a time via
   two separate [pointsto_M_acc] calls doesn't compose (the second access
   would need to be performed on the *already-modified* map returned by the
   first wand, instead of being independent of it). *)

Lemma pointsto_M_acc2 ρ LM x y lcx lcy :
  x ≠ y ->
  LM !! x = Some lcx ->
  LM !! y = Some lcy ->
  pointsto_M ρ LM -∗
    x ↦ #(content_of (ρ x) lcx) ∗ rec_repr (ρ x) lcx ∗
    y ↦ #(content_of (ρ y) lcy) ∗ rec_repr (ρ y) lcy ∗
    (∀ lcx' lcy',
       x ↦ #(content_of (ρ x) lcx') -∗ rec_repr (ρ x) lcx' -∗
       y ↦ #(content_of (ρ y) lcy') -∗ rec_repr (ρ y) lcy' -∗
       pointsto_M ρ (<[x:=lcx']> (<[y:=lcy']> LM))).
Proof.
  intros Hne HLMx HLMy. iIntros "HM". unfold pointsto_M.
  iDestruct (big_sepM_delete _ LM x lcx HLMx with "HM") as "[[Hx Hrecx] HM]".
  assert (HLMy' : (delete x LM) !! y = Some lcy) by (rewrite lookup_delete_ne; [exact HLMy | exact Hne]).
  iDestruct (big_sepM_delete _ (delete x LM) y lcy HLMy' with "HM") as "[[Hy Hrecy] HM]".
  iFrame "Hx Hrecx Hy Hrecy".
  iIntros (lcx' lcy') "Hx Hrecx Hy Hrecy".
  unfold pointsto_M.
  rewrite -(insert_delete_eq (<[y:=lcy']> LM) x lcx').
  rewrite (delete_insert_ne LM x y lcy' Hne).
  rewrite -(insert_delete_eq (delete x LM) y lcy').
  rewrite (big_sepM_insert _ (<[y:=lcy']> (delete y (delete x LM))) x lcx').
  2: { apply lookup_insert_None.
       split.
       - rewrite lookup_delete_ne; [apply lookup_delete_eq | exact (not_eq_sym Hne)].
       - exact (not_eq_sym Hne). }
  iSplitL "Hx Hrecx"; [iFrame|].
  rewrite (big_sepM_insert _ (delete y (delete x LM)) y lcy'); [|apply lookup_delete_eq].
  iFrame.
Qed.

(* Like [pointsto_M_acc2], but the put-back wand also lets the caller swap
   in a *different* record at [x]/[y] — not just a different [lcontent] tag
   at the same record. Needed for [link]/[union]: installing a [Link]
   allocates a brand-new record block (OCaml's [{parent = y}]), so the
   vertex's record-location entry in [ρ] genuinely changes, unlike [find]'s
   in-place field mutation (which is exactly why [pointsto_M_acc2] alone,
   with [ρ] held fixed, can't close this case). *)

Lemma pointsto_M_acc2_realloc ρ LM x y lcx lcy :
  x ≠ y ->
  LM !! x = Some lcx ->
  LM !! y = Some lcy ->
  pointsto_M ρ LM -∗
    x ↦ #(content_of (ρ x) lcx) ∗ rec_repr (ρ x) lcx ∗
    y ↦ #(content_of (ρ y) lcy) ∗ rec_repr (ρ y) lcy ∗
    (∀ rx' ry' lcx' lcy',
       x ↦ #(content_of rx' lcx') -∗ rec_repr rx' lcx' -∗
       y ↦ #(content_of ry' lcy') -∗ rec_repr ry' lcy' -∗
       pointsto_M (fun z => if decide (z = x) then rx' else if decide (z = y) then ry' else ρ z)
         (<[x:=lcx']> (<[y:=lcy']> LM))).
Proof.
  intros Hne HLMx HLMy. iIntros "HM". unfold pointsto_M.
  iDestruct (big_sepM_delete _ LM x lcx HLMx with "HM") as "[[Hx Hrecx] HM]".
  assert (HLMy' : (delete x LM) !! y = Some lcy) by (rewrite lookup_delete_ne; [exact HLMy | exact Hne]).
  iDestruct (big_sepM_delete _ (delete x LM) y lcy HLMy' with "HM") as "[[Hy Hrecy] HM]".
  iFrame "Hx Hrecx Hy Hrecy".
  iIntros (rx' ry' lcx' lcy') "Hx Hrecx Hy Hrecy".
  unfold pointsto_M.
  rewrite -(insert_delete_eq (<[y:=lcy']> LM) x lcx').
  rewrite (delete_insert_ne LM x y lcy' Hne).
  rewrite -(insert_delete_eq (delete x LM) y lcy').
  rewrite (big_sepM_insert _ (<[y:=lcy']> (delete y (delete x LM))) x lcx').
  2: { apply lookup_insert_None.
       split.
       - rewrite lookup_delete_ne; [apply lookup_delete_eq | exact (not_eq_sym Hne)].
       - exact (not_eq_sym Hne). }
  rewrite decide_True; [|reflexivity].
  iSplitL "Hx Hrecx"; [iFrame|].
  rewrite (big_sepM_insert _ (delete y (delete x LM)) y lcy'); [|apply lookup_delete_eq].
  rewrite decide_False; [|exact (not_eq_sym Hne)].
  rewrite decide_True; [|reflexivity].
  iSplitL "Hy Hrecy"; [iFrame|].
  iApply (big_sepM_proper with "HM").
  intros z lc Hz.
  rewrite decide_False.
  2: { intro Heqzx. subst z.
       rewrite lookup_delete_ne in Hz; [|exact (not_eq_sym Hne)].
       rewrite lookup_delete_eq in Hz. discriminate. }
  rewrite decide_False; [done|].
  intro Heqzy. subst z. rewrite lookup_delete_eq in Hz. discriminate.
Qed.

(* The read-only variant, mirroring [pointsto_M_acc_same]. *)

Lemma pointsto_M_acc2_same ρ LM x y lcx lcy :
  x ≠ y ->
  LM !! x = Some lcx ->
  LM !! y = Some lcy ->
  pointsto_M ρ LM -∗
    x ↦ #(content_of (ρ x) lcx) ∗ rec_repr (ρ x) lcx ∗
    y ↦ #(content_of (ρ y) lcy) ∗ rec_repr (ρ y) lcy ∗
    (x ↦ #(content_of (ρ x) lcx) -∗ rec_repr (ρ x) lcx -∗
     y ↦ #(content_of (ρ y) lcy) -∗ rec_repr (ρ y) lcy -∗
     pointsto_M ρ LM).
Proof.
  intros Hne HLMx HLMy. iIntros "HM".
  iDestruct (pointsto_M_acc2 with "HM") as "(Hx & Hrecx & Hy & Hrecy & HM)"; [exact Hne|exact HLMx|exact HLMy|].
  iFrame "Hx Hrecx Hy Hrecy". iIntros "Hx Hrecx Hy Hrecy".
  iSpecialize ("HM" $! lcx lcy with "Hx Hrecx Hy Hrecy").
  rewrite (insert_id LM y lcy HLMy).
  rewrite (insert_id LM x lcx HLMx).
  iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* Public lemmas about the representation predicate. *)

(* If [UF D R V] holds, then [R] is idempotent. *)

Theorem UF_idempotent : forall D R V,
  UF D R V -∗ ⌜ idempotent elem R ⌝.
Proof using.
  iIntros (D R V) "HUF". iDestruct "HUF" as (F ρ LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply idempotent_R; eauto.
Qed.

(* If [UF D R V] holds, then [R] preserves [D]. *)

Theorem UF_image : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ R x ∈ D ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F ρ LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply sticky_R; eauto.
Qed.

(* If [UF D R V] holds, then [R] is the identity outside of [D]. *)

Theorem UF_identity : forall D R V x, x ∉ D ->
  UF D R V -∗ ⌜ R x = x ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F ρ LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply R_is_identity_outside_D; eauto.
Qed.

(* If [UF D R V] holds, then [V] is compatible with [R]. *)

Theorem UF_compatible : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ V x = V (R x) ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F ρ LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. apply Hdata.
Qed.

(* An empty instance of the Union-Find data structure can be created out of
   thin air. This is how the data structure is initialized. (We no longer
   need a fancy update / invariant here: that was for the TC/TR ghost state
   supporting the amortized-complexity analysis, which we dropped.) *)

Theorem UF_create : forall V, ⊢ UF ∅ id V.
Proof.
  iIntros (V). iExists (UnionFind02EmptyCreate.empty elem), (λ x, x), ∅.
  iSplit; [|iSplit].
  - iPureIntro. constructor.
    + apply is_dsf_empty.
    + intro x. apply is_repr_empty.
    + intro x. reflexivity.
  - iPureIntro. split; [reflexivity|]. intros x Hx. set_solver.
  - rewrite /pointsto_M big_sepM_empty. done.
Qed.

(* Two separate instances of the UnionFind data structure can be merged, without
   actually doing anything at runtime. *)

(* In principle, we could also prove the converse property, [UF_split]. A UnionFind
   data structure can be split in two independent parts, provided the split respects
   the equivalence relation. Considering the amount of dreary work that went into
   establishing [UF_join], I leave this to future work. *)

(* [pointsto_M_disjoint]/[pointsto_M_union]: needed to combine two separate
   [UF] instances' worth of heap ownership. [pointsto_M_union]'s proof is
   generic in the per-vertex resource (it never inspects [lcontent]), so it's
   ported unchanged from the old single-level version. *)

Lemma pointsto_M_disjoint : forall ρ1 ρ2 LM1 LM2,
  pointsto_M ρ1 LM1 -∗ pointsto_M ρ2 LM2 -∗ ⌜ LM1 ##ₘ LM2 ⌝.
Proof.
  iIntros "* HM1 HM2" (x).
  destruct (LM1 !! x) as [lc1|] eqn:Heq1, (LM2 !! x) as [lc2|] eqn:Heq2=>//.
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq1 with "HM1") as "(Hx1 & _ & _)".
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq2 with "HM2") as "(Hx2 & _ & _)".
  iCombine "Hx1 Hx2" gives %Hbad. exfalso. destruct Hbad as [Hbad _]. eapply dfrac_full_exclusive; exact Hbad.
Qed.

Lemma pointsto_M_union : forall ρ LM1 LM2,
  LM1 ##ₘ LM2 ->
  pointsto_M ρ LM1 ∗ pointsto_M ρ LM2 ⊣⊢ pointsto_M ρ (LM1 ∪ LM2).
Proof.
  intros ρ LM1 LM2 HLM12. unfold pointsto_M.
  induction LM1 as [|l x LM1 ? IH] using map_ind.
  { by rewrite big_opM_empty !left_id. }
  rewrite -insert_union_l !big_sepM_insert //; last first.
  { apply lookup_union_None; split; [done|]. specialize (HLM12 l).
    rewrite lookup_insert_eq in HLM12. revert HLM12. case: (LM2 !! l)=>//=. }
  rewrite -assoc. f_equiv. apply IH. by eapply map_disjoint_insert_l.
Qed.

Theorem UF_join : forall D1 R1 V1 D2 R2 V2,
  UF D1 R1 V1 -∗ UF D2 R2 V2 -∗
  UF
    (D1 ∪ D2)
    (fun x => if decide (x ∈ D1) then R1 x else R2 x)
    (fun x => if decide (x ∈ D1) then V1 x else V2 x)
  ∗ ⌜ D1 ## D2 ⌝.
Proof.
  iIntros (D1 R1 V1 D2 R2 V2) "HUF1 HUF2".
  iDestruct "HUF1" as (F1 ρ1 LM1 HInv1 HMem1) "HM1".
  iDestruct "HUF2" as (F2 ρ2 LM2 HInv2 HMem2) "HM2".
  destruct HInv1 as [Hdsf1 Hincl1 Hdata1].
  destruct HInv2 as [Hdsf2 Hincl2 Hdata2].
  destruct HMem1 as [Hdom1 HMfun1].
  destruct HMem2 as [Hdom2 HMfun2].
  iDestruct (pointsto_M_disjoint with "HM1 HM2") as %HLM12.
  assert (HD12 : D1 ## D2).
  { intros x Hx1 Hx2.
    assert (Hin1 : is_Some (LM1 !! x)) by (apply elem_of_dom; rewrite Hdom1; exact Hx1).
    assert (Hin2 : is_Some (LM2 !! x)) by (apply elem_of_dom; rewrite Hdom2; exact Hx2).
    destruct Hin1 as [lc1 Heq1]. destruct Hin2 as [lc2 Heq2].
    eapply map_disjoint_spec; eauto. }
  assert (HnotD2 : forall x, x ∈ D1 -> x ∉ D2) by (intros x Hx1 Hx2; eapply HD12; eauto).
  assert (HnotD1 : forall x, x ∈ D2 -> x ∉ D1) by (intros x Hx2 Hx1; eapply HD12; eauto).
  iSplit; [|done].
  iExists (union elem F1 F2), (λ x, if decide (x ∈ D1) then ρ1 x else ρ2 x), (LM1 ∪ LM2).
  iSplit.
  - (* Preservation of [Inv]. *)
    iPureIntro. constructor.
    + eapply is_dsf_join; eauto.
    + intros x. destruct (decide (x ∈ D1)) as [HxD1 | HxD1].
      * eapply (is_repr_join_direct_1 elem _ _ D1 D2 F1 F2 HD12 Hdsf1 Hdsf2); eauto.
      * eapply (is_repr_join_direct_2 elem _ _ D1 D2 F1 F2 HD12 Hdsf1 Hdsf2); eauto.
    + intros x. destruct (decide (x ∈ D1)) as [HxD1 | HxD1].
      * assert (HRD1 : R1 x ∈ D1) by (eapply sticky_R; eauto).
        destruct (decide (R1 x ∈ D1)) as [_ | Hc]; [|tauto].
        apply Hdata1.
      * destruct (decide (x ∈ D2)) as [HxD2 | HxD2].
        -- assert (HRD2 : R2 x ∈ D2) by (eapply sticky_R; eauto).
           destruct (decide (R2 x ∈ D1)) as [Hc | _]; [exfalso; eapply HnotD1; eauto|].
           apply Hdata2.
        -- assert (HReq : R2 x = x) by (eapply R_is_identity_outside_D; eauto).
           rewrite HReq. destruct (decide (x ∈ D1)) as [Hc | _]; [tauto|]. reflexivity.
  - iSplit.
    + (* Preservation of [Mem]. *)
      iPureIntro. split.
      { rewrite dom_union_L Hdom1 Hdom2. reflexivity. }
      intros x Hx. apply elem_of_union in Hx. destruct Hx as [Hx1 | Hx2].
      * assert (HxnD2 : x ∉ D2) by (eapply HnotD2; eauto).
        assert (Heq : (LM1 ∪ LM2) !! x = LM1 !! x).
        { destruct (LM1 !! x) as [lc|] eqn:HeqLM1.
          - eapply lookup_union_Some_l; eauto.
          - exfalso. eapply (proj2 (not_elem_of_dom LM1 x) HeqLM1). rewrite Hdom1; exact Hx1. }
        rewrite Heq. specialize (HMfun1 x Hx1).
        destruct (LM1 !! x) as [[v|y]|] eqn:HeqLM1x; [|left; exact HMfun1|exact HMfun1].
        destruct HMfun1 as [Hroot1 Hv1].
        split; [|destruct (decide (x ∈ D1)) as [_ | Hc]; [exact Hv1 | tauto]].
        apply is_root_join. split; [exact Hroot1|].
        intros y' HF2. destruct (proj1 Hdsf2 x y' HF2) as [Hx2' _]. eapply HxnD2; exact Hx2'.
      * assert (HxnD1 : x ∉ D1) by (eapply HnotD1; eauto).
        assert (Heq : (LM1 ∪ LM2) !! x = LM2 !! x).
        { destruct (LM2 !! x) as [lc|] eqn:HeqLM2.
          - eapply lookup_union_Some_r; eauto.
          - exfalso. eapply (proj2 (not_elem_of_dom LM2 x) HeqLM2). rewrite Hdom2; exact Hx2. }
        rewrite Heq. specialize (HMfun2 x Hx2).
        destruct (LM2 !! x) as [[v|y]|] eqn:HeqLM2x; [|right; exact HMfun2|exact HMfun2].
        destruct HMfun2 as [Hroot2 Hv2].
        split; [|destruct (decide (x ∈ D1)) as [Hc | _]; [tauto | exact Hv2]].
        apply is_root_join. split; [|exact Hroot2].
        intros y' HF1. destruct (proj1 Hdsf1 x y' HF1) as [Hx1' _]. eapply HxnD1; exact Hx1'.
    + (* The joined record-location map agrees with [ρ1] on [LM1] and [ρ2] on
         [LM2], so [pointsto_M] of each piece is recovered unchanged. *)
      iApply pointsto_M_union; [exact HLM12|].
      iSplitL "HM1".
      * unfold pointsto_M. iApply (big_sepM_mono with "HM1"). iIntros (x lc Hx) "He".
        apply elem_of_dom_2 in Hx. rewrite Hdom1 in Hx. rewrite decide_True //.
      * unfold pointsto_M. iApply (big_sepM_mono with "HM2"). iIntros (x lc Hx) "He".
        apply elem_of_dom_2 in Hx. rewrite Hdom2 in Hx.
        rewrite decide_False; [done| apply HnotD1; exact Hx].
Qed.

(* -------------------------------------------------------------------------- *)

(* [make] has already been ported above ([make_spec]/[imp_make]); the old
   TC/rank-based version that used to live here has been removed. *)

(* -------------------------------------------------------------------------- *)

(* Verification of [find]. *)

(* Because [find] is a recursive function, we must begin with a specification
   that is amenable to an inductive proof. It states that [find] essentially
   implements the mathematical predicate [bw_ipc]. If [bw_ipc F x d F'] holds,
   which means that path compression at [x] requires [d] steps and changes the
   graph from [F] to [F'], then [find] requires [d+1] time credits and changes
   the memory from [M] to some [M'] that agrees with [F']. Furthermore, the
   value [r] returned by [find] is the representative of [x]. *)

Definition find := (EAnonFun (AnonFunction __branches7)).

Definition find_spec' ( e : elem) (m : microvx) : iProp Σ :=
  ∀ ρ d D R F F' M V,
    ⌜Inv D F R V⌝ -∗
    ⌜Mem D F V M⌝ -∗
    ⌜e ∈ D⌝ -∗
    ⌜bw_ipc _ F e d F'⌝ -∗
    pointsto_M ρ M -∗
    imp m {{ λ (x : elem), ∃ M', ⌜x = R e⌝ ∗ pointsto_M ρ M' ∗ ⌜Mem D F' V M'⌝ }}.

(* -------------------------------------------------------------------------- *)

(* Pattern-matching infrastructure for [match !x with Root _ -> ... | Link
   {parent=y} as link -> ... end].

   [imp_branches]/[next_branch]'s generic machinery (via [pattern_hook]) lets
   the framework drive the [Root _ | Link _] dispatch on the abstract
   scrutinee [c] automatically, but it has a real bug: when the match
   continuation's postcondition [φ] is still an evar at the point the
   framework tries to resolve it (via the "apply eq_refl" shortcut in
   [apply_deep_handle_cons], see [handler_tactics.v]), it gets pinned to
   [fun η' => η' = δ] *without* being gated by the match condition (e.g.
   [c = Root rr]) — so the resulting branch-body goal is not actually
   constrained to the matched case, and is unsound to rely on (provably so:
   destructing [c] inside such a goal exposes a genuine, unprovable
   counterexample in the unmatched case).

   The fix here is to *not* go through [imp_branches]/[next_branch]'s
   automatic φ-guessing for this match. Instead, [deep_handle_cons] is
   applied manually (see [find_spec_inductive] below) with an explicit,
   correctly-gated [Hη] for each branch — e.g. for [Root]:
     [fun η' => (exists rr, c = Root rr) /\ η' = δ]
   so the branch-body goal genuinely carries [c = Root rr]. [pat_Root_fixed]/
   [pat_Link_fixed] below are the [pattern ...] facts for these two
   specific, hard-coded [Hη] choices (no generic recursive sub-pattern
   parameter, unlike [splay.v]'s [pat_pLeaf]/[pat_pNode] — that generic
   shape is exactly what's vulnerable to the bug above, since it leaves the
   continuation postcondition as an evar for the framework to mis-resolve). *)

Lemma solve_encode_Root (rr : record) (c : @content val _) :
  Root rr = c -> VData "Root" (#rr :: nil) = #c.
Proof. intros <-. reflexivity. Qed.

Lemma solve_encode_Link (lr : record) (c : @content val _) :
  Link lr = c -> VData "Link" (#lr :: nil) = #c.
Proof. intros <-. reflexivity. Qed.

Local Hint Resolve solve_encode_Root solve_encode_Link : encode.

Lemma pat_Root p η δ c φ ζ :
  (∀ (r : record),
    c = @Root val _ r →
    pattern η δ p #r φ (ζ r)) →
  pattern η δ (PData "Root" [p]) #c φ
    ((∃ r, c = Link r) ∨ (∃ r, c = Root r ∧ ζ r)).
Proof.
  intros Hp.
  destruct c.
  - eapply pattern_exn_mono.
    eapply pat_PData_eq. rewrite encode_encode'; reflexivity.

    eapply pats_PCons. apply Hp. reflexivity.
    intros ??. apply pats_PNil. assumption.
    intros [Hζ|[]].
    right; eauto.
  - eapply pattern_exn_mono.
    eapply pat_PData_neq. rewrite encode_encode'; reflexivity. auto.
    intros _; left; eauto.
Qed.

Ltac pat_root :=
  eapply pat_Root.

Lemma pat_Link p η δ c φ ζ :
  (∀ (r : record),
    c = @Link val _ r →
    pattern η δ p #r φ (ζ r)) →
  pattern η δ (PData "Link" [p]) #c φ
    ((∃ r, c = Root r) ∨ (∃ r, c = Link r ∧ ζ r)).
Proof.
  intros Hp.
  destruct c.
  - eapply pattern_exn_mono.
    eapply pat_PData_neq. rewrite encode_encode'; reflexivity. auto.
    intros _; left; eauto.
  - eapply pattern_exn_mono.
    eapply pat_PData_eq. rewrite encode_encode'; reflexivity.

    eapply pats_PCons. apply Hp. reflexivity.
    intros ??. apply pats_PNil. assumption.
    intros [Hζ|[]].
    right; eauto.
Qed.

Ltac pat_link :=
  eapply pat_Link.

Ltac pattern_hook ::=
  first
    [ pat_root | pat_link ].

(* Lemma pat_Root_fixed η0 (c : @content val _) :
  pattern η0 η0 (PData "Root" [PAny]) #c
    (λ η', ∃ rr, c = Root rr ∧ η' = η0)
    (∃ lr, c = Link lr).
Proof.
  destruct c as [rr | lr].
  - eapply pattern_exn_mono.
    + eapply pat_PData_eq.
      * erewrite solve_encode_Root; eauto.
      * eapply pats_PCons.
        2:{ intros δ' Hδ'. eapply pats_PNil. exact Hδ'. }
        eapply pat_PAny. exists rr; split; [reflexivity | reflexivity].
    + intros [[]|[]].
  - eapply pattern_exn_mono.
    + eapply pat_PData_neq.
      * erewrite solve_encode_Link; eauto.
      * eauto.
    + intros _. exists lr. reflexivity.
Qed. *)

(* Lemma pat_Root_var δ0 η0 (c : @content val _) s : *)
(*   pattern δ0 η0 (PData "Root" [PVar s]) #c *)
(*     (λ η', ∃ rr, c = Root rr ∧ η' = (s, #rr)::η0 ) *)
(*     (∃ lr, c = Link lr). *)
(* Proof. *)
(*   destruct c as [rr | lr]. *)
(*   - eapply pattern_exn_mono. *)
(*     + eapply pat_PData_eq. *)
(*       * erewrite solve_encode_Root; eauto. *)
(*       * eapply pats_PCons. *)
(*         2:{ intros δ' Hδ'. eapply pats_PNil. exact Hδ'. } *)
(*         eapply pat_PVar. exists rr; split; [reflexivity | reflexivity]. *)
(*     + intros [[]|[]]. *)
(*   - eapply pattern_exn_mono. *)
(*     + eapply pat_PData_neq. *)
(*       * erewrite solve_encode_Link; eauto. *)
(*       * eauto. *)
(*     + intros _. exists lr. reflexivity. *)
(* Qed. *)

(* Lemma pat_Link_fixed η0 (c : @content val _) : *)
(*   pattern η0 η0 (PData "Link" [PVar "link"]) #c *)
(*     (λ η', ∃ lr, c = Link lr ∧ η' = ("link" ~> #lr; η0)) *)
(*     (∃ rr, c = Root rr). *)
(* Proof. *)
(*   destruct c as [rr | lr]. *)
(*   - eapply pattern_exn_mono. *)
(*     + eapply pat_PData_neq. *)
(*       * erewrite solve_encode_Root; eauto. *)
(*       * eauto. *)
(*     + intros _. exists rr. reflexivity. *)
(*   - eapply pattern_exn_mono. *)
(*     + eapply pat_PData_eq. *)
(*       * erewrite solve_encode_Link; eauto. *)
(*       * eapply pats_PCons. *)
(*         2:{ intros δ' Hδ'. eapply pats_PNil. exact Hδ'. } *)
(*         eapply pat_PVar. exists lr. split; reflexivity. *)
(*     + intros [[]|[]]. *)
(* Qed. *)

Lemma find_spec_inductive η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find find_spec') η -∗
  imp (eval η find) {{ λ c, □ iSpec τ[elem] c find_spec' }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  unfold find_spec' at 2.
  iIntros (ρ d D R F F' M V HInv HMem Hin Hbw_ipc) "HM".
  iApply imp_please; iNext.
  (* The outer, always-matching [PAlias PAny "x"] binder for the function's
     own argument; unrelated to the source-level [match !x with ...]. *)
  imp_match elem. rewrite -encode_encode'.
  (* Read [e]'s content cell with the *read-only* accessor: since [find]
     recurses on the whole structure, [e] stays in the heap and is put back
     unchanged by [Hback]. [Hlc] is the [Mem] fact about [e]'s content. *)
  destruct (M !! e) as [lc|] eqn:Heq;
    pose proof (proj2 HMem e Hin) as Hlc; rewrite Heq in Hlc; [|contradiction].
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hx & Hrec & Hback)".
  imp_match (@content val _) with "[Hx]".
  iIntros "[-> Hx]".
  next_branch.

  { (* [Root _ -> x]: [e] is its own representative; the heap is unchanged. *)
    iIntros (η1) "(%rr & %Hc & ->)". imp_path.
    destruct lc; last discriminate. destruct Hlc as [ His_root HV ].
    iExists M.
    iDestruct ("Hback" with "Hx Hrec") as "$". iPureIntro.
    split.
    - symmetry. eapply is_root_R_self; eauto.
    - assert (F' = F) as ->
        by (inversion Hbw_ipc; subst; [reflexivity | exfalso; eapply His_root; eauto]).
      assumption. }

  next_branch.
  { (* [Link link -> ...]: here [link = ρ e]. Recurse on [e]'s parent [y],
       then compress [e]'s record in place. *)
    iIntros (?) "(%r & %Hlinkeq & ->)".
    destruct lc as [v|y]; first discriminate.
    inversion_clear Hlinkeq.
    simpl.
    (* Read [link.parent], i.e. [e]'s parent [y]. *)
    iApply (imp_ELet_var (B:=elem) with "[Hrec]").
    { imp_record. }

    simpl. iIntros (?) "(-> & Hrec)". unfold "!!τ". simpl.

    (* Decompose the iterated-compression derivation at [e]: it steps to [y]
       and recurses, with [F' = compress F0 e (R y)]. *)
    pose proof (Inv_dsf _ _ _ _ HInv) as Hdsf.
    assert (HyD : y ∈ D) by (eapply (proj1 Hdsf); eauto).
    assert (exists l0 F0, bw_ipc elem F y l0 F0 /\ F' = compress elem F0 e (R y))
      as (l0 & F0 & Hipc0 & HFeq0).
    { inversion Hbw_ipc as [x0 Hr0 | x0 y0 z0 ll Fl Fl' HFl Hrl Hbwl HFl']; subst.
      - exfalso. apply (Hr0 y), Hlc.
      - assert (y0 = y) as -> by (eapply (proj1 (proj2 Hdsf)); eauto).
        assert (z0 = R y) as -> by
          (eapply functional_is_repr; [exact Hdsf | exact Hrl | eapply (Inv_incl _ _ _ _ HInv)]).
        eauto 10. }

    (* Put [e] back and recurse [find y] on the *whole* heap — no restriction:
       [ρ] is preserved by the call, so [e]'s record is recoverable below. *)
    iDestruct ("Hback" with "Hx Hrec") as "HM".
    iApply (imp_ELet_var (B:=elem) with "[HM]").
    { iApply (imp_EApp τ[elem]). { imp_path. } imp_path.
      simpl. iIntros (x) "->". iIntros (m) "Hm".
      iApply ("Hm" with "[%//] [%//] [%//] [%//] HM"). }
    simpl.
    iIntros (z) "(%M2' & -> & HM' & %HMem')".

    (* The recursion never touches [e] ([e] is not reachable from [y]), so [e]
       is still a [Link] to [y] in the returned [M2'], with the same record. *)
    assert (Hdsf0 : is_dsf elem _ _ D F0) by (eapply is_dsf_bw_ipc; eauto).
    assert (HF0ey : F0 e y).
    { assert (Hnr : ¬ rtc F y e)
        by (intro Hc; eapply edge_no_return_path; [exact Hdsf|exact Hlc|exact Hc]).
      apply (proj2 (bw_ipc_outside_unchanged elem _ _ F y l0 F0 Hipc0 e Hnr y)). assumption. }
    assert (Heq2 : M2' !! e = Some (LLink y)).
    { pose proof (proj2 HMem' e Hin) as Hf2. destruct (M2' !! e) as [[v2|y2]|] eqn:E.
      - exfalso. eapply (proj1 Hf2); exact HF0ey.
      - do 2 f_equal. eapply (proj1 (proj2 Hdsf0)); [exact Hf2 | exact HF0ey].
      - exfalso; exact Hf2. }
    iDestruct (pointsto_M_acc _ _ _ _ Heq2 with "HM'") as "(Hx & Hrec & Hback)".

    (* [if z != y then link.parent <- z]; either way [e]'s record ends up
       [LLink (R y)]. Put it back, then conclude with [Mem_compress]. *)
    iApply (imp_ESeq with "[-]").
    set_postcondition (λ _, pointsto_M ρ (<[e:=LLink (R y)]> M2')).
    iApply imp_EIfThen.
    { set_postcondition (λ b, ⌜b = negb (locations.eqb (R y) y)⌝)%I.
      iApply imp_EBoolNeg.
      iApply (imp_EOpPhysEq_loc with "[] []"); [imp_path|imp_path|].
      iIntros "!>" (l1 l2) "-> -> //". }
    iIntros (b) "->".
    destruct (locations.eqb_spec (R y) y) as [HRy|HRy]; simpl.

    + (* [R y = y]: no write; [e]'s record already points to [y = R y]. *)
      rewrite HRy. iApply ("Hback" $! (LLink y) with "Hx Hrec").

    + (* [R y ≠ y]: perform [link.parent <- R y]. *)
      iApply (imp_wand with "[Hrec]").
      { iApply (imp_record_update with "Hrec [] []"); [split; simpl; lia|imp_path|imp_path]. }
      iIntros (?) "(%w & -> & Hrec)".
      iApply ("Hback" $! (LLink (R y)) with "Hx Hrec").

    + (* Continuation: [e] and [y] share a representative, and the updated heap
         is a [Mem] for [F' = compress F0 e (R y)] directly by [Mem_compress]. *)
      iIntros "HMfinal". imp_path.
      iExists (<[e:=LLink (R y)]> M2'). iFrame "HMfinal".
      iSplitR.
      { iPureIntro. symmetry.
        eapply (is_equiv_incl_same_R elem _ _ D F Hdsf R (Inv_incl _ _ _ _ HInv) e y).
        eapply path_is_equiv; eauto using rtc_l, rtc_refl. }
      iPureIntro. rewrite HFeq0. apply Mem_compress; [exact HMem' | exact Hin]. }

  exfalso. resolve_no_match.
Qed.

Definition find_spec (e : elem) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜e ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ (x : elem), ⌜x = R e⌝ ∗ UF D R V }}.

Lemma find_proof :
  ∀ find, iSpec τ[elem] find find_spec' -∗ iSpec τ[elem] find find_spec.
Proof.
  iIntros (find) "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x m) "Hspec".
  unfold find_spec, find_spec', tapp.
  iIntros (D R V) "%Hin HUF".
  iDestruct "HUF" as "(%F & %ρ & %LM & %HInv & %HMem & Hpointsto)".
  pose proof (Inv_dsf D F R V HInv) as Hdsf.
  edestruct (ipc_defined elem _ _ D F Hdsf x) as (d & F' & Hipc).
  iSpecialize ("Hspec" with "[//] [//] [//] [//] Hpointsto").
  iApply (imp_wand with "Hspec").
  iIntros (y) "(%M' & -> & Hpointsto & %HMem')".
  iSplit; first done.
  iFrame "∗%". iPureIntro.
  split; eauto 10 using is_dsf_bw_ipc, bw_ipc_preserves_RF_agreement.
Qed.

(* -------------------------------------------------------------------------- *)

Definition get_spec (e : elem) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜e ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ (x : val), ⌜x = V e⌝ ∗ UF D R V }}.

Definition get := (EAnonFun __fun19).

Lemma get_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec)%I η -∗
  imp (eval η get) {{ λ c, □ iSpec τ[elem] c get_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  unfold get_spec.
  iIntros (D R V) "%Hin HUF".
  iApply imp_please; iNext.

  imp_match elem. rewrite -encode_encode'.
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F ρ M HI HM) "HM".
  assert (M !! (R e) = Some (LRoot (V (R e)))) as Heq.
  { eapply Mem_root; eauto. }
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hx & Hrec & Hback)".

  imp_match (@content val _) with "[Hx]".
  iIntros "(-> & Hx)".
  simpl.

  iApply deep_handle_cons. { iPureIntro. apply cpat_CVal. apply pat_Root_var. }
  iSplit; last first.
  { iIntros "(% & %HF)". discriminate HF. }
  iIntros (?) "(%rr & %HRoot & ->)". inversion_clear HRoot.
  iDestruct "Hrec" as "(%rank & Hown)".
  iApply (imp_wand with "[Hown]").
  { imp_record. }
  iIntros (?) "(-> & Hown)".
  iSplit; first iPureIntro. { by rewrite HRV. }
  iSpecialize ("Hback" with "Hx [Hown]").
  { iFrame. }
  iFrame "∗%".
Qed.

(* -------------------------------------------------------------------------- *)

Definition set_spec (e : elem) (v : val) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜e ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ (x : unit), UF D R (update1 V R e v) }}.

Definition set := (EAnonFun (AnonFun "x" (EAnonFun __fun23))).

Lemma set_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec)%I η -∗
  imp (eval η set) {{ λ c, □ iSpec τ[elem;val] c set_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (e v).
  unfold set_spec.
  iIntros (D R V) "%Hin HUF".
  iApply imp_please; iNext.

  imp_match val.
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F ρ M HI HM) "HM".
  assert (M !! (R e) = Some (LRoot (V (R e)))) as Heq.
  { eapply Mem_root; eauto. }
  iDestruct (pointsto_M_acc _ _ _ _ Heq with "HM") as "(Hx & Hrec & Hback)".

  imp_match (@content val _) with "[Hx]".
  iIntros "(-> & Hx)".
  simpl.

  iApply deep_handle_cons. { iPureIntro. apply cpat_CVal. apply pat_Root_var. }
  iSplit; last first.
  { iIntros "(% & %HF)". discriminate HF. }
  iIntros (?) "(%rr & %HRoot & ->)". inversion_clear HRoot.
  iDestruct "Hrec" as "(%rank & Hown)".
  iApply (imp_wand with "[Hown]").
  { iApply (imp_record_update with "Hown"). split; simpl; lia.
    imp_path. imp_path. }
  iIntros ([]) "(% & -> & Hown) /=".

  iSpecialize ("Hback" $! (LRoot _) with "Hx [Hown]").
  { iFrame. }
  iFrame "Hback". iPureIntro.
  eauto using Inv_update1, Mem_update1.
Qed.

(* -------------------------------------------------------------------------- *)

Definition union_spec (x y : elem) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜x ∈ D⌝ -∗
    ⌜y ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ z, UF D (update2 R R x y z) (update2 V R x y (V z)) ∗ ⌜z = R x ∨ z = R y⌝ }}.

Definition union := EAnonFun (AnonFun "x" (EAnonFun __fun41)).

Lemma union_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec) η -∗
  imp (eval η union) {{ λ c, □ iSpec τ[elem;elem] c union_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (x y).
  unfold union_spec.
  iIntros (D R V) "%Hin_x %Hin_y HUF".
  iApply imp_please; iNext.
  imp_match elem. rewrite -encode_encode'.
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".

  imp_if.
  { set_postcondition (λ b, ⌜b = locations.eqb (R x) (R y)⌝)%I.
    iApply imp_EOpPhysEq_loc; [imp_path|imp_path|].
    iIntros "!>" (??) "-> -> //". }

  { iIntros "%Heq".
    imp_path.
    iSplit; last (iPureIntro; tauto).
    iDestruct "HUF" as "(%F & %ρ & %M & %HI & %HM & Hpts)".
    iFrame. iPureIntro. simpl.
    eexists. split.
    - destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [|congruence].
      eapply Inv_update2_diag; [exact HI | exact HReq].
    - destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [|congruence].
      rewrite (update2_V_diag D F R V x y HI HReq).
      exact HM. }

  iIntros "%Hneq".
  iPoseProof (UF_image with "HUF") as "%HRD_x"; first apply Hin_x.
  iPoseProof (UF_image with "HUF") as "%HRD_y"; first apply Hin_y.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iDestruct "HUF" as (F ρ M HI HM) "HM".
  assert (M !! (R x) = Some (LRoot (V (R x)))) as Heq_x.
  { eapply Mem_root; eauto. }
  assert (M !! (R y) = Some (LRoot (V (R y)))) as Heq_y.
  { eapply Mem_root; eauto. }

  destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [ congruence | ].

  iPoseProof (pointsto_M_acc2_realloc with "HM") as "(Hx & Hrepr_x & Hy & Hrepr_y & Hback)".
  eassumption. eassumption. eassumption.
  simpl.

  imp_match (@content val _ * @content val _)%type with "[Hx Hy]".
  { imp_tuple with "[Hx] [Hy]". }

  destruct a as [??].
  iIntros "((-> & Hx) & (-> & Hy))".
  iApply deep_handle_cons.
  { iPureIntro. apply cpat_CVal.
    eapply pat_PTuple. rewrite encode_encode'. reflexivity.
    eapply pats_PCons. apply pat_Root_var.
    intros ? (? & HeqRoot & ->).
    inversion_clear HeqRoot. clear x0.
    eapply pats_PCons. eapply pat_Root_var.
    intros ? (? & HeqRoot & ->).
    inversion_clear HeqRoot. clear x0.
    eapply pats_PNil. apply eq_refl. }
  iSplit; last first.
  { iIntros "%HF". exfalso.
    destruct HF as [(? & HF) | [(? & HF) | []]]; congruence. }
  iIntros (?) "<-".

  iDestruct "Hrepr_x" as "(%x_rank & Hown_x)".
  iDestruct "Hrepr_y" as "(%y_rank & Hown_y)".
  iApply (imp_ELet_pair (A:=Z) (B:=Z) with "[Hown_x Hown_y]").
  { imp_tuple with "[Hown_x] [Hown_y]". }
  iIntros (??) "((-> & Hown_x) & (-> & Hown_y)) /=".

  iApply (imp_EIfThenElse).
  { iApply imp_EOpLt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

  { iApply (imp_ESeq with "[Hx]").
    { iApply (imp_EStore'
        (A:=@content val Encode_val)
        (Φ := ∃ (r : record), ownRepr r 1 {| parent := R y |} ∗ R x ↦ #(@Link val _ r))
        with "Hx"). imp_path.
      set_postcondition (λ l, ∃ r, ⌜l = Link r⌝ ∗ ownRepr r 1 {| parent := R y |})%I.
      imp_step. { iApply imp_record. simpl; lia. iApply imp_evals_singleton. imp_path. }
      - iIntros (?). iIntros "(% & Hown & ->)".
        by iFrame.
      - iIntros "!>" (?) "(% & -> & Hown) $".
        iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    imp_path. iSplit; last (iPureIntro; tauto).
    unfold UF.
    iExists (UnionFind03Link.link elem F (R x) (R y)).
    iExists (fun z => if decide (z = R x) then r else if decide (z = R y) then ρ (R y) else ρ z).
    iExists (<[R x:=LLink (R y)]> M).
    iSpecialize ("Hback" $! _ _ (LLink (R y)) (LRoot (V (R y))) with "Hlink Hown_link Hy [Hown_y]").
    { iFrame. }
    rewrite (insert_id M); last assumption. iFrame. iPureIntro.
    split.
    - rewrite -(update2_root _ R R x y (R y) HRidem).
      assert (update2 R R (R x) (R y) (R y) = UnionFind03Link.link_R elem _ (R x) (R y) R) as ->.
      { extensionality t. symmetry. apply link_R_eq_update2. apply HRidem. }
      eapply Inv_link; eauto.
      rewrite -(update2_root _ V R x y (V (R y)) HRidem). reflexivity.
    - eapply Mem_link; eauto.
      rewrite -(update2_root _ V R x y (V (R y)) HRidem). reflexivity. }

  iApply imp_EIfThenElse. { iApply imp_EOpGt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

  { iApply (imp_ESeq with "[Hy]").
    { iApply (imp_EStore'
        (A:=@content val Encode_val)
        (Φ := ∃ (r : record), ownRepr r 1 {| parent := R x |} ∗ R y ↦ #(@Link val _ r))
        with "Hy"). imp_path.
      set_postcondition (λ l, ∃ r, ⌜l = Link r⌝ ∗ ownRepr r 1 {| parent := R x |})%I.
      imp_data.
      { iApply imp_record. simpl. lia.
        iApply imp_evals_singleton. imp_path. }
      - iIntros (?) "(% & Hown & ->)".
        by iFrame.
      - iIntros "!>" (?) "(% & -> & Hown) $".
        iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    imp_path. iSplit; last (iPureIntro; tauto).
    unfold UF.
    iExists (UnionFind03Link.link elem F (R y) (R x)).
    iExists (fun z => if decide (z = R x) then ρ (R x) else if decide (z = R y) then r else ρ z).
    iExists (<[R y:=LLink (R x)]> M).
    iSpecialize ("Hback" $! _ _ (LRoot (V (R x))) (LLink (R x)) with "Hx [Hown_x] Hlink Hown_link").
    { iFrame. }
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption. iFrame. iPureIntro.
    split.
    - rewrite -(update2_root _ R R x y (R x) HRidem).
      rewrite (update2_sym _ R R (R x) (R y) (R x)).
      assert (update2 R R (R y) (R x) (R x) = UnionFind03Link.link_R elem _ (R y) (R x) R) as ->.
      { extensionality t. symmetry. apply link_R_eq_update2. apply HRidem. }
      eapply Inv_link; eauto.
      rewrite (update2_sym _ V R (R y) (R x) (V (R x))).
      rewrite (update2_root _ V R x y (V (R x)) HRidem).
      reflexivity.
    - eapply Mem_link; eauto.
      rewrite (update2_sym _ V R (R y) (R x) (V (R x))).
      rewrite (update2_root _ V R x y (V (R x)) HRidem).
      reflexivity. }

  iApply (imp_ESeq with "[Hy]").
    { iApply (imp_EStore'
        (A:=@content val Encode_val)
        (Φ := ∃ (r : record), ownRepr r 1 {| parent := R x |} ∗ R y ↦ #(@Link val _ r))
        with "Hy"). imp_path.
      set_postcondition (λ l, ∃ r, ⌜l = Link r⌝ ∗ ownRepr r 1 {| parent := R x |})%I.
      imp_step. { iApply imp_record. simpl; lia.
        iApply imp_evals_singleton. imp_path. }
      - iIntros (?). iIntros "(% & Hown & ->)".
        by iFrame.
      - iIntros "!>" (?) "(% & -> & Hown) $".
        iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    iApply (imp_ESeq with "[Hown_x]").
    { iApply (imp_record_update with "Hown_x"). split;simpl;lia.
      imp_path. imp_arith. }
    iIntros "(% & -> & Hown_x) /=".
    imp_path. iSplit; last (iPureIntro; tauto).
    unfold UF.
    iExists (UnionFind03Link.link elem F (R y) (R x)).
    iExists (fun z => if decide (z = R x) then ρ (R x) else if decide (z = R y) then r else ρ z).
    iExists (<[R y:=LLink (R x)]> M).
    iSpecialize ("Hback" $! _ _ (LRoot (V (R x))) (LLink (R x)) with "Hx [Hown_x] Hlink Hown_link").
    { iFrame. }
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption. iFrame. iPureIntro.
    split.
    - rewrite -(update2_root _ R R x y (R x) HRidem).
      rewrite (update2_sym _ R R (R x) (R y) (R x)).
      assert (update2 R R (R y) (R x) (R x) = UnionFind03Link.link_R elem _ (R y) (R x) R) as ->.
      { extensionality t. symmetry. apply link_R_eq_update2. apply HRidem. }
      eapply Inv_link; eauto.
      rewrite (update2_sym _ V R (R y) (R x) (V (R x))).
      rewrite (update2_root _ V R x y (V (R x)) HRidem).
      reflexivity.
    - eapply Mem_link; eauto.
      rewrite (update2_sym _ V R (R y) (R x) (V (R x))).
      rewrite (update2_root _ V R x y (V (R x)) HRidem).
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The rest of this file is the original CFML/TLC-based development,
   not yet ported to Osiris (and using notations/tactics that don't exist
   here, e.g. [\in], [TC], [«...»], [wp_tick_*]). Commented out for now so
   the file parses end-to-end; kept around since we may want to reuse/adapt
   these proofs (in particular [link_spec]) when porting [link]/[get]/[set]/
   etc. the same way [make]/[find] were ported above. *)

(*
Lemma find_spec_inductive: forall d D R F K F' M V x,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  bw_ipc F x d F' ->
  TCTR_invariant nmax -∗
  {{{ pointsto_M M ∗ TC (11*d+11) }}}
    «find #x»
  {{{ M', RET #(R x); pointsto_M M' ∗ ⌜ Mem D F' K V M' ⌝ }}}.
Proof using.
  intros d. induction_wf IH: Wf_nat.lt_wf d. intros d.
  introv IH HI HM Dx HC. iIntros "#?" (Φ) "!# [HM TC] HΦ /=".
  iDestruct "TC" as "[TCd TC]". wp_tick_rec.
  assert (HV := HM _ Dx). destruct (M !! x) as [c|] eqn:? =>//.
  iDestruct (pointsto_M_acc_same with "HM") as (v Hv) "[Hx HM]"=>//. wp_tick_load.
  iDestruct ("HM" with "Hx") as "HM".
  destruct (val_of_content_Some _ _ Hv) as [(k1 & k2 & v' & -> & -> & ?)|(y & -> & ->)].
  (* Case: Root. *)
  { wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_seq.
    destruct HV as [HR HP]. forwards* EQ : is_root_R_self HR. rewrite EQ.
    iApply "HΦ". iFrame. iPureIntro.
    invert HC; intros. by subst. by false* a_root_has_no_parent HR.
  }
  (* Case: Link. *)
  { wp_tick_match. rename HV into HF. invert HC.
    { intros. subst F. subst. false* a_root_has_no_parent. }
    intros F'0 F'' x0 y0 z' d' HF' HR' HB' EF' Ex Ed EF''. subst F'' x0 d.
    lets* E: is_dsf_functional D HF HF'. subst y0. clear HF'.
    assert (y \in D). { eauto with confined is_dsf. }
    assert (z' = R y). { symmetry. eapply is_repr_incl_R; eauto. } subst z'.
    forwards IH' : IH HI HM HB'; [math|done|].
    iCombine "TCd TC" as "TC".
    math_rewrite (11 * S d' + 6 = 11 * d' + 11 + 6)%nat.
    iDestruct "TC" as "[TCd TC]".
    wp_apply (IH' with "[//] [$HM $TCd]").
    iIntros (M') "[HM' hM']". iDestruct "hM'" as %HM'. wp_tick_let.
    assert (HV := HM' _ Dx). destruct (M' !! x) as [c|] eqn:? =>//.
    iDestruct (pointsto_M_acc with "HM'") as (v' Hv') "[Hx HM']"=>//.
    wp_tick_inj. wp_tick_store. wp_tick_seq.
    iDestruct ("HM'" $! (Link (R y)) _ eq_refl with "Hx") as "HM'".
    assert (is_equiv F x y). { eauto using path_is_equiv with rtclosure. }
    assert (R x = R y) as ->. { eauto using is_equiv_incl_same_R. }
    iApply ("HΦ" with "[$HM']").
    iPureIntro. applys~ Mem_compress HM'. }
Qed.

(* The function call [find x] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns the representative of [x]. *)

Theorem find_spec : forall D R V x, x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 44) }}}
    «find #x»
  {{{ RET #(R x); UF D R V }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC1] HΦ".
  iDestruct "UF" as (F K M HI HM) "(HM & TC2 & TR)".
  forwards* (d&F'&HC&HP): amortized_cost_of_iterated_path_compression_simplified x.
  iCombine "TC1 TC2" as "TC".
  rewrite [TC (_ + _)](TC_weaken _ (11*Phi D F' K + (11 * d + 11))%nat); [|lia].
  iDestruct "TC" as "[TC1 TC2]".
  iApply (find_spec_inductive with "[//] [$TC2 $HM]")=>//.
  iIntros "!>" (M') "[HM' %]". iApply "HΦ".
  iExists _, _, _. iFrame. iPureIntro. split; [|done].
  split; eauto 10 using is_rdsf_bw_ipc, bw_ipc_preserves_RF_agreement.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [get]. *)

(* The function call [get x] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns the data stored at [x]. *)

Theorem get_spec : forall D R V x, x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 57) }}}
    «get #x»
  {{{ RET V x; UF D R V }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (22 * alpha (card D) + 57 = 22 * alpha (card D) + 44 + 13)%nat.
  iDestruct "TC" as "[TC1 TC2]".
  wp_tick_rec.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//.
  iIntros "UF". wp_tick_let. iDestruct "UF" as (F K M HI HM) "[HM TC]".
  forwards* (Drx&Rrx): Inv_root x (R x).
  forwards* EM: Mem_root (R x).
  iDestruct (pointsto_M_acc_same with "HM") as (v Hv) "[Hx HM]"=>//. wp_tick_load.
  iDestruct ("HM" with "Hx") as "HM".
  destruct (val_of_content_Some_Root _ _ _ Hv) as (k1 & -> & _).
  wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_let.
  rewrite -(Inv_data _ _ _ _ _ HI). iApply "HΦ".
  iExists _, _, _. eauto with iFrame.
Qed.


(* -------------------------------------------------------------------------- *)

(* Verification of [set]. *)

(* The function call [set x v] requires [UF D R V] as well as O(alpha(D)) time
   credits. It produces [UF D R V'], where [V'] is obtained from [V] by mapping
   the equivalence class of [x] to [v]. *)

Theorem set_spec : forall D R V x v,
  x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 62) }}}
    «set #x v»
  {{{ RET #(); UF D R (update1 V R x «v»%V) }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (22 * alpha (card D) + 62 = 22 * alpha (card D) + 44 + 18)%nat.
  iDestruct "TC" as "[TC1 TC2]".
  wp_tick_rec. wp_tick_let. wp_apply (find_spec with "[//] [$TC1 $UF]")=>//.
  iIntros "UF". wp_tick_let. iDestruct "UF" as (F K M HI HM) "[HM TC]".
  forwards* (Drx&Rrx): Inv_root x (R x).
  forwards* EM: Mem_root (R x).
  iDestruct (pointsto_M_acc with "HM") as (v' Hv') "[Hx HM]"=>//. wp_tick_load.
  destruct (val_of_content_Some_Root _ _ _ Hv') as (k1 & -> & _).
  wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_seq.
  wp_tick_pair. wp_tick_inj. wp_tick_store.
  iApply "HΦ". iExists _, _, _. iFrame.
  iSplit; [auto using Inv_update1|]. iSplit; [eauto using Mem_update1|].
  rewrite Rrx. iApply ("HM" with "[%] Hx").
  simpl in *. by destruct (to_mach_int (K (R x))); inversion Hv'.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [eq]. *)

(* The function call [eq x y] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns a Boolean outcome which
   indicates whether [x] and [y] are members of a common equivalence class. *)

Theorem eq_spec : forall D R V x y,
  x \in D -> y \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (44 * alpha (card D) + 92) }}}
    «eq #x #y»
  {{{ RET #(bool_decide (R x = R y)); UF D R V }}}.
Proof using.
  introv Dx Dy. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (44 * alpha (card D) + 92 =
                (22 * alpha (card D) + 44) + (22 * alpha (card D) + 44) + 4)%nat.
  iDestruct "TC" as "[[TC1 TC2] TC3]".
  wp_tick_rec. wp_tick_let.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//. iIntros "UF".
  wp_apply (find_spec with "[//] [$TC2 $UF]")=>//. iIntros "UF".
  wp_tick_op.
  rewrite (bool_decide_ext (#(R x) = #(R y)) (R x = R y)); last (split; congruence).
  by iApply "HΦ".
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [link]. (This is an internal function.) *)

(* The function call [link x y] requires [UF D R V] as well as O(1) time credits.
   It requires [x] and [y] to be roots. It chooses the new representative [z] to
   be one of [x] or [y], and returns [z], together with [UF D' R' V'], where:
   1. [D'] is [D], i.e., the domain is unchanged;
   2. [R'] is [R], where the equivalence classes of [x] and [y] are mapped to [z];
   3. [V'] is [V], where the equivalence classes of [x] and [y] are mapped to [V z].
*)

Lemma link_spec : forall D R V x y,
  (log2 (log2 nmax) < word_size - 1)%nat ->
  x \in D ->
  y \in D ->
  R x = x ->
  R y = y ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC 61 }}}
    «link #x #y»
  {{{ z, RET #z; UF D (update2 R R x y z) (update2 V R x y (V z)) ∗
                   ⌜z = x \/ z = y⌝}}}.
Proof using.
  introv Hnmax Dx Dy Rx Ry. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  wp_tick_rec. wp_tick_let.
  iDestruct "UF" as (F K M HI HM) "(HM & TC'TR)".
  wp_tick_op. case_bool_decide as Hxy.
  (* Case: [x == y]. *)
  { inversion Hxy. subst. wp_tick_if. iApply "HΦ".
    rewrite update2_R_self; [|by eauto]. erewrite update2_V_self; [|by eauto..].
    iSplit; [|by auto]. iExists _, _, _. auto with iFrame. }
  (* Case: [x != y]. *)
  wp_tick_if.
  forwards Hx: HM Dx. forwards Hy: HM Dy.
  destruct (M !! x) as [cx|] eqn:EQx, (M !! y) as [cy|] eqn:EQy=>//.
  iDestruct (pointsto_M_acc_same _ x with "HM") as (v Hv) "[Hx HM]"=>//.
  wp_tick_load. iDestruct ("HM" with "Hx") as "HM".
  destruct cx; last by false; eauto using a_root_has_no_parent, R_self_is_root.
  destruct (val_of_content_Some_Root _ _ _ Hv) as (k1 & -> & ?).
  wp_tick_match. wp_tick_proj. wp_tick_let. wp_tick_proj. wp_tick_let.
  iDestruct (pointsto_M_acc_same _ y with "HM") as (v' Hv') "[Hy HM]"=>//.
  wp_tick_load. iDestruct ("HM" with "Hy") as "HM".
  destruct cy; last by false; eauto using a_root_has_no_parent, R_self_is_root.
  destruct (val_of_content_Some_Root _ _ _ Hv') as (k1' & -> & ?).
  wp_tick_match. wp_tick_proj. wp_tick_let. wp_tick_proj. wp_tick_seq.
  destruct Hx as (HRx&Kx&Vx). substs. destruct Hy as (HRy&Ky&Vy). substs.
  wp_tick_op; case_bool_decide; wp_tick_if;
    [|wp_tick_op; case_bool_decide; wp_tick_if].
  (* Sub-case: [K x < K y]. *)
  { iDestruct (pointsto_M_acc _ _ _ EQx with "HM") as (? _) "[Hx HM]".
    wp_tick_inj. wp_tick_store. wp_tick_seq. iApply "HΦ". iSplit; [|by auto].
    Inv_link
    (* F' := *) (UnionFind03Link.link F x y)
    (* K' := *) K
    (* V' := *) (update2 V R x y (V y))
                x y
    (* z  := *) y.
    iDestruct "TC'TR" as "[TC' TR]". iCombine "TC' TC" as "TC".
    iExists _, _, (<[x:=Link y]>M). iFrame "% TR".
    rewrite TC_weaken; [iFrame "TC"|lia]. iSplit; [by eauto using Mem_link|].
    by iApply "HM". }
  (* Sub-case: [K x > K y]. *)
  { iDestruct (pointsto_M_acc _ _ _ EQy with "HM") as (? _) "[Hy HM]".
    wp_tick_inj. wp_tick_store. wp_tick_seq. iApply "HΦ".
    rewrite [update2 _ _ _ _ x]update2_sym. rewrite [update2 _ _ _ _ (V x)]update2_sym.
    iSplit; [|by auto].
    Inv_link
    (* F' := *) (UnionFind03Link.link F y x)
    (* K' := *) K
    (* V' := *) (update2 V R y x (V x))
                y x
    (* z  := *) x.
    iDestruct "TC'TR" as "[TC' TR]". iCombine "TC' TC" as "TC".
    iExists _, _, (<[y:=Link x]>M). iFrame "% TR".
    rewrite TC_weaken; [iFrame "TC"|lia]. iSplit; [by eauto using Mem_link|].
    by iApply "HM". }
  (* Sub-case: [K x = K y]. *)
  { iDestruct (pointsto_M_acc _ _ _ EQy with "HM") as (? _) "[Hy HM]"=>//.
    wp_tick_inj. wp_tick_store.
    iDestruct ("HM" $! (Link _) _ eq_refl with "Hy") as "HM".
    Inv_link
    (* F' := *) (UnionFind03Link.link F y x)
    (* K' := *) (fupdate K x (1 + K y)%nat)
    (* V' := *) (update2 V R x y (V x))
                x y
    (* z  := *) x.
    iDestruct "TC'TR" as "[TC' TR]".
    iMod (TR_lt_nmax with "[//] TR") as "[TR %]" ; first done.
    iCombine "TC' TR" as "TC'TR".
    iAssert (⌜card D ≤ nmax⌝)%I%nat as %HDnmax%Nat.log2_le_mono.
    { auto with lia. }
    assert (bool_decide (mach_int_bounded (`k1 + 1))).
    { assert (log2 nmax < 2 ^ (word_size - 1))%nat.
      { destruct (decide (0 < log2 nmax)%nat); [by eapply Nat.log2_lt_pow2|].
        assert (log2 nmax = 0%nat) as -> by lia. apply power_positive. lia. }
      forwards* Hklog: rank_is_logarithmic (fupdate K x (S (K y))) x.
      rewrite fupdate_same in Hklog.
      assert (S (K y) < 2 ^ (word_size - 1))%nat as HK%inj_lt by lia.
      rewrite Z2Nat.inj_pow -Z.shiftl_1_l Nat2Z.inj_sub in HK;
        [|pose proof word_size_gt_1; lia].
      apply bool_decide_pack. split.
      { destruct (bool_decide_unpack _ (proj2_sig k1)) as [? _]. lia. }
      assert (`k1 = `k1') as -> by lia. rewrite (_:`k1' = K y) //.
      rewrite Z.add_comm -(Nat2Z.inj_add 1). done. }
    wp_tick_seq. wp_tick_op.
    { by rewrite /bin_op_eval /= /to_mach_int decide_True_pi. }
    iDestruct (pointsto_M_acc _ x with "HM") as (v'' Hv'') "[Hx HM]".
    { rewrite lookup_insert_ne //. congruence. }
    wp_tick_pair. wp_tick_inj. wp_tick_store. wp_tick_seq.
    iApply "HΦ". iSplit; [|by auto].
    iDestruct "TC'TR" as "[TC' TR]".
    iExists _, _, _. iFrame "% TR".
    iCombine "TC' TC" as "TC". rewrite TC_weaken; [iFrame "TC"|lia].
    iSplit; last iApply ("HM" with "[%] Hx").
    { iPureIntro. applys* Mem_link_incr HM. congruence. applys update2_sym. }
    rewrite /= -(_:(`k1 + 1) = (K y + 1)%nat) //.
    { by rewrite /to_mach_int decide_True_pi /=. }
    assert (`k1 + 1 = K y + 1)%Z as -> by lia. by rewrite ->Nat2Z.inj_add. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [union]. *)

(* The function call [union x y] requires [UF D R V] as well as O(alpha(D)) time
   credits. It chooses the new representative [z] to be one of [x] or [y], and
   returns [z], together with [UF D' R' V'], where:
   1. [D'] is [D], i.e., the domain is unchanged;
   2. [R'] is [R], where the equivalence classes of [x] and [y] are mapped to [z];
   3. [V'] is [V], where the equivalence classes of [x] and [y] are mapped to [V z].
*)

Theorem union_spec : forall D R V x y,
  (log2 (log2 nmax) < word_size - 1)%nat ->
  x \in D ->
  y \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (44 * alpha (card D) + 152) }}}
    «union #x #y»
  {{{ z, RET #z; UF D (update2 R R x y z) (update2 V R x y (V z)) ∗
                 ⌜z = R x \/ z = R y⌝ }}}.
Proof using.
  introv Hnmax Dx Dy.
  math_rewrite (44 * alpha (card D) + 152 =
                (22 * alpha (card D) + 44) + (22 * alpha (card D) + 44) + 61 + 3)%nat.
  iIntros "#?" (Φ) "!# [UF [[[TC1 TC2] TC3] TC4]] HΦ".
  wp_tick_rec. wp_tick_let.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//. iIntros "UF".
  wp_apply (find_spec with "[//] [$TC2 $UF]")=>//. iIntros "UF".
  iDestruct (UF_image _ _ _ x with "UF") as %? =>//.
  iDestruct (UF_image _ _ _ y with "UF") as %? =>//.
  iDestruct (UF_idempotent with "UF") as %Idem =>//.
  wp_apply (link_spec _ _ _ _ _ Hnmax with "[//] [$TC3 $UF]")=>//.
  iIntros (z). by rewrite !update2_root.
Qed.
*)

End UnionFind.

(* [final_theorems] referenced names ([get_spec]/[set_spec]/[eq_spec]/
   [union_spec]/[UF_idempotent]/[UF_image]/[UF_identity]/[UF_compatible]/
   [UF_create]/[UF_join]) that aren't defined anywhere in the ported part of
   this file yet; commented out alongside the CFML dead code above. *)
(*
Definition final_theorems :=
  (@UF_idempotent,
   @UF_image,
   @UF_identity,
   @UF_compatible,
   @UF_create,
   @UF_join,
   @make_spec,
   @find_spec,
   @get_spec,
   @set_spec,
   @eq_spec,
   @union_spec).

Print Assumptions final_theorems.
*)
