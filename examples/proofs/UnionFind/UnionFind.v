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

(* [root]/[link] are mutable OCaml records, so at the heap level a vertex's
   content (Root/Link) only stores a [record], i.e. a pointer to a *separate*
   heap block holding the record's own fields (rank/value, or parent). *)

(* The logical type of the content of a vertex. *)
Inductive content :=
| cRoot : record -> content
| cLink : record -> content.

Local Instance val_of_content : Encode content :=
  { encode' := λ c, match c with
                    | cRoot r => VData "Root" [ #r ]
                    | cLink r => VData "Link" [ #r ]
                    end }.

Local Instance root_data : Data "Root" τ[record] content :=
  { ctor_apply := λ r, cRoot r;
    ctor_encode := λ r, eq_refl }.

Local Instance link_data : Data "Link" τ[record] content :=
  { ctor_apply := λ r, cLink r;
    ctor_encode := λ r, eq_refl }.

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

Record Inv D F R V : Prop := {
  Inv_dsf  : DSF F D;
  Inv_incl : rel_incl R (Repr F);
  Inv_data : forall x, V x = V (R x)
}.

Local Hint Resolve Inv_dsf Inv_incl Inv_data : core.

Global Instance Inv_idem_R `{Inv D F R V} : Idempotent R.
Proof. destruct Inv0. apply _. Qed.

(* -------------------------------------------------------------------------- *)

(* [ownRecord r qp a] owns the fields of the record block pointed to by [r]. *)

(* [lcontent] is the logical content of a vertex, as exposed to [Mem]/[Inv]
   - i.e. with the rank dropped and the record-pointer indirection hidden.

   [pointsto_M] below is what relates this logical view back to the actual
   two-level heap representation (vertex location -> content -> record block). *)

Inductive lcontent :=
| LRoot : val -> lcontent
| LLink : elem -> lcontent.

(* The heap-level description of a vertex: the location of the record block
   backing it, and its logical content. The memory of the whole structure is
   a single finite map [M : gmap elem vcell]. *)
Local Notation vcell := (record * lcontent)%type.

(* The predicate [Mem ...] relates the mathematical graph encoded by [D/F/V]
   and the memory encoded by the finite map [M]. In short,
    1. [M]'s domain is exactly [D] (in particular, no entries outside [D] —
       this is what lets us derive that a freshly-allocated vertex is not in
       [D] from the fact that it cannot already have an [M] entry);
    2. the links in [M] coincide with the links in [F];
    3. the data stored at a root in [M] agrees with [V]. (We don't track the
       rank's value at all, having dropped the complexity analysis it was
       for; the actual rank field stored in memory is existentially
       quantified away in [rec_repr] below.)
   [Mem] never inspects the record-location component of a [vcell]: where a
   vertex's record block lives is a purely heap-level matter. *)

Definition Mem D F V (M : gmap elem vcell) : Prop :=
  dom M = D ∧
  ∀ x, match M !! x with
       | Some (_, LLink y) => F x y
       | Some (_, LRoot v) => Root F x /\ v = V x
       | None => True
       end.

(* [rec_repr lr lc] owns the record block at [lr] backing a vertex whose
   logical content is [lc]. A root's rank is not tracked, so it stays
   existential; a link stores its parent directly. *)

Definition rec_repr (lr : record) (lc : lcontent) : iProp Σ :=
  match lc with
  | LRoot v => ∃ k : Z, lr ⤇ ({| rank := k; value := v |} : root (A:=val))
  | LLink y => lr ⤇ ({| parent := y |} : link (A:=val))
  end.

(* The content *value* stored in [x]'s ref cell: a [Root]/[Link] tag wrapping
   the pointer [lr] to [x]'s record block. *)

Definition content_of (lr : record) (lc : lcontent) : content :=
  match lc with LRoot _ => cRoot lr | LLink _ => cLink lr end.

(* [vertex x lr lc] is the full heap footprint of one vertex [x]: its
   content cell, pointing at the record block [lr], and that block itself. *)

Definition vertex x (lr : record) (lc : lcontent) : iProp Σ :=
  (x ↦ #(content_of lr lc) ∗ rec_repr lr lc)%I.

(* [pointsto_M M] asserts ownership of the whole two-level heap: [vertex x
   lr lc] for each entry [x ↦ (lr, lc)] of [M]. Crucially the record
   locations are part of [M] rather than existentially hidden per entry:
   since [find] only ever mutates record *fields* (never a content cell,
   and never reallocating a record), the record-location skeleton [skel M]
   below is an invariant of [find], so [x]'s own record is recoverable by
   name after the recursive call. This is what lets [find] recurse on the
   *whole* structure — no framing of [x]'s resources out of the recursion,
   and no reachable-set restriction. *)

Definition pointsto_M (M : gmap elem vcell) : iProp Σ :=
  ([∗ map] x ↦ c ∈ M, vertex x c.1 c.2)%I.

(* The record-location skeleton of the memory. [find]'s inductive spec
   asserts [skel M' = skel M]: path compression rewrites record fields but
   never moves a vertex's record block. *)

Definition skel (M : gmap elem vcell) : gmap elem record := fst <$> M.

Lemma skel_insert M x lr lc lc' :
  M !! x = Some (lr, lc) ->
  skel (<[x:=(lr, lc')]> M) = skel M.
Proof.
  intros HM. rewrite /skel fmap_insert /=.
  apply insert_id. rewrite lookup_fmap HM //.
Qed.

Lemma skel_lookup M M' x lr lc :
  skel M' = skel M ->
  M !! x = Some (lr, lc) ->
  exists lc', M' !! x = Some (lr, lc').
Proof.
  intros Hskel HM.
  assert (Hx : skel M' !! x = Some lr) by (rewrite Hskel /skel lookup_fmap HM //).
  rewrite /skel lookup_fmap in Hx.
  destruct (M' !! x) as [[lr' lc']|]; simplify_eq/=; eauto.
Qed.

(* [UF D R V] is the representation predicate. It is an abstract predicate:
   the client uses this predicate, but does not know how it is defined. It
   quantifies existentially over [F/M], which therefore are not exposed to
   the client. *)

Definition UF D R V : iProp Σ :=
  (∃ F M,
  ⌜ Inv D F R V ⌝ ∗
  ⌜ Mem D F V M ⌝ ∗
  pointsto_M M)%I.

(* -------------------------------------------------------------------------- *)

(* The functions [V] and [R] are compatible with [R]. In other words, every
   member of an equivalence class must have the same image through [V] (see
   [Inv_data]) and through [R]. For this reason, when we wish to update one of
   these functions, we must update it not just at one point, but at a whole
   equivalence class. *)

(* The function [update1 R f x b] coincides with the function [f] everywhere,
   except on the equivalence class of [x], whose elements are mapped to [b]. *)

Definition update_class {B : Type} R x (f : elem -> B) (b : B) :=
  fcupdate f (fun z => R z = R x) b.

Local Notation "f .[ x -/ R /> b ]" :=
    (update_class R x f b)
      (at level 2, left associativity, format "f .[ x  -/ R />  b ]").

Lemma lookup_update_class :
  ∀ (B : Type) f x R (b : B),
  f.[ x -/R/> b ] x = b.
Proof.
  intros.
  unfold update_class, fcupdate.
  rewrite decide_True; reflexivity.
Qed.

Lemma lookup_update_class_ne :
  ∀ (B : Type) (f : elem → B) R x b a,
  R a ≠ R x ->
  f.[x -/R/> b] a = f a.
Proof.
  intros.
  unfold update_class, fcupdate.
  rewrite decide_False; [ reflexivity | assumption ].
Qed.

Lemma update_class_root `{@Idempotent elem R} {B : Type} (f : elem → B) x b :
  f.[R x -/R/> b] = f.[x -/R/> b].
Proof.
  unfold update_class, fcupdate.
  extensionality a.
  rewrite idempotent.
  case_decide; reflexivity.
Qed.

Lemma lookup_class_root `{@Idempotent elem R} {B : Type} (f : elem → B) r x b :
  f x = f (R x) →
  f.[r -/R/> b] x = f.[r -/R/> b] (R x).
Proof.
  intros Hequiv.
  unfold update_class, fcupdate.
  rewrite idempotent.
  case_decide; first reflexivity.
  apply Hequiv.
Qed.

(* We can reorder updates if they are to the same value [b]. *)

Lemma update_classes_comm {B : Type} (f : elem → B) R x y b :
  f.[x -/R/> b].[y -/R/> b] = f.[y -/R/> b].[x -/R/> b].
Proof.
  unfold update_class, fcupdate.
  extensionality a.
  case_decide; case_decide; tauto.
Qed.

(* Updating [x]'s class to [R x]/[V (R x)] is a no-op on [R]/[V]. *)

Lemma update_class_R_diag R x :
  R.[ x -/R/> (R x)] = R.
Proof.
  unfold update_class, fcupdate.
  extensionality a. case_decide; eauto.
Qed.

Lemma update_class_V_diag D F R V x :
  Inv D F R V →
  V.[x -/R/> V (R x)] = V.
Proof.
  intros HI.
  unfold update_class, fcupdate.
  extensionality a.
  case_decide as Hcase; last reflexivity.
  rewrite -Hcase.
  erewrite <- Inv_data; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Inv]. *)

(* If [x] is in the domain and [r] is its representative, then [r] is in the
   domain and [r] is its own representative. *)

Lemma Inv_root D F R V x r :
  Inv D F R V ->
  x ∈ D ->
  r = R x ->
  r ∈ D /\ R r = r.
Proof.
  intros [Hdsf Hincl Hdata] Hx ->.
  split.
  - eapply sticky_R; eauto.
  - eapply idempotent_R; eauto.
Qed.

(* The invariant is preserved when a new element [r] is created and the
   function [V] is updated at [r] in an arbitrary manner. *)

Lemma Inv_make D F R V D' V' r v :
  Inv D F R V ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  V' = V.[r -/R/> v] ->
  Inv D' F R V'.
Proof.
  intros [Hdsf Hincl Hdata] Hr -> ->.
  constructor.
  - apply is_dsf_create. exact Hdsf.
  - exact Hincl.
  - intros x.
    apply lookup_class_root, Hdata.
Qed.

(* The invariant is preserved by updating [V] at one equivalence class. *)

Lemma Inv_update_class D F R V x b :
  Inv D F R V ->
  Inv D F R V.[ x -/R/> b].
Proof.
  intros [Hdsf Hincl Hdata].
  constructor; [exact Hdsf | exact Hincl | ].
  intros.
  apply lookup_class_root, Hdata .
Qed.

Lemma unfold_link_R R x y :
  UnionFind03Link.link_R x y R =
  R.[x -/R/> y].
Proof.
  unfold UnionFind03Link.link_R, update_class, fcupdate.
  reflexivity.
Qed.

(* The invariant is preserved by a [link] operation. *)

(* The hypotheses is that the invariant holds and [x] and [y] are distinct
   roots in the domain. The conclusion is that the invariant holds again,
   with [x]'s equivalence class folded into [y]'s (so [y] becomes the new
   representative).

   The original picked whichever of [x]/[y] becomes the new representative
   based on rank, to keep the trees balanced for its complexity bound.
   We drop that as we do not need the logical model to be balanced. *)

Lemma Inv_link D F R V F' R' V' x y :
  Inv D F R V ->
  x ≠ y ->
  x ∈ D ->
  y ∈ D ->
  R x = x ->
  R y = y ->
  F' = UnionFind03Link.link F x y ->
  V' = V.[x -/R/> (V y)] ->
  R' = (UnionFind03Link.link_R x y R) ->
  Inv D F' R' V'.
Proof.
  intros HInv Hneq Hx Hy HRx HRy -> -> ->.
  constructor.
  - eapply is_dsf_link; eauto using R_self_is_root.
  - eapply link_R_link_agree; eauto using R_self_is_root.
  - intros w.
    unfold update_class, fcupdate, link_R.
    case_decide; [ case_decide; reflexivity | ].
    rewrite (idempotent (Idempotent:=@Inv_idem_R _ _ _ _ HInv)).
    case_decide; [ contradiction | ].
    eapply Inv_data; eassumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Mem]. *)

(* If [x] is in the domain and is a root, then [M] maps [x] to [LRoot]
   with data [V x] (backed by some record block [r]). *)

Lemma Mem_root D F R V M x :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  R x = x ->
  exists lr, M !! x = Some (lr, LRoot (V x)).
Proof.
  intros HInv [Hdom HM] Dx Rxx.
  specialize (HM x).
  destruct (M !! x) as [[lr [w | y]] | ] eqn:Heq.
  - exists lr. destruct HM as [_ Hv]. congruence.
  - exfalso.
    assert (Root F x) by (eapply R_self_is_root; eauto).
    eapply is_root, HM.
  - exfalso. eapply (not_elem_of_dom M). apply Heq. by rewrite Hdom.
Qed.

(* Conversely, if [M] maps [x] to [LRoot], then [x] is a root whose data is
   as predicted by [M]. (We don't track a rank value at all anymore.) *)

Lemma Mem_root_inv D F R V M x lr vx :
  Mem D F V M ->
  M !! x = Some (lr, LRoot vx) ->
  Root F x /\ vx = V x.
Proof.
  intros [Hdom HM] HE.
  specialize (HM x). rewrite HE in HM. exact HM.
Qed.

(* [Mem] is preserved when a new element [r] is created and the function
   [V] is updated at [r] in an arbitrary manner. (The original also
   inserted rank 0 at [r]; since we don't track rank, there's nothing to
   record there beyond [LRoot v].) *)

Lemma Mem_make D F R V D' M r v lr :
  Inv D F R V ->
  Mem D F V M ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  Mem D' F V.[r -/R/> v] (<[r:=(lr, LRoot v)]>M).
Proof.
  intros HInv [Hdom HM] Hr ->.
  split.
  - rewrite dom_insert_L Hdom. set_solver.
  - intros x. destruct (decide (x = r)) as [->|Hne].
    + rewrite lookup_insert_eq. split.
      * eapply only_roots_outside_D; eauto.
      * by rewrite lookup_update_class.
    + rewrite lookup_insert_ne; [|congruence].
      specialize (HM x).
      destruct (M !! x) as [[lr0 [v0|y]]|] eqn:Heq; [|exact HM|exact HM].
      split; [tauto|].
      assert (Hx : x ∈ D) by (rewrite -Hdom; eapply elem_of_dom_2; eauto).
      unfold update_class, fcupdate. destruct (decide (R x = R r)) as [Heqr|Hner]; [|tauto].
      exfalso.
      assert (HRr : R r = r) by (eapply R_is_identity_outside_D; eauto).
      destruct HInv as [Hdsf Hincl _].
      assert (Hxd : R x ∈ D) by (eapply sticky_R; eauto).
      rewrite Heqr HRr in Hxd. set_solver.
Qed.

(* [Mem] is preserved by installing a link from a root [x] to a root [y]. *)

Lemma Mem_link D F R V V' M x y lr :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  x = R x ->
  y = R y ->
  V' = V.[y -/R/> (V y)].[ x -/R/> (V y)] ->
  Mem D (UnionFind03Link.link F x y) V' (<[x:=(lr, LLink y)]>M).
Proof.
  intros HInv [Hdom HM] Hx Hxr Hyr ->.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply link_appears.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[lr0 [w|y']]|] eqn:Heq; [|apply link_previous; exact HM | exact HM].
      destruct HM as [Hroota Hva].
      split.
      * apply is_root_link; [exact Hroota | congruence].
      * rewrite {2}Hyr. erewrite update_class_V_diag; last eassumption.
        unfold update_class, fcupdate.
        assert (Hra : R a = a) by (eapply is_root_R_self; eauto).
        case_decide; congruence.
Qed.

(* [Mem] is preserved by installing a direct link from [x] to [y] during
   path compression. *)

Lemma Mem_compress D F V M x y lr :
  Mem D F V M ->
  x ∈ D ->
  Mem D (compress F x y) V (<[x:=(lr, LLink y)]>M).
Proof.
  intros [Hdom HM] Dx.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply compress_x_z.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[lr0 [w|y']]|] eqn:Heq;
        [|apply compress_preserves_other_edges; [exact HM | congruence] | exact HM].
      destruct HM as [Hroota Hva]. split; [|exact Hva].
      apply compress_preserves_roots_other_than_x; [congruence | exact Hroota].
Qed.

(* [Mem] is preserved when [V] is updated at one equivalence class and [M]
   is updated at the representative element. *)

Lemma Mem_update D F R V M r x v lr :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  r = R x ->
  Mem D F V.[x -/R/> v] (<[r := (lr, LRoot v)]>M).
Proof.
  intros HInv [Hdom HM] Hx ->.
  assert (Hrr : R x ∈ D /\ R (R x) = R x) by (apply (Inv_root _ _ _ _ _ _ HInv Hx eq_refl)).
  destruct Hrr as [Hrd Hrr].
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (R x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. split.
      * eapply R_self_is_root; eauto.
      * assert (Idempotent R). apply (@Inv_idem_R _ _ _ _ HInv).
        rewrite <- lookup_class_root; eauto.
        by rewrite lookup_update_class.
    + rewrite lookup_insert_ne; [|exact Hne].
      destruct (M !! a) as [[lr0 [v0|y]]|] eqn:Heq; [|exact HM|exact HM].
      destruct HM as [Hroota Hva]. split; [exact Hroota|].
      rewrite lookup_update_class_ne; [ assumption | ].
      intros HeqR. apply Hne. rewrite -HeqR.
      eapply is_root_R_self; eauto.
Qed.

(* A vertex with no [LM] entry is, by [Mem]'s domain equation, not in [D]. *)

Lemma Mem_not_elem_of_dom D F V M x :
  Mem D F V M ->
  M !! x = None ->
  x ∉ D.
Proof.
  intros [Hdom _] Heq.
  rewrite -Hdom. eapply not_elem_of_dom_2. exact Heq.
Qed.

(* If [pointsto_M M] and [x ↦ v] are both owned, [x] cannot already be an
   [M] entry (otherwise we'd own [x] twice). Combined with [Mem]'s domain
   equation, this is how we show a freshly-allocated vertex is not in [D]. *)

Lemma pointsto_M_fresh (M : gmap elem vcell) x v :
  pointsto_M M -∗ x ↦ v -∗ ⌜M !! x = None⌝.
Proof.
  iIntros "HM Hx".
  destruct (M !! x) as [c|] eqn:Heq; [|done].
  iExFalso.
  iDestruct (big_sepM_lookup with "HM") as "[Hx' _]"; [exact Heq|].
  iCombine "Hx Hx'" gives %Hbad.
  destruct Hbad as [Hbad _]. exfalso; eapply dfrac_full_exclusive; exact Hbad.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [make]. *)

(* [record]/[ERecord] operations need the records they build to fit within
   [max_array_length] *)
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

(* The function call [make v] requires [UF D R V]. It returns a new element
   [x]. It updates the data structure to [UF D' R V'], where:
   - [D'] is [D] extended with [x];
   - [V'] is [V] extended with a mapping of [x] to [v]. *)

Definition make_spec : val → microvx → iProp Σ :=
  λ v m,
    (∀ D R V,
       UF D R V -∗
       imp m {{ λ (x : elem), UF (D ∪ {[x]}) R V.[x -/R/> v] ∗ ⌜x ∉ D ∧ R x = x⌝ }})%I.

Lemma imp_make η :
  ⊢ imp (eval η (EAnonFun __make)) {{ λ c, □ iSpec τ[val] c make_spec }}.
Proof.
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  iIntros (D R V) "HUF".
  iApply imp_please; iNext.
  (* Goal: [ ref (Root { rank = 0; value = v }) ] *)
  iApply (imp_ERef2' (A:=content)). { imp_data. }

  simpl.
  iIntros "!>" (x r) "(%root_rec & -> & % & % & Hown & -> & ->) Hr".

  iDestruct "HUF" as (F LM) "(%HInv & %HMem & HptM)".
  iDestruct (pointsto_M_fresh with "HptM Hr") as %HxLM.
  iSplitL.
  - (* extend [LM] at the fresh vertex [x] with its just-allocated record. *)
    iExists F, (<[r:=(root_rec, LRoot v)]>LM).
    iSplit; [iPureIntro; eapply Inv_make; eauto using Mem_not_elem_of_dom |].
    iSplit; [iPureIntro; eapply Mem_make; eauto using Mem_not_elem_of_dom |].
    rewrite /pointsto_M big_sepM_insert; [|exact HxLM].
    simpl. iFrame.
  - iPureIntro. split; [ eapply Mem_not_elem_of_dom; eassumption | ].
    eapply R_is_identity_outside_D; eauto using Mem_not_elem_of_dom.
Qed.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about the representation predicate [pointsto_M]. *)

(* [pointsto_M_acc] gives access to a single [vertex], plus a wand to put a
   vertex back and recover [pointsto_M] at the updated map. *)

Lemma pointsto_M_acc M x lr lc :
  M !! x = Some (lr, lc) ->
  pointsto_M M -∗
    vertex x lr lc ∗
    (∀ lr' lc', vertex x lr' lc' -∗ pointsto_M (<[x:=(lr', lc')]> M)).
Proof.
  intros HM. iIntros "HM".
  iDestruct (big_sepM_insert_acc _ _ _ _ HM with "HM") as "[$ HM]".
  iIntros (lr' lc') "Hv". iApply ("HM" $! (lr', lc') with "Hv").
Qed.

(* A read-only variant. *)

Lemma pointsto_M_acc_same M x lr lc :
  M !! x = Some (lr, lc) ->
  pointsto_M M -∗
    vertex x lr lc ∗ (vertex x lr lc -∗ pointsto_M M).
Proof.
  intros HM. iIntros "HM".
  iDestruct (big_sepM_lookup_acc _ _ _ _ HM with "HM") as "[$ HM]".
  iIntros "Hv". iApply ("HM" with "Hv").
Qed.

(* A generic two-key variant of [big_sepM_insert_acc]: simultaneous access
   to two distinct entries, with a wand to put both back.
   Needed for expressions like [!x, !y] that read both sides "in parallel". *)

Lemma big_sepM_insert_acc_2 `{Countable K} {A} (Φ : K → A → iProp Σ)
    (m : gmap K A) (i j : K) (x y : A) :
  i ≠ j ->
  m !! i = Some x ->
  m !! j = Some y ->
  ([∗ map] k↦a ∈ m, Φ k a) -∗
    Φ i x ∗ Φ j y ∗
    (∀ (x' y' : A), Φ i x' -∗ Φ j y' -∗ [∗ map] k↦a ∈ <[i:=x']> (<[j:=y']> m), Φ k a).
Proof.
  intros Hne Hi Hj. iIntros "Hm".
  iDestruct (big_sepM_delete _ m i x Hi with "Hm") as "[$ Hm]".
  assert (Hj' : (delete i m) !! j = Some y)
    by (rewrite lookup_delete_ne; [exact Hj | exact Hne]).
  iDestruct (big_sepM_delete _ (delete i m) j y Hj' with "Hm") as "[$ Hm]".
  iIntros (x' y') "Hi Hj".
  rewrite -(insert_delete_eq (<[j:=y']> m) i x').
  rewrite (delete_insert_ne m i j y' Hne).
  rewrite -(insert_delete_eq (delete i m) j y').
  rewrite (big_sepM_insert _ (<[j:=y']> (delete j (delete i m))) i x').
  2: { apply lookup_insert_None.
       split.
       - rewrite lookup_delete_ne; [apply lookup_delete_eq | exact (not_eq_sym Hne)].
       - exact (not_eq_sym Hne). }
  iFrame "Hi".
  rewrite (big_sepM_insert _ (delete j (delete i m)) j y'); [|apply lookup_delete_eq].
  iFrame.
Qed.

(* The two-location variant of [pointsto_M_acc]. *)

Lemma pointsto_M_acc2 M x y rx ry lcx lcy :
  x ≠ y ->
  M !! x = Some (rx, lcx) ->
  M !! y = Some (ry, lcy) ->
  pointsto_M M -∗
    vertex x rx lcx ∗ vertex y ry lcy ∗
    (∀ rx' ry' lcx' lcy',
       vertex x rx' lcx' -∗ vertex y ry' lcy' -∗
       pointsto_M (<[x:=(rx', lcx')]> (<[y:=(ry', lcy')]> M))).
Proof.
  intros Hne Hx Hy. iIntros "HM".
  iDestruct (big_sepM_insert_acc_2 _ _ _ _ _ _ Hne Hx Hy with "HM")
    as "($ & $ & HM)".
  iIntros (rx' ry' lcx' lcy') "Hvx Hvy".
  iApply ("HM" $! (rx', lcx') (ry', lcy') with "Hvx Hvy").
Qed.

(* -------------------------------------------------------------------------- *)

(* Program rules for operating on a vertex. *)

Lemma imp_vertex_load {η E Ψ ζ} x lr lc (e : expr) :
  vertex x lr lc -∗
  impure E (eval η e) Ψ ζ (λ l', ⌜l' = x⌝) -∗
  impure E (eval η (ELoad e)) Ψ ζ
    (λ c : content, ⌜c = content_of lr lc⌝ ∗ vertex x lr lc).
Proof.
  iIntros "[Hx Hrec] He".
  iApply (imp_wand with "[Hx He]").
  { iApply (imp_ELoad with "Hx He"). }
  iIntros (c) "[-> Hx]". by iFrame.
Qed.

Lemma imp_vertex_read_parent {η E Ψ ζ} x lr y (e : expr) :
  vertex x lr (LLink y) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 0)) Ψ ζ
    (λ z : elem, ⌜z = y⌝ ∗ vertex x lr (LLink y)).
Proof.
  iIntros "[Hx Hrec] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (z) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_parent {η E Ψ ζ} x lr y (e1 e2 : expr) Φ :
  vertex x lr (LLink y) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 0 e2)) Ψ ζ
    (λ _ : unit, ∃ z : elem, Φ z ∗ vertex x lr (LLink z)).
Proof.
  iIntros "[Hx Hrec] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%z & HΦ & Hrec)". iExists z. by iFrame.
Qed.

Lemma imp_vertex_read_value {η E Ψ ζ} x lr v (e : expr) :
  vertex x lr (LRoot v) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 1)) Ψ ζ
    (λ w : val, ⌜w = v⌝ ∗ vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (w) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_value {η E Ψ ζ} x lr v (e1 e2 : expr) Φ :
  vertex x lr (LRoot v) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 1 e2)) Ψ ζ
    (λ _ : unit, ∃ w : val, Φ w ∗ vertex x lr (LRoot w)).
Proof.
  iIntros "[Hx (%k & Hrec)] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%w & HΦ & Hrec)". iExists w. by iFrame.
Qed.

Lemma imp_vertex_read_rank {η E Ψ ζ} x lr v (e : expr) :
  vertex x lr (LRoot v) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 0)) Ψ ζ
    (λ _ : Z, vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (w) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_rank {η E Ψ ζ} x lr v (e1 e2 : expr) Φ :
  vertex x lr (LRoot v) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 0 e2)) Ψ ζ
    (λ _ : unit, ∃ k : Z, Φ k ∗ vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%k' & HΦ & Hrec)". iExists k'. by iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* Public lemmas about the representation predicate. *)

(* If [UF D R V] holds, then [R] is idempotent. *)

Theorem UF_idempotent : forall D R V,
  UF D R V -∗ ⌜Idempotent R ⌝.
Proof using.
  iIntros (D R V) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. apply _.
Qed.

(* If [UF D R V] holds, then [R] preserves [D]. *)

Theorem UF_image : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ R x ∈ D ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply sticky_R; eauto.
Qed.

(* If [UF D R V] holds, then [R] is the identity outside of [D]. *)

Theorem UF_identity : forall D R V x, x ∉ D ->
  UF D R V -∗ ⌜ R x = x ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply R_is_identity_outside_D; eauto.
Qed.

(* If [UF D R V] holds, then [V] is compatible with [R]. *)

Theorem UF_compatible : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ V x = V (R x) ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. apply Hdata.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [find]. *)

(* Because [find] is a recursive function, we must begin with a specification
   that is amenable to an inductive proof. [find_spec'] states that [find]
   implements the mathematical predicate [bw_ipc]. If [bw_ipc F x d F'] holds,
   which means that path compression at [x] requires [d] steps and changes the
   graph from [F] to [F'], then [find] changes the memory from [M] to some [M']
   that agrees with [F']. Furthermore, the value [r] returned by [find] is the
   representative of [x]. *)


Definition find_spec' ( e : elem) (m : microvx) : iProp Σ :=
  ∀ d D R F F' M V,
    ⌜Inv D F R V⌝ -∗
    ⌜Mem D F V M⌝ -∗
    ⌜e ∈ D⌝ -∗
    ⌜bw_ipc F e d F'⌝ -∗
    pointsto_M M -∗
    imp m {{ λ (x : elem), ∃ M',
      ⌜x = R e⌝ ∗ ⌜skel M' = skel M⌝ ∗ pointsto_M M' ∗ ⌜Mem D F' V M'⌝ }}.

(* -------------------------------------------------------------------------- *)

(* Pure lemmas backing [find_spec_inductive]'s reasoning about the iterated
   path compression derivation [bw_ipc]. *)

(* At a root, compression does nothing. *)

Lemma bw_ipc_at_root F e d F' :
  Root F e ->
  bw_ipc F e d F' ->
  F' = F.
Proof.
  intros * His_root Hbw_ipc.
  inversion Hbw_ipc; subst; [reflexivity|].
  exfalso; eapply His_root; eauto.
Qed.

(* At a link [F e y], the derivation necessarily steps to [y]: it recurses
   on [y] (an element of [D]) and finishes by compressing [e] directly to
   the representative [R y]. *)

Lemma bw_ipc_at_link D F R V e y d F' :
  Inv D F R V ->
  F e y ->
  bw_ipc F e d F' ->
  y ∈ D /\
  ∃ l Fres, bw_ipc F y l Fres /\ F' = compress Fres e (R y).
Proof.
  intros * HInv Hlc Hbw_ipc.
  pose proof (Inv_dsf _ _ _ _ HInv) as Hdsf.
  split. { destruct Hdsf. eapply confined, Hlc. }
  inversion Hbw_ipc as [? Hroot | ]; subst.
  - exfalso. apply (is_root y), Hlc.
  - assert (y0 = y) as -> by (destruct Hdsf; eapply functional; eauto).
    assert (z = R y) as -> by
      (eapply functional_is_repr; [exact Hdsf | eassumption | eapply (Inv_incl _ _ _ _ HInv)]).
    eauto 10.
Qed.

(* Compression starting at [e]'s parent [y] never reaches back to [e],
   so [e]'s entry is unchanged. *)

Lemma link_untouched_by_ipc D F V M M' Fres e re y l :
  DSF F D ->
  F e y ->
  bw_ipc F y l Fres ->
  Mem D Fres V M' ->
  skel M' = skel M ->
  M !! e = Some (re, LLink y) ->
  M' !! e = Some (re, LLink y).
Proof.
  intros Hdsf Hlc Hipc HMem' Hskel Heq.
  destruct (skel_lookup _ _ _ _ _ Hskel Heq) as (lc' & Heq').
  assert (HF0ey : Fres e y).
  { eapply (bw_ipc_outside_unchanged _ _ _).
    - apply Hipc.
    - intro Hc. eapply edge_no_return_path. exact Hdsf. exact Hlc. exact Hc.
    - apply Hlc. }
  destruct HMem' as [_ HMem']. specialize (HMem' e). rewrite Heq' in HMem'.
  destruct lc' as [v2|y2].
  { exfalso. eapply HMem'. apply HF0ey. }
  rewrite Heq'. repeat f_equal.
  assert (HyD : y ∈ D) by (destruct Hdsf; eapply confined; eauto).
  assert (DSF Fres D) as [_ Hdsf0 _]
    by (eapply is_dsf_bw_ipc; eauto).
  eapply functional; eauto.
Qed.

(* One step up the forest does not change the representative. *)

Lemma R_of_parent : forall D F R V e y,
  Inv D F R V ->
  F e y ->
  R e = R y.
Proof.
  intros * [Hdsf Hincl _] Hlc.
  eapply is_equiv_incl_same_R.
  - apply Hdsf.
  - exact Hincl.
  - eapply path_is_equiv; eauto using rtc_l, rtc_refl.
Qed.

(* -------------------------------------------------------------------------- *)

(* Pattern-matching infrastructure for [match !x with Root _ -> ... | Link
   {parent=y} as link -> ... end]. *)

Lemma solve_encode_Root (rr : record) (c : content) :
  cRoot rr = c -> VData "Root" (#rr :: nil) = #c.
Proof. intros <-. reflexivity. Qed.

Lemma solve_encode_Link (lr : record) (c : content) :
  cLink lr = c -> VData "Link" (#lr :: nil) = #c.
Proof. intros <-. reflexivity. Qed.

Local Hint Resolve solve_encode_Root solve_encode_Link : encode.

Lemma pat_Root p η δ c φ ζ :
  (∀ (r : record),
    c = cRoot r →
    pattern η δ p #r φ (ζ r)) →
  pattern η δ (PData "Root" [p]) #c φ
    ((∃ r, c = cLink r) ∨ (∃ r, c = cRoot r ∧ ζ r)).
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
    c = cLink r →
    pattern η δ p #r φ (ζ r)) →
  pattern η δ (PData "Link" [p]) #c φ
    ((∃ r, c = cRoot r) ∨ (∃ r, c = cLink r ∧ ζ r)).
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

Lemma find_spec_inductive η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find find_spec') η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EMatch (ELoad (EPath ["x"])) __find_branches))))
    {{ λ c, □ iSpec τ[elem] c find_spec' }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  unfold find_spec' at 2.
  iIntros (d D R F F' M V HInv HMem Hin Hbw_ipc) "HM".
  iApply imp_please; iNext.
  (* Read [e]'s content cell with the *read-only* accessor: since [find]
     recurses on the whole structure, [e] stays in the heap and is put back
     unchanged by [Hback]. [Hlc] is the [Mem] fact about [e]'s content. *)
  destruct (M !! e) as [[re lc]|] eqn:Heq;
    pose proof (proj2 HMem e) as Hlc; rewrite Heq in Hlc;
    [|destruct (Mem_not_elem_of_dom _ _ _ _ _ HMem Heq Hin)].
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  (* Goal: [ match !x with ... ] *)
  imp_match content with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "[-> Hv]".
  next_branch.

  { (* [Root _ -> x]: [e] is its own representative *)
    iIntros (η1) "(%rr & %Hc & ->)". imp_path.
    iDestruct ("Hback" with "Hv") as "$". iPureIntro.
    destruct lc; last discriminate. destruct Hlc as [His_root HV].
    split_and!.
    - symmetry. eapply is_root_R_self; eauto.
    - reflexivity.
    - assert (F' = F) as -> by (eapply bw_ipc_at_root; eauto).
      assumption. }

  next_branch.
  { (* [Link link -> ...]: Recurse on [e]'s parent [y],
       then compress [e]'s record in place. *)
    iIntros (?) "(%r & %Hlinkeq & ->)".
    destruct lc as [v|y]; first discriminate.
    injection Hlinkeq as <-.
    simpl.
    (* Read [link.parent], i.e. [e]'s parent [y]. *)
    iApply (imp_ELet_var (B:=elem) with "[Hv]").
    { iApply (imp_vertex_read_parent with "Hv"). imp_path. }

    simpl. iIntros (?) "(-> & Hv)".

    (* Decompose the iterated-compression derivation at [e]: it steps to [y]
       (an element of [D]) and recurses, with [F' = compress F0 e (R y)]. *)
    destruct (bw_ipc_at_link _ _ _ _ _ _ _ _ HInv Hlc Hbw_ipc)
      as (HyD & l0 & F0 & Hipc0 & HFeq0).
    iDestruct ("Hback" with "Hv") as "HM".

    (* Goal: [ let z = find y in ... ] *)
    iApply (imp_ELet_var (B:=elem) with "[HM]").
    { iApply (imp_EApp τ[elem]). { imp_path. } { imp_path. }
      simpl. iIntros (x) "-> %m Hm".
      iApply ("Hm" with "[%//] [%//] [%//] [%//] HM"). }
    simpl.
    iIntros (z) "(%M2' & -> & %Hskel & HM' & %HMem')".

    (* The recursion never touches [e] ([e] is not reachable from [y]), so [e]
       is still a [Link] to [y] in the returned [M2'], with the same record
       [re] (by skeleton preservation). *)
    assert (Heq2 : M2' !! e = Some (re, LLink y))
      by (eapply link_untouched_by_ipc; eauto).

    iDestruct (pointsto_M_acc with "HM'") as "(Hv & Hback)".
    { eassumption. }

    (* Goal: [ if z != y then ... else ...; z ] *)
    iApply (imp_ESeq with "[-]").
    (* set_postcondition (λ _, pointsto_M (<[e:=(re, LLink (R y))]> M2')). *)
    imp_if.
    { set_postcondition (λ b, ⌜b = negb (locations.eqb (R y) y)⌝)%I.
      iApply imp_EBoolNeg.
      iApply (imp_EOpPhysEq_loc with "[] []"); [imp_path|imp_path|].
      iIntros "!>" (l1 l2) "-> -> //". }

    + (* [R y ≠ y]: perform [link.parent <- R y]. *)
      iIntros "%Heqb".
      destruct (locations.eqb_spec (R y) y) as [HRy|HRy]; first discriminate.
      iApply (imp_wand with "[Hv]").
      { iApply (imp_vertex_write_parent with "Hv [] []"); [imp_path|imp_path]. }
      iIntros (?) "(%w & -> & Hv)".
      iApply ("Hback" $! re (LLink (R y)) with "Hv").

    + (* [R y = y]: no write; [e]'s record already points to [y = R y]. *)
      iIntros "%Heqb".
      destruct (locations.eqb_spec (R y) y) as [HRy|HRy]; last discriminate.
      rewrite HRy. iApply ("Hback" $! re (LLink y) with "Hv").

    + (* Continuation: [e] and [y] share a representative, and the updated heap
         is a [Mem] for [F' = compress F0 e (R y)] directly by [Mem_compress]. *)
      iIntros "HMfinal". imp_path.
      iExists (<[e:=(re, LLink (R y))]> M2'). iFrame "HMfinal". iPureIntro.
      split_and!.
      { symmetry. eapply R_of_parent; eauto. }
      { erewrite skel_insert; [exact Hskel | exact Heq2]. }
      rewrite HFeq0. apply Mem_compress; [exact HMem' | exact Hin]. }

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
  iDestruct "HUF" as "(%F & %LM & %HInv & %HMem & Hpointsto)".
  pose proof (Inv_dsf D F R V HInv) as Hdsf.
  edestruct (ipc_defined D F x Hdsf) as (d & F' & Hipc).
  iSpecialize ("Hspec" with "[//] [//] [//] [//] Hpointsto").
  iApply (imp_wand with "Hspec").
  iIntros (y) "(%M' & -> & %Hskel & Hpointsto & %HMem')".
  iSplit; first done.
  iFrame "∗%". iPureIntro.
  split; eauto.
  eapply is_dsf_bw_ipc; eauto.
  eapply bw_ipc_preserves_RF_agreement; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Definition get_spec (e : elem) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜e ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ (x : val), ⌜x = V e⌝ ∗ UF D R V }}.

Lemma get_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec)%I η -∗
  imp (eval η (EAnonFun __get)) {{ λ c, □ iSpec τ[elem] c get_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  unfold get_spec.
  iIntros (D R V) "%Hin HUF".
  iApply imp_please; iNext.

  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists lr, M !! (R e) = Some (lr, LRoot (V (R e)))) as (lr & Heq).
  { eapply Mem_root; eauto using idempotent. }
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  imp_match content with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "(-> & Hv)".
  simpl.
  next_branch.
  { iApply (imp_wand with "[Hv]").
    { iApply (imp_vertex_read_value with "Hv"). imp_path. }
    iIntros (?) "(-> & Hv)".
    iSplit; first iPureIntro. { by rewrite HRV. }
    iSpecialize ("Hback" with "Hv").
    iFrame "∗%". }
  next_branch. exfalso. resolve_no_match.
Qed.

(* -------------------------------------------------------------------------- *)

Definition set_spec (e : elem) (v : val) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜e ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ (x : unit), UF D R V.[ e -/R/> v] }}.

Lemma set_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec)%I η -∗
  imp (eval η (EAnonFun __set)) {{ λ c, □ iSpec τ[elem;val] c set_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (e v).
  unfold set_spec.
  iIntros (D R V) "%Hin HUF".
  iApply imp_please; iNext.

  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[%//] HUF"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists lr, M !! (R e) = Some (lr, LRoot (V (R e)))) as (lr & Heq).
  { eapply Mem_root; eauto using idempotent. }
  iDestruct (pointsto_M_acc _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  imp_match content with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "(-> & Hv)".
  next_branch.

  { iApply (imp_wand with "[Hv]").
    { iApply (imp_vertex_write_value with "Hv [] []"); [imp_path|imp_path]. }
    iIntros ([]) "(% & -> & Hv) /=".

    iSpecialize ("Hback" $! lr (LRoot _) with "Hv").
    iFrame "Hback". iPureIntro.
    eauto using Inv_update_class, Mem_update. }
  next_branch. exfalso.
  simpl in *|-.
  resolve_no_match.
Qed.

(* -------------------------------------------------------------------------- *)

Definition union_spec (x y : elem) (m : microvx) : iProp Σ :=
  ∀ D R V,
    ⌜x ∈ D⌝ -∗
    ⌜y ∈ D⌝ -∗
    UF D R V -∗
    imp m {{ λ z, UF D R.[y -/R/> z].[x -/R/> z] V.[y -/R/> (V z)].[x -/R/> (V z)] ∗
                  ⌜z = R x ∨ z = R y⌝ }}.

Lemma union_proof η :
  in_env "find" (λ c, □ iSpec τ[elem] c find_spec) η -∗
  imp (eval η (EAnonFun __union)) {{ λ c, □ iSpec τ[elem;elem] c union_spec }}.
Proof.
  iIntros "#Hfind".
  iApply imp_EAnon_pers.
  iIntros "!>" (x y).
  unfold union_spec.
  iIntros (D R V) "%Hin_x %Hin_y HUF".
  iApply imp_please; iNext.
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
    iDestruct "HUF" as "(%F & %M & %HI & %HM & Hpts)".
    destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [|congruence].
    rewrite {1 3} HReq.
    rewrite !update_class_R_diag.
    erewrite !update_class_V_diag; try eassumption.
    iFrame "∗%". }

  iIntros "%Hneq".
  iPoseProof (UF_image with "HUF") as "%HRD_x"; first apply Hin_x.
  iPoseProof (UF_image with "HUF") as "%HRD_y"; first apply Hin_y.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists rx, M !! (R x) = Some (rx, LRoot (V (R x)))) as (rx & Heq_x).
  { eapply Mem_root; eauto using idempotent. }
  assert (exists ry, M !! (R y) = Some (ry, LRoot (V (R y)))) as (ry & Heq_y).
  { eapply Mem_root; eauto using idempotent. }

  destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [ congruence | ].

  iPoseProof (pointsto_M_acc2 with "HM") as "(Hvx & Hvy & Hback)".
  eassumption. eassumption. eassumption.

  imp_match (content * content)%type with "[Hvx Hvy]".
  { imp_tuple with "[Hvx] [Hvy]".
    { iApply (imp_vertex_load with "Hvx"). imp_path. }
    { iApply (imp_vertex_load with "Hvy"). imp_path. } }

  destruct a as [??].
  iIntros "((-> & Hvx) & (-> & Hvy))".
  next_branch; last first. { next_branch. exfalso. resolve_no_match. }

  iApply (imp_ELet_pair (A:=Z) (B:=Z) with "[Hvx Hvy]").
  { imp_tuple with "[Hvx] [Hvy]".
    { iApply (imp_vertex_read_rank with "Hvx"). imp_path. }
    { iApply (imp_vertex_read_rank with "Hvy"). imp_path. } }
  iIntros (??) "(Hvx & Hvy) /=".

  iApply (imp_EIfThenElse).
  { iApply imp_EOpLt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

  { (* [R x]'s record block is replaced wholesale: take the content cell out
       of the vertex and drop the old record block. *)
    iDestruct "Hvx" as "[Hx _]".
    iApply (imp_ESeq with "[Hx]").
    { (* Goal:= [ x := Link { parent = y } ] *)
      iApply (imp_EStore'
        (A:=content)
        (Φ := ∃ (r : record), r ⤇ {| parent := R y |} ∗ R x ↦ #(cLink r))
        with "Hx").
      - imp_path.
      - imp_data.
      - iIntros "!>" (?) "(% & -> & % & Hown & ->) $". iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    iSpecialize ("Hback" $! _ _ (LLink (R y)) with "[$Hlink $Hown_link] Hvy").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_class_R_diag. erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [x]
       updated to [R y]: [UF D R.[x -/R/> R y] V.[x -/R/> V (R y)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R x) (R y)).
    iPureIntro.
    rewrite (insert_id M); last assumption.
    split.
    - eapply Inv_link; eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto. by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto. }

  iApply imp_EIfThenElse. { iApply imp_EOpGt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

   { (* Same record-block replacement, this time on [R y]'s side. *)
    iDestruct "Hvy" as "[Hy _]".
    iApply (imp_ESeq with "[Hy]").
    { iApply (imp_EStore'
        (A:=content)
        (Φ := ∃ (r : record), r ⤇ {| parent := R x |} ∗ R y ↦ #(cLink r))
        with "Hy").
      imp_path. imp_data.
      iIntros "!>" (?) "(% & -> & % & Hown & ->) $".
      iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    iSpecialize ("Hback" $! _ r _ (LLink (R x))
      with "Hvx [$Hlink $Hown_link]").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_classes_comm update_class_R_diag.
    rewrite update_classes_comm; erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [y]
       updated to [R x]: [UF D R.[y -/R/> R x] V.[y -/R/> V (R x)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R y) (R x)).
    iPureIntro.
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption.
    split.
    - eapply (Inv_link _ _ _ _ _ _ _ (R y)); eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto. by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto. }

  iDestruct "Hvy" as "[Hy _]".
  iApply (imp_ESeq with "[Hy]").
    { iApply (imp_EStore'
        (A:=content)
        (Φ := ∃ (r : record), r ⤇ {| parent := R x |} ∗ R y ↦ #(cLink r))
        with "Hy").
      - imp_path.
      - imp_data.
      - iIntros "!>" (?) "(% & -> & % & Hown & ->) $".
        iApply "Hown". }
    iIntros "(% & Hown_link & Hlink)".
    iApply (imp_ESeq with "[Hvx]").
    { iApply (imp_vertex_write_rank with "Hvx [] []"); [imp_path|imp_arith]. }
    iIntros "(% & % & Hvx) /=".
    iSpecialize ("Hback" $! _ r _ (LLink (R x)) with "Hvx [$Hlink $Hown_link]").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_classes_comm update_class_R_diag.
    rewrite update_classes_comm; erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [y]
       updated to [R x]: [UF D R.[y -/R/> R x] V.[y -/R/> V (R x)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R y) (R x)).
    iPureIntro.
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption.
    split.
    - eapply (Inv_link _ _ _ _ _ _ _ (R y)); eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto.
      by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto.
Qed.

End UnionFind.
