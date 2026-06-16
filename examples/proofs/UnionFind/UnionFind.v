From osiris Require Import osiris.
From osiris.examples Require Import og_UnionFindBasic.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link UnionFind04Compress.

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

(* [pointsto_M LM] asserts ownership of the whole two-level heap shape
   described by [LM]: for each vertex [x], ownership of its [content] cell,
   and ownership of the record block that content points to. *)

Definition pointsto_M (LM : gmap elem lcontent) : iProp Σ :=
  ([∗ map] x ↦ lc ∈ LM,
     match lc with
     | LRoot v => ∃ (rr : record) (k : Z),
         x ↦ #(Root rr : @content val _) ∗ ownRepr rr 1 ({| rank := k; value := v |} : root (A:=val))
     | LLink y => ∃ (lr : record),
         x ↦ #(Link lr : @content val _) ∗ ownRepr lr 1 ({| parent := y |} : link (A:=val))
     end)%I.

(* [UF D R V] is the representation predicate. It is an abstract predicate:
   the client uses this predicate, but does not know how it is defined. It
   quantifies existentially over [F/LM], which therefore are not exposed to
   the client. *)

Definition UF D R V : iProp Σ :=
  (∃ F LM,
  ⌜ Inv D F R V ⌝ ∗
  ⌜ Mem D F V LM ⌝ ∗
  pointsto_M LM)%I.

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

Lemma pointsto_M_fresh : forall (LM : gmap elem lcontent) x v,
  pointsto_M LM -∗ x ↦ v -∗ ⌜LM !! x = None⌝.
Proof.
  iIntros (LM x v) "HM Hx".
  destruct (LM !! x) as [lc|] eqn:Heq; [|done].
  iExFalso.
  iDestruct (big_sepM_lookup with "HM") as "Hc"; [exact Heq|].
  destruct lc as [vv | y].
  - iDestruct "Hc" as (rr k) "[Hx' _]".
    iCombine "Hx Hx'" gives %Hbad.
    destruct Hbad as [Hbad _]. exfalso; eapply dfrac_full_exclusive; exact Hbad.
  - iDestruct "Hc" as (lr) "[Hx' _]".
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
    iApply (imp_EData (τ:=τ[record]) _ _ (λ rr, ownRepr rr 1 ({|rank:=0;value:=v|}:root(A:=val)))%I).
    - iApply (imp_wand with "[]").
      { iApply imp_evals_singleton.
        iApply (imp_record (A:=root(A:=val)) (τ:=τ[Z;val])
                  [EInt 0; EPath ["v"]] (λ k vv, ⌜k=0⌝ ∗ ⌜vv=v⌝)%I).
        - rewrite /τ_length /=. lia.
        - iApply imp_evals_cons.
          + iApply imp_EInt.
          + iApply imp_evals_singleton. iApply imp_EPath.
            simpl. f_equal. encode. instantiate (1:=v); reflexivity.
            iPureIntro; reflexivity. }
      iIntros (r) "H". rewrite bi_texist_equiv. iDestruct "H" as ([k vv]) "(Hown & -> & ->)".
      iApply "Hown".
    - iIntros (rr) "Hown". iNext. iExists rr. eauto. }
  iIntros (x) "(%a & (%rr & -> & Hown) & Hx)".
  iDestruct "HUF" as (F LM) "(%HInv & %HMem & HptM)".
  iDestruct (pointsto_M_fresh with "HptM Hx") as %HxLM.
  assert (HxD : x ∉ D) by (eapply Mem_not_elem_of_dom; eauto).
  iSplitR "".
  - iExists F, (<[x:=LRoot v]>LM).
    iSplit; [iPureIntro; eapply Inv_make; eauto|].
    iSplit; [iPureIntro; eapply Mem_make; eauto|].
    rewrite /pointsto_M big_sepM_insert; [|exact HxLM].
    iSplitL "Hown Hx"; [iExists rr, 0; iFrame|iFrame].
  - iPureIntro. split; [exact HxD|].
    eapply R_is_identity_outside_D; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about the representation predicate and about [pointsto_M].
   (These are part of the old, not-yet-ported function-specification
   machinery below — they still reference the single-level [content]/
   [val_of_content] encoding, not our two-level [lcontent]/[pointsto_M].) *)


Lemma pointsto_M_acc : forall M x c,
  M !! x = Some c ->
  pointsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗
     (∀ c' v', ⌜val_of_content c' = Some v'⌝ -∗
               x ↦ v' -∗ pointsto_M (<[x:=c']>M)).
Proof.
  introv HM. iIntros "HM".
  rewrite -[in pointsto_M M](insert_id M _ _ HM) -insert_delete_eq /pointsto_M.
  rewrite big_sepM_insert ?lookup_delete_eq //. iDestruct "HM" as "[Hc HM]".
  destruct (val_of_content c); [|done]. iExists _. iFrame. iSplit; [done|].
  iIntros (c' v' Hv') "?".
  rewrite -insert_delete_eq big_sepM_insert ?lookup_delete_eq // Hv'. iFrame.
Qed.

Lemma pointsto_M_acc_same : forall M x c,
  M !! x = Some c ->
  pointsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗ (x ↦ v -∗ pointsto_M M).
Proof.
  introv HM. iIntros "HM".
  iDestruct (pointsto_M_acc with "HM") as (v Hv) "[Hv HM]"; [done|].
  iExists _. iFrame. iSplit; [done|].
  iSpecialize ("HM" $! _ _ Hv). by rewrite insert_id.
Qed.

(* TODO : that should go into Iris libraries for big ops *)
Lemma pointsto_M_union : forall M1 M2,
  M1 ##ₘ M2 ->
  pointsto_M M1 ∗ pointsto_M M2 ⊣⊢ pointsto_M (M1 ∪ M2).
Proof.
  introv HM12. unfold pointsto_M.
  induction M1 as [|l x M1 ? IH] using map_ind.
  { by rewrite big_opM_empty !left_id. }
  rewrite -insert_union_l !big_sepM_insert //; last first.
  { apply lookup_union_None; split; [done|]. specialize (HM12 l).
    rewrite lookup_insert_eq in HM12. revert HM12. case: (M2 !! l)=>//=. }
  rewrite -assoc. f_equiv. apply IH. by eapply map_disjoint_insert_l.
Qed.

Lemma pointsto_M_insert : forall M x c v,
  M !! x = None ->
  val_of_content c = Some v ->
  x ↦ v ∗ pointsto_M M ⊣⊢ pointsto_M (<[x:=c]>M).
Proof.
  introv Mxc Hcv. by rewrite /pointsto_M big_sepM_insert // Hcv.
Qed.

Lemma pointsto_M_disjoint : forall M1 M2,
  pointsto_M M1 -∗ pointsto_M M2 -∗ ⌜ M1 ##ₘ M2 ⌝.
Proof.
  iIntros "* HM1 HM2" (x). unfold pointsto_M.
  destruct (M1!!x) eqn:HM1, (M2!!x) eqn:HM2=>//.
  iDestruct (big_sepM_lookup with "HM1") as "H1"=>//.
  iDestruct (big_sepM_lookup with "HM2") as "H2"=>//.
  do 2 destruct val_of_content; try done.
  by iCombine "H1 H2" gives %[].
Qed.

(* -------------------------------------------------------------------------- *)

(* Public lemmas about the representation predicate. *)

(* If [UF D R V] holds, then [R] is idempotent. *)

Theorem UF_idempotent : forall D R V,
  UF D R V -∗ ⌜ idempotent R ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using idempotent_R.
Qed.

(* If [UF D R V] holds, then [R] preserves [D]. *)

Theorem UF_image : forall D R V x, x \in D →
  UF D R V -∗ ⌜ R x \in D ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using sticky_R.
Qed.

(* If [UF D R V] holds, then [R] is the identity outside of [D]. *)

Theorem UF_identity : forall D R V x, x \notin D ->
  UF D R V -∗ ⌜ R x = x ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using R_is_identity_outside_D.
Qed.

(* If [UF D R V] holds, then [V] is compatible with [R]. *)

Theorem UF_compatible : forall D R V x, x \in D ->
  UF D R V -∗ ⌜ V x = V (R x) ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto.
Qed.

(* An empty instance of the Union-Find data structure can be created out of
   thin air. This is how the data structure is initialized. *)

Theorem UF_create : forall V,
  TCTR_invariant nmax ={⊤}=∗ UF \{} id V.
Proof using.
  unfold UF. iIntros (V) "#?".
  iExists (@LibRelation.empty elem), (λ _, 0%nat), ∅.
  repeat iSplitL.
  { iPureIntro. constructors.
    { apply is_rdsf_empty. }
    { intro x. eapply is_repr_empty. }
    { eauto. } }
  { iIntros "!%" (??). false. }
  { rewrite /pointsto_M. by auto. }
  { rewrite Phi_empty. by iApply zero_TC. }
  { rewrite card_empty. by iApply zero_TR. }
Qed.

(* Two separate instances of the UnionFind data structure can be merged, without
   actually doing anything at runtime. *)

(* In principle, we could also prove the converse property, [UF_split]. A UnionFind
   data structure can be split in two independent parts, provided the split respects
   the equivalence relation. Considering the amount of dreary work that went into
   establishing [UF_join], I leave this to future work. *)

Theorem UF_join : forall D1 R1 V1 D2 R2 V2,
  UF D1 R1 V1 -∗ UF D2 R2 V2 -∗
  UF
    (D1 \u D2)
    (fun x => If x \in D1 then R1 x else R2 x)
    (fun x => If x \in D1 then V1 x else V2 x)
  ∗ ⌜ D1 \# D2 ⌝.
Proof using.
  intros.
  iDestruct 1 as (F1 K1 M1 HI1 HM1) "(HM1 & HTC1 & TR1)".
  iDestruct 1 as (F2 K2 M2 HI2 HM2) "(HM2 & HTC2 & TR2)".
  sets D: (D1 \u D2).
  sets R: (fun x => If x \in D1 then R1 x else R2 x).
  sets V: (fun x => If x \in D1 then V1 x else V2 x).
  set (F := LibRelation.union F1 F2).
  set (K := fun x => If x \in D1 then K1 x else K2 x).
  set (M := M1 ∪ M2).

  (* Disjointness lemmas. Trivial and painful. *)

  iDestruct (pointsto_M_disjoint with "HM1 HM2") as %HM12.

  assert (forall x, x \in D1 -> x \in D2 -> False).
  { intros l Hl1%HM1 Hl2%HM2. specialize (HM12 l).
    destruct (M1!!l) eqn:HM1l=>//. destruct (M2!!l) eqn:HM2l=>//. }

  assert (D1 \# D2) by by rew_set.

  assert (forall x, x \in D2 -> x \notin D1).
  { intros. intro. eauto. }

  assert (forall x y, F1 x y -> x \in D1).
  { eauto with confined is_dsf. }

  assert (forall x y, F2 x y -> x \in D2).
  { eauto with confined is_dsf. }

  assert (forall x, x \in D1 -> F1 x = F x).
  { intros. subst F. extens; intros y.
    unfold LibRelation.union; split; intros; try branches; eauto; false; eauto. }

  assert (forall x, x \in D2 -> F2 x = F x).
  { intros. subst F. extens; intros y.
    unfold LibRelation.union; split; intros; try branches; eauto; false; eauto. }

  assert (forall x, x \in D1 -> K1 x = K x).
  { intros. subst K. simpl. cases_if~. }

  assert (forall x, x \in D2 -> K2 x = K x).
  { intros. subst K. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> R1 x = R x).
  { intros. subst R. simpl. cases_if~. }

  assert (forall x, x \in D2 -> R2 x = R x).
  { intros. subst R. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> V1 x = V x).
  { intros. subst V. simpl. cases_if~. }

  assert (forall x, x \in D2 -> V2 x = V x).
  { intros. subst V. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> M1!!x = M!!x).
  { intros x Hx%HM1. subst M. destruct (M1!!x) eqn:? =>//.
    symmetry. by apply lookup_union_Some_l. }

  assert (forall x, x \in D2 -> M2!!x = M!!x).
  { intros x Hx%HM2. subst M. destruct (M2!!x) eqn:? =>//.
    symmetry. by apply lookup_union_Some_r. }

  iSplit; last done. iExists F, K, M.

  iCombine "HTC1 HTC2" as "HTC".
  iCombine "TR1 TR2" as "HTR".
  rewrite -pointsto_M_union // -Nat.mul_add_distr_l (@Phi_join 1 _ D F K); eauto.
  rewrite -card_disjoint_union; eauto using is_rdsf_finite; [].
  iFrame. iPureIntro. split.

  (* Preservation of [Inv]. *)
  { destruct HI1, HI2. constructor.
    (* Preservation of [is_rdsf]. *)
    { subst D F K. eapply is_rdsf_join; eauto. }
    (* Preservation of the agreement between [R] and [F]. *)
    { intros x. subst F R. simpl. cases_if.
      (* Case: [x \in D1]. *)
      { eapply is_repr_join_direct_1; eauto. }
      (* Case: [x \notin D1]. *)
      { eapply is_repr_join_direct_2; eauto. }
    }
    (* Preservation of the compatibility of [V]. *)
    { intros x. subst V R. simpl. cases_if; [ | destruct (classic (x \in D2)) ].
      (* Case: [x \in D1]. *)
      { assert (R1 x \in D1). { eauto using sticky_R. }
        cases_if. intuition eauto. }
      (* Case: [x \in D2]. *)
      { assert (R2 x \in D2). { eauto using sticky_R. }
        cases_if. false; eauto. eauto. }
      (* Case: [x \notin D1 \u D2]. *)
      { assert (h: R2 x = x). { eapply R_is_identity_outside_D; eauto with is_dsf. }
        rewrite h. cases_if. reflexivity. }
    }
  }

  (* Preservation of [Mem]. *)
  { intros x Dx. subst D. rewrite in_union_eq in Dx.
    destruct Dx as [ Dx | Dx ].
    { forwards : HM1 Dx. destruct (M1!!x) as [c|] eqn:EQM1=>//.
      unfold is_root in *. rewrite (lookup_union_Some_l _ _ _ _ EQM1) //.
      repeat match goal with h: forall_ x \in D1, _ |- _ =>
        specializes h Dx; try rewrite <- h
      end. done. }
    { forwards : HM2 Dx. destruct (M2!!x) as [c|] eqn:EQM2=>//.
      unfold is_root in *. rewrite (lookup_union_Some_r _ _ _ _ HM12 EQM2) //.
      repeat match goal with h: forall_ x \in D2, _ |- _ =>
        specializes h Dx; try rewrite <- h
      end. done. } }
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [make]. *)

(* The function call [make v] requires [UF D R V] as well as O(1) time credits.
   It returns a new element [x], that is, [x] is not in [D]. It updates the
   data structure to [UF D' R' V'], where:
   1. [D'] is [D] extended with [x];
   2. [R'] is [R];
   3. [V'] is [V] extended with a mapping of [x] to [v]. *)

Theorem make_spec : forall D R V v,
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC 26 }}}
    «make v»
  {{{ (x : elem), RET #x;
      let D' := D \u \{x} in
      let V' := update1 V R x «v»%V in
      UF D' R V' ∗
      ⌜x \notin D /\
       R x = x⌝ }}}.
Proof using.
  iIntros "* #?" (Φ) "!# [HF TC] HΦ".
  wp_tick_rec. wp_tick_pair. wp_tick_inj.
  iMod zero_TR as "TR".
  wp_tick. wp_alloc x as "Hx". iApply "HΦ".
  iDestruct "HF" as (F K M HI HM) "(HM & TC' & TR')".

  iAssert ⌜M !! x = None⌝%I as %Mx.
  { case HMx: (M!!x)=>//.
    iDestruct (big_sepM_lookup with "HM") as "Hx'"=>//.
    destruct val_of_content; try done.
    by iCombine "Hx Hx'" gives %[]. }
  assert (x \notin D) as Dx.
  { intros Dx%HM. by rewrite Mx in Dx. }

  iSplit; [|by eauto 10 using R_is_identity_outside_D].
  iExists _, _, (<[x:=Root 0 _]>M).
  rewrite -Phi_extend 1?Nat.mul_add_distr_l; eauto; [].
  iCombine "TC' TC" as "$".

  rewrite card_disjoint_union; eauto using is_rdsf_finite, finite_single; last first.
  { by rewrite disjoint_single_r_eq. }
  rewrite card_single. iCombine "TR' TR" as "$".

  repeat iSplit; try iPureIntro.
  { applys* Inv_make. } { applys* Mem_make. }
  iApply pointsto_M_insert; [done| |by iFrame].
  rewrite /= /to_mach_int decide_True_pi /=; [by apply (proj2_sig mach_int_0)|].
  intros ?. by rewrite (exists_proj1_pi _ mach_int_0).
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [find]. *)

(* Because [find] is a recursive function, we must begin with a specification
   that is amenable to an inductive proof. It states that [find] essentially
   implements the mathematical predicate [bw_ipc]. If [bw_ipc F x d F'] holds,
   which means that path compression at [x] requires [d] steps and changes the
   graph from [F] to [F'], then [find] requires [d+1] time credits and changes
   the memory from [M] to some [M'] that agrees with [F']. Furthermore, the
   value [r] returned by [find] is the representative of [x]. *)

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

End UnionFind.

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
