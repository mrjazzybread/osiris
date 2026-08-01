From iris.base_logic.lib Require Import invariants ghost_map.
From stdpp Require Import relations.

From osiris Require Import osiris.
From osiris.stdlib.proofs Require Import atomic.
From osiris.examples Require Import og_ConcurrentUnionFind.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link.

(** * Concurrent union-find

    This file contains the verification of the concurrent union-find data
    structure. *)

(* A vertex is a two-field record { id; content }. *)
Notation elem := record.

(* Field offsets of the vertex record. *)
Notation id_field := 0%Z (only parsing).
Notation content_field := 1%Z (only parsing).

Definition ufN : namespace := nroot .@ "concurrent_uf".

(* [elem]/[record] is [tc_opaque loc]; expose [loc]'s instances so that
   vertices and content records can be used as ghost-map keys. *)
Local Instance record_eq_decision : EqDecision record.
Proof. unfold record; simpl. apply _. Defined.
Local Instance record_countable : Countable record.
Proof. unfold record; simpl. apply _. Defined.

(* The static description of a content record; see below. The value
   carried by [CRoot] is the record's payload at allocation time — since a
   [Root] record's [value] field is never actually written again (see the
   comment above [content_own]), this value is permanent, and recording it
   in [cinfo] itself (rather than as a separate, ephemeral existential in
   [content_own]) is what lets [union]'s functional spec relate its
   returned [Some r] to a genuine, persistent fact (the discardable
   fragment [rc ↪[γc]□ CRoot r]) instead of an unconstrained existential. *)
Inductive cinfo :=
| CRoot (v : val)
| CLink (b : Z).

Section ConcurrentUnionFind.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ record cinfo,
          !ghost_mapG Σ Z unit}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.

(* ------------------------------------------------------------------------ *)
(* Persistent block knowledge. *)

(* [isBlockP b t] is the persistent knowledge that the block [b] has the
   mutability tag [t]. It is obtained by persisting the block's points-to
   at allocation time, which is sound because the tag of a record block
   never changes. It is what resolves the physical comparisons performed
   by the CAS instructions. *)

Definition isBlockP (b : locations.loc) (t : mut_tag) : iProp Σ :=
  isBlock b DfracDiscarded t.

Global Instance isBlockP_persistent b t : Persistent (isBlockP b t).
Proof. rewrite /isBlockP /isBlock. apply _. Qed.

(* [record] is typeclass-opaque, so the previous instance does not apply
   to [record]-typed arguments; restate it. *)
Global Instance isBlockP_persistent_rec (rc : record) t :
  Persistent (isBlockP rc t) := isBlockP_persistent rc t.

(* ------------------------------------------------------------------------ *)
(* The registry of content records. *)

(* A content record is the record block wrapped in a [Root]/[Link]
   constructor. Its "static" description never changes over its lifetime:
   - a [Root] record stays a root record (its [value] field is in fact
     never written);
   - a [Link] record keeps, forever, a parent whose identifier is strictly
     smaller than the bound [b] fixed at its creation (path compression
     only ever lowers the parent's identifier).
   This stability is what makes the description [cinfo] a persistent
   fragment of the ghost registry [γc], and is the key to reasoning about
   the racy read of the [parent] field: even if the vertex that carried
   this record has moved on, the record itself still satisfies its
   description. *)

(* The content value carried by a vertex whose content record is [rc]. *)

Definition cval (ci : cinfo) rc : val :=
  match ci with
  | CRoot _ => VInline "Root" rc
  | CLink _ => VInline "Link" rc
  end.

(* ------------------------------------------------------------------------ *)
(* Representation predicates. *)

(* [vertex γ x i] is the persistent knowledge that [x] is a vertex of the
   structure with identifier [i]. *)

Definition vertex (γ : gname) x i : iProp Σ :=
  ∃ (li lc : locations.loc),
    x ↪[γ]□ i ∗
    isBlockLocs x [li; lc] ∗
    isBlockP x Mut ∗
    li ↦□ #i.

Global Instance vertex_persistent γ x i : Persistent (vertex γ x i).
Proof. apply _. Qed.

(* [content_own γ γc rc ci] is the invariant-owned footprint of the
   content record [rc], as described by [ci]. *)

Definition content_own (γ γc : gname) rc (ci : cinfo) : iProp Σ :=
  match ci with
  | CRoot v =>
      ∃ (lv : locations.loc),
        isBlockLocs rc [lv] ∗ isBlockP rc Mut ∗ lv ↦ v
  | CLink b =>
      ∃ (lp : locations.loc) (y : elem) j,
        isBlockLocs rc [lp] ∗ isBlockP rc Mut ∗
        lp ↦ #y ∗ vertex γ y j ∗ ⌜(j < b)%Z⌝
  end.

(* [vertex_own γ γc γn x i] is the invariant-owned footprint of the
   vertex [x]: its content cell, holding a registered content record
   whose description is compatible with [x]'s identifier, together
   with the exclusive ownership of [i] in the identifier registry
   [γn] — this is what makes identifiers injective (see [union]'s
   [x.id <> y.id] assertion below): two vertices both claiming the
   same identifier would both need to exclusively own the same [γn]
   fragment, which is impossible. *)

(* [F] is the *abstract* equivalence graph: a permanent, ghost-only record
   of the edges installed by successful [union] calls. It is deliberately
   decoupled from [content_own]'s [CLink] case, whose stored parent is a
   mere (possibly stale, since path compression is unproven/axiomatized
   here — see [findc_spec] below) witness for [find]'s weak rank bound.
   [F] only ever changes in [union_proof], via [UnionFind03Link.link]; a
   vertex's own tag ([CRoot]/[CLink]) is correlated with [F]'s topology
   (root-ness only, never the specific edge target) via [vertex_own]'s
   last conjunct below. *)

Definition vertex_own (γ γc γn : gname) (F : elem → elem → Prop) x i : iProp Σ :=
  ∃ (li lc : locations.loc) rc (ci : cinfo),
    isBlockLocs x [li; lc] ∗
    lc ↦ cval ci rc ∗
    rc ↪[γc]□ ci ∗
    ⌜∀ b, ci = CLink b → (b ≤ i)%Z⌝ ∗
    ⌜match ci with CRoot _ => Root F x | CLink _ => ¬ Root F x end⌝ ∗
    i ↪[γn] ().

(* The global invariant: the authoritative maps of vertices and content
   records, together with their physical footprints, and the registry
   of identifiers already handed out by [G.fresh]. *)

(* [G.fresh] hands out genuine OCaml [int]s, so every identifier ever
   registered in [M] is representable; this is what lets [union] bridge
   the machine-level comparison [x.id > y.id] back to a [Z]-level fact
   usable in [content_own]'s [CLink] bound. *)

(* [F]'s edges strictly decrease the identifier: every [union] CAS only
   ever installs an edge from the higher-id side to the lower-id side
   (that's exactly the [x.id > y.id] branch guard). This is what rules
   out cycles even when the *target* of a freshly-installed edge is no
   longer a root by the time the edge goes in (a genuine possibility: the
   target is a STALE [findc] snapshot, and nothing re-checks its
   root-status right before the CAS) — a cycle would need some edge along
   it to *increase* the id, contradicting this invariant. See
   [dsf_link_general] below, which reuses this instead of the (root-only)
   [UnionFind03Link.is_dsf_link]. *)

Definition id_bounded (M : gmap elem Z) (F : elem → elem → Prop) : Prop :=
  ∀ w z iw iz, F w z → M !! w = Some iw → M !! z = Some iz → (iz < iw)%Z.

Definition uf_inv (γ γc γn : gname) : iProp Σ :=
  ∃ (M : gmap elem Z) (C : gmap record cinfo) (N : gmap Z unit)
    (F : elem → elem → Prop),
    ghost_map_auth γ 1 M ∗
    ghost_map_auth γc 1 C ∗
    ghost_map_auth γn 1 N ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜DSF F (dom M)⌝ ∗
    ⌜id_bounded M F⌝ ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ γc γn F x i) ∗
    ([∗ map] rc ↦ ci ∈ C, content_own γ γc rc ci).

Definition is_uf (γ γc γn : gname) : iProp Σ :=
  inv ufN (uf_inv γ γc γn).

(* An empty structure can always be created; the empty graph is trivially a
   disjoint set forest over the empty domain ([is_dsf_empty],
   [UnionFind02EmptyCreate.v]). *)

Lemma uf_alloc E :
  ⊢ |={E}=> ∃ γ γc γn, is_uf γ γc γn.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γ) "Hγ".
  iMod (ghost_map_alloc_empty (K:=record) (V:=cinfo)) as (γc) "Hγc".
  iMod (ghost_map_alloc_empty (K:=Z) (V:=unit)) as (γn) "Hγn".
  iMod (inv_alloc ufN _ (uf_inv γ γc γn) with "[Hγ Hγc Hγn]") as "#Hinv".
  { iNext. iExists ∅, ∅, ∅, (empty elem). iFrame. iSplitR.
    { iPureIntro. intros x i. rewrite lookup_empty. discriminate. }
    iSplitR.
    { iPureIntro. rewrite dom_empty_L. exact (is_dsf_empty elem _ _). }
    iSplitR.
    { iPureIntro. intros w z iw iz []. }
    by rewrite !big_sepM_empty. }
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* The [cas] top-level alias. *)

(* The example's first top-level binding is
   [let cas = Atomic.Loc.compare_and_set]. Given the [Atomic] module's
   specification (stdlib/proofs/atomic.v), the alias satisfies
   [compare_and_set_spec] — the logically-atomic CAS triple over
   inline-record contents, generic in the "expected"/"new value"
   argument type [A] via [Encode A]. The proofs of [set], [update] and
   [union] hypothesize [in_env "cas" (λ c, □ ∀ A `{Encode A}, iSpec
   τ[loc; A; A] c compare_and_set_spec) η], which this lemma discharges
   when walking the module's top-level items. *)

Lemma cas_proof η :
  in_env "Atomic" atomic_module_spec η -∗
  imp (eval η (EPath ["Atomic"; "Loc"; "compare_and_set"]))
    {{ λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec }}.
Proof.
  iIntros "HAtomic".
  iDestruct (atomic_cas_path_spec with "HAtomic") as (cas Hcas) "#Hspec".
  iApply (imp_EPath (A:=val) cas).
  { exact Hcas. }
  iExact "Hspec".
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [G.fresh]. *)

(* [G.fresh]'s specification is strengthened to hand back exclusive
   ownership of the returned identifier [i] in the registry [γn]: this
   is what lets [make_proof] register [i] injectively (via
   [vertex_own]'s [i ↪[γn] ()] conjunct), which in turn is what lets
   [union_proof] discharge [assert (x.id <> y.id)]. *)

Definition fresh_spec (γ γc γn : gname) (u : unit) (m : microvx) : iProp Σ :=
  is_uf γ γc γn -∗
  imp m {{ λ i : Z, i ↪[γn] () ∗ ⌜representable i⌝ }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [make]. *)

(* [make v] returns a fresh vertex of the structure. *)

Definition make_spec (γ γc γn : gname) (v : val) (m : microvx) : iProp Σ :=
  is_uf γ γc γn -∗
  imp m {{ λ x : elem, ∃ i, vertex γ x i }}.

(* [record]/[ERecord] allocations must fit within [max_array_length]. *)
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof γ γc γn η :
  path_spec ["G"; "fresh"] (λ fresh, □ iSpec τ[unit] fresh (fresh_spec γ γc γn))%I η -∗
  imp (eval η (EAnonFun __make)) {{ λ c, □ iSpec τ[val] c (make_spec γ γc γn) }}.
Proof.
  iIntros "(%g & %Hg & #Hfresh)".
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  iIntros "#Hinv".
  iApply imp_please; iNext.
  unfold __make. simpl. rewrite {1}/deco.

  (* Goal: [ let id = G.fresh() and content = Root { value = v } in ... ] *)
  iApply (imp_ELet (A:=elem)).
  { iApply (imp_bindings_cons (A:=Z) (λ i : Z, i ↪[γn] () ∗ ⌜representable i⌝)%I with "[] [] []").
    { (* [G.fresh ()], through the [fresh_spec] hypothesis. *)
      rewrite {1}/deco.
      iApply (imp_EApp τ[unit]).
      { rewrite {1}/deco. iApply (imp_EPath (A:=val) g).
        { simpl. exact Hg. }
        iApply "Hfresh". }
      { rewrite {1}/deco. imp_step. }
      simpl. iIntros (u) "_ %m Hm". iNext. iApply ("Hm" with "Hinv"). }
    { iIntros (a) "_". iPureIntro. apply pat_PVar.
      instantiate (1 := λ (w : Z) (l : env), l = [("id", #w)]). reflexivity. }
    (* [Root { value = v }]: allocation of the content record. *)
    iApply (imp_bindings_singleton (A:=record)
        (H:={| encode' := λ rc : record, VInline "Root" rc |})
        (λ r : record, ∃ lv : locations.loc,
           isBlockLocs r [lv] ∗ isBlock r (DfracOwn 1) Mut ∗ lv ↦ v)%I
        with "[] [] []").
    { rewrite {1}/deco.
      iApply (imp_wand with "[]").
      { iApply (imp_EInline (τ:=τ[val]) (λ w : val, ⌜w = v⌝)%I).
        { simpl. lia. }
        iApply (imp_evals_singleton (A:=val)).
        rewrite {1}/deco. imp_path. simpl. done. }
      simpl. iIntros (r) "H".
      iDestruct "H" as (xs) "((%ls & #Hlocs & Htag & Hxs) & ->)".
      (* The freshly allocated block has exactly one field location. *)
      iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv) "[-> Hlv]".
      iEval (rewrite list_z.singleton_unfold) in "Hlocs".
      iExists lv. iFrame "Hlocs". iFrame. }
    { iIntros (rc) "_". iPureIntro. apply pat_PVar.
      instantiate (1 := λ (w : val) (l : env), l = [("content", w)]).
      reflexivity. }
    { iIntros (rc δ) "HΦ1 ->".
      instantiate (1 := (λ δ : env, ∃ (rc : record) (lv : locations.loc),
        ⌜δ = [("content", VInline "Root" rc)]⌝ ∗
        isBlockLocs rc [lv] ∗ isBlock rc (DfracOwn 1) Mut ∗ lv ↦ v)%I).
      iDestruct "HΦ1" as (lv) "(#Hlocs & Htag & Hlv)".
      iExists rc, lv. iFrame "∗#". done. } }
  iIntros (δ) "(%a & %η' & %δ' & -> & [Htok %Hrepa] & %HP & HQ)".
  iDestruct "HQ" as (rc lv) "(-> & #Hlocs & Htag & Hlv)".
  subst η'. simpl.

  (* Goal: [ { id; content } ]. Allocate the vertex, then register it (and
     its content record) in the invariant; this last step is a pure ghost
     update, performed under [imp_fupd]. *)
  iApply imp_fupd.
  rewrite {1}/deco.
  iApply (imp_wand with "[]").
  { iApply (imp_ERecord (τ:=τ[Z; val])
      (λ i c, ⌜i = a⌝ ∗ ⌜c = VInline "Root" rc⌝)%I Mut).
    { simpl. lia. }
    iApply (imp_evals_cons (A:=Z)).
    { rewrite {1}/deco. imp_path. }
    iApply (imp_evals_singleton (A:=val)).
    rewrite {1}/deco. imp_path. }
  simpl. iIntros (x) "H".
  iDestruct "H" as (i c) "((%ls & #Hxlocs & Hxtag & Hxs) & -> & ->)".
  (* The vertex block has exactly two field locations: [li] and [lc]. *)
  iDestruct (big_opLZ.big_sepLZ2_pair_inv_r with "Hxs") as (li lc) "(-> & Hli & Hlc)".

  (* Persist the immutable knowledge: the [id] field and both block tags. *)
  iMod (gen_heap.pointsto_persist with "Hli") as "#Hli".
  iDestruct "Hxtag" as (xls) "Hxtag".
  iMod (gen_heap.pointsto_persist with "Hxtag") as "Hxtag".
  iAssert (isBlockP x Mut) with "[Hxtag]" as "#HxP".
  { iExists xls. iFrame. }
  iDestruct "Htag" as (rls) "Htag".
  iMod (gen_heap.pointsto_persist with "Htag") as "Htag".
  iAssert (isBlockP rc Mut) with "[Htag]" as "#HrcP".
  { iExists rls. iFrame. }

  (* Register the vertex and its content record in the invariant. *)
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  (* [x] is fresh: an existing entry would own [lc] a second time. *)
  destruct (M !! x) as [ix|] eqn:HMx.
  { iDestruct (big_sepM_lookup with "HM") as "Hvo"; first exact HMx.
    assert (Inhabited elem) as Hinh by (unfold elem, record; simpl; apply _).
    assert (Inhabited cinfo) as Hcinh by exact (populate (CRoot v)).
    iDestruct "Hvo" as (li' lc' rc' ci') "(#Hxlocs' & Hlc' & _)".
    iAssert (▷ ⌜[li; lc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
    { iNext. iApply (isBlockLocs_valid with "Hxlocs' Hxlocs"). }
    simplify_eq.
    iDestruct "Hlc'" as ">Hlc'".
    iCombine "Hlc Hlc'" gives %Hbad.
    destruct Hbad as [Hbad _]. exfalso.
    eapply dfrac_full_exclusive. exact Hbad. }
  (* [rc] is fresh: an existing entry would own [lv] a second time. *)
  destruct (C !! rc) as [ci0|] eqn:HCrc.
  { iDestruct (big_sepM_lookup with "HC") as "Hco"; first exact HCrc.
    destruct ci0 as [v0|b]; simpl.
    { iDestruct "Hco" as (lv') "(#Hlocs' & _ & Hlv')".
      iAssert (▷ ⌜[lv'] = [lv]⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hlocs Hlocs'"). }
      simplify_eq.
      iDestruct "Hlv'" as ">Hlv'".
      iCombine "Hlv Hlv'" gives %Hbad.
      destruct Hbad as [Hbad _]. exfalso.
      eapply dfrac_full_exclusive. exact Hbad. }
    { assert (Inhabited elem) as Hinh by (unfold elem, record; simpl; apply _).
      iDestruct "Hco" as (lp y j) "(#Hlocs' & _ & Hlp & _)".
      iAssert (▷ ⌜[lp] = [lv]⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hlocs Hlocs'"). }
      simplify_eq.
      iDestruct "Hlp" as ">Hlp".
      iCombine "Hlv Hlp" gives %Hbad.
      destruct Hbad as [Hbad _]. exfalso.
      eapply dfrac_full_exclusive. exact Hbad. } }
  iMod (ghost_map_insert rc (CRoot v) with "Hcauth") as "[Hcauth Hrcfrag]";
    first exact HCrc.
  iMod (ghost_map_elem_persist with "Hrcfrag") as "#Hrcfrag".
  iMod (ghost_map_insert x a with "Hauth") as "[Hauth Hxfrag]";
    first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hlv Htok]") as "_".
  { iNext. iExists (<[x:=a]> M), (<[rc:=CRoot v]> C), N, F.
    iFrame "Hauth Hcauth Hnauth".
    iSplitR.
    { iPureIntro. intros x' i' Hx'.
      destruct (decide (x' = x)) as [->|Hne].
      { rewrite lookup_insert_eq in Hx'. simplify_eq. exact Hrepa. }
      { rewrite lookup_insert_ne in Hx'; last done. exact (Hrep x' i' Hx'). } }
    iSplitR.
    { iPureIntro. rewrite dom_insert_L.
      eapply is_dsf_covariant_in_D; [exact HdsfF|]. set_solver. }
    iSplitR.
    { iPureIntro. intros w z iw iz HFwz Hw Hz.
      destruct (decide (w = x)) as [->|Hwne].
      { destruct HdsfF as [[Hconf'] _ _]. exfalso.
        destruct (Hconf' x z HFwz) as [Hwd _]. apply not_elem_of_dom in HMx. contradiction. }
      rewrite lookup_insert_ne in Hw; last done.
      destruct (decide (z = x)) as [->|Hzne].
      { destruct HdsfF as [[Hconf'] _ _]. exfalso.
        destruct (Hconf' w x HFwz) as [_ Hzd]. apply not_elem_of_dom in HMx. contradiction. }
      rewrite lookup_insert_ne in Hz; last done.
      exact (HidF w z iw iz HFwz Hw Hz). }
    iSplitL "HM Hlc Htok".
    { rewrite big_sepM_insert; last exact HMx.
      iSplitL "Hlc Htok".
      { iExists li, lc, rc, (CRoot v). iFrame "Hxlocs Hlc Hrcfrag Htok".
        iSplit.
        { iPureIntro. intros b Hb. discriminate. }
        iPureIntro. eapply only_roots_outside_D; [exact HdsfF|].
        apply not_elem_of_dom. exact HMx. }
      iApply "HM". }
    rewrite big_sepM_insert; last exact HCrc.
    iSplitL "Hlv".
    { simpl. iExists lv. iFrame "Hlocs HrcP Hlv". }
    iApply "HC". }
  iModIntro. iExists a.
  iExists li, lc. iFrame "Hxfrag Hxlocs HxP Hli".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [find]. *)

(* [find x] returns a vertex [z] of the structure such that [z]'s
   identifier is at most [x]'s identifier. (The full specification — [z]
   lies in the same equivalence class as [x] — additionally requires the
   linearizability argument, which is future work.) *)

Definition find_spec (γ γc γn : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    imp m {{ λ z : elem, ∃ j, vertex γ z j ∗ ⌜(j ≤ i)%Z⌝ }}.

(* Proof outline:
   1. Read [x.content] with [imp_ERecordAccess_atomic]: open [uf_inv]
      around the single atomic load of the content cell and extract the
      persistent description of the loaded content record — [rc ↪[γc]□ ci]
      with [ci = CLink b → b ≤ i], plus the record's field location in
      the link case.
   2. Case on [ci]:
      - [CRoot]: the first branch matches with a wildcard sub-pattern
        (no field read) and returns [x]; conclude with [j := i].
      - [CLink b]: the first branch is refuted; the second branch
        pattern-matches [{ parent = y }] against [rc], *re-reading* the
        racy [parent] field. [ipat_PRecord_var_atomic] performs this
        single field load under [uf_inv]: even if [x] has moved on, the
        registered description [rc ↪[γc]□ (CLink b)] guarantees the
        field holds some [y] with [vertex γ y j ∗ j < b]. Recurse
        through the [in_env "find"] hypothesis and conclude by
        transitivity ([j < b ≤ i]). *)

Lemma find_proof γ γc γn η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ γc γn)) η -∗
  imp (eval η (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))))
    {{ λ c, □ iSpec τ[elem] c (find_spec γ γc γn) }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_spec.
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.
  iDestruct "Hx" as (li lc) "(#Hxfrag & #Hxlocs & #HxP & #Hli)".

  (* Goal: [ match x.content with ... ]. The scrutinee is read atomically
     under the invariant; the match continuation receives the loaded
     value together with the persistent description of its record. *)
  imp_match val $! (λ v : val,
    ∃ (rc : record) (ci : cinfo),
      ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ i)%Z⌝ ∗
      match ci with
      | CRoot _ => True
      | CLink b => ∃ lp : locations.loc, isBlockLocs rc [lp]
      end)%I with "[]".
  { (* The atomic read of the content cell. *)
    iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [li; lc] x
              with "Hxlocs [] []").
    { by vm_compute. }
    { imp_path. }
    (* The content field is the second field location. *)
    assert (Hlc1 : @lookup_total Z loc (list loc)
        (@list_z.listz_lookup_total loc locations.inhabited_loc)
        1%Z [li; lc] = lc) by (vm_compute; reflexivity).
    rewrite Hlc1.
    iNext.
    iInv "Hinv" as "H" "Hclose".
    iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
    iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
    rewrite (big_sepM_delete _ M x i); last exact HMx.
    iDestruct "HM" as "[Hvo HM]".
    assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
    assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
    iDestruct "Hvo" as (li' lc' rc ci) "(#Hxlocs' & Hlc & >#Hrc & >%Hb & >%HFx & Htok)".
    iAssert (▷ ⌜[li; lc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
    { iNext. iApply (isBlockLocs_valid with "Hxlocs' Hxlocs"). }
    simplify_eq.
    iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
    rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
    iDestruct "HC" as "[Hco HC]".
    iModIntro.
    iExists (cval ci rc).
    iSplitL "Hlc"; first by iFrame.
    iIntros "!> Hlc".
    (* Extract the persistent payload, restore both footprints, close. *)
    iAssert (match ci with
             | CRoot _ => True
             | CLink _ => ∃ lp : loc, isBlockLocs rc [lp]
             end)%I as "#Hpayload".
    { destruct ci as [v0|b]; first done.
      iDestruct "Hco" as (lp y j) "(#Hrclocs & _)".
      eauto. }
    iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hco Htok]") as "_".
    { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
      iSplitR; first done.
      iSplitR; first done.
      iSplitL "HM Hlc Htok".
      { rewrite (big_sepM_delete _ M x i); last exact HMx.
        iSplitL "Hlc Htok".
        { iExists li', lc', rc, ci. iFrame "Hxlocs Hlc Hrc Htok".
          iSplit; [done|iPureIntro; exact HFx]. }
        iApply "HM". }
      rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
      iFrame "Hco HC". }
    iModIntro.
    iExists rc, ci. iFrame "Hrc Hpayload".
    iSplit; iPureIntro; [done | exact Hb]. }
  iIntros "(%rc & %ci & -> & #Hrc & %Hb & #Hpayload)".
  destruct ci as [v0|b]; simpl.

  { (* [Root _ -> x]: no field read; [x] is returned, with [j := i]. *)
    next_branch.
    imp_path.
    iPureIntro; lia. }

  (* [Link { parent = y } -> find y]: the [Root] branch is refuted; the
     [Link] record pattern re-reads the racy [parent] field atomically. *)
  iDestruct "Hpayload" as (lp) "#Hrclocs".
  next_branch.
  next_branch.
  iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lp with "Hrclocs []").
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C rc (CLink b)); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
  iDestruct "Hco" as (lp' y j) "(#Hrclocs' & #HrcP & Hlp & #Hy & >%Hj)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hrclocs' Hrclocs"). }
  simplify_eq.
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlp]") as "_".
  { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth HM". iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    rewrite (big_sepM_delete _ C rc (CLink b)); last exact HCrc.
    iSplitL "Hlp".
    { iExists lp', y, j. iFrame "Hrclocs HrcP Hlp Hy". done. }
    iApply "HC". }
  iModIntro.

  (* Recurse on the parent: [j < b ≤ i]. *)
  iApply (imp_EApp τ[elem]). { imp_path. } { imp_path. }
  simpl. iIntros (z) "-> %m Hm".
  iNext.
  iSpecialize ("Hm" $! j with "Hinv Hy").
  iApply (imp_wand with "Hm").
  iIntros (z) "(%j0 & #Hz & %Hj0)".
  iExists j0. iFrame "Hz". iPureIntro.
  specialize (Hb b eq_refl). lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [findc] (assumed for now). *)

(* [findc] has the same observable contract as [find] (it returns some
   vertex [z] whose identifier is at most [x]'s), the [compress] calls it
   makes along the way being pure path-compression optimizations. Proving
   [findc]/[compress] themselves (in particular the non-atomic write
   [link.parent <- z]) is future work; [set]/[update]/[union] are verified
   here assuming this specification holds.

   The extra [∃ D F, ...] conjunct is a *snapshot*: [z] was [x]'s
   representative in the abstract equivalence graph [F] (see [uf_inv])
   valid at [findc]'s own linearization instant. [F] only ever grows (via
   [union]'s [link]), so this snapshot can be carried forward to any later
   instant's graph via [rtc_subrel] — see [union_proof]'s use of it, which
   needs exactly this to bridge [findc]'s (possibly stale, by the time
   [union] performs its own fresh CAS-time read) result back to the
   invariant's current [F]. *)

Definition findc_spec (γ γc γn : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    imp m {{ λ z : elem, ∃ j, vertex γ z j ∗ ⌜(j ≤ i)%Z⌝ ∗
             ∃ D F, ⌜DSF F D⌝ ∗ ⌜x ∈ D⌝ ∗ ⌜Repr F x z⌝ }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [set]. *)

(* [set x cx'] is the internal, two-argument recursive helper (the public,
   one-argument [set x v] wraps [Root {value = v}] and calls it). The
   caller supplies ownership of the freshly-allocated record underlying
   [cx'] — it must be a not-yet-registered [Root] record — which [set]
   consumes when its CAS succeeds, registering it in the content-record
   registry [γc]. On failure it hands the same ownership back to the
   caller through the postcondition, ready for another attempt. *)

Definition set_content_spec (γ γc γn : gname) (x : elem) (cx' : val) (m : microvx) : iProp Σ :=
  ∀ i rc' lv' v,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    ⌜cx' = VInline "Root" rc'⌝ -∗
    isBlockLocs rc' [lv'] -∗
    isBlockP rc' Mut -∗
    lv' ↦ v -∗
    imp m {{ λ _ : unit, True }}.

Lemma set_proof γ γc γn η :
  ▷ in_env "set" (λ set, □ iSpec τ[elem; val] set (set_content_spec γ γc γn)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn)) η -∗
  in_env "cas"
    (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __set_fun))))
    {{ λ c, □ iSpec τ[elem; val] c (set_content_spec γ γc γn) }}.
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x cx').
  unfold set_content_spec.
  iIntros (i rc' lv' v) "#Hinv #Hx -> #Hrc'locs #Hrc'P Hlv'".
  iApply imp_please; iNext.
  unfold __set_fun.
  simpl.
  rewrite {1}/deco.
  iApply (imp_ELet_var (B:=elem)).
  {
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  simpl.
  iIntros (z) "-> %m Hm".
  iNext.
  unfold findc_spec.
  iSpecialize ("Hm" $! i with "Hinv Hx").
  iApply "Hm".
  }
  iIntros (z) "(%j & #Hz & %Hj & _)".
  iDestruct "Hz" as (lzi lzc) "(#Hzfrag & #Hzlocs & #HzP & #Hzli)".
  iApply (imp_ELet_var (λ v : val, ∃ rc ci,
    ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ j)%Z⌝ ∗ isBlockP rc Mut)%I).
  {
  rewrite {1}/deco.
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lzi; lzc] z with "Hzlocs [] []").
  {
  by vm_compute.
  }
  {
  imp_path.
  }
  assert (Hlc1 : @lookup_total Z loc (list loc)
      (@list_z.listz_lookup_total loc locations.inhabited_loc)
      1%Z [lzi; lzc] = lzc) by (vm_compute; reflexivity).
  rewrite Hlc1.
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
  assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
  iDestruct "Hvo" as (li' lc' rc ci) "(#Hzlocs' & Hlc & >#Hrc & >%Hbound & >%HFz & Htok)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hzlocs' Hzlocs").
  }
  simplify_eq.
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iModIntro.
  iExists (cval ci rc).
  iSplitL "Hlc"; first by iFrame.
  iIntros "!> Hlc".
  iAssert (isBlockP rc Mut) as "#HrcP".
  {
  destruct ci as [v0|b].
  {
  iDestruct "Hco" as (lv0) "(_ & $ & _)".
  }
  {
  iDestruct "Hco" as (lp y0 j0) "(_ & $ & _)".
  }
  }
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hco Htok]") as "_".
  {
  iNext.
  iExists M, C, N, F.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc Htok".
  {
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iSplitL "Hlc Htok".
  {
  iExists li', lc', rc, ci.
  iFrame "Hzlocs Hlc Hrc Htok".
  iSplit; [done|iPureIntro; exact HFz].
  }
  iApply "HM".
  }
  rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
  iFrame "Hco HC".
  }
  iModIntro.
  iExists rc, ci.
  iFrame "Hrc HrcP".
  iSplit; iPureIntro; [done | exact Hbound].
  }
  iIntros (cxv) "(%rc & %ci & -> & #Hrc & %Hbound & #HrcP)".
  (* Re-match on the already-loaded [cx]: a plain path lookup, closed
     automatically by [imp_match]'s own scrutinee handling. *)
  imp_match val with "[]".
  destruct ci as [v0|b]; simpl.
  next_branch.
  rewrite {1}/deco.
  iApply (imp_EIfThenElse _ _ _ _ (λ b : bool, if b then True else lv' ↦ v)%I with "[Hlv'] []").
  rewrite {1}/deco.
  iApply (imp_EApp τ[loc; val; val]).
  {
  iDestruct "Hcas" as (casv Hcasv) "#Hcasspec".
  iApply (imp_EPath (A:=val) casv).
  { exact Hcasv. }
  iApply ("Hcasspec" $! val _).
  }
  { iApply (imp_EAtomicLoc (Φ := λ l : loc, ⌜l = lzc⌝)%I 1%Z z [lzi; lzc]).
    { list_z.length. lia. }
    { iApply "Hzlocs". }
    { imp_path. }
    equality. }
  {
  imp_path.
  }
  {
  imp_path.
  }
  simpl.
  iIntros (cx'v cxv) "-> %l -> ->".
  iIntros (m) "Hm".
  iNext.
  iApply ("Hm" $! (⊤ ∖ ↑ufN)).
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
  assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
  iDestruct "Hvo" as (li'' lc'' rc0 ci0) "(#Hzlocs'' & Hlc & >#Hrc0 & >%Hbound0 & >%HFz0 & Htok0)".
  iAssert (▷ ⌜[lzi; lzc] = [li''; lc'']⌝)%I with "[]" as ">%Heql2".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hzlocs'' Hzlocs").
  }
  simplify_eq.
  iDestruct (ghost_map_lookup with "Hcauth Hrc0") as %HCrc0.
  rewrite (big_sepM_delete _ C rc0 ci0); last exact HCrc0.
  iDestruct "HC" as "[Hco0 HC]".
  iAssert (▷ isBlockP rc0 Mut)%I as "#Hrc0P".
  {
  iNext.
  destruct ci0 as [v0'|b0].
  {
  iDestruct "Hco0" as (lv0) "(_ & $ & _)".
  }
  {
  iDestruct "Hco0" as (lp0 y0 j0) "(_ & $ & _)".
  }
  }
  set (c0 := match ci0 with CRoot _ => "Root" | CLink _ => "Link" end).
  assert (Hcval0 : cval ci0 rc0 = VInline c0 rc0) by (destruct ci0; reflexivity).
  iModIntro.
  iExists c0, "Root", rc0, rc, DfracDiscarded, DfracDiscarded, Mut.
  iSplitR; first done.
  rewrite <- Hcval0.
  iFrame "Hlc Hrc0P HrcP".
  iNext.
  iIntros "Hlc' _ _".
  destruct (locations.eqb_spec rc0 rc) as [Heq|Hneq].
  -
  subst rc0.
  iDestruct (ghost_map_elem_agree with "Hrc0 Hrc") as %Heqci0.
  subst ci0.
  iDestruct "Hco0" as (lv0) "(#Hlv0locs & _ & Hlv0)".
  destruct (decide (rc' = rc)) as [->|Hne].
  {
  iAssert (▷ ⌜[lv'] = [lv0]⌝)%I with "[]" as ">%Heqlv".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlv0locs Hrc'locs").
  }
  assert (Heqlv0 : lv' = lv0) by (injection Heqlv; done).
  iEval (rewrite Heqlv0) in "Hlv'".
  iCombine "Hlv0 Hlv'" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  destruct (C !! rc') as [ci1|] eqn:HCrc'.
  {
  assert (HCrc'del : delete rc C !! rc' = Some ci1)
      by (rewrite lookup_delete_ne; done).
  iDestruct (big_sepM_lookup with "HC") as "Hco1"; first exact HCrc'del.
  destruct ci1 as [v1|b1]; simpl.
  {
  iDestruct "Hco1" as (lv1) "(#Hlocs1 & _ & Hlv1)".
  iAssert (▷ ⌜[lv'] = [lv1]⌝)%I with "[]" as ">%Heqlv1".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlocs1 Hrc'locs").
  }
  assert (Heqlv1' : lv' = lv1) by (injection Heqlv1; done).
  iEval (rewrite Heqlv1') in "Hlv'".
  iCombine "Hlv1 Hlv'" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  iDestruct "Hco1" as (lp1 y1 j1) "(#Hlocs1 & _ & Hlp1 & _)".
  iAssert (▷ ⌜[lv'] = [lp1]⌝)%I with "[]" as ">%Heqlv1".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlocs1 Hrc'locs").
  }
  assert (Heqlp1' : lv' = lp1) by (injection Heqlv1; done).
  iEval (rewrite Heqlp1') in "Hlv'".
  iCombine "Hlv' Hlp1" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  iMod (ghost_map_insert rc' (CRoot v) with "Hcauth") as "[Hcauth Hrc'frag]";
  first exact HCrc'.
  iMod (ghost_map_elem_persist with "Hrc'frag") as "#Hrc'frag".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hlv0 Hlv' Htok0]") as "_".
  {
  iNext.
  iExists M, (<[rc':=CRoot v]> C), N, F.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc' Htok0".
  {
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iSplitL "Hlc' Htok0".
  {
  iExists li'', lc'', rc', (CRoot v).
  iFrame "Hzlocs Hlc' Hrc'frag Htok0".
  iSplit.
  { iPureIntro. intros b0 Hb0. discriminate. }
  iPureIntro. exact HFz0.
  }
  iApply "HM".
  }
  rewrite big_sepM_insert; last exact HCrc'.
  iSplitL "Hlv' Hrc'locs".
  {
  simpl.
  iExists lv'.
  iFrame "Hrc'locs Hrc'P Hlv'".
  }
  rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc0.
  iSplitL "Hlv0".
  {
  simpl.
  iExists lv0.
  iFrame "Hlv0locs HrcP Hlv0".
  }
  iApply "HC".
  }
  iModIntro.
  done.
  -
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hco0 Htok0]") as "_".
  {
  iNext.
  iExists M, C, N, F.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc' Htok0".
  {
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iSplitL "Hlc' Htok0".
  {
  iExists li'', lc'', rc0, ci0.
  iFrame "Hzlocs Hlc' Hrc0 Htok0".
  iSplit; [done|iPureIntro; exact HFz0].
  }
  iApply "HM".
  }
  rewrite (big_sepM_delete _ C rc0 ci0); last exact HCrc0.
  iFrame "Hco0 HC".
  }
  iModIntro.
  iFrame "Hlv'".
  -
  iIntros ([|]) "HΦb".
  iApply imp_EUnit.
  done.
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem; val]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  {
  imp_path.
  }
  iIntros (xv cx'v) "-> -> %m Hm".
  iNext.
  unfold set_content_spec.
  iAssert (vertex γ z j) as "Hzv".
  {
  iExists lzi, lzc.
  iFrame "Hzfrag Hzlocs HzP Hzli".
  }
  iSpecialize ("Hm" $! j rc' lv' v with "Hinv Hzv").
  iApply ("Hm" with "[//] Hrc'locs Hrc'P HΦb").
  -
  next_branch.
  next_branch.
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem; val]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  {
  imp_path.
  }
  iIntros (xv cx'v) "-> -> %m Hm".
  iNext.
  iAssert (vertex γ z j) as "Hzv".
  {
  iExists lzi, lzc.
  iFrame "Hzfrag Hzlocs HzP Hzli".
  }
  iApply ("Hm" $! j rc' lv' v with "Hinv Hzv [//] Hrc'locs Hrc'P Hlv'").
Qed.

(* The public, one-argument [set x v]: allocates the fresh [Root {value =
   v}] record and calls the internal, two-argument [set] above. *)

Definition set_spec (γ γc γn : gname) (x : elem) (v : val) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    imp m {{ λ _ : unit, True }}.

Lemma set_wrapper_proof γ γc γn η :
  in_env "set" (λ setv, □ iSpec τ[elem; val] setv (set_content_spec γ γc γn)) η -∗
  imp (eval η (EAnonFun __set)) {{ λ c, □ iSpec τ[elem; val] c (set_spec γ γc γn) }}.
Proof.
  iIntros "#ISet".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x v).
  unfold set_spec.
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.
  unfold __set.
  simpl.
  rewrite {1}/deco.
  iApply (imp_ELet_var (B:=record)
      (H0:={| encode' := λ rc : record, VInline "Root" rc |})
      (λ rc : record, ∃ lv0 : locations.loc,
         isBlockLocs rc [lv0] ∗ isBlock rc (DfracOwn 1) Mut ∗ lv0 ↦ v)%I).
  rewrite {1}/deco.
  iApply (imp_wand with "[]").
  {
  iApply (imp_EInline (τ:=τ[val]) (λ w : val, ⌜w = v⌝)%I).
  {
  simpl.
  lia.
  }
  iApply (imp_evals_singleton (A:=val)).
  rewrite {1}/deco.
  imp_path.
  simpl.
  done.
  }
  simpl.
  iIntros (r) "H".
  iDestruct "H" as (xs) "((%ls & #Hlocs & Htag & Hxs) & ->)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv0) "[-> Hlv0]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs".
  iExists lv0. iFrame "Hlocs". iFrame.
  iIntros (rc') "(%lv0 & #Hlocs & Htag & Hlv0)".
  iApply imp_fupd.
  iDestruct "Htag" as (rls) "Htag".
  iMod (gen_heap.pointsto_persist with "Htag") as "Htag".
  iAssert (isBlockP rc' Mut) with "[Htag]" as "#Hrc'P".
  {
  iExists rls.
  iFrame.
  }
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem; val]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  {
  imp_path.
  }
  iIntros (xv cx'v) "-> -> %m Hm".
  iNext.
  unfold set_content_spec.
  iApply (imp_wand with "[Hm Hinv Hx Hlocs Hrc'P Hlv0]").
  {
  iApply ("Hm" $! i rc' lv0 v with "Hinv Hx [//] Hlocs Hrc'P Hlv0").
  }
  iIntros (u) "_".
  iModIntro.
  done.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [update]. *)

(* [update x f] repeatedly reads the root's current value and CASes in
   [Root {value = f v}], retrying on failure. Unlike [set], each retry
   allocates its own fresh record internally (there is no externally
   supplied [cx'] to thread through failed attempts), so the proof does
   not need [set_content_spec]'s ownership hand-back trick. [f] is
   treated as an arbitrary total pure function: the caller supplies a
   trivial safety spec for it, [∀ w, imp (call f w) {{ λ _, True }}]. *)

Definition update_spec (γ γc γn : gname) (x : elem) (f : val) (m : microvx) : iProp Σ :=
  □ (∀ w : val, imp (call f w) {{ λ _ : val, True }}) -∗
  ∀ i,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    imp m {{ λ _ : unit, True }}.

(* An [Encode record] instance reading a record as a [Root]-tagged
   inline value, used (explicitly, not as a section-wide [Instance], so
   as not to shadow [Encode_record] for every other [elem]-typed goal
   in this file) to instantiate [compare_and_set_spec]'s generic
   argument type directly at [record], matching what [imp_EInline] and
   the atomic record-read rules naturally produce. *)

Definition root_enc : Encode record := {| encode' := λ r : record, VInline "Root" r |}.

Lemma update_proof γ γc γn η :
  ▷ in_env "update" (λ update, □ iSpec τ[elem; val] update (update_spec γ γc γn)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn)) η -∗
  in_env "cas"
    (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __update_fun))))
    {{ λ c, □ iSpec τ[elem; val] c (update_spec γ γc γn) }}.
Proof.
  iIntros "#IUpdate #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x f).
  unfold update_spec.
  iIntros "#Hf".
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.
  unfold __update_fun.
  simpl.
  rewrite {1}/deco.
  iApply (imp_ELet_var (B:=elem)).
  {
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  simpl.
  iIntros (z) "-> %m Hm".
  iNext.
  unfold findc_spec.
  iSpecialize ("Hm" $! i with "Hinv Hx").
  iApply "Hm".
  }
  iIntros (z) "(%j & #Hz & %Hj & _)".
  iDestruct "Hz" as (lzi lzc) "(#Hzfrag & #Hzlocs & #HzP & #Hzli)".
  iApply (imp_ELet_var (λ v : val, ∃ rc ci,
    ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ j)%Z⌝ ∗ isBlockP rc Mut ∗
    match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I).
  {
  rewrite {1}/deco.
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lzi; lzc] z with "Hzlocs [] []").
  {
  by vm_compute.
  }
  {
  imp_path.
  }
  assert (Hlc1 : @lookup_total Z loc (list loc)
      (@list_z.listz_lookup_total loc locations.inhabited_loc)
      1%Z [lzi; lzc] = lzc) by (vm_compute; reflexivity).
  rewrite Hlc1.
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
  assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
  iDestruct "Hvo" as (li' lc' rc ci) "(#Hzlocs' & Hlc & >#Hrc & >%Hbound & >%HFz & Htok)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hzlocs' Hzlocs").
  }
  simplify_eq.
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iModIntro.
  iExists (cval ci rc).
  iSplitL "Hlc"; first by iFrame.
  iIntros "!> Hlc".
  iAssert (isBlockP rc Mut ∗
    match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I
    as "#[HrcP Hpayload]".
  {
  destruct ci as [v0|b].
  {
  iDestruct "Hco" as (lv0) "(#Hlocs0 & #Htag & _)".
  iSplit; [iExact "Htag"|].
  eauto.
  }
  {
  iDestruct "Hco" as (lp y0 j0) "(_ & #Htag & _)".
  iSplit; [iExact "Htag"|].
  done.
  }
  }
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hco Htok]") as "_".
  {
  iNext.
  iExists M, C, N, F.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc Htok".
  {
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iSplitL "Hlc Htok".
  {
  iExists li', lc', rc, ci.
  iFrame "Hzlocs Hlc Hrc Htok".
  iSplit; [done|iPureIntro; exact HFz].
  }
  iApply "HM".
  }
  rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
  iFrame "Hco HC".
  }
  iModIntro.
  iExists rc, ci.
  iFrame "Hrc HrcP Hpayload".
  iSplit; iPureIntro; [done | exact Hbound].
  }
  iIntros (cxv) "(%rc & %ci & -> & #Hrc & %Hbound & #HrcP & #Hpayload)".
  (* Re-match on the already-loaded [cx]: a plain path lookup, closed
     automatically by [imp_match]'s own scrutinee handling. *)
  imp_match val with "[]".
  destruct ci as [v0|b]; simpl.
  iDestruct "Hpayload" as (lv) "#Hrclocs".
  next_branch.
  iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iDestruct "Hco" as (lv') "(#Hlocs' & _ & Hlv)".
  iAssert (▷ ⌜[lv] = [lv']⌝)%I with "[]" as ">%Heql".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlocs' Hrclocs").
  }
  simplify_eq.
  iModIntro.
  iExists v0.
  iSplitL "Hlv"; first by iFrame.
  iIntros "!> Hlv".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlv]") as "_".
  {
  iNext.
  iExists M, C, N, F.
  iFrame "Hauth Hcauth Hnauth HM". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
  iSplitL "Hlv".
  {
  iExists lv'.
  iFrame "Hlocs' HrcP Hlv".
  }
  iApply "HC".
  }
  iModIntro.
  rewrite {1}/deco.
  iApply (imp_EIfThenElse _ _ _ _ (λ _ : bool, True)%I).
  rewrite {1}/deco.
  iApply (imp_EApp (@type_nel.Tcons loc _ (@type_nel.Tcons record root_enc (@type_nel.Tbase record root_enc)))).
  {
  iDestruct "Hcas" as (casv Hcasv) "#Hcasspec".
  iApply (imp_EPath (A:=val) casv).
  {
  exact Hcasv.
  }
  iApply ("Hcasspec" $! record root_enc).
  }
  {
  rewrite {1}/deco.
  iApply (imp_EAtomicLoc (Φ := λ l : loc, ⌜l = lzc⌝)%I 1%Z z [lzi; lzc]).
  {
  by vm_compute.
  }
  {
  iNext.
  iExact "Hzlocs".
  }
  {
  imp_path.
  }
  assert (Hlc1 : @lookup_total Z loc (list loc)
      (@list_z.listz_lookup_total loc locations.inhabited_loc)
      1%Z [lzi; lzc] = lzc) by (vm_compute; reflexivity).
  rewrite Hlc1.
  iNext.
  done.
  }
  {
  imp_path.
  }
  rewrite {1}/deco.
  iApply (imp_wand _ _ _ _ _ (λ r : elem, ∃ (lv0 : locations.loc) (w : val),
    isBlockLocs r [lv0] ∗ isBlock r (DfracOwn 1) Mut ∗ lv0 ↦ w)%I with "[]").
  {
  iApply (imp_EInline (τ:=τ[val]) (λ w : val, True)%I).
  {
  simpl.
  lia.
  }
  iApply (imp_evals_singleton (A:=val)).
  rewrite {1}/deco.
  iApply (imp_EApp' (B:=val) _ _ _ (λ c : val, ⌜c = f⌝)%I (λ w : val, ⌜w = v0⌝)%I).
  {
  rewrite {1}/deco.
  imp_path.
  }
  {
  imp_path.
  }
  iNext.
  iIntros (f0 w0) "-> ->".
  iApply "Hf".
  }
  iIntros (r) "H".
  iDestruct "H" as (x0) "((%ls & #Hlocs2 & Htag2 & Hxs2) & _)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs2") as (lv2) "[-> Hlv2]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs2".
  iExists lv2, x0. iFrame "Hlocs2 Htag2 Hlv2".
  iIntros (rc3 rc2) "->".
  iIntros (lc2) "-> Hown".
  iIntros (m2) "Hm2".
  iNext.
  iApply "Hm2".
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M2 C2 N2 F2) "(>Hauth & >Hcauth & >Hnauth & >%Hrep2 & >%HdsfF2 & >%HidF2 & HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M2 z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
  assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
  iDestruct "Hvo" as (li'' lc'' rc0 ci0) "(#Hzlocs'' & Hlc & >#Hrc0 & >%Hbound0 & >%HFz0 & Htok0)".
  iAssert (▷ ⌜[lzi; lzc] = [li''; lc'']⌝)%I with "[]" as ">%Heql2".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hzlocs'' Hzlocs").
  }
  simplify_eq.
  iDestruct (ghost_map_lookup with "Hcauth Hrc0") as %HCrc0.
  rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
  iDestruct "HC" as "[Hco0 HC]".
  iAssert (▷ isBlockP rc0 Mut)%I as "#Hrc0P".
  {
  iNext.
  destruct ci0 as [v1|b0].
  {
  iDestruct "Hco0" as (lv0) "(_ & $ & _)".
  }
  {
  iDestruct "Hco0" as (lp0 y0 j0) "(_ & $ & _)".
  }
  }
  set (c0 := match ci0 with CRoot _ => "Root" | CLink _ => "Link" end).
  assert (Hcval0 : cval ci0 rc0 = VInline c0 rc0) by (destruct ci0; reflexivity).
  iModIntro.
  iExists c0, "Root", rc0, rc, DfracDiscarded, DfracDiscarded, Mut.
  iSplitR; first done.
  rewrite <- Hcval0.
  iFrame "Hlc Hrc0P HrcP".
  iNext.
  iIntros "Hlc' _ _".
  destruct (locations.eqb_spec rc0 rc) as [Heq|Hneq].
  subst rc0.
  iDestruct (ghost_map_elem_agree with "Hrc0 Hrc") as %Heqci0.
  subst ci0.
  iDestruct "Hco0" as (lv0) "(#Hlv0locs & _ & Hlv0)".
  iDestruct "Hown" as (lv3 w3) "(#Hlv3locs & Htag3 & Hlv3)".
  destruct (decide (rc3 = rc)) as [->|Hne].
  {
  iAssert (▷ ⌜[lv3] = [lv0]⌝)%I with "[]" as ">%Heqlv".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlv0locs Hlv3locs").
  }
  assert (Heqlv0 : lv3 = lv0) by (injection Heqlv; done).
  iEval (rewrite Heqlv0) in "Hlv3".
  iEval (rewrite <- Heqlv0) in "Hlv0".
  iCombine "Hlv0 Hlv3" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  destruct (C2 !! rc3) as [ci1|] eqn:HCrc3.
  {
  assert (HCrc3del : delete rc C2 !! rc3 = Some ci1)
    by (rewrite lookup_delete_ne; done).
  iDestruct (big_sepM_lookup with "HC") as "Hco1"; first exact HCrc3del.
  destruct ci1 as [v2|b1]; simpl.
  {
  iDestruct "Hco1" as (lv1) "(#Hlocs1 & _ & Hlv1)".
  iAssert (▷ ⌜[lv3] = [lv1]⌝)%I with "[]" as ">%Heqlv1".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs").
  }
  assert (Heqlv1' : lv1 = lv3) by (injection Heqlv1; done).
  iEval (rewrite Heqlv1') in "Hlv1".
  iEval (rewrite -Heqlv1') in "Hlv3".
  iCombine "Hlv1 Hlv3" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  iDestruct "Hco1" as (lp1 y1 j1) "(#Hlocs1 & _ & Hlp1 & _)".
  iAssert (▷ ⌜[lv3] = [lp1]⌝)%I with "[]" as ">%Heqlv1".
  {
  iNext.
  iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs").
  }
  assert (Heqlp1' : lp1 = lv3) by (injection Heqlv1; done).
  iEval (rewrite -Heqlp1') in "Hlv3".
  iCombine "Hlv3 Hlp1" gives %Hbad.
  destruct Hbad as [Hbad _].
  exfalso.
  eapply dfrac_full_exclusive.
  exact Hbad.
  }
  iDestruct "Htag3" as (rls3) "Htag3".
  iMod (gen_heap.pointsto_persist with "Htag3") as "Htag3".
  iAssert (isBlockP rc3 Mut) with "[Htag3]" as "#Hrc3P".
  {
  iExists rls3.
  iFrame.
  }
  iMod (ghost_map_insert rc3 (CRoot w3) with "Hcauth") as "[Hcauth Hrc3frag]";
  first exact HCrc3.
  iMod (ghost_map_elem_persist with "Hrc3frag") as "#Hrc3frag".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hlv0 Hlv3 Htok0]") as "_".
  {
  iNext.
  iExists M2, (<[rc3:=CRoot w3]> C2), N2, F2.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc' Htok0".
  {
  rewrite (big_sepM_delete _ M2 z j); last exact HMz.
  iSplitL "Hlc' Htok0".
  {
  iExists li'', lc'', rc3, (CRoot w3).
  iFrame "Hzlocs Hlc' Hrc3frag Htok0".
  iSplit.
  { iPureIntro. intros b0 Hb0. discriminate. }
  iPureIntro. exact HFz0.
  }
  iApply "HM".
  }
  rewrite big_sepM_insert; last exact HCrc3.
  iSplitL "Hlv3".
  {
  simpl.
  iExists lv3.
  iFrame "Hlv3locs Hrc3P Hlv3".
  }
  rewrite (big_sepM_delete _ C2 rc (CRoot v0)); last exact HCrc0.
  iSplitL "Hlv0".
  {
  simpl.
  iExists lv0.
  iFrame "Hlv0locs HrcP Hlv0".
  }
  iApply "HC".
  }
  iModIntro.
  done.
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hco0 Htok0]") as "_".
  {
  iNext.
  iExists M2, C2, N2, F2.
  iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL "HM Hlc' Htok0".
  {
  rewrite (big_sepM_delete _ M2 z j); last exact HMz.
  iSplitL "Hlc' Htok0".
  {
  iExists li'', lc'', rc0, ci0.
  iFrame "Hzlocs Hlc' Hrc0 Htok0".
  iSplit; [done|iPureIntro; exact HFz0].
  }
  iApply "HM".
  }
  rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
  iFrame "Hco0 HC".
  }
  iModIntro.
  done.
  iIntros ([|]) "_".
  -
  iApply imp_EUnit.
  done.
  -
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem; val]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  {
  imp_path.
  }
  iIntros (xv fv) "-> -> %m3 Hm3".
  iNext.
  unfold update_spec.
  iAssert (vertex γ z j) as "Hzv".
  {
  iExists lzi, lzc.
  iFrame "Hzfrag Hzlocs HzP Hzli".
  }
  iSpecialize ("Hm3" with "Hf").
  iSpecialize ("Hm3" $! j).
  iApply ("Hm3" with "Hinv Hzv").
  -
  next_branch.
  next_branch.
  rewrite {1}/deco.
  iApply (imp_EApp τ[elem; val]).
  {
  imp_path.
  }
  {
  imp_path.
  }
  {
  imp_path.
  }
  iIntros (xv fv) "-> -> %m3 Hm3".
  iNext.
  iAssert (vertex γ z j) as "Hzv".
  {
  iExists lzi, lzc.
  iFrame "Hzfrag Hzlocs HzP Hzli".
  }
  iSpecialize ("Hm3" with "Hf").
  iSpecialize ("Hm3" $! j).
  iApply ("Hm3" with "Hinv Hzv").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [union]. *)

(* A full functional specification, mirroring the sequential union-find's
   own [union_spec] (see [UnionFind.v]) but adapted to the concurrent
   setting: instead of a caller-owned [D R V] resource returned updated
   (impossible here — [is_uf] is a shared invariant, not something a
   single caller can hold exclusively, and nothing in this file tracks a
   *single*, monotonically-growing ghost history of the equivalence graph
   across separate invariant opens — see the note below), every fact is
   an *existential snapshot*, local to whichever [uf_inv] open produced
   it: "there existed a valid disjoint-set forest [F] over domain [D],
   at some point during this call, such that ...".

   - [None]: [x] and [y] share a common representative — [same_class x y]
     below, unfolding to [∃ z, ev_reaches x z ∧ ev_reaches y z]: [Repr Fx x
     z] from [x]'s own [findc] snapshot, [Repr Fy y z] from [y]'s (a
     separate, generally later, snapshot: [union] calls [findc] on [x]
     then on [y], each independently opening the invariant).
   - [Some r]: [x] and [y] turned out distinct, and [rc ↪[γc]□ CRoot r] is
     the PERSISTENT registration of whichever root's content record ([rc])
     got absorbed — [r] is exactly the value that was stored there. Since
     a content record's [cinfo] tag never changes once registered (see
     [cinfo]'s own comment), this fact survives forever, even though the
     vertex [z] whose content [rc] used to be has since become a [Link]:
     the caller gets back a genuine, checkable fact about [r]'s provenance,
     not just an unconstrained value.

   Why two independent snapshots instead of one shared [F]: [findc]'s
   result for [x] and for [y] come from two separate, independently-timed
   invariant opens, and nothing here maintains monotone ghost state
   relating an *earlier* snapshot's graph to a *later* one (that would
   need e.g. a [mono_list]-style history of installed edges, threaded
   through a dedicated ghost name — not built here, since [findc] itself
   is still only an assumed specification, not proven). Stating the
   result as "some [Fx] valid when [x] was found" and "some [Fy] valid
   when [y] was found" is exactly what the proof can honestly establish
   without that extra machinery, and is still a real, non-trivial
   functional characterization: [z] is a genuine graph-theoretic
   representative on each side, not just an opaque returned pointer.

   The return value's TYPE is [option val], not [option elem]: [Root]'s
   "value" field ([content_own]'s CRoot case) is untyped ([lv ↦ v] for an
   arbitrary [v : val], mirroring [set]/[update]'s own genericity). *)

(* [snap_reaches u z]: [z] is [u]'s representative in *some* valid
   disjoint-set forest [F] — a single-snapshot fact, exactly what one
   [findc] call (or one successful CAS's own closing argument) can
   honestly establish. [ev_reaches] is its reflexive-transitive closure:
   a *chain* of such single-snapshot facts, each possibly witnessed by a
   completely different [F] (no shared history needed between them).

   This is what lets [union_proof]'s recursive calls compose without a
   monotone ghost history: a call on [x]/[y] first derives [snap_reaches
   x a]/[snap_reaches y y'] from its own [findc], then either finishes
   directly (one hop) or recurses on [a]/[y'] — and the recursive call's
   own [ev_reaches a z]/[ev_reaches y' z] chains with the first hop via
   plain [rtc] transitivity ([rtc_l]) into [ev_reaches x z]/[ev_reaches y
   z], regardless of whether the recursive call's internal snapshots have
   anything to do with this call's [Fx]/[Fy]. *)

Definition snap_reaches (u z : elem) : Prop := ∃ D F, DSF F D ∧ u ∈ D ∧ Repr F u z.

Definition ev_reaches : elem -> elem -> Prop := rtc snap_reaches.

(* [x] and [y] have become equivalent: they share a common representative
   in the chain of successive snapshots [ev_reaches] tracks. Naming this
   separately (rather than inlining the existential in [union_spec]) is
   what lets the [None] case read, at a glance, as "x and y are equal". *)

Definition same_class (x y : elem) : Prop := ∃ z, ev_reaches x z ∧ ev_reaches y z.

Definition union_spec (γ γc γn : gname) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ i j,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    vertex γ y j -∗
    imp m {{ λ ov : option val,
      match ov with
      | None => ⌜same_class x y⌝
      | Some r => ∃ z rc, (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc ↪[γc]□ CRoot r
      end }}.

(* An [Encode record] instance reading a record as a [Link]-tagged inline
   value, analogous to [root_enc], used to CAS a freshly allocated
   [Link { parent = ... }] content record into a vertex's [content]
   field via the generic [compare_and_set_spec]. *)

Definition link_enc : Encode record := {| encode' := λ r : record, VInline "Link" r |}.

(* Following [F]-edges strictly decreases the identifier, given
   [id_bounded]: an easy induction along the path, confining each
   intermediate vertex into [dom M] (hence giving it an id to compare)
   via [DSF]'s own [Confined] component. *)

Lemma path_id_decrease (M : gmap elem Z) (F : elem -> elem -> Prop) :
  DSF F (dom M) ->
  id_bounded M F ->
  forall w z, rtc F w z -> forall iw iz, M !! w = Some iw -> M !! z = Some iz -> w <> z -> (iz < iw)%Z.
Proof.
  intros Hdsf Hid w z Hpath.
  induction Hpath as [w | w w' z HF Hpath IH]; intros iw iz Hiw Hiz Hne.
  - contradiction.
  - destruct Hdsf as [[Hconf'] _ _].
    destruct (Hconf' w w' HF) as [_ Hw'd].
    apply elem_of_dom in Hw'd as [iw' Hiw'].
    destruct (decide (w' = z)) as [->|Hne'].
    + exact (Hid w z iw iz HF Hiw Hiz).
    + specialize (IH iw' iz Hiw' Hiz Hne').
      pose proof (Hid w w' iw iw' HF Hiw Hiw') as Hstep.
      lia.
Qed.

(* The generalized edge-addition lemma [union_proof] actually needs:
   unlike [UnionFind03Link.is_dsf_link], this does NOT require the new
   edge's target [y'] to currently be a root — only that [y']'s id is
   strictly below [a]'s (exactly the [x.id > y.id] branch guard). This
   matters because [y'] is a STALE [findc]-time snapshot: nothing
   re-checks its root-status right before the CAS that installs the edge,
   so a concurrent [union] could in principle have already merged [y']
   away by then. Soundness (no cycle, [Defined Repr] still holds) comes
   from [id_bounded] instead: if [y']'s current representative [ry] were
   ever equal to [a], the (necessarily nonempty, since [y' ≠ a]) path
   [y' ->* a] would force [id a < id y'] via [path_id_decrease],
   contradicting the branch guard [id y' < id a] directly — so [ry ≠ a],
   and [w]'s new representative (for any [w] that used to route to [a])
   is simply [ry] itself, reached via [w ->* a -> y' ->* ry]. *)

Lemma dsf_link_general (M : gmap elem Z) (F : elem -> elem -> Prop) (a y' : elem) (ia iy : Z) :
  DSF F (dom M) ->
  id_bounded M F ->
  M !! a = Some ia ->
  M !! y' = Some iy ->
  Root F a ->
  (iy < ia)%Z ->
  a <> y' ->
  DSF (link F a y') (dom M) /\ id_bounded M (link F a y').
Proof.
  intros Hdsf Hid HMa HMy HRoota Hlt Hne.
  assert (HaD : a ∈ dom M) by (eapply elem_of_dom_2; eauto).
  assert (HyD : y' ∈ dom M) by (eapply elem_of_dom_2; eauto).
  pose proof (dsf_confined F) as [Hconf'].
  pose proof (dsf_defined F) as [Hdef].
  split.
  - constructor.
    + constructor. intros w z Hlink. destruct Hlink as [HF|[-> ->]].
      * exact (Hconf' w z HF).
      * split; assumption.
    + eapply functional_link; eauto.
    + constructor. intros w.
      destruct (Hdef w) as [r Hr].
      destruct (decide (r = a)) as [->|Hra].
      * destruct (Hdef y') as [ry Hry].
        destruct Hry as [Hpathyry Hrootry].
        destruct Hr as [Hpathwa _].
        assert (Hryne : ry <> a).
        { intros Heqrya.
          assert (Hneq : y' <> a) by (intros Heq; apply Hne; symmetry; exact Heq).
          rewrite Heqrya in Hpathyry.
          pose proof (path_id_decrease M F Hdsf Hid y' a Hpathyry iy ia HMy HMa Hneq) as Hgt.
          lia. }
        exists ry.
        assert (Hpathwa' : rtc (link F a y') w a).
        { eapply rtc_subrel; [|exact Hpathwa]. intros x0 y0 HFxy. left. exact HFxy. }
        assert (Hpathwy : rtc (link F a y') w y').
        { eapply rtc_r; [exact Hpathwa' | exact (link_appears F a y')]. }
        assert (Hpathyry' : rtc (link F a y') y' ry).
        { eapply rtc_subrel; [|exact Hpathyry]. intros x0 y0 HFxy. left. exact HFxy. }
        assert (Hpathwry : rtc (link F a y') w ry) by (eapply rtc_trans; eauto).
        assert (Hrootry' : Root (link F a y') ry).
        { apply is_root_link; [exact Hrootry | exact (not_eq_sym Hryne)]. }
        exact (Build_Repr _ w ry Hpathwry Hrootry').
      * exists r.
        apply is_repr_link_2; [exact Hr | exact Hra].
  - intros w z iw iz Hlink Hiw Hiz.
    destruct Hlink as [HF|[-> ->]].
    + exact (Hid w z iw iz HF Hiw Hiz).
    + simplify_eq. lia.
Qed.

(* [link]'s only effect on root-ness, for any vertex [w] other than the
   one it installs the new edge at, is none at all: [link F a y']'s edges
   are exactly [F]'s edges plus [a -> y'], so a vertex [w ≠ a] has no new
   outgoing edge and loses none of its old ones. *)

Lemma root_link_ne (F : elem -> elem -> Prop) (a y' w : elem) :
  w ≠ a -> (Root F w <-> Root (link F a y') w).
Proof.
  intros Hne. split.
  - intros Hroot. apply is_root_link; [exact Hroot | exact (not_eq_sym Hne)].
  - intros [Hroot2]. constructor. intros y0 HF0. apply (Hroot2 y0). left. exact HF0.
Qed.

(* Consequently, [uf_inv]'s big [∗ map] of [vertex_own]s over a map that
   does not (yet) contain [a] is unaffected by widening its indexing
   graph via [link a y']: this is what lets [union_proof] re-close the
   invariant's untouched vertices after registering [a]'s own tag flip
   (the ONLY entry that actually needs [link]'s new edge). *)

Lemma vertex_own_widen_link γ γc γn (F0 : elem -> elem -> Prop) (a y' : elem) (M' : gmap elem Z) :
  M' !! a = None ->
  ([∗ map] w ↦ i ∈ M', vertex_own γ γc γn F0 w i) -∗
  [∗ map] w ↦ i ∈ M', vertex_own γ γc γn (link F0 a y') w i.
Proof.
  iIntros (Ha) "HM".
  iApply (big_sepM_impl with "HM").
  iIntros "!>" (w i Hw) "Hvo".
  iDestruct "Hvo" as (li lc rc ci) "(Hlocs & Hlc & Hrc & %Hb & %HF & Htok)".
  iExists li, lc, rc, ci. iFrame "Hlocs Hlc Hrc Htok".
  iSplit; first done.
  iPureIntro.
  assert (Hne : w ≠ a) by (intros ->; congruence).
  destruct ci as [|b].
  - apply (root_link_ne F0 a y' w Hne). exact HF.
  - intros Hroot. apply HF. apply (root_link_ne F0 a y' w Hne). exact Hroot.
Qed.

(* Proof outline for the internal (2-arg, recursive) [union]:
   1. Call [findc] on both [x] and [y] (via [imp_bindings_cons] /
      [imp_bindings_singleton], mirroring [make_proof]'s two-binding
      pattern), obtaining vertices [a], [y'] with ids [i'], [j'].
   2. [x == y]: physical equality on the (non-inline) records [a]/[y'],
      via the new [imp_EOpPhysEq_record] rule (VRecord physical equality
      needs to consult the store — at least one operand must be a
      mutable block, which [vertex]'s [isBlockP _ Mut] provides). True
      branch returns [None]; false branch gives [a ≠ y' : record].
   3. [assert (x.id <> y.id)]: this is a REAL proof obligation. From
      [a ≠ y'] (as *records*, i.e. distinct heap locations) we derive
      [i' ≠ j'] via the id-uniqueness ghost map [γn]: opening [uf_inv]
      (through a bare fancy update [|={⊤}=> ...], since [iInv] cannot
      mask-change around a non-atomic sequence of reasoning — only a
      single physical/atomic step — so the invariant access must be
      packaged as its own self-contained fupd and then [iMod]'d into
      the [imp] proof via the [elim_modal_fupd_imp] instance), looking
      up both [a] and [y'] in [M] (justified distinct via [a ≠ y']),
      extracting both [i' ↪[γn] ()] and [j' ↪[γn] ()]: if [i' = j']
      these coincide and [dfrac_full_exclusive] is contradictory,
      otherwise [i' ≠ j']. Reading [x.id]/[y.id] themselves goes through
      the new [imp_ERecordAccess_pers] rule (record-field access through
      a persistent/discardable points-to, since [vertex]'s [id] field is
      immutable and shared via [DfracDiscarded] — the existing
      [imp_ERecordAccess]/[imp_ERecordAccess2] rules need a fractional
      [ownBlock] and do not apply here). The final numeric step bridges
      the machine-level [int.eq] back to the [Z]-level [i' ≠ j'] via
      [eq_repr_repr], which needs [representable i']/[representable j']
      — obtained for free from [uf_inv]'s [Hrep] invariant alongside the
      id-uniqueness lookup.
   4. [if x.id > y.id then <CAS Link{parent=y'} into x'.content; Some v>
      else union x y] and the symmetric case for [y.id > x.id]: atomically
      read the [Root] content, allocate [Link{parent=...}] via
      [imp_EInline], CAS it in via the polymorphic [compare_and_set_spec]
      (through [val] directly — see [imp_wand_observe]'s use below — since
      the "seen"/"new" arguments carry different tags), and on success
      register the new content record as [CLink i'] (resp. [CLink j'])
      in [γc] — needs the parent's id strictly below the bound, i.e.
      [j' < i'] (resp. [i' < j']), from the branch guard.
   5. The graph [F] (see [uf_inv]) only changes at step 4's successful
      CAS, via [UnionFind03Link.link] — literally the same primitive the
      sequential proof's own [Inv_link] uses. [None] (step 2's true
      branch) needs [is_equiv F x y] for the *current* [F], derived by
      bridging each side's [findc]-time snapshot ([Repr Fx x a]/
      [Repr Fy y y']) forward to the current instant via [rtc_subrel] (
      [F] only grows, and a vertex's own outgoing edge is permanent once
      installed) together with [a]/[y']'s current root-ness (freshly
      re-observed via [vertex_own]'s tag correlation, right there in this
      proof — not reused from the stale snapshot). *)

Lemma union_proof γ γc γn η :
  ▷ in_env "union" (λ union, □ iSpec τ[elem; elem] union (union_spec γ γc γn)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn)) η -∗
  in_env "cas"
    (λ cas, □ ∀ A `{Encode A}, iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __union_fun))))
    {{ λ c, □ iSpec τ[elem; elem] c (union_spec γ γc γn) }}.
Proof.
  iIntros "#IUnion #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold union_spec.
  iIntros (i j) "#Hinv #Hx #Hy".
  iApply imp_please; iNext.
  unfold __union_fun.
  simpl.
  rewrite {1}/deco.
  iApply imp_ELet.
  { iApply (imp_bindings_cons (A:=elem) (λ z : elem, ∃ i', vertex γ z i' ∗ ⌜(i' ≤ i)%Z⌝ ∗ ∃ Dx Fx, ⌜DSF Fx Dx⌝ ∗ ⌜x ∈ Dx⌝ ∗ ⌜Repr Fx x z⌝)%I with "[] [] []").
    { rewrite {1}/deco.
      iApply (imp_EApp τ[elem]).
      { imp_path. }
      { imp_path. }
      simpl. iIntros (z) "-> %m Hm". iNext.
      unfold findc_spec.
      iSpecialize ("Hm" $! i with "Hinv Hx").
      iApply "Hm". }
    { iIntros (a) "_". iPureIntro. apply pat_PVar.
      instantiate (1 := λ (w:elem)(l:env), l=[("x",#w)]). reflexivity. }
    { iApply (imp_bindings_singleton (A:=elem) (λ z:elem, ∃ j', vertex γ z j' ∗ ⌜(j'≤j)%Z⌝ ∗ ∃ Dy Fy, ⌜DSF Fy Dy⌝ ∗ ⌜y ∈ Dy⌝ ∗ ⌜Repr Fy y z⌝)%I with "[] [] []").
      { rewrite {1}/deco.
        iApply (imp_EApp τ[elem]).
        { imp_path. }
        { imp_path. }
        simpl. iIntros (z) "-> %m Hm". iNext.
        unfold findc_spec.
        iSpecialize ("Hm" $! j with "Hinv Hy").
        iApply "Hm". }
      { iIntros (a) "_". iPureIntro. apply pat_PVar.
        instantiate (1 := λ (w:val)(l:env), l=[("y",w)]). reflexivity. }
      { iIntros (a δ) "HΦ1 ->".
        instantiate (1 := (λ δ:env, ∃ (y':elem)(j':Z), ⌜δ=[("y",#y')]⌝ ∗ vertex γ y' j' ∗ ⌜(j'≤j)%Z⌝ ∗
          ∃ Dy Fy, ⌜DSF Fy Dy⌝ ∗ ⌜y ∈ Dy⌝ ∗ ⌜Repr Fy y y'⌝)%I).
        iDestruct "HΦ1" as (j') "(Hv & %Hj' & %Dy & %Fy & %HdsfFy & %HyDy & %HReprY)".
        iExists a, j'. iFrame.
        iPureIntro. split; [done|]. split; [exact Hj'|]. exists Dy, Fy. auto. } } }
  iIntros (δ) "(%a & %η' & %δ' & -> & (%i' & Hxv & %Hi' & %Dx & %Fx & %HdsfFx & %HxDx & %HReprXa) & %HP & (%y' & %j' & -> & Hyv & %Hj' & %Dy & %Fy & %HdsfFy & %HyDy & %HReprYy'))".
  subst η'.
  simpl.
  iDestruct "Hxv" as (lai lac) "(#Hafrag & #Hxlocs & #HaP & #Hali)".
  iDestruct "Hyv" as (lyi lyc) "(#Hyfrag & #Hylocs & #HyP & #Hyli)".
  rewrite {1}/deco.
  iApply (imp_EIfThenElse _ _ _ _ (λ b : bool, if b then ⌜a = y'⌝ else ⌜a ≠ y'⌝)%I).
  { iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I (λ l : record, ⌜l = y'⌝)%I _ Mut Mut).
    { by left. }
    { iApply (imp_EPath (A:=record) a).
      { reflexivity. }
      iSplit; [done|].
      iDestruct "HaP" as "$". }
    { iApply (imp_EPath (A:=record) y').
      { reflexivity. }
      iSplit; [done|].
      iDestruct "HyP" as "$". }
    { iIntros "!>" (l1 l2) "-> ->".
      destruct (locations.eqb_spec a y') as [->|Hneq].
      - done.
      - done. } }
  iIntros ([|]) "%Heq".
  { iApply (imp_wand _ _ _ _ _ (λ ov : option val,
      match ov with
      | None => ⌜same_class x y⌝
      | Some r => ∃ z rc, (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc ↪[γc]□ CRoot r
      end)%I with "[]").
    { iApply imp_EConstant. }
    iIntros (v) "->".
    simpl.
    iPureIntro.
    exists a.
    split.
    { apply rtc_once. exists Dx, Fx. eauto. }
    { subst a. apply rtc_once. exists Dy, Fy. eauto. } }
  iAssert (|={⊤}=> ⌜i' ≠ j' ∧ representable i' ∧ representable j'⌝)%I as "Hfupd".
  {
    iInv "Hinv" as "H" "Hclose".
    iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
    iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMa.
    iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
    rewrite (big_sepM_delete _ M a i'); last exact HMa.
    iDestruct "HM" as "[Hvoa HM]".
    assert (HMy' : delete a M !! y' = Some j').
    { rewrite lookup_delete_ne; [exact HMy | exact Heq]. }
    rewrite (big_sepM_delete _ (delete a M) y' j'); last exact HMy'.
    iDestruct "HM" as "[Hvoy HM]".
    assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
    assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
    iDestruct "Hvoa" as (lia lca rca cia) "(#Hlocsa & Hlca & >#Hrca & >%Hbounda & >%HFa & Htoka)".
    iDestruct "Hvoy" as (liy lcy rcy ciy) "(#Hlocsy & Hlcy & >#Hrcy & >%Hboundy & >%HFy2 & Htoky)".
    destruct (decide (i' = j')) as [->|Hij].
    - iDestruct "Htoka" as ">Htoka".
      iDestruct "Htoky" as ">Htoky".
      iCombine "Htoka Htoky" gives %Hbad.
      destruct Hbad as [Hbad _]. exfalso.
      eapply dfrac_full_exclusive. exact Hbad.
    - iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlca Htoka Hlcy Htoky]") as "_".
      { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
        iSplitR; first done.
        iSplitR; first done.
        iSplitL "HM Hlca Htoka Hlcy Htoky".
        { rewrite (big_sepM_delete _ M a i'); last exact HMa.
          iSplitL "Hlca Htoka".
          { iExists lia, lca, rca, cia. iFrame "Hlocsa Hlca Hrca Htoka". iSplit; [iPureIntro; exact Hbounda|iPureIntro; exact HFa]. }
          rewrite (big_sepM_delete _ (delete a M) y' j'); last exact HMy'.
          iSplitL "Hlcy Htoky".
          { iExists liy, lcy, rcy, ciy. iFrame "Hlocsy Hlcy Hrcy Htoky". iSplit; [iPureIntro; exact Hboundy|iPureIntro; exact HFy2]. }
          iApply "HM". }
        iApply "HC". }
      iModIntro. iPureIntro. split; [exact Hij|split; [exact (Hrep a i' HMa)|exact (Hrep y' j' HMy)]].
  }
  iMod "Hfupd" as "%Hij".
  destruct Hij as (Hij & Hrepi & Hrepj).
  rewrite {1}/deco.
  imp_match unit with "[]".
  { iApply (imp_EAssert (R:=⌜i' ≠ j'⌝%I)).
    iSplit; first done.
    rewrite {1}/deco.
    iApply (imp_EOpNe (A1:=Z) (A2:=Z) _ _ _ (λ n:Z,⌜n=i'⌝)%I (λ n:Z,⌜n=j'⌝)%I).
    { rewrite {1}/deco.
      assert (Hlc0a : @lookup_total Z loc (list loc)
            (@list_z.listz_lookup_total loc locations.inhabited_loc)
            0%Z [lai; lac] = lai) by (vm_compute; reflexivity).
      iApply (imp_ERecordAccess_pers _ _ [lai;lac] _ i').
      { by vm_compute. }
      { iExact "Hxlocs". }
      { imp_path. }
      { rewrite Hlc0a. iExact "Hali". }
      { rewrite Hlc0a. iIntros "!> _". done. } }
    { rewrite {1}/deco.
      assert (Hlc0b : @lookup_total Z loc (list loc)
            (@list_z.listz_lookup_total loc locations.inhabited_loc)
            0%Z [lyi; lyc] = lyi) by (vm_compute; reflexivity).
      iApply (imp_ERecordAccess_pers _ _ [lyi;lyc] _ j').
      { by vm_compute. }
      { iExact "Hylocs". }
      { imp_path. }
      { rewrite Hlc0b. iExact "Hyli". }
      { rewrite Hlc0b. iIntros "!> _". done. } }
    { iIntros "!>" (v1 v2) "-> ->".
      rewrite /ne_val /eq_val /=.
      iApply imp_ret; first reflexivity.
      iSplit; [iPureIntro|done].
      rewrite eq_repr_repr; try assumption.
      destruct (Z.eqb_spec i' j') as [Habs|_]; [exfalso; exact (Hij Habs)|done]. } }
  iIntros "%HR".
  destruct a0. simpl.
  next_branch.
  iApply (imp_EIfThenElse _ _ _ _ (λ b : bool, ⌜b = (i' >? j')%Z⌝)%I).
  { iApply (imp_EOpGt_Z _ _ _ i' j').
    { exact Hrepi. }
    { exact Hrepj. }
    { assert (Hlc0a : @lookup_total Z loc (list loc)
          (@list_z.listz_lookup_total loc locations.inhabited_loc)
          0%Z [lai; lac] = lai) by (vm_compute; reflexivity).
      iApply (imp_ERecordAccess_pers _ _ [lai;lac] _ i').
      { by vm_compute. }
      { iExact "Hxlocs". }
      { imp_path. }
      { rewrite Hlc0a. iExact "Hali". }
      { rewrite Hlc0a. iIntros "!> _". done. } }
    { assert (Hlc0b : @lookup_total Z loc (list loc)
          (@list_z.listz_lookup_total loc locations.inhabited_loc)
          0%Z [lyi; lyc] = lyi) by (vm_compute; reflexivity).
      iApply (imp_ERecordAccess_pers _ _ [lyi;lyc] _ j').
      { by vm_compute. }
      { iExact "Hylocs". }
      { imp_path. }
      { rewrite Hlc0b. iExact "Hyli". }
      { rewrite Hlc0b. iIntros "!> _". done. } } }
  iIntros ([|]) "%Hcmp2".
  { (* [let cx = x.content in match cx with | Root {v} -> if cas[...] cx
       (Link{parent=y}) then Some v else union x y | _ -> union x y]. This
       mirrors [update_proof]'s own atomic-content-read + match, replacing
       the [Root{value=f v}] installation with [Link{parent=y}]. *)
    iApply (imp_ELet_var (λ v : val, ∃ rc ci,
        ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ i')%Z⌝ ∗ isBlockP rc Mut ∗
        match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I).
    { rewrite {1}/deco.
      iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lai; lac] a with "Hxlocs [] []").
      { by vm_compute. }
      { imp_path. }
      assert (Hlc1 : @lookup_total Z loc (list loc)
          (@list_z.listz_lookup_total loc locations.inhabited_loc)
          1%Z [lai; lac] = lac) by (vm_compute; reflexivity).
      rewrite Hlc1.
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
      iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMz.
      rewrite (big_sepM_delete _ M a i'); last exact HMz.
      iDestruct "HM" as "[Hvo HM]".
      assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
      assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
      iDestruct "Hvo" as (li' lc' rc ci) "(#Hzlocs' & Hlc & >#Hrc & >%Hbound & >%HFa & Htok)".
      iAssert (▷ ⌜[lai; lac] = [li'; lc']⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hzlocs' Hxlocs"). }
      simplify_eq.
      iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
      rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
      iDestruct "HC" as "[Hco HC]".
      iModIntro.
      iExists (cval ci rc).
      iSplitL "Hlc"; first by iFrame.
      iIntros "!> Hlc".
      iAssert (isBlockP rc Mut ∗
        match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I
        as "#[HrcP Hpayload]".
      { destruct ci as [v0|b].
        { iDestruct "Hco" as (lv0) "(#Hlocs0 & #Htag & _)".
          iSplit; [iExact "Htag"|]. eauto. }
        { iDestruct "Hco" as (lp y0 j0) "(_ & #Htag & _)".
          iSplit; [iExact "Htag"|]. done. } }
      iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hco Htok]") as "_".
      { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
        iSplitR; first done.
        iSplitR; first done.
        iSplitL "HM Hlc Htok".
        { rewrite (big_sepM_delete _ M a i'); last exact HMz.
          iSplitL "Hlc Htok".
          { iExists li', lc', rc, ci. iFrame "Hxlocs Hlc Hrc Htok". iSplit; [done|iPureIntro; exact HFa]. }
          iApply "HM". }
        rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
        iFrame "Hco HC". }
      iModIntro.
      iExists rc, ci.
      iFrame "Hrc HrcP Hpayload".
      iSplit; iPureIntro; [done | exact Hbound]. }
    iIntros (cxv) "(%rc & %ci & -> & #Hrc & %Hbound & #HrcP & #Hpayload)".
    (* Re-match on the already-loaded [cx]: a plain path lookup, closed
       automatically by [imp_match]'s own scrutinee handling. *)
    imp_match val with "[]".
    destruct ci as [v0|b]; simpl.
    { iDestruct "Hpayload" as (lv) "#Hrclocs".
      next_branch.
      iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
      iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
      rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
      iDestruct "HC" as "[Hco HC]".
      iDestruct "Hco" as (lv') "(#Hlocs' & _ & Hlv)".
      iAssert (▷ ⌜[lv] = [lv']⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hlocs' Hrclocs"). }
      simplify_eq.
      iModIntro.
      iExists v0.
      iSplitL "Hlv"; first by iFrame.
      iIntros "!> Hlv".
      iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlv]") as "_".
      { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth HM". iSplitR; first done.
        iSplitR; first done.
        iSplitR; first done.
        rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
        iSplitL "Hlv".
        { iExists lv'. iFrame "Hlocs' HrcP Hlv". }
        iApply "HC". }
      iModIntro.
      rewrite {1}/deco.
      iApply (imp_EIfThenElse _ _ _ _ (λ _ : bool, True)%I).
      rewrite {1}/deco.
      (* The CAS call is instantiated at [A := val] with the identity
         [Encode_val] instance (not [root_enc]/[link_enc]): unlike
         [update_proof] — which installs another [Root]-tagged record and
         so can keep both the "seen" and "new" CAS arguments at the same
         [Encode record] instance — here the "seen" value ([cx], Root-
         tagged) and the "new" value ([Link{parent=y}], Link-tagged) need
         *different* tags, which a single [A := record, Henc] instantiation
         cannot express ([compare_and_set_spec]'s single [Encode A] is
         shared by both positions). Going through [val] directly (with the
         trivial identity encoding) sidesteps this. *)
      iApply (imp_EApp (@type_nel.Tcons loc _ (@type_nel.Tcons val Encode_val (@type_nel.Tbase val Encode_val)))).
      { iDestruct "Hcas" as (casv Hcasv) "#Hcasspec".
        iApply (imp_EPath (A:=val) casv).
        { exact Hcasv. }
        iApply ("Hcasspec" $! val Encode_val). }
      { rewrite {1}/deco.
        iApply (imp_EAtomicLoc (Φ := λ l : loc, ⌜l = lac⌝)%I 1%Z a [lai; lac]).
        { by vm_compute. }
        { iNext. iExact "Hxlocs". }
        { imp_path. }
        assert (Hlc1' : @lookup_total Z loc (list loc)
            (@list_z.listz_lookup_total loc locations.inhabited_loc)
            1%Z [lai; lac] = lac) by (vm_compute; reflexivity).
        rewrite Hlc1'.
        iNext. done. }
      { imp_path. }
      (* The "new" argument: allocate [Link{parent=y}] (as an [elem]) and
         view its record as a [val] via [imp_wand_observe], the [Observe]-
         crossing analogue of [imp_wand] — bridging [imp_EInline]'s natural
         [elem]-typed conclusion (pinned to the ["Link"]-tag instance
         [encode_record "Link"], which [imp_EInline] itself uses internally,
         hence must be supplied explicitly) up to the [val]-typed slot the
         [A := val] CAS call expects. *)
      iApply (imp_wand_observe (A:=elem) (H:=@observe_encode elem (encode_record "Link"))
        _ _ _ _ _ (fun w : val => ∃ r' : elem, ⌜w = VInline "Link" r'⌝ ∗
          ∃ lv0 : loc, isBlockLocs r' [lv0] ∗ isBlock r' (DfracOwn 1) Mut ∗ lv0 ↦ #y')%I
        with "[] []").
      { rewrite {1}/deco.
        iApply (imp_EInline (τ:=τ[elem]) (λ w : elem, ⌜w = y'⌝)%I).
        { simpl. lia. }
        iApply (imp_evals_singleton (A:=elem)).
        imp_path.
        done. }
      { iIntros (r) "H".
        iDestruct "H" as (x0) "H".
        iEval (simpl) in "H".
        iDestruct "H" as "[Hown %Heq4]".
        simplify_eq.
        iDestruct "Hown" as (ls) "(#Hlocs2 & Htag2 & Hxs2)".
        iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs2") as (lv2) "[-> Hlv2]".
        iEval (rewrite list_z.singleton_unfold) in "Hlocs2".
        iExists (VInline "Link" r).
        iSplit; first done.
        iExists r.
        iSplit; first done.
        iExists lv2.
        iFrame "Hlocs2 Htag2 Hlv2". }
      iIntros (x0).
      iIntros (rc2) "->".
      iIntros (lc2) "->".
      iIntros "Hown".
      iIntros (m2) "Hm2".
      iNext.
      iApply "Hm2".
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M2 C2 N2 F2) "(>Hauth & >Hcauth & >Hnauth & >%Hrep2 & >%HdsfF2 & >%HidF2 & HM & HC)".
      iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMa2.
      rewrite (big_sepM_delete _ M2 a i'); last exact HMa2.
      iDestruct "HM" as "[Hvo HM]".
      assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
      assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
      iDestruct "Hvo" as (li'' lc'' rc0 ci0) "(#Hzlocs'' & Hlc & >#Hrc0 & >%Hbound0 & >%HFa2 & Htok0)".
      iAssert (▷ ⌜[lai; lac] = [li''; lc'']⌝)%I with "[]" as ">%Heql2".
      { iNext. iApply (isBlockLocs_valid with "Hzlocs'' Hxlocs"). }
      simplify_eq.
      iDestruct (ghost_map_lookup with "Hcauth Hrc0") as %HCrc0.
      rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
      iDestruct "HC" as "[Hco0 HC]".
      iAssert (▷ isBlockP rc0 Mut)%I as "#Hrc0P".
      { iNext.
        destruct ci0 as [v0'|b0].
        { iDestruct "Hco0" as (lv0) "(_ & $ & _)". }
        { iDestruct "Hco0" as (lp0 y0 j0) "(_ & $ & _)". } }
      set (c0 := match ci0 with CRoot _ => "Root" | CLink _ => "Link" end).
      assert (Hcval0 : cval ci0 rc0 = VInline c0 rc0) by (destruct ci0; reflexivity).
      iModIntro.
      iExists c0, "Root", rc0, rc, DfracDiscarded, DfracDiscarded, Mut.
      iSplitR; first done.
      rewrite <- Hcval0.
      iFrame "Hlc Hrc0P HrcP".
      iNext.
      iIntros "Hlc' _ _".
      (* [rc0 = rc]: the CAS succeeded, installing the freshly-allocated
         [Link{parent=y'}] record ([r']) as [x]'s content. Registering it
         in [γc] as [CLink i'] needs [r']'s freshness (it cannot already be
         registered, since [imp_EInline] owns its field exclusively — ruled
         out by the same [dfrac_full_exclusive] case-split [update_proof]
         performs for its own freshly-allocated [Root] record, see
         [update_proof]'s handling of [rc3]) and [j' < i'] (from the
         [x.id > y.id] branch guard, [Hcmp2]). Soundness of extending the
         graph via [link] (rather than requiring [y']'s root-status right
         now, which nothing re-checks) comes from [dsf_link_general]'s
         id-bound argument — see its comment. *)
      destruct (locations.eqb_spec rc0 rc) as [Heqrc|Hnerc].
      { subst rc0.
        iDestruct (ghost_map_elem_agree with "Hrc0 Hrc") as %Heqci0.
        subst ci0.
        iDestruct "Hco0" as (lv0) "(#Hlv0locs & _ & Hlv0)".
        iDestruct "Hown" as (r') "[-> Hownfoot]".
        iDestruct "Hownfoot" as (lv3) "(#Hlv3locs & Htag3 & Hlv3)".
        iAssert (▷ ⌜[lv'] = [lv0]⌝)%I with "[]" as ">%Heqlv0".
        { iNext. iApply (isBlockLocs_valid with "Hlv0locs Hlocs'"). }
        assert (Heqlv0' : lv0 = lv') by (injection Heqlv0; done).
        subst lv0.
        destruct (decide (r' = rc)) as [->|Hne].
        { iAssert (▷ ⌜[lv3] = [lv']⌝)%I with "[]" as ">%Heqlv".
          { iNext. iApply (isBlockLocs_valid with "Hlv0locs Hlv3locs"). }
          assert (Heqlv' : lv3 = lv') by (injection Heqlv; done).
          subst lv3.
          iCombine "Hlv0 Hlv3" gives %Hbad.
          destruct Hbad as [Hbad _].
          exfalso. eapply dfrac_full_exclusive. exact Hbad. }
        destruct (C2 !! r') as [ci1|] eqn:HCr'.
        { assert (HCr'del : delete rc C2 !! r' = Some ci1) by (rewrite lookup_delete_ne; done).
          iDestruct (big_sepM_lookup with "HC") as "Hco1"; first exact HCr'del.
          destruct ci1 as [v2|b1]; simpl.
          { iDestruct "Hco1" as (lv1) "(#Hlocs1 & _ & Hlv1)".
            iAssert (▷ ⌜[lv3] = [lv1]⌝)%I with "[]" as ">%Heqlv1".
            { iNext. iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs"). }
            assert (Heqlv1' : lv1 = lv3) by (injection Heqlv1; done).
            subst lv1.
            iCombine "Hlv1 Hlv3" gives %Hbad.
            destruct Hbad as [Hbad _].
            exfalso. eapply dfrac_full_exclusive. exact Hbad. }
          iDestruct "Hco1" as (lp1 y1 j1) "(#Hlocs1 & _ & Hlp1 & _)".
          iAssert (▷ ⌜[lv3] = [lp1]⌝)%I with "[]" as ">%Heqlp1".
          { iNext. iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs"). }
          assert (Heqlp1' : lp1 = lv3) by (injection Heqlp1; done).
          subst lp1.
          iCombine "Hlv3 Hlp1" gives %Hbad.
          destruct Hbad as [Hbad _].
          exfalso. eapply dfrac_full_exclusive. exact Hbad. }
        iDestruct "Htag3" as (ls3) "Htag3".
        iMod (gen_heap.pointsto_persist with "Htag3") as "Htag3".
        iAssert (isBlockP r' Mut) with "[Htag3]" as "#Hr'P".
        { iExists ls3. iFrame. }
        iMod (ghost_map_insert r' (CLink i') with "Hcauth") as "[Hcauth Hr'frag]"; first exact HCr'.
        iMod (ghost_map_elem_persist with "Hr'frag") as "#Hr'frag".
        iAssert (vertex γ y' j') as "Hy'vertex".
        { iExists lyi, lyc. iFrame "Hyfrag Hylocs HyP Hyli". }
        assert (Hlt : (j' < i')%Z).
        { assert (Hle : (i' <= j')%Z -> False).
          { intros Hle. apply Hij. lia. }
          pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
        assert (HRoota2 : Root F2 a) by exact HFa2.
        iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy2.
        pose proof (dsf_link_general M2 F2 a y' i' j' HdsfF2 HidF2 HMa2 HMy2 HRoota2 Hlt Heq) as [HdsfF2' HidF2'].
        iAssert ([∗ map] w ↦ i0 ∈ delete a M2, vertex_own γ γc γn (link F2 a y') w i0)%I with "[HM]" as "HM".
        { iApply (vertex_own_widen_link with "HM"). rewrite lookup_delete_eq. done. }
        iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hlv0 Hlv3 Htok0 Hy'vertex]") as "_".
        { iNext.
          iExists M2, (<[r':=CLink i']> C2), N2, (link F2 a y').
          iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
          iSplitR; first (iPureIntro; exact HdsfF2').
          iSplitR; first (iPureIntro; exact HidF2').
          iSplitL "HM Hlc' Htok0".
          { rewrite (big_sepM_delete _ M2 a i'); last exact HMa2.
            iSplitL "Hlc' Htok0".
            { iExists li'', lc'', r', (CLink i').
              iFrame "Hzlocs'' Hlc' Hr'frag Htok0".
              iSplit.
              { iPureIntro. intros b0 Hb0. injection Hb0 as ->. lia. }
              iPureIntro. intros [Hr]. eapply (Hr y'). right. done. }
            iApply "HM". }
          rewrite big_sepM_insert; last exact HCr'.
          iSplitL "Hlv3 Hy'vertex".
          { simpl. iExists lv3, y', j'. iFrame "Hlv3locs Hr'P Hlv3 Hy'vertex". iPureIntro. exact Hlt. }
          rewrite (big_sepM_delete _ C2 rc (CRoot v0)); last exact HCrc0.
          iSplitL "Hlv0".
          { simpl. iExists lv'. iFrame "Hlv0locs HrcP Hlv0". }
          iApply "HC". }
        iModIntro.
        done. }
      { iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hco0 Htok0]") as "_".
        { iNext.
          iExists M2, C2, N2, F2.
          iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iSplitL "HM Hlc' Htok0".
          { rewrite (big_sepM_delete _ M2 a i'); last exact HMa2.
            iSplitL "Hlc' Htok0".
            { iExists li'', lc'', rc0, ci0.
              iFrame "Hzlocs'' Hlc' Hrc0 Htok0". iSplit; [done|iPureIntro; exact HFa2]. }
            iApply "HM". }
          rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
          iFrame "Hco0 HC". }
        iModIntro.
        done. }
      iIntros ([|]) "_".
      { rewrite {1}/deco.
        iApply (imp_wand _ _ _ _ _ (λ ov : option val,
          match ov with
          | None => ⌜same_class x y⌝
          | Some r => ∃ z rc', (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc' ↪[γc]□ CRoot r
          end)%I with "[]").
        { iApply imp_EData.
          { iApply (imp_evals_singleton (A:=val)). imp_path. }
          { iIntros (v) "->".
            instantiate (1 := (fun ov : option val => match ov with
              | None => ⌜same_class x y⌝
              | Some r => ∃ z rc', (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc' ↪[γc]□ CRoot r
              end)%I).
            simpl.
            iExists a, rc. iFrame "Hrc". iLeft. iPureIntro. apply rtc_once. exists Dx, Fx. eauto. } }
        iIntros (v) "$". }
      { rewrite {1}/deco.
        iApply (imp_EApp τ[elem; elem]).
        { imp_path. }
        { imp_path. }
        { imp_path. }
        iIntros (xv yv) "-> -> %m3 Hm3".
        iNext.
        unfold union_spec.
        iAssert (vertex γ a i') as "Havertex".
        { iExists lai, lac. iFrame "Hafrag Hxlocs HaP Hali". }
        iAssert (vertex γ y' j') as "Hy'vertex2".
        { iExists lyi, lyc. iFrame "Hyfrag Hylocs HyP Hyli". }
        iSpecialize ("Hm3" $! i' j' with "Hinv Havertex Hy'vertex2").
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        destruct ov as [r|].
        { iDestruct "Hov" as (z rc') "[Hzdisj Hrcfrag]".
          iDestruct "Hzdisj" as "[%Hz|%Hz]".
          { iExists z, rc'. iFrame "Hrcfrag". iLeft. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dx, Fx. eauto. }
          { iExists z, rc'. iFrame "Hrcfrag". iRight. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dy, Fy. eauto. } }
        { iDestruct "Hov" as "%Hsc".
          destruct Hsc as (z & Hza & Hzy).
          iPureIntro. exists z.
          split.
          { eapply rtc_l; [|exact Hza]. exists Dx, Fx. eauto. }
          { eapply rtc_l; [|exact Hzy]. exists Dy, Fy. eauto. } } } }
    { (* The [CLink] wildcard fallthrough: [x.content] raced ahead of us
         (already a [Link], not a [Root]) — retry via the outer recursive
         [union x y] call, mirroring [find_proof]'s own [CRoot]/[CLink]
         match handling. *)
      next_branch.
      next_branch.
      rewrite {1}/deco.
      iApply (imp_EApp τ[elem; elem]).
      { imp_path. }
      { imp_path. }
      { imp_path. }
      iIntros (xv yv) "-> -> %m3 Hm3".
      iNext.
      unfold union_spec.
      iAssert (vertex γ a i') as "Havertex".
      { iExists lai, lac. iFrame "Hafrag Hxlocs HaP Hali". }
      iAssert (vertex γ y' j') as "Hy'vertex2".
      { iExists lyi, lyc. iFrame "Hyfrag Hylocs HyP Hyli". }
      iSpecialize ("Hm3" $! i' j' with "Hinv Havertex Hy'vertex2").
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      destruct ov as [r|].
      { iDestruct "Hov" as (z rc') "[Hzdisj Hrcfrag]".
        iDestruct "Hzdisj" as "[%Hz|%Hz]".
        { iExists z, rc'. iFrame "Hrcfrag". iLeft. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dx, Fx. eauto. }
        { iExists z, rc'. iFrame "Hrcfrag". iRight. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dy, Fy. eauto. } }
      { iDestruct "Hov" as "%Hsc".
        destruct Hsc as (z & Hza & Hzy).
        iPureIntro. exists z.
        split.
        { eapply rtc_l; [|exact Hza]. exists Dx, Fx. eauto. }
        { eapply rtc_l; [|exact Hzy]. exists Dy, Fy. eauto. } } } }
  { (* [x.id <= y.id]: the symmetric CAS on [y.content], installing
       [Link{parent=x}] and (on success) registering it as [CLink j']
       (needs [i' < j'], from [Hcmp2] together with [Hij : i' ≠ j']). *)
    iApply (imp_ELet_var (λ v : val, ∃ rc ci,
        ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ j')%Z⌝ ∗ isBlockP rc Mut ∗
        match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I).
    { rewrite {1}/deco.
      iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lyi; lyc] y' with "Hylocs [] []").
      { by vm_compute. }
      { imp_path. }
      assert (Hlc1 : @lookup_total Z loc (list loc)
          (@list_z.listz_lookup_total loc locations.inhabited_loc)
          1%Z [lyi; lyc] = lyc) by (vm_compute; reflexivity).
      rewrite Hlc1.
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
      iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMz.
      rewrite (big_sepM_delete _ M y' j'); last exact HMz.
      iDestruct "HM" as "[Hvo HM]".
      assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
      assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
      iDestruct "Hvo" as (li' lc' rc ci) "(#Hzlocs' & Hlc & >#Hrc & >%Hbound & >%HFy & Htok)".
      iAssert (▷ ⌜[lyi; lyc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hzlocs' Hylocs"). }
      simplify_eq.
      iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
      rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
      iDestruct "HC" as "[Hco HC]".
      iModIntro.
      iExists (cval ci rc).
      iSplitL "Hlc"; first by iFrame.
      iIntros "!> Hlc".
      iAssert (isBlockP rc Mut ∗
        match ci with CRoot _ => ∃ lv : locations.loc, isBlockLocs rc [lv] | CLink _ => True end)%I
        as "#[HrcP Hpayload]".
      { destruct ci as [v0|b].
        { iDestruct "Hco" as (lv0) "(#Hlocs0 & #Htag & _)".
          iSplit; [iExact "Htag"|]. eauto. }
        { iDestruct "Hco" as (lp y0 j0) "(_ & #Htag & _)".
          iSplit; [iExact "Htag"|]. done. } }
      iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc Hco Htok]") as "_".
      { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
        iSplitR; first done.
        iSplitR; first done.
        iSplitL "HM Hlc Htok".
        { rewrite (big_sepM_delete _ M y' j'); last exact HMz.
          iSplitL "Hlc Htok".
          { iExists li', lc', rc, ci. iFrame "Hylocs Hlc Hrc Htok". iSplit; [done|iPureIntro; exact HFy]. }
          iApply "HM". }
        rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
        iFrame "Hco HC". }
      iModIntro.
      iExists rc, ci.
      iFrame "Hrc HrcP Hpayload".
      iSplit; iPureIntro; [done | exact Hbound]. }
    iIntros (cxv) "(%rc & %ci & -> & #Hrc & %Hbound & #HrcP & #Hpayload)".
    (* Re-match on the already-loaded [cy]: a plain path lookup, closed
       automatically by [imp_match]'s own scrutinee handling. *)
    imp_match val with "[]".
    destruct ci as [v0|b]; simpl.
    { iDestruct "Hpayload" as (lv) "#Hrclocs".
      next_branch.
      iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M C N F) "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
      iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
      rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
      iDestruct "HC" as "[Hco HC]".
      iDestruct "Hco" as (lv') "(#Hlocs' & _ & Hlv)".
      iAssert (▷ ⌜[lv] = [lv']⌝)%I with "[]" as ">%Heql".
      { iNext. iApply (isBlockLocs_valid with "Hlocs' Hrclocs"). }
      simplify_eq.
      iModIntro.
      iExists v0.
      iSplitL "Hlv"; first by iFrame.
      iIntros "!> Hlv".
      iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlv]") as "_".
      { iNext. iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth HM". iSplitR; first done.
        iSplitR; first done.
        iSplitR; first done.
        rewrite (big_sepM_delete _ C rc (CRoot v0)); last exact HCrc.
        iSplitL "Hlv".
        { iExists lv'. iFrame "Hlocs' HrcP Hlv". }
        iApply "HC". }
      iModIntro.
      rewrite {1}/deco.
      iApply (imp_EIfThenElse _ _ _ _ (λ _ : bool, True)%I).
      rewrite {1}/deco.
      iApply (imp_EApp (@type_nel.Tcons loc _ (@type_nel.Tcons val Encode_val (@type_nel.Tbase val Encode_val)))).
      { iDestruct "Hcas" as (casv Hcasv) "#Hcasspec".
        iApply (imp_EPath (A:=val) casv).
        { exact Hcasv. }
        iApply ("Hcasspec" $! val Encode_val). }
      { rewrite {1}/deco.
        iApply (imp_EAtomicLoc (Φ := λ l : loc, ⌜l = lyc⌝)%I 1%Z y' [lyi; lyc]).
        { by vm_compute. }
        { iNext. iExact "Hylocs". }
        { imp_path. }
        assert (Hlc1' : @lookup_total Z loc (list loc)
            (@list_z.listz_lookup_total loc locations.inhabited_loc)
            1%Z [lyi; lyc] = lyc) by (vm_compute; reflexivity).
        rewrite Hlc1'.
        iNext. done. }
      { imp_path. }
      (* Installs [Link{parent=x}] (rather than [{parent=y}] as the
         x.id > y.id branch does), mirroring that branch's own
         [imp_wand_observe]/[imp_EInline] bridge. *)
      iApply (imp_wand_observe (A:=elem) (H:=@observe_encode elem (encode_record "Link"))
        _ _ _ _ _ (fun w : val => ∃ r' : elem, ⌜w = VInline "Link" r'⌝ ∗
          ∃ lv0 : loc, isBlockLocs r' [lv0] ∗ isBlock r' (DfracOwn 1) Mut ∗ lv0 ↦ #a)%I
        with "[] []").
      { rewrite {1}/deco.
        iApply (imp_EInline (τ:=τ[elem]) (λ w : elem, ⌜w = a⌝)%I).
        { simpl. lia. }
        iApply (imp_evals_singleton (A:=elem)).
        imp_path.
        done. }
      { iIntros (r) "H".
        iDestruct "H" as (x0) "H".
        iEval (simpl) in "H".
        iDestruct "H" as "[Hown %Heq4]".
        simplify_eq.
        iDestruct "Hown" as (ls) "(#Hlocs2 & Htag2 & Hxs2)".
        iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs2") as (lv2) "[-> Hlv2]".
        iEval (rewrite list_z.singleton_unfold) in "Hlocs2".
        iExists (VInline "Link" r).
        iSplit; first done.
        iExists r.
        iSplit; first done.
        iExists lv2.
        iFrame "Hlocs2 Htag2 Hlv2". }
      iIntros (x0).
      iIntros (rc2) "->".
      iIntros (lc2) "->".
      iIntros "Hown".
      iIntros (m2) "Hm2".
      iNext.
      iApply "Hm2".
      iNext.
      iInv "Hinv" as "H" "Hclose".
      iDestruct "H" as (M2 C2 N2 F2) "(>Hauth & >Hcauth & >Hnauth & >%Hrep2 & >%HdsfF2 & >%HidF2 & HM & HC)".
      iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMa2.
      rewrite (big_sepM_delete _ M2 y' j'); last exact HMa2.
      iDestruct "HM" as "[Hvo HM]".
      assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
      assert (Inhabited cinfo) by exact (populate (CLink 0%Z)).
      iDestruct "Hvo" as (li'' lc'' rc0 ci0) "(#Hzlocs'' & Hlc & >#Hrc0 & >%Hbound0 & >%HFy2 & Htok0)".
      iAssert (▷ ⌜[lyi; lyc] = [li''; lc'']⌝)%I with "[]" as ">%Heql2".
      { iNext. iApply (isBlockLocs_valid with "Hzlocs'' Hylocs"). }
      simplify_eq.
      iDestruct (ghost_map_lookup with "Hcauth Hrc0") as %HCrc0.
      rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
      iDestruct "HC" as "[Hco0 HC]".
      iAssert (▷ isBlockP rc0 Mut)%I as "#Hrc0P".
      { iNext.
        destruct ci0 as [v0'|b0].
        { iDestruct "Hco0" as (lv0) "(_ & $ & _)". }
        { iDestruct "Hco0" as (lp0 y0 j0) "(_ & $ & _)". } }
      set (c0 := match ci0 with CRoot _ => "Root" | CLink _ => "Link" end).
      assert (Hcval0 : cval ci0 rc0 = VInline c0 rc0) by (destruct ci0; reflexivity).
      iModIntro.
      iExists c0, "Root", rc0, rc, DfracDiscarded, DfracDiscarded, Mut.
      iSplitR; first done.
      rewrite <- Hcval0.
      iFrame "Hlc Hrc0P HrcP".
      iNext.
      iIntros "Hlc' _ _".
      destruct (locations.eqb_spec rc0 rc) as [Heqrc|Hnerc].
      { subst rc0.
        iDestruct (ghost_map_elem_agree with "Hrc0 Hrc") as %Heqci0.
        subst ci0.
        iDestruct "Hco0" as (lv0) "(#Hlv0locs & _ & Hlv0)".
        iDestruct "Hown" as (r') "[-> Hownfoot]".
        iDestruct "Hownfoot" as (lv3) "(#Hlv3locs & Htag3 & Hlv3)".
        iAssert (▷ ⌜[lv'] = [lv0]⌝)%I with "[]" as ">%Heqlv0".
        { iNext. iApply (isBlockLocs_valid with "Hlv0locs Hlocs'"). }
        assert (Heqlv0' : lv0 = lv') by (injection Heqlv0; done).
        subst lv0.
        destruct (decide (r' = rc)) as [->|Hne].
        { iAssert (▷ ⌜[lv3] = [lv']⌝)%I with "[]" as ">%Heqlv".
          { iNext. iApply (isBlockLocs_valid with "Hlv0locs Hlv3locs"). }
          assert (Heqlv' : lv3 = lv') by (injection Heqlv; done).
          subst lv3.
          iCombine "Hlv0 Hlv3" gives %Hbad.
          destruct Hbad as [Hbad _].
          exfalso. eapply dfrac_full_exclusive. exact Hbad. }
        destruct (C2 !! r') as [ci1|] eqn:HCr'.
        { assert (HCr'del : delete rc C2 !! r' = Some ci1) by (rewrite lookup_delete_ne; done).
          iDestruct (big_sepM_lookup with "HC") as "Hco1"; first exact HCr'del.
          destruct ci1 as [v2|b1]; simpl.
          { iDestruct "Hco1" as (lv1) "(#Hlocs1 & _ & Hlv1)".
            iAssert (▷ ⌜[lv3] = [lv1]⌝)%I with "[]" as ">%Heqlv1".
            { iNext. iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs"). }
            assert (Heqlv1' : lv1 = lv3) by (injection Heqlv1; done).
            subst lv1.
            iCombine "Hlv1 Hlv3" gives %Hbad.
            destruct Hbad as [Hbad _].
            exfalso. eapply dfrac_full_exclusive. exact Hbad. }
          iDestruct "Hco1" as (lp1 y1 j1) "(#Hlocs1 & _ & Hlp1 & _)".
          iAssert (▷ ⌜[lv3] = [lp1]⌝)%I with "[]" as ">%Heqlp1".
          { iNext. iApply (isBlockLocs_valid with "Hlocs1 Hlv3locs"). }
          assert (Heqlp1' : lp1 = lv3) by (injection Heqlp1; done).
          subst lp1.
          iCombine "Hlv3 Hlp1" gives %Hbad.
          destruct Hbad as [Hbad _].
          exfalso. eapply dfrac_full_exclusive. exact Hbad. }
        iDestruct "Htag3" as (ls3) "Htag3".
        iMod (gen_heap.pointsto_persist with "Htag3") as "Htag3".
        iAssert (isBlockP r' Mut) with "[Htag3]" as "#Hr'P".
        { iExists ls3. iFrame. }
        iMod (ghost_map_insert r' (CLink j') with "Hcauth") as "[Hcauth Hr'frag]"; first exact HCr'.
        iMod (ghost_map_elem_persist with "Hr'frag") as "#Hr'frag".
        iAssert (vertex γ a i') as "Havertex".
        { iExists lai, lac. iFrame "Hafrag Hxlocs HaP Hali". }
        assert (Hlt : (i' < j')%Z).
        { assert (Hle : (i' <= j')%Z).
          { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. exact Hgt. }
          lia. }
        assert (HRoota2 : Root F2 y') by exact HFy2.
        iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMx2.
        pose proof (dsf_link_general M2 F2 y' a j' i' HdsfF2 HidF2 HMa2 HMx2 HRoota2 Hlt (not_eq_sym Heq)) as [HdsfF2' HidF2'].
        iAssert ([∗ map] w ↦ i0 ∈ delete y' M2, vertex_own γ γc γn (link F2 y' a) w i0)%I with "[HM]" as "HM".
        { iApply (vertex_own_widen_link with "HM"). rewrite lookup_delete_eq. done. }
        iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hlv0 Hlv3 Htok0 Havertex]") as "_".
        { iNext.
          iExists M2, (<[r':=CLink j']> C2), N2, (link F2 y' a).
          iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
          iSplitR; first (iPureIntro; exact HdsfF2').
          iSplitR; first (iPureIntro; exact HidF2').
          iSplitL "HM Hlc' Htok0".
          { rewrite (big_sepM_delete _ M2 y' j'); last exact HMa2.
            iSplitL "Hlc' Htok0".
            { iExists li'', lc'', r', (CLink j').
              iFrame "Hzlocs'' Hlc' Hr'frag Htok0".
              iSplit.
              { iPureIntro. intros b0 Hb0. injection Hb0 as ->. lia. }
              iPureIntro. intros [Hr]. eapply (Hr a). right. done. }
            iApply "HM". }
          rewrite big_sepM_insert; last exact HCr'.
          iSplitL "Hlv3 Havertex".
          { simpl. iExists lv3, a, i'. iFrame "Hlv3locs Hr'P Hlv3 Havertex". iPureIntro. exact Hlt. }
          rewrite (big_sepM_delete _ C2 rc (CRoot v0)); last exact HCrc0.
          iSplitL "Hlv0".
          { simpl. iExists lv'. iFrame "Hlv0locs HrcP Hlv0". }
          iApply "HC". }
        iModIntro.
        done. }
      { iMod ("Hclose" with "[Hauth Hcauth Hnauth HM HC Hlc' Hco0 Htok0]") as "_".
        { iNext.
          iExists M2, C2, N2, F2.
          iFrame "Hauth Hcauth Hnauth". iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iSplitL "HM Hlc' Htok0".
          { rewrite (big_sepM_delete _ M2 y' j'); last exact HMa2.
            iSplitL "Hlc' Htok0".
            { iExists li'', lc'', rc0, ci0.
              iFrame "Hzlocs'' Hlc' Hrc0 Htok0". iSplit; [done|iPureIntro; exact HFy2]. }
            iApply "HM". }
          rewrite (big_sepM_delete _ C2 rc0 ci0); last exact HCrc0.
          iFrame "Hco0 HC". }
        iModIntro.
        done. }
      iIntros ([|]) "_".
      { rewrite {1}/deco.
        iApply (imp_wand _ _ _ _ _ (λ ov : option val,
          match ov with
          | None => ⌜same_class x y⌝
          | Some r => ∃ z rc', (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc' ↪[γc]□ CRoot r
          end)%I with "[]").
        { iApply imp_EData.
          { iApply (imp_evals_singleton (A:=val)). imp_path. }
          { iIntros (v) "->".
            instantiate (1 := (fun ov : option val => match ov with
              | None => ⌜same_class x y⌝
              | Some r => ∃ z rc', (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ rc' ↪[γc]□ CRoot r
              end)%I).
            simpl.
            iExists y', rc. iFrame "Hrc". iRight. iPureIntro. apply rtc_once. exists Dy, Fy. eauto. } }
        iIntros (v) "$". }
      { rewrite {1}/deco.
        iApply (imp_EApp τ[elem; elem]).
        { imp_path. }
        { imp_path. }
        { imp_path. }
        iIntros (xv yv) "-> -> %m3 Hm3".
        iNext.
        unfold union_spec.
        iAssert (vertex γ a i') as "Havertex".
        { iExists lai, lac. iFrame "Hafrag Hxlocs HaP Hali". }
        iAssert (vertex γ y' j') as "Hy'vertex2".
        { iExists lyi, lyc. iFrame "Hyfrag Hylocs HyP Hyli". }
        iSpecialize ("Hm3" $! i' j' with "Hinv Havertex Hy'vertex2").
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        destruct ov as [r|].
        { iDestruct "Hov" as (z rc') "[Hzdisj Hrcfrag]".
          iDestruct "Hzdisj" as "[%Hz|%Hz]".
          { iExists z, rc'. iFrame "Hrcfrag". iLeft. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dx, Fx. eauto. }
          { iExists z, rc'. iFrame "Hrcfrag". iRight. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dy, Fy. eauto. } }
        { iDestruct "Hov" as "%Hsc".
          destruct Hsc as (z & Hza & Hzy).
          iPureIntro. exists z.
          split.
          { eapply rtc_l; [|exact Hza]. exists Dx, Fx. eauto. }
          { eapply rtc_l; [|exact Hzy]. exists Dy, Fy. eauto. } } } }
    { next_branch.
      next_branch.
      rewrite {1}/deco.
      iApply (imp_EApp τ[elem; elem]).
      { imp_path. }
      { imp_path. }
      { imp_path. }
      iIntros (xv yv) "-> -> %m3 Hm3".
      iNext.
      unfold union_spec.
      iAssert (vertex γ a i') as "Havertex".
      { iExists lai, lac. iFrame "Hafrag Hxlocs HaP Hali". }
      iAssert (vertex γ y' j') as "Hy'vertex2".
      { iExists lyi, lyc. iFrame "Hyfrag Hylocs HyP Hyli". }
      iSpecialize ("Hm3" $! i' j' with "Hinv Havertex Hy'vertex2").
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      destruct ov as [r|].
      { iDestruct "Hov" as (z rc') "[Hzdisj Hrcfrag]".
        iDestruct "Hzdisj" as "[%Hz|%Hz]".
        { iExists z, rc'. iFrame "Hrcfrag". iLeft. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dx, Fx. eauto. }
        { iExists z, rc'. iFrame "Hrcfrag". iRight. iPureIntro. eapply rtc_l; [|exact Hz]. exists Dy, Fy. eauto. } }
      { iDestruct "Hov" as "%Hsc".
        destruct Hsc as (z & Hza & Hzy).
        iPureIntro. exists z.
        split.
        { eapply rtc_l; [|exact Hza]. exists Dx, Fx. eauto. }
        { eapply rtc_l; [|exact Hzy]. exists Dy, Fy. eauto. } } } }
Qed.

End ConcurrentUnionFind.
