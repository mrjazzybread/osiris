From iris.base_logic.lib Require Import invariants ghost_map.

From osiris Require Import osiris.
From osiris.stdlib.proofs Require Import atomic.
From osiris.examples Require Import og_ConcurrentUnionFind.

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

(* The static description of a content record; see below. *)
Inductive cinfo :=
| CRoot
| CLink (b : Z).

Section ConcurrentUnionFind.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ record cinfo}.

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
  | CRoot => VInline "Root" rc
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
  | CRoot =>
      ∃ (lv : locations.loc) (v : val),
        isBlockLocs rc [lv] ∗ isBlockP rc Mut ∗ lv ↦ v
  | CLink b =>
      ∃ (lp : locations.loc) (y : elem) j,
        isBlockLocs rc [lp] ∗ isBlockP rc Mut ∗
        lp ↦ #y ∗ vertex γ y j ∗ ⌜(j < b)%Z⌝
  end.

(* [vertex_own γ γc x i] is the invariant-owned footprint of the vertex
   [x]: its content cell, holding a registered content record whose
   description is compatible with [x]'s identifier. *)

Definition vertex_own (γ γc : gname) x i : iProp Σ :=
  ∃ (li lc : locations.loc) rc (ci : cinfo),
    isBlockLocs x [li; lc] ∗
    lc ↦ cval ci rc ∗
    rc ↪[γc]□ ci ∗
    ⌜∀ b, ci = CLink b → (b ≤ i)%Z⌝.

(* The global invariant: the authoritative maps of vertices and content
   records, together with their physical footprints. *)

Definition uf_inv (γ γc : gname) : iProp Σ :=
  ∃ (M : gmap elem Z) (C : gmap record cinfo),
    ghost_map_auth γ 1 M ∗
    ghost_map_auth γc 1 C ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ γc x i) ∗
    ([∗ map] rc ↦ ci ∈ C, content_own γ γc rc ci).

Definition is_uf (γ γc : gname) : iProp Σ :=
  inv ufN (uf_inv γ γc).

(* An empty structure can always be created. *)

Lemma uf_alloc E :
  ⊢ |={E}=> ∃ γ γc, is_uf γ γc.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γ) "Hγ".
  iMod (ghost_map_alloc_empty (K:=record) (V:=cinfo)) as (γc) "Hγc".
  iMod (inv_alloc ufN _ (uf_inv γ γc) with "[Hγ Hγc]") as "#Hinv".
  { iNext. iExists ∅, ∅. iFrame. by rewrite !big_sepM_empty. }
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* The [cas] top-level alias. *)

(* The example's first top-level binding is
   [let cas = Atomic.Loc.compare_and_set]. Given the [Atomic] module's
   specification (stdlib/proofs/atomic.v), the alias satisfies
   [compare_and_set_spec] — the logically-atomic CAS triple over
   inline-record contents. The proofs of [set], [update] and [union]
   hypothesize [in_env "cas" (λ c, □ iSpec τ[loc; val; val] c
   compare_and_set_spec) η], which this lemma discharges when walking
   the module's top-level items. *)

Lemma cas_proof η :
  in_env "Atomic" atomic_module_spec η -∗
  imp (eval η (EPath ["Atomic"; "Loc"; "compare_and_set"]))
    {{ λ cas, □ iSpec τ[loc; val; val] cas compare_and_set_spec }}.
Proof.
  iIntros "HAtomic".
  iDestruct (atomic_cas_path_spec with "HAtomic") as (cas Hcas) "#Hspec".
  iApply (imp_EPath (A:=val) cas).
  { exact Hcas. }
  iExact "Hspec".
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [G.fresh]. *)

(* This specification will have
   to be strengthened to guarantee uniqueness of the returned
   identifiers, e.g. with an exclusive ghost token. *)

Definition fresh_spec (u : unit) (m : microvx) : iProp Σ :=
  imp m {{ λ i : Z, True }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [make]. *)

(* [make v] returns a fresh vertex of the structure. *)

Definition make_spec (γ γc : gname) (v : val) (m : microvx) : iProp Σ :=
  is_uf γ γc -∗
  imp m {{ λ x : elem, ∃ i, vertex γ x i }}.

(* [record]/[ERecord] allocations must fit within [max_array_length]. *)
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof γ γc η :
  path_spec ["G"; "fresh"] (λ fresh, □ iSpec τ[unit] fresh fresh_spec)%I η -∗
  imp (eval η (EAnonFun __make)) {{ λ c, □ iSpec τ[val] c (make_spec γ γc) }}.
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
  { iApply (imp_bindings_cons (A:=Z) (λ _ : Z, True)%I with "[] [] []").
    { (* [G.fresh ()], through the [fresh_spec] hypothesis. *)
      rewrite {1}/deco.
      iApply (imp_EApp τ[unit]).
      { rewrite {1}/deco. iApply (imp_EPath (A:=val) g).
        { simpl. exact Hg. }
        iApply "Hfresh". }
      { rewrite {1}/deco. imp_step. }
      simpl. iIntros (u) "_ %m Hm". iNext. iApply "Hm". }
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
      iPoseProof (big_opLZ.big_sepLZ2_length with "Hxs") as "%Hlen".
      simpl in Hlen.
      (* The freshly allocated block has exactly one field location. *)
      destruct ls as [|lv [|]]; try (simpl in Hlen; lia).
      { iDestruct (big_opLZ.big_sepLZ2_nil_inv_l with "Hxs") as %Hnil;
          discriminate. }
      { iExists lv. iFrame "Hlocs Htag".
        iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
          as (w ws Heq) "[Hlv _]".
        simpl in Heq. simplify_eq. iFrame. }
      { iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
          as (w ws Heq) "[_ Hxs]".
        simpl in Heq. simplify_eq.
        iDestruct (big_opLZ.big_sepLZ2_nil_inv_r with "Hxs") as %Hnil;
          discriminate. } }
    { iIntros (rc) "_". iPureIntro. apply pat_PVar.
      instantiate (1 := λ (w : val) (l : env), l = [("content", w)]).
      reflexivity. }
    { iIntros (rc δ) "HΦ1 ->".
      instantiate (1 := (λ δ : env, ∃ (rc : record) (lv : locations.loc),
        ⌜δ = [("content", VInline "Root" rc)]⌝ ∗
        isBlockLocs rc [lv] ∗ isBlock rc (DfracOwn 1) Mut ∗ lv ↦ v)%I).
      iDestruct "HΦ1" as (lv) "(#Hlocs & Htag & Hlv)".
      iExists rc, lv. iFrame "∗#". done. } }
  iIntros (δ) "(%a & %η' & %δ' & -> & _ & %HP & HQ)".
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
  iPoseProof (big_opLZ.big_sepLZ2_length with "Hxs") as "%Hlen".
  (* The vertex block has exactly two field locations: [li] and [lc]. *)
  destruct ls as [|li [|lc [|]]].
  { iDestruct (big_opLZ.big_sepLZ2_nil_inv_l with "Hxs") as %Hnil;
      discriminate. }
  { iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
      as (w ws Heq) "[_ Hxs]".
    simpl in Heq; simplify_eq. }
  2:{ iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
        as (w ws Heq) "[_ Hxs]".
      simpl in Heq; simplify_eq.
      iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
        as (w' ws' Heq') "[_ Hxs]".
      simplify_eq.
      iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
        as (w'' ws'' Heq'') "[_ _]".
      discriminate. }
  iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
    as (w ws Heq) "[Hli Hxs]".
  simpl in Heq; simplify_eq.
  iDestruct (big_opLZ.big_sepLZ2_cons_inv_l with "Hxs")
    as (w' ws' Heq') "[Hlc _]".
  simplify_eq.

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
  iDestruct "H" as (M C) "(>Hauth & >Hcauth & HM & HC)".
  (* [x] is fresh: an existing entry would own [lc] a second time. *)
  destruct (M !! x) as [ix|] eqn:HMx.
  { iDestruct (big_sepM_lookup with "HM") as "Hvo"; first exact HMx.
    assert (Inhabited elem) as Hinh by (unfold elem, record; simpl; apply _).
    assert (Inhabited cinfo) as Hcinh by exact (populate CRoot).
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
    destruct ci0; simpl.
    { iDestruct "Hco" as (lv' v') "(#Hlocs' & _ & Hlv')".
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
  iMod (ghost_map_insert rc CRoot with "Hcauth") as "[Hcauth Hrcfrag]";
    first exact HCrc.
  iMod (ghost_map_elem_persist with "Hrcfrag") as "#Hrcfrag".
  iMod (ghost_map_insert x a with "Hauth") as "[Hauth Hxfrag]";
    first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod ("Hclose" with "[Hauth Hcauth HM HC Hlc Hlv]") as "_".
  { iNext. iExists (<[x:=a]> M), (<[rc:=CRoot]> C).
    iFrame "Hauth Hcauth".
    iSplitL "HM Hlc".
    { rewrite big_sepM_insert; last exact HMx.
      iSplitL "Hlc".
      { iExists li, lc, rc, CRoot. iFrame "Hxlocs Hlc Hrcfrag".
        iPureIntro. intros b Hb. discriminate. }
      iApply "HM". }
    rewrite big_sepM_insert; last exact HCrc.
    iSplitL "Hlv".
    { simpl. iExists lv, v. iFrame "Hlocs HrcP Hlv". }
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

Definition find_spec (γ γc : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc -∗
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

Lemma find_proof γ γc η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ γc)) η -∗
  imp (eval η (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))))
    {{ λ c, □ iSpec τ[elem] c (find_spec γ γc) }}.
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
  iApply (imp_EMatch (A':=val) (λ v : val,
    ∃ (rc : record) (ci : cinfo),
      ⌜v = cval ci rc⌝ ∗ rc ↪[γc]□ ci ∗ ⌜∀ b, ci = CLink b → (b ≤ i)%Z⌝ ∗
      match ci with
      | CRoot => True
      | CLink b => ∃ lp : locations.loc, isBlockLocs rc [lp]
      end)%I with "[]").
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
    iDestruct "H" as (M C) "(>Hauth & >Hcauth & HM & HC)".
    iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
    rewrite (big_sepM_delete _ M x i); last exact HMx.
    iDestruct "HM" as "[Hvo HM]".
    assert (Inhabited elem) by (unfold elem, record; simpl; apply _).
    assert (Inhabited cinfo) by exact (populate CRoot).
    iDestruct "Hvo" as (li' lc' rc ci) "(#Hxlocs' & Hlc & >#Hrc & >%Hb)".
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
             | CRoot => True
             | CLink _ => ∃ lp : loc, isBlockLocs rc [lp]
             end)%I as "#Hpayload".
    { destruct ci as [|b]; first done.
      iDestruct "Hco" as (lp y j) "(#Hrclocs & _)".
      eauto. }
    iMod ("Hclose" with "[Hauth Hcauth HM HC Hlc Hco]") as "_".
    { iNext. iExists M, C. iFrame "Hauth Hcauth".
      iSplitL "HM Hlc".
      { rewrite (big_sepM_delete _ M x i); last exact HMx.
        iSplitL "Hlc".
        { iExists li', lc', rc, ci. iFrame "Hxlocs Hlc Hrc". done. }
        iApply "HM". }
      rewrite (big_sepM_delete _ C rc ci); last exact HCrc.
      iFrame "Hco HC". }
    iModIntro.
    iExists rc, ci. iFrame "Hrc Hpayload".
    iSplit; iPureIntro; [done | exact Hb]. }
  iIntros (v) "(%rc & %ci & -> & #Hrc & %Hb & #Hpayload)".
  iNext.
  destruct ci as [|b]; simpl.

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
  iDestruct "H" as (M C) "(>Hauth & >Hcauth & HM & HC)".
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
  iMod ("Hclose" with "[Hauth Hcauth HM HC Hlp]") as "_".
  { iNext. iExists M, C. iFrame "Hauth Hcauth HM".
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

End ConcurrentUnionFind.
