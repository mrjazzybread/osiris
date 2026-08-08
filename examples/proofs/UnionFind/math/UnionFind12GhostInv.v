From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map.
From stdpp Require Import relations.

From osiris Require Import osiris.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link
               UnionFind05IteratedCompression UnionFind11Bounded.

Require Export UnionFind08DataConc UnionFind09Reaches UnionFind10ReprPred.

Local Notation elem := record.

Definition ufN : namespace := nroot .@ "concurrent_uf".

Section uf_inv.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types i j : Z.
Implicit Types γ γc γn γR : gname.

(* The global invariant: the authoritative maps of vertices and content
   records, together with their physical footprints, and the registry
   of identifiers. *)

Definition uf_inv (γ γc γn γR : gname) : iProp Σ :=
  ∃ (M : gmap elem Z) (C : gmap content cinfo) (N : gmap Z unit)
    (R : gset (elem * elem)) (F : elem → elem → Prop),
    ghost_map_auth γ 1 M ∗
    ghost_map_auth γc 1 C ∗
    ghost_map_auth γn 1 N ∗
    own γR (● R) ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜DSF F (dom M)⌝ ∗
    ⌜id_bounded M F⌝ ∗
    ⌜reaches_sound R F⌝ ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ γc γn γR F x i) ∗
    ([∗ map] c ↦ ci ∈ C, content_own γ γc γR c ci).

Definition is_uf (γ γc γn γR : gname) : iProp Σ :=
  inv ufN (uf_inv γ γc γn γR).

(* An empty structure can always be created; the empty graph is trivially a
   disjoint set forest over the empty domain ([is_dsf_empty],
   [UnionFind02EmptyCreate.v]). *)

Lemma uf_alloc E :
  ⊢ |={E}=> ∃ γ γc γn γR, is_uf γ γc γn γR.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γ) "Hγ".
  iMod (ghost_map_alloc_empty (K:=content) (V:=cinfo)) as (γc) "Hγc".
  iMod (ghost_map_alloc_empty (K:=Z) (V:=unit)) as (γn) "Hγn".
  iMod (own_alloc (● (∅ : gset (elem * elem)))) as (γR) "HγR";
    first by apply auth_auth_valid.
  iMod (inv_alloc ufN _ (uf_inv γ γc γn γR) with "[Hγ Hγc Hγn HγR]") as "#Hinv".
  { iNext. iExists ∅, ∅, ∅, ∅, (empty elem). iFrame.
    iSplit; [iPureIntro; intros x i; rewrite lookup_empty; discriminate|].
    iSplit; [iPureIntro; rewrite dom_empty_L; exact (is_dsf_empty elem _ _)|].
    iSplit; [iPureIntro; intros w z iw iz []|].
    iSplit; [iPureIntro; intros u w Huw; set_solver|].
    by rewrite !big_sepM_empty. }
  iModIntro. iExists γ, γc, γn, γR. iExact "Hinv".
Qed.

(* ------------------------------------------------------------------------ *)
(* Accessing the invariant.

   [uf_inv] is never destructured outside this file, and inside it only
   by the four accessors below. Each one hands out exactly the resources
   its callers consume — and a wand to give them back — rather than the
   whole pile of components; the ones a caller does not need it never
   sees, which is what keeps the function proofs free of invariant
   bookkeeping.

   The first accessor is the purely ghost one. [reaches_refl],
   [reaches_trans], [reaches_sibling] and [vertex_representable] all read
   the identifier map [M] and the abstract graph [F], change at most the
   recorded-pairs set [R], and touch no physical footprint at all — so
   that is all this exposes. Which of the pure facts each of them
   actually uses is visible at their call sites, where the rest are
   introduced as [_]. *)

Lemma uf_inv_ghost_acc γ γc γn γR :
  ▷ uf_inv γ γc γn γR -∗
  ◇ ∃ (M : gmap elem Z) (R : gset (elem * elem)) F,
      ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
      ⌜DSF F (dom M)⌝ ∗ ⌜id_bounded M F⌝ ∗ ⌜reaches_sound R F⌝ ∗
      ghost_map_auth γ 1 M ∗ own γR (● R) ∗
      (∀ R', ⌜reaches_sound R' F⌝ -∗
             ghost_map_auth γ 1 M -∗ own γR (● R') -∗ ▷ uf_inv γ γc γn γR).
Proof.
  iIntros "H".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  iModIntro. iExists M, R, F.
  do 4 (iSplitR; first done).
  iFrame "Hauth HRauth".
  iIntros (R') "%HRs' Hauth HRauth". iNext.
  iExists M, C, N, R', F. by iFrame.
Qed.

(* [uf_frame γ γc γn γR z j c] is everything [uf_inv] owns that a step on
   vertex [z]'s content cell never inspects: the identifier map [M] with
   its abstract graph [F], the identifier registry, the recorded
   reachability pairs, and every OTHER vertex's footprint. Packaging it
   under one name is what lets the accessors below expose the content
   registry alone.

   The frame is indexed by the content [c] the cell holds, because that
   is the one thing the cell and the graph still have to agree on: [c]'s
   tag says whether [z] is a root of [F]. Putting it back with a content
   of the same tag ([uf_inv_reassemble]) needs no graph reasoning; the
   one step that flips the tag ([uf_inv_reassemble_link]) is where the
   graph grows. *)

Definition uf_frame (γ γc γn γR : gname) z j (c : content) : iProp Σ :=
  ∃ (M : gmap elem Z) (N : gmap Z unit) (R : gset (elem * elem)) F,
    ⌜M !! z = Some j⌝ ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜DSF F (dom M)⌝ ∗ ⌜id_bounded M F⌝ ∗ ⌜reaches_sound R F⌝ ∗
    ⌜if content_root c then Root F z else ¬ Root F z⌝ ∗
    ghost_map_auth γ 1 M ∗ ghost_map_auth γn 1 N ∗ own γR (● R) ∗
    j ↪[γn] () ∗
    ([∗ map] x ↦ i ∈ delete z M, vertex_own γ γc γn γR F x i).

(* [uf_inv_split] singles out one vertex's footprint: given [z]'s
   persistent [vertex] components, it hands back the content cell
   [lzc ↦ #c] of [z], the registration and description [ci] of the
   content record [c] it currently holds, the content registry (which a
   caller installing a fresh record has to extend), and the frame.
   [uf_inv_reassemble] is the converse, for a possibly *different*
   content record of the same tag — which is exactly what a successful
   [Root]-to-[Root] CAS produces. *)

Lemma uf_inv_split γ γc γn γR z j lzi lzc :
  z ↪[γ]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ γc γn γR -∗
  ◇ ∃ (C : gmap content cinfo) c ci,
      ⌜C !! c = Some ci⌝ ∗
      ⌜∀ b h, ci = CLink b h → (b ≤ j)%Z ∧ h = z⌝ ∗
      ghost_map_auth γc 1 C ∗ c ↪[γc]□ ci ∗
      ▷ (lzc ↦ #c) ∗
      ▷ content_own γ γc γR c ci ∗
      ▷ ([∗ map] d ↦ cd ∈ delete c C, content_own γ γc γR d cd) ∗
      ▷ uf_frame γ γc γn γR z j c.
Proof.
  iIntros "#Hzfrag #Hzlocs H".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  iDestruct "Hvo" as (li' lc' c ci)
    "(#Hzlocs' & Hlc & >#Hrc & >%Hbound & >%HFz & Htok)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hzlocs' Hzlocs"). }
  simplify_eq.
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C c ci); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iExists C, c, ci.
  iModIntro.
  do 2 (iSplitR; first done).
  iFrame "Hcauth Hrc Hlc Hco HC".
  iNext. iExists M, N, R, F.
  do 6 (iSplitR; first done).
  iFrame "Hauth Hnauth HRauth Htok HM".
Qed.

Lemma uf_inv_reassemble γ γc γn γR (C : gmap content cinfo) z j lzi lzc c c' ci' :
  content_root c' = content_root c →
  C !! c' = Some ci' →
  (∀ b h, ci' = CLink b h → (b ≤ j)%Z ∧ h = z) →
  ghost_map_auth γc 1 C -∗
  c' ↪[γc]□ ci' -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #c' -∗
  content_own γ γc γR c' ci' -∗
  ([∗ map] d ↦ cd ∈ delete c' C, content_own γ γc γR d cd) -∗
  uf_frame γ γc γn γR z j c -∗
  uf_inv γ γc γn γR.
Proof.
  intros Htag HCc' Hbound.
  iIntros "Hcauth #Hc' #Hzlocs Hlc Hco HC Hframe".
  iDestruct "Hframe" as (M N R F)
    "(%HMz & %Hrep & %HdsfF & %HidF & %HRs & %HFz &
      Hauth & Hnauth & HRauth & Htok & HM)".
  iExists M, C, N, R, F. iFrame "Hauth Hcauth Hnauth HRauth".
  do 4 (iSplitR; first done).
  iSplitL "HM Hlc Htok".
  { rewrite (big_sepM_delete _ M z j); last exact HMz.
    iSplitL "Hlc Htok".
    { iExists lzi, lzc, c', ci'. iFrame "Hzlocs Hlc Hc' Htok".
      iSplit; first done.
      iPureIntro. rewrite Htag. exact HFz. }
    iApply "HM". }
  rewrite (big_sepM_delete _ C c' ci'); last exact HCc'.
  iFrame "Hco HC".
Qed.

(* The other way to put the frame back, for a successful linking CAS —
   the one place where the abstract graph [F] grows: vertex [z], a root
   (which is what [content_root c = true] says, through the frame's own
   tag conjunct) with identifier [j], has just had its content cell swung
   to the brand new link value [CtLink rcn], registered with bound
   [b ≤ j] and holder [z] (the cell the value is going into is [z]'s own
   — that is what makes [z] the holder). The new record's [content_init]
   already carries the parent [y] and the strict bound [jy < b], which is
   everything [dsf_link_general] needs to justify widening [F] by the
   edge [z → y] without re-checking [y]'s root-status.

   This is also where the link's [reaches γR z y] — the extra conjunct
   [content_own] carries over [content_init] — is born, and it is the
   only primitive source of a [reaches] fact in the whole file: the
   widened graph [link F z y] contains the edge [z → y] outright, so
   [y] is reachable from [z] in it, and the pair is recorded in [R].
   Every other [reaches] in the development is derived from these by
   [reaches_trans].

   Recording the pair is a ghost update, so the conclusion is a basic
   update rather than a bare [uf_inv]; the caller ([uf_cas_fupd]) is
   already inside a fancy update when it re-closes, so it simply
   [iMod]s this before handing the result to its [Hclose]. *)

Lemma uf_inv_reassemble_link γ γc γn γR (C : gmap content cinfo) z j b lzi lzc
    c (rcn : elem) :
  content_root c = true →
  C !! CtLink rcn = None →
  (b ≤ j)%Z →
  ghost_map_auth γc 1 (<[CtLink rcn := CLink b z]> C) -∗
  CtLink rcn ↪[γc]□ CLink b z -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #(CtLink rcn) -∗
  content_init γ γc (CtLink rcn) (CLink b z) -∗
  ([∗ map] d ↦ cd ∈ C, content_own γ γc γR d cd) -∗
  uf_frame γ γc γn γR z j c -∗
  |==> uf_inv γ γc γn γR.
Proof.
  intros Htag HCn Hbj.
  iIntros "Hcauth #Hr #Hzlocs Hlc Hco HC Hframe".
  iDestruct "Hframe" as (M N R F)
    "(%HMz & %Hrep & %HdsfF & %HidF & %HRs & %HFz &
      Hauth & Hnauth & HRauth & Htok & HM)".
  rewrite Htag in HFz.
  (* Peek at the new link's parent [y]: a registered vertex whose
     identifier sits strictly below [b], hence strictly below [j]. *)
  iDestruct "Hco" as (y jy) "(Hrec & #Hy & %Hjy)".
  iDestruct (vertex_frag with "Hy") as "#Hyfrag".
  iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
  assert (Hzy : z ≠ y).
  { intros ->. rewrite HMz in HMy. simplify_eq. lia. }
  pose proof (dsf_link_general M F z y j jy HdsfF HidF HMz HMy HFz
                ltac:(lia) Hzy) as [HdsfF' HidF'].
  (* Record the freshly-installed edge: this is the link's permanent tie
     to its holder's class, and [z → y] is an edge of the widened graph
     by construction. *)
  iMod (reaches_update _ _ (link F z y) z y with "HRauth")
    as (R') "(HRauth & #Hzy & %HRs' & _)".
  { by apply reaches_sound_link. }
  { apply rtc_once, link_appears. }
  iModIntro.
  iExists M, (<[CtLink rcn := CLink b z]> C), N, R', (link F z y).
  iFrame "Hauth Hcauth Hnauth HRauth".
  do 4 (iSplitR; first done).
  iSplitL "HM Hlc Htok".
  { rewrite (big_sepM_delete _ M z j); last exact HMz.
    iSplitL "Hlc Htok".
    { iExists lzi, lzc, (CtLink rcn), (CLink b z).
      iFrame "Hzlocs Hlc Hr Htok".
      iSplit.
      { iPureIntro. intros b' h' Hb'. injection Hb' as -> ->. done. }
      iPureIntro. simpl. intros [Hr']. eapply (Hr' y). right. done. }
    iApply (vertex_own_widen_link with "HM").
    rewrite lookup_delete_eq. done. }
  rewrite big_sepM_insert; last exact HCn.
  iSplitL "Hrec".
  { iExists y, jy. by iFrame "Hrec Hy Hzy". }
  iApply "HC".
Qed.

(* [find] and [update] also reach a content record *directly*, without
   going through a vertex: they re-read a field of a record whose
   registration [c ↪[γc]□ ci] they already hold. Nothing about the
   invariant changes across such a step, so this one is an ordinary
   accessor — borrow [content_own], hand it back — rather than a
   split/reassemble pair, and it exposes that one record's footprint and
   nothing else. *)

Lemma uf_inv_content_acc γ γc γn γR c ci :
  c ↪[γc]□ ci -∗
  ▷ uf_inv γ γc γn γR -∗
  ◇ (▷ content_own γ γc γR c ci ∗
     (▷ content_own γ γc γR c ci -∗ ▷ uf_inv γ γc γn γR)).
Proof.
  iIntros "#Hrc H".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C c ci); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iModIntro. iFrame "Hco".
  iIntros "Hco". iNext.
  iExists M, C, N, R, F. iFrame "Hauth Hcauth Hnauth HRauth HM".
  do 4 (iSplitR; first done).
  rewrite (big_sepM_delete _ C c ci); last exact HCrc.
  iFrame "Hco HC".
Qed.

(* The last member of the family, for [make]: rather than putting an
   existing vertex back, this registers a brand new one — with its own
   brand new content record — extending both authoritative maps. The
   caller hands over the fresh vertex's content cell, the fresh content
   record, and the identifier token, and gets back the invariant plus
   the vertex's own persistent fragment; it never sees a component.

   Neither [x] nor [c] can be registered already: an existing entry
   would own the very field the caller is still holding.

   Widening [M] is where the pure invariants have to be re-established,
   which is the bulk of the proof: [representable] for the new id, [DSF]
   by covariance in the domain, and [id_bounded] because [F] confines its
   edges to the *old* domain and so has none touching [x] at all. *)

Lemma uf_inv_insert_vertex γ γc γn γR E x i li lc (c : content) v :
  representable i →
  isBlockLocs x [li; lc] -∗
  lc ↦ #c -∗
  content_own γ γc γR c (CRoot v) -∗
  i ↪[γn] () -∗
  ▷ uf_inv γ γc γn γR ={E}=∗
  ▷ uf_inv γ γc γn γR ∗ x ↪[γ]□ i.
Proof.
  intros Hrepi.
  iIntros "#Hxlocs Hlc Hco Htok H".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  destruct (M !! x) as [ix|] eqn:HMx.
  { iDestruct (big_sepM_lookup _ _ x ix with "HM") as "Hvo"; first exact HMx.
    iAssert (▷ False)%I with "[Hlc Hvo]" as ">[]".
    iNext. iApply (vertex_own_fresh_ne with "Hxlocs Hlc Hvo"). }
  destruct (C !! c) as [ci0|] eqn:HCrc.
  { iDestruct (big_sepM_lookup _ _ _ ci0 with "HC") as "Hco0"; first exact HCrc.
    iAssert (▷ False)%I with "[Hco Hco0]" as ">[]".
    iNext. iApply (content_own_excl γ γc γR c (CRoot v) ci0 with "Hco Hco0"). }
  iMod (ghost_map_insert c (CRoot v) with "Hcauth") as "[Hcauth Hrc]";
    first exact HCrc.
  iMod (ghost_map_elem_persist with "Hrc") as "#Hrc".
  iMod (ghost_map_insert x i with "Hauth") as "[Hauth Hxfrag]";
    first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iModIntro. iFrame "Hxfrag". iNext.
  destruct c as [rc|rc]; last by iDestruct "Hco" as "[]".
  iExists (<[x := i]> M), (<[CtRoot rc := CRoot v]> C), N, R, F.
  iFrame "Hauth Hcauth Hnauth HRauth".
  iSplitR.
  { iPureIntro. intros x' i' Hx'.
    destruct (decide (x' = x)) as [->|Hne].
    { rewrite lookup_insert_eq in Hx'. simplify_eq. exact Hrepi. }
    { rewrite lookup_insert_ne in Hx'; last done. exact (Hrep x' i' Hx'). } }
  iSplitR.
  { iPureIntro. rewrite dom_insert_L.
    eapply is_dsf_covariant_in_D; [exact HdsfF|]. set_solver. }
  iSplitR.
  { iPureIntro. intros w z iw iz HFwz Hw Hz.
    destruct HdsfF as [[Hconf'] _ _].
    destruct (decide (w = x)) as [->|Hwne].
    { exfalso. destruct (Hconf' x z HFwz) as [Hwd _].
      apply not_elem_of_dom in HMx. contradiction. }
    rewrite lookup_insert_ne in Hw; last done.
    destruct (decide (z = x)) as [->|Hzne].
    { exfalso. destruct (Hconf' w x HFwz) as [_ Hzd].
      apply not_elem_of_dom in HMx. contradiction. }
    rewrite lookup_insert_ne in Hz; last done.
    exact (HidF w z iw iz HFwz Hw Hz). }
  iSplitR; first done.
  iSplitL "HM Hlc Htok".
  { rewrite big_sepM_insert; last exact HMx.
    iSplitL "Hlc Htok".
    { iExists li, lc, (CtRoot rc), (CRoot v). iFrame "Hxlocs Hlc Hrc Htok".
      iSplit.
      { iPureIntro. intros b h Hb. discriminate. }
      iPureIntro. simpl. eapply only_roots_outside_D; [exact HdsfF|].
      apply not_elem_of_dom. exact HMx. }
    iApply "HM". }
  rewrite big_sepM_insert; last exact HCrc.
  iFrame "Hco HC".
Qed.

End uf_inv.

Section reaches.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* ------------------------------------------------------------------------ *)
(* The [reaches] API. *)

(* Reflexivity: [rtc] is reflexive, so the pair is recordable at any
   open whatsoever. *)

Lemma reaches_refl γ γc γn γR x :
  is_uf γ γc γn γR ={⊤}=∗ reaches γR x x.
Proof.
  iIntros "#Hinv".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ghost_acc with "H") as (M R F)
    "(_ & _ & _ & %HRs & Hauth & HRauth & Hback)".
  iMod (reaches_update _ _ F x x with "HRauth") as (R') "(HRauth & #Hxx & %HRs' & _)";
    [exact HRs | reflexivity |].
  iMod ("Hclose" with "[Hback Hauth HRauth]") as "_";
    first by iApply ("Hback" with "[//] Hauth HRauth").
  by iModIntro.
Qed.

(* Transitivity. *)

Lemma reaches_trans γ γc γn γR x y z :
  is_uf γ γc γn γR -∗ reaches γR x y -∗ reaches γR y z ={⊤}=∗ reaches γR x z.
Proof.
  iIntros "#Hinv #Hxy #Hyz".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ghost_acc with "H") as (M R F)
    "(_ & _ & _ & %HRs & Hauth & HRauth & Hback)".
  iDestruct (reaches_lookup with "HRauth Hxy") as %Hxy.
  iDestruct (reaches_lookup with "HRauth Hyz") as %Hyz.
  iMod (reaches_update _ _ F x z with "HRauth") as (R') "(HRauth & #Hxz & %HRs' & _)";
    [exact HRs | by eapply rtc_trans; apply HRs |].
  iMod ("Hclose" with "[Hback Hauth HRauth]") as "_";
    first by iApply ("Hback" with "[//] Hauth HRauth").
  by iModIntro.
Qed.

End reaches.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API: the only interface the function proofs use. It
   speaks of [vertex], [is_uf], [content_info] and the persistent
   registration fragments — never of the invariant's components. *)

Section uf_api.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ γc γn γR : gname.

(* Reading a vertex's content cell, in the shape the atomic record-access
   rule wants. The reader learns [content_info] — the loaded value is
   registered, its description matches its tag, and in the link case
   names [z] as the holder with a bound dominated by [z]'s identifier —
   and gives the cell straight back, unchanged. *)

Lemma uf_vertex_content_acc γ γc γn γR z j lzi lzc (Φ : content → iProp Σ) :
  is_uf γ γc γn γR -∗
  z ↪[γ]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ (∀ c : content, content_info γc z c j -∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hzfrag #Hzlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (C c ci)
    "(%HCc & %Hbound & Hcauth & #Hc & Hlc & Hco & HC & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (content_own_info with "Hc Hco") as "[#Hinfo Hco]"; first exact Hbound.
  iMod ("Hclose" with "[Hcauth Hlc Hco HC Hframe]") as "_".
  { iNext.
    iApply (uf_inv_reassemble γ γc γn γR C z j lzi lzc c c ci
              with "Hcauth Hc Hzlocs Hlc Hco HC Hframe"); done. }
  iModIntro. iApply ("HΦ" with "Hinfo").
Qed.

(* Registering a fresh vertex: the caller owns the vertex record — its
   [id] field holding a fresh identifier, its [content] cell a fresh,
   unregistered [Root] content — and trades all of it for the persistent
   [vertex] fact. *)

Lemma register_vertex γ γc γn γR i (c : content) v r :
  representable i →
  is_uf γ γc γn γR -∗
  i ↪[γn] () -∗
  content_own γ γc γR c (CRoot v) -∗
  r ⤇ {| vertex_id_f := i; vertex_content_f := #c |} ={⊤}=∗
  vertex γ r i.
Proof.
  iIntros (Hrepi) "#Hinv Htok Hco Hown".
  iDestruct "Hown" as (flocs) "(#Hxlocs & #HxP & Hxs)".
  (* The vertex block has exactly two field locations: [li] and [lc]. *)
  iDestruct (big_opLZ.big_sepLZ2_pair_inv_r with "Hxs") as (li lc) "(-> & Hli & Hlc)".

  (* Persist the [id] field, which never changes again. Both blocks'
     mutability tags are already persistent: [ownRecord] holds them that
     way, so nothing has to be discarded here. *)
  iMod (gen_heap.pointsto_persist with "Hli") as "#Hli".

  (* Register the vertex and its content record in the invariant. *)
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_insert_vertex with "Hxlocs Hlc Hco Htok H") as "[H #Hxfrag]";
    first exact Hrepi.
  iMod ("Hclose" with "H") as "_".
  iModIntro.
  iExists li, lc. iFrame "Hxfrag Hxlocs HxP Hli".
Qed.

(* What [union]'s [assert (x.id <> y.id)] needs: distinct vertices have
   distinct — and, from [uf_inv]'s own [representable] conjunct, machine-
   comparable — identifiers. The two vertices' footprints are the only
   thing read, and the invariant is handed back unchanged. *)

Lemma vertex_ids_ne γ γc γn γR (a w : elem) ia iw :
  a ≠ w →
  is_uf γ γc γn γR -∗
  vertex γ a ia -∗
  vertex γ w iw -∗
  |={⊤}=> ⌜ia ≠ iw ∧ representable ia ∧ representable iw⌝.
Proof.
  iIntros (Hne) "#Hinv #Ha #Hw".
  iDestruct (vertex_frag with "Ha") as "#Hafrag".
  iDestruct (vertex_frag with "Hw") as "#Hwfrag".
  iInv "Hinv" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)" "Hclose".
  iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMa.
  iDestruct (ghost_map_lookup with "Hauth Hwfrag") as %HMw.
  assert (HMw' : delete a M !! w = Some iw) by (rewrite lookup_delete_ne; done).
  rewrite (big_sepM_delete _ M a ia); last exact HMa.
  iDestruct "HM" as "[Hvoa HM]".
  rewrite (big_sepM_delete _ (delete a M) w iw); last exact HMw'.
  iDestruct "HM" as "[Hvow HM]".
  destruct (decide (ia = iw)) as [->|Hij].
  { iAssert (▷ False)%I with "[Hvoa Hvow]" as ">[]".
    iNext. iApply (vertex_own_id_ne with "Hvoa Hvow"). }
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth Hvoa Hvow HM HC]") as "_".
  { iNext. iExists M, C, N, R, F. iFrame "Hauth Hcauth Hnauth HRauth HC".
    do 4 (iSplitR; first done).
    rewrite (big_sepM_delete _ M a ia); last exact HMa.
    rewrite (big_sepM_delete _ (delete a M) w iw); last exact HMw'.
    iFrame "Hvoa Hvow HM". }
  iModIntro. iPureIntro.
  split; [exact Hij | split; [exact (Hrep a ia HMa) | exact (Hrep w iw HMw)]].
Qed.

(* A single vertex's identifier is machine-comparable. [vertex_ids_ne]
   yields this too, but only for a pair of vertices already known to be
   distinct; [compress] compares identifiers of vertices it has no
   distinctness fact about. *)

Lemma vertex_representable γ γc γn γR x i :
  is_uf γ γc γn γR -∗ vertex γ x i ={⊤}=∗ ⌜representable i⌝.
Proof.
  iIntros "#Hinv #Hx".
  iDestruct (vertex_frag with "Hx") as "#Hxfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ghost_acc with "H") as (M R F)
    "(%Hrep & _ & _ & %HRs & Hauth & HRauth & Hback)".
  iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
  iMod ("Hclose" with "[Hback Hauth HRauth]") as "_";
    first by iApply ("Hback" with "[//] Hauth HRauth").
  iModIntro. iPureIntro. exact (Hrep _ _ HMx).
Qed.

(* The step that makes path compression verifiable.

   Given that [x] reaches both [y] and [z], and that [z]'s identifier is
   strictly below [y]'s, conclude that [y] reaches [z].

   Both hypotheses are read back against a *single* open's [F] — which is
   the whole reason [reaches] had to be ghost state — and there the two
   paths out of [x] are linearly ordered ([path_confluent], using that a
   disjoint-set forest is [Functional]). Only one of the two orders is
   consistent with the identifiers: a nonempty path [z ⟶* y] would force
   [id y < id z] via [path_id_decrease], contradicting the hypothesis. So
   the surviving case is [y ⟶* z], which is recorded and handed back.

   This is exactly the reasoning behind [compress]'s [y.id > z.id] guard:
   the test is what licenses rerouting [x] from [y] to [z] while keeping
   every link's parent inside its holder's class. *)

Lemma reaches_sibling γ γc γn γR (x y z : elem) jy jz :
  (jz < jy)%Z →
  is_uf γ γc γn γR -∗
  vertex γ y jy -∗
  vertex γ z jz -∗
  reaches γR x y -∗
  reaches γR x z ={⊤}=∗
  reaches γR y z.
Proof.
  iIntros (Hlt) "#Hinv #Hy #Hz #Hxy #Hxz".
  iDestruct (vertex_frag with "Hy") as "#Hyfrag".
  iDestruct (vertex_frag with "Hz") as "#Hzfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ghost_acc with "H") as (M R F)
    "(_ & %HdsfF & %HidF & %HRs & Hauth & HRauth & Hback)".
  iDestruct (reaches_lookup with "HRauth Hxy") as %Hinxy.
  iDestruct (reaches_lookup with "HRauth Hxz") as %Hinxz.
  iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  assert (Hyz : rtc F y z).
  { pose proof (dsf_functional F) as Hfun.
    destruct (path_confluent F Hfun x y (HRs _ _ Hinxy) z (HRs _ _ Hinxz))
      as [Hyz | Hzy]; first exact Hyz.
    destruct (decide (z = y)) as [->|Hne]; first reflexivity.
    exfalso.
    pose proof (path_id_decrease M F HdsfF HidF z y Hzy jz jy HMz HMy Hne).
    lia. }
  iMod (reaches_update _ _ F y z with "HRauth") as (R') "(HRauth & #Hyz & %HRs' & _)";
    [exact HRs | exact Hyz |].
  iMod ("Hclose" with "[Hback Hauth HRauth]") as "_";
    first by iApply ("Hback" with "[//] Hauth HRauth").
  by iModIntro.
Qed.

End uf_api.

(* ------------------------------------------------------------------------ *)
(* Re-reading (and, for [compress], rewriting) the single field of an
   already-registered content record, without going through any vertex:
   these accessors produce exactly the mask-changing fupd that the atomic
   rules ([ipat_PRecord_atomic], [imp_ERecordAccess_atomic],
   [imp_ERecordSet_atomic]) consume. All of them expose that one field
   and nothing else.

   For a [Root] record the field's value is pinned by the registration
   itself; for a [Link] record the caller learns that the loaded parent
   is a vertex strictly below the registered bound and inside the
   holder's class — even if the record's erstwhile vertex has moved
   on — and, symmetrically, may store any parent it can establish the
   same three facts about. *)

Section uf_acc.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ γc γn γR : gname.

Lemma uf_root_value_acc γ γc γn γR rc v lp (Φ : val → iProp Σ) :
  is_uf γ γc γn γR -∗
  CtRoot rc ↪[γc]□ CRoot v -∗
  isBlockLocs rc [lp] -∗
  ▷ Φ v -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ w -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ w).
Proof.
  iIntros "#Hinv #Hrc #Hlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_root) in "Hco".
  iDestruct "Hco" as (lv') "(#Hlocs' & #HP & Hlv)".
  iAssert (▷ ⌜[lp] = [lv']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists v.
  iSplitL "Hlv"; first by iFrame.
  iIntros "!> Hlv".
  iMod ("Hclose" with "[Hback Hlv]") as "_".
  { iApply "Hback". iNext. rewrite content_own_root.
    iExists lv'. iFrame "Hlocs' HP Hlv". }
  iModIntro. iApply "HΦ".
Qed.

(* The [Link] counterpart, and the single primitive the three link
   accessors below are built from: it borrows the [parent] field,
   reporting the vertex it currently holds, and takes back a field
   holding any vertex the caller can place strictly below the registered
   bound and inside the holder's class. Reading is the special case where
   the same vertex goes back. *)

Lemma uf_link_field_acc γ γc γn γR rc b h lp :
  is_uf γ γc γn γR -∗
  CtLink rc ↪[γc]□ CLink b h -∗
  isBlockLocs rc [lp] -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ (y : elem) jy,
    ▷ (lp ↦ #y) ∗ ▷ (vertex γ y jy ∗ reaches γR h y ∗ ⌜(jy < b)%Z⌝) ∗
    (∀ (z : elem) k, ⌜(k < b)%Z⌝ -∗ vertex γ z k -∗ reaches γR h z -∗
       lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> True).
Proof.
  iIntros "#Hinv #Hrc #Hlocs".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_link) in "Hco".
  iDestruct "Hco" as (lp' y jy) "(#Hlocs' & #HP & Hlp & #Hy & >%Hjy & #Hsnap)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists y, jy.
  iFrame "Hlp".
  iSplitR; first by iNext; iFrame "Hy Hsnap".
  iIntros (z k) "%Hk #Hz #Hhz Hlp".
  iMod ("Hclose" with "[Hback Hlp]") as "_".
  { iApply "Hback". iNext. rewrite content_own_link.
    iExists lp', z, k. by iFrame "Hlocs' HP Hlp Hz Hhz". }
  by iModIntro.
Qed.

Lemma uf_link_parent_acc γ γc γn γR rc b h lp (Φ : val → iProp Σ) :
  is_uf γ γc γn γR -∗
  CtLink rc ↪[γc]□ CLink b h -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < b)%Z⌝ -∗ reaches γR h y -∗ vertex γ y j -∗ Φ #y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ w -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ w).
Proof.
  iIntros "#Hinv #Hrc #Hlocs HΦ".
  iMod (uf_link_field_acc with "Hinv Hrc Hlocs") as (y jy) "(Hlp & Hy & Hback)".
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iDestruct "Hy" as "(#Hyv & #Hsnap & %Hjy)".
  iMod ("Hback" $! y jy with "[//] Hyv Hsnap Hlp") as "_".
  iModIntro. iApply ("HΦ" with "[//] Hsnap Hyv").
Qed.

(* The same accessor, with the loaded parent existentially quantified at
   [elem] rather than at [val]. [ipat_PRecord_atomic] — the rule
   behind [find]'s [Link { parent = y }] pattern — is [val]-shaped, but
   [compress] reads the field through an ordinary [let y = link.parent],
   i.e. [imp_ERecordAccess_atomic], whose loaded value is at the
   postcondition's own type. Only the witness of the existential
   differs. *)

Lemma uf_link_parent_acc_elem γ γc γn γR rc b h lp (Φ : elem → iProp Σ) :
  is_uf γ γc γn γR -∗
  CtLink rc ↪[γc]□ CLink b h -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < b)%Z⌝ -∗ reaches γR h y -∗ vertex γ y j -∗ Φ y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ y : elem, ▷ lp ↦ #y ∗ ▷ (lp ↦ #y -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ y).
Proof.
  iIntros "#Hinv #Hrc #Hlocs HΦ".
  iMod (uf_link_field_acc with "Hinv Hrc Hlocs") as (y jy) "(Hlp & Hy & Hback)".
  iModIntro. iExists y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iDestruct "Hy" as "(#Hyv & #Hsnap & %Hjy)".
  iMod ("Hback" $! y jy with "[//] Hyv Hsnap Hlp") as "_".
  iModIntro. iApply ("HΦ" with "[//] Hsnap Hyv").
Qed.

(* Rerouting a link's [parent] field, which is what path compression
   does. Unlike the CAS this is an ordinary (racy, non-atomic in the
   source, single-store in the semantics) write, so it is a plain
   accessor: borrow the field, hand back a new one. The obligation it
   levies is [content_own]'s link conjunct for the NEW parent — the
   caller must show the vertex it is rerouting to is registered, sits
   below the record's registered bound, and is already reachable from
   the record's holder. *)

Lemma uf_link_parent_set γ γc γn γR rc b h lp (z : elem) k (Φ : iProp Σ) :
  (k < b)%Z →
  is_uf γ γc γn γR -∗
  CtLink rc ↪[γc]□ CLink b h -∗
  isBlockLocs rc [lp] -∗
  vertex γ z k -∗
  reaches γR h z -∗
  ▷ Φ -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ).
Proof.
  iIntros (Hk) "#Hinv #Hrc #Hlocs #Hz #Hhz HΦ".
  iMod (uf_link_field_acc with "Hinv Hrc Hlocs") as (y jy) "(Hlp & _ & Hback)".
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hback" $! z k with "[//] Hz Hhz Hlp") as "_".
  by iModIntro.
Qed.

(* The CAS lemma: everything the [compare_and_set_spec] premise needs
   when the CASed cell is a vertex's content cell, packaged once. The
   caller supplies the vertex (through its ghost fragment and the block
   locations produced by [vertex_content_ptr]), the registration of the
   [Root] value it expects to see, and ownership of the fresh,
   unregistered replacement [cnew] described by [cinew]. On success
   [cnew] is registered — the caller gets the persistent fragment, and
   the invariant absorbs the replacement, growing the abstract graph by
   the new link's edge when [cinew] is a [CLink]; on failure the
   untouched [content_own] comes back, ready for another attempt.

   This is the one caller of [uf_inv_split] that needs more than the
   content cell: it extends the content registry, so it takes the
   registry map [C] as well. Everything else stays inside the frame. *)

Lemma uf_cas_fupd (Φ : bool → iProp Σ)
      γ γc γn γR z i lzc (rce : elem) vexp (cnew : content) cinew :
  (∀ b h, cinew = CLink b h → (b ≤ i)%Z ∧ h = z) →
  is_uf γ γc γn γR -∗
  z ↪[γ]□ i -∗
  (∃ li, isBlockLocs z [li; lzc]) -∗
  CtRoot rce ↪[γc]□ CRoot vexp -∗
  isBlock rce DfracDiscarded Mut -∗
  content_init γ γc cnew cinew -∗
  ▷ (∀ b : bool,
       (if b then cnew ↪[γc]□ cinew else content_init γ γc cnew cinew) -∗ Φ b) -∗
  |={⊤,⊤ ∖ ↑ufN}=>
    ∃ c cs (r rs : record) dq1 dq2 t,
      ⌜#(CtRoot rce) = VInline cs rs⌝ ∗
      ▷ lzc ↦ VInline c r ∗ ▷ isBlock r dq1 t ∗ ▷ isBlock rs dq2 Mut ∗
      ▷ (lzc ↦ (if locations.eqb r rs then #cnew else VInline c r) -∗
         isBlock r dq1 t -∗ isBlock rs dq2 Mut -∗
         |={⊤ ∖ ↑ufN,⊤}=> Φ (locations.eqb r rs)).
Proof.
  intros Hbound.
  iIntros "#Hinv #Hzfrag (%lzi & #Hzlocs) #Hrce #HrceP Hco' HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (C c0 ci0)
    "(%HCc0 & %Hbound0 & Hcauth & #Hc0 & Hlc & Hco0 & HC & Hframe)".
  iAssert (▷ (isBlock (content_loc c0) DfracDiscarded Mut ∗ content_own γ γc γR c0 ci0))%I
    with "[Hco0]" as "[#Hc0P Hco0]".
  { iNext. iApply (content_own_mut with "Hco0"). }
  iModIntro.
  iExists (content_tag c0), (content_tag (CtRoot rce)), (content_loc c0), rce,
          DfracDiscarded, DfracDiscarded, Mut.
  iSplitR; first by rewrite content_encode_inline.
  rewrite -{1}(content_encode_inline c0).
  iFrame "Hlc Hc0P HrceP".
  iNext.
  iIntros "Hlc' _ _".
  iDestruct (ghost_map_lookup with "Hcauth Hrce") as %HCe.
  destruct (locations.eqb_spec (content_loc c0) rce) as [Heq|Hne]; last first.

  { (* CAS failure: the cell still holds [c0]; close untouched and hand
       the fresh record's ownership back. *)
    iEval (rewrite -content_encode_inline) in "Hlc'".
    iMod ("Hclose" with "[Hcauth Hlc' Hco0 HC Hframe]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn γR C z i lzi lzc c0 c0 ci0
                with "Hcauth Hc0 Hzlocs Hlc' Hco0 HC Hframe"); done. }
    iModIntro. iApply ("HΦ" $! false with "Hco'"). }

  (* CAS success: the current content value sits at the very record the
     expected [Root] registration describes — so it IS that [Root] value
     ([content_own] owns each registered value's single field, ruling
     out a same-record [Link]), and [z] is presently a root. *)
  destruct c0 as [rc0|rc0]; simpl in Heq; subst rc0; last first.
  { iDestruct (big_sepM_lookup _ _ (CtRoot rce) (CRoot vexp) with "HC") as "Hcoe".
    { rewrite lookup_delete_ne; [exact HCe | discriminate]. }
    iDestruct (content_own_excl_loc with "Hco0 Hcoe") as "[]". done. }
  iDestruct (ghost_map_elem_agree with "Hc0 Hrce") as %->.

  (* The replacement is fresh: its single field is still owned by the
     caller, so no registered entry can be [cnew]. *)
  iAssert ⌜C !! cnew = None⌝%I with "[Hco' Hco0 HC]" as %HCnew.
  { destruct (C !! cnew) as [ci1|] eqn:HCnew; last done.
    iExFalso.
    destruct (decide (cnew = CtRoot rce)) as [->|Hnew].
    - iApply (content_init_own_excl_loc with "Hco' Hco0"); done.
    - iDestruct (big_sepM_lookup _ _ cnew ci1 with "HC") as "Hco1".
      { rewrite lookup_delete_ne; done. }
      iApply (content_init_own_excl_loc with "Hco' Hco1"); done. }
  iMod (ghost_map_insert cnew cinew with "Hcauth") as "[Hcauth Hnewfrag]";
    first exact HCnew.
  iMod (ghost_map_elem_persist with "Hnewfrag") as "#Hnewfrag".

  (* The absorbed [Root] value goes back into the registry's big star as
     an ordinary (now unreachable) entry. *)
  iAssert ([∗ map] c' ↦ ci' ∈ C, content_own γ γc γR c' ci')%I
    with "[Hco0 HC]" as "HC".
  { rewrite (big_sepM_delete _ C (CtRoot rce) (CRoot vexp)); last exact HCe.
    iFrame "Hco0 HC". }

  destruct cinew as [v'|b h].

  { (* The new content is a [Root]: [z] stays a root, [F] is unchanged.
       A root carries no [reaches], so [content_init] and [content_own]
       coincide here. *)
    destruct cnew as [rcn|rcn]; last by iDestruct "Hco'" as "[]".
    iEval (rewrite (content_init_root _ _ γR)) in "Hco'".
    iAssert ([∗ map] c' ↦ ci' ∈ delete (CtRoot rcn) (<[CtRoot rcn := CRoot v']> C),
               content_own γ γc γR c' ci')%I with "[HC]" as "HC".
    { rewrite delete_insert_eq (delete_id _ _ HCnew). iApply "HC". }
    iMod ("Hclose" with "[Hcauth Hlc' Hco' HC Hframe]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn γR (<[CtRoot rcn := CRoot v']> C) z i
                lzi lzc (CtRoot rce) (CtRoot rcn) (CRoot v')
                with "Hcauth Hnewfrag Hzlocs Hlc' Hco' HC Hframe");
        first [ reflexivity | apply lookup_insert_eq | discriminate ]. }
    iModIntro. iApply ("HΦ" $! true with "Hnewfrag"). }

  (* The new content is a [Link]: [z] stops being a root and [F] grows
     by the new edge. The registration's holder is forced to be [z] —
     the cell being CASed is [z]'s own — which is exactly what
     [uf_inv_reassemble_link] needs to mint the link's [reaches γR z y].
     That minting is a ghost update, hence the [iMod] before closing. *)
  destruct cnew as [rcn|rcn]; first by iDestruct "Hco'" as "[]".
  destruct (Hbound b h eq_refl) as [Hbi ->].
  (* The pure premises are supplied positionally rather than left to a
     trailing [first [...]]: unlike the [iApply]s elsewhere in this
     proof, [iMod] leaves the main goal open, so a [;]-chained tactic
     would be run against it too. *)
  iMod (uf_inv_reassemble_link γ γc γn γR C z i b lzi lzc (CtRoot rce) rcn
          eq_refl HCnew Hbi
          with "Hcauth Hnewfrag Hzlocs Hlc' Hco' HC Hframe")
    as "Hufinv".
  iMod ("Hclose" with "[Hufinv]") as "_"; first by iNext.
  iModIntro. iApply ("HΦ" $! true with "Hnewfrag").
Qed.

End uf_acc.
