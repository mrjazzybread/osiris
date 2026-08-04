From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map.
From stdpp Require Import relations.

From osiris Require Import osiris.
From osiris.stdlib.proofs Require Import atomic.
From osiris.examples Require Import og_ConcurrentUnionFind.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link UnionFind08GhostReach.

(** * Concurrent union-find

    This file contains the verification of the concurrent union-find data
    structure. *)

(* A vertex is a two-field record { id; content }. *)
Notation elem := record.

(* Field offsets of the vertex record. *)
Notation id_field := 0%Z (only parsing).
Notation content_field := 1%Z (only parsing).

Definition ufN : namespace := nroot .@ "concurrent_uf".

(* The static description of a content record; see below. The value
   carried by [CRoot] is the record's payload at allocation time — since a
   [Root] record's [value] field is never actually written again (see the
   comment above [content_own]), this value is permanent, and recording it
   in [cinfo] itself (rather than as a separate, ephemeral existential in
   [content_own]) is what lets [union]'s functional spec relate its
   returned [Some r] to a genuine, persistent fact (the discardable
   fragment [CtRoot rc ↪[γc]□ CRoot r]) instead of an unconstrained
   existential.

   [CLink] additionally records the *holder* [h]: the (unique) vertex
   whose content cell the link value was installed into. A link value is
   born in exactly one vertex's cell — [union]'s CAS — and is never
   moved to another (every CAS in the code swings a [Root] value out,
   never a [Link] in elsewhere), so the holder is as permanent as the
   bound and can live in the registration. It is what lets a reader of
   [x]'s content cell recognize, from the persistent fragment alone,
   that the link it loaded describes [x] itself — the key to [find]'s
   same-class postcondition. *)
Inductive cinfo :=
| CRoot (v : val)
| CLink (b : Z) (h : elem).

Section ConcurrentUnionFind.

(* [content] is the *key* of the content registry [γc]: the registry
   maps each content value ever stored in a vertex's content cell to
   its static description [cinfo]. *)

Inductive content := CtRoot (r : record) | CtLink (r : record).

Definition content_loc (c : content) : record :=
  match c with CtRoot rc | CtLink rc => rc end.

Definition content_root (c : content) : bool :=
  match c with CtRoot _ => true | CtLink _ => false end.

Definition content_tag (c : content) :=
  match c with CtRoot _ => "Root" | CtLink _ => "Link" end.

Global Instance Encode_content : Encode content :=
  {| encode' c := match c with
                  | CtRoot r => VInline "Root" r
                  | CtLink r => VInline "Link" r
                  end |}.

Global Instance Inline_content_Root : Inline "Root" content :=
  {| inline_apply := CtRoot; inline_encode := λ _, eq_refl |}.

Global Instance Inline_content_Link : Inline "Link" content :=
  {| inline_apply := CtLink; inline_encode := λ _, eq_refl |}.

(* The stored shape of a [content] value, for the rules (notably the
   CAS) that inspect the raw [VInline] representation. *)

Lemma content_encode_inline c :
  #c = VInline (content_tag c) (content_loc c).
Proof. rewrite encode_encode'. by destruct c. Qed.

Instance content_eq_decision : EqDecision content.
Proof. solve_decision. Defined.

Instance content_countable : Countable content.
Proof.
  apply (inj_countable' (λ c, (content_root c, content_loc c))
           (λ p, if (p.1 : bool) then CtRoot p.2 else CtLink p.2)).
  by intros [].
Defined.

Instance content_inhabited : Inhabited content := populate (CtRoot (Loc 0%Z)).

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ γc γn γR : gname.

(* ------------------------------------------------------------------------ *)
(* [RecordRepr] instances for the three record shapes allocated in this
   file ([Root{value}], [Link{parent}], the vertex's own {id;content}),
   so that [imp_record] can be used at their allocation sites instead of
   the raw tuple-level [imp_EInline]/[imp_ERecord]. *)

Record root_fields : Type := mkRootFields { root_value : val }.

Instance root_fields_repr : RecordRepr root_fields τ[val] Mut :=
  { repr_to_types r := r.(root_value);
    types_to_repr := λ v, {| root_value := v |};
    repr_id := λ v, eq_refl }.

Record link_fields : Type := mkLinkFields { link_parent : elem }.

Instance link_fields_repr : RecordRepr link_fields τ[elem] Mut :=
  { repr_to_types r := r.(link_parent);
    types_to_repr := λ p, {| link_parent := p |};
    repr_id := λ p, eq_refl }.

Record vertex_fields : Type := mkVertexFields { vertex_id_f : Z; vertex_content_f : val }.

Instance vertex_fields_repr : RecordRepr vertex_fields τ[Z; val] Mut :=
  { repr_to_types r := (r.(vertex_id_f), r.(vertex_content_f));
    types_to_repr := λ i c, {| vertex_id_f := i; vertex_content_f := c |};
    repr_id := λ '(i, c), eq_refl }.

(* ------------------------------------------------------------------------ *)
(* Representation predicates. *)

(* [vertex γ x i] is the persistent knowledge that [x] is a vertex of the
   structure with identifier [i]. *)

Definition vertex (γ : gname) x i : iProp Σ :=
  ∃ (li lc : locations.loc),
    x ↪[γ]□ i ∗
    isBlockLocs x [li; lc] ∗
    isBlock x DfracDiscarded Mut ∗
    li ↦□ #i.

Global Instance vertex_persistent γ x i : Persistent (vertex γ x i).
Proof. apply _. Qed.

(* [content_own γ γc γR c ci] is the invariant-owned footprint of the
   content value [c] as described by [ci]. The description is a
   *diagonal*: a [CtRoot] value is only ever registered as [CRoot v],
   and a [CtLink] value as [CLink b h].

   The link case ties the current parent [y] to the holder [h]'s
   equivalence class: [reaches γR h y]. *)

Definition content_own (γ γc γR : gname) (c : content) (ci : cinfo) : iProp Σ :=
  match c, ci with
  | CtRoot rc, CRoot v => rc ⤇ {| root_value := v |}
  | CtLink rc, CLink b h =>
      ∃ (y : elem) j, rc ⤇ {| link_parent := y |} ∗ vertex γ y j ∗
                      ⌜(j < b)%Z⌝ ∗ reaches γR h y
  | _, _ => False
  end.

(* [content_init γ γc c ci] is what the creator of a fresh content
   value can put together before it is installed anywhere.

   The [reaches] fact we find in [content_own] comes into existence at
   the installing CAS. [uf_cas_fupd] consumes a [content_init] and
   upgrades it internally. *)

Definition content_init (γ γc : gname) (c : content) (ci : cinfo) : iProp Σ :=
  match c, ci with
  | CtRoot rc, CRoot v => rc ⤇ {| root_value := v |}
  | CtLink rc, CLink b h =>
      ∃ (y : elem) j, rc ⤇ {| link_parent := y |} ∗ vertex γ y j ∗ ⌜(j < b)%Z⌝
  | _, _ => False
  end.

Lemma content_init_root γ γc γR c v :
  content_init γ γc c (CRoot v) ⊣⊢ content_own γ γc γR c (CRoot v).
Proof. destruct c; reflexivity. Qed.

(* The field-level view of a content record:
   [imp_ERecordAccess_atomic], [ipat_PRecord_var_atomic], and the CAS
   consume a single field's points-to. *)

Lemma content_own_root γ γc γR rc v :
  content_own γ γc γR (CtRoot rc) (CRoot v) ⊣⊢
  ∃ lv : locations.loc, isBlockLocs rc [lv] ∗ isBlock rc DfracDiscarded Mut ∗ lv ↦ v.
Proof.
  rewrite /content_own /ownRecord /ownBlock /=.
  iSplit.
  - iIntros "(%ls & #Hlocs & #HP & Hxs)".
    iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv) "[-> Hlv]".
    iEval (rewrite list_z.singleton_unfold) in "Hlocs".
    iExists lv. iFrame "Hlocs HP Hlv".
  - iIntros "(%lv & #Hlocs & #HP & Hlv)".
    iExists [lv]. iFrame "Hlocs HP".
    iApply big_opLZ.big_sepLZ2_singleton. iFrame "Hlv".
Qed.

Lemma content_own_link γ γc γR rc b h :
  content_own γ γc γR (CtLink rc) (CLink b h) ⊣⊢
  ∃ (lp : locations.loc) (y : elem) j,
    isBlockLocs rc [lp] ∗ isBlock rc DfracDiscarded Mut ∗ lp ↦ #y ∗ vertex γ y j ∗
    ⌜(j < b)%Z⌝ ∗ reaches γR h y.
Proof.
  rewrite /content_own /ownRecord /ownBlock /=.
  iSplit.
  - iIntros "(%y & %j & (%ls & #Hlocs & #HP & Hxs) & #Hy & %Hj & #Hsnap)".
    iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lp) "[-> Hlp]".
    iEval (rewrite list_z.singleton_unfold) in "Hlocs".
    iExists lp, y, j. iFrame "Hlocs HP Hlp Hy Hsnap". done.
  - iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj & #Hsnap)".
    iExists y, j. iFrame "Hy Hsnap". iSplit; last done.
    iExists [lp]. iFrame "Hlocs HP".
    iApply big_opLZ.big_sepLZ2_singleton. iFrame "Hlp".
Qed.

Lemma content_init_link γ γc rc b h :
  content_init γ γc (CtLink rc) (CLink b h) ⊣⊢
  ∃ (lp : locations.loc) (y : elem) j,
    isBlockLocs rc [lp] ∗ isBlock rc DfracDiscarded Mut ∗ lp ↦ #y ∗ vertex γ y j ∗
    ⌜(j < b)%Z⌝.
Proof.
  rewrite /content_init /ownRecord /ownBlock /=.
  iSplit.
  - iIntros "(%y & %j & (%ls & #Hlocs & #HP & Hxs) & #Hy & %Hj)".
    iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lp) "[-> Hlp]".
    iEval (rewrite list_z.singleton_unfold) in "Hlocs".
    iExists lp, y, j. iFrame "Hlocs HP Hlp Hy". done.
  - iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj)".
    iExists y, j. iFrame "Hy". iSplit; last done.
    iExists [lp]. iFrame "Hlocs HP".
    iApply big_opLZ.big_sepLZ2_singleton. iFrame "Hlp".
Qed.

(* [vertex_own γ γc γn γR F x i] is the invariant-owned footprint of
   the vertex [x]: its content cell, holding a registered content
   record whose description is compatible with [x]'s identifier,
   together with the exclusive ownership of [i] in the identifier
   registry [γn]. *)

(* [F] is the equivalence graph.

   It is decoupled from [content_own]'s [CLink] case: the physically
   stored parent need not be [F]'s own edge target, since path
   compression is free to reroute it.

   What ties the two together is [content_own]'s [reaches γR h y]
   conjunct, which places the stored parent in the holder's class while
   saying nothing about which edge it is. *)

Definition vertex_own (γ γc γn γR : gname) (F : elem → elem → Prop) x i : iProp Σ :=
  ∃ (li lc : locations.loc) (c : content) (ci : cinfo),
    isBlockLocs x [li; lc] ∗
    lc ↦ #c ∗
    c ↪[γc]□ ci ∗
    ⌜∀ b h, ci = CLink b h → (b ≤ i)%Z ∧ h = x⌝ ∗
    ⌜if content_root c then Root F x else ¬ Root F x⌝ ∗
    i ↪[γn] ().

(* [F]'s edges strictly decrease the identifier. This rules out cycles
   even when the target of a freshly-installed edge is no longer a root
   by the time the edge goes in. *)

Definition id_bounded (M : gmap elem Z) (F : elem → elem → Prop) : Prop :=
  ∀ w z iw iz, F w z → M !! w = Some iw → M !! z = Some iz → (iz < iw)%Z.

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
(* The [reaches] API. *)

(* Reflexivity: [rtc] is reflexive, so the pair is recordable at any
   open whatsoever. *)

Lemma reaches_refl γ γc γn γR x :
  is_uf γ γc γn γR ={⊤}=∗ reaches γR x x.
Proof.
  iIntros "#Hinv".
  iInv "Hinv" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HR & >%Hrep & >%HdsfF & >%HidF & >%HRs & HM & HC)"
    "Hclose".
  iMod (reaches_update _ _ F x x with "HR") as (R') "(HR & #Hxx & %HRs' & %Hsub)";
    [exact HRs | reflexivity |].
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HR HM HC]") as "_".
  { iNext. iExists M, C, N, R', F. by iFrame. }
  by iModIntro.
Qed.

(* Transitivity. *)

Lemma reaches_trans γ γc γn γR x y z :
  is_uf γ γc γn γR -∗ reaches γR x y -∗ reaches γR y z ={⊤}=∗ reaches γR x z.
Proof.
  iIntros "#Hinv #Hxy #Hyz".
  iInv "Hinv" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HR & >%Hrep & >%HdsfF & >%HidF & >%HRs & HM & HC)"
    "Hclose".
  iDestruct (reaches_lookup with "HR Hxy") as %Hxy.
  iDestruct (reaches_lookup with "HR Hyz") as %Hyz.
  iMod (reaches_update _ _ F x z with "HR") as (R') "(HR & #Hxz & %HRs' & %Hsub)";
    [exact HRs | by eapply rtc_trans; apply HRs |].
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HR HM HC]") as "_".
  { iNext. iExists M, C, N, R', F. by iFrame. }
  by iModIntro.
Qed.

(* ------------------------------------------------------------------------ *)
(* Working with the invariant. *)

Instance inhabited_elem : Inhabited elem.
Proof. by (unfold elem, record; simpl; apply _). Qed.

Instance inhabited_cinfo : Inhabited cinfo.
Proof. exact (populate (CLink 0%Z inhabitant)). Qed.

(* Every content record is a mutable block. *)

Lemma content_own_mut γ γc γR c ci :
  content_own γ γc γR c ci -∗
  isBlock (content_loc c) DfracDiscarded Mut ∗ content_own γ γc γR c ci.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b h]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv & #Hlocs & #HP & Hlv)".
    iSplitR; [iExact "HP"|]. iExists lv. by iFrame "#∗".
  - rewrite content_own_link.
    iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj & #Hsnap)".
    iSplitR; [iExact "HP"|]. iExists lp, y, j. by iFrame "#∗".
Qed.

(* Every content record has exactly one field.
   Callers that go on to read that field atomically need its location. *)

Lemma content_own_locs γ γc γR c ci :
  content_own γ γc γR c ci -∗
  (∃ lv : locations.loc, isBlockLocs (content_loc c) [lv]) ∗ content_own γ γc γR c ci.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b h]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv & #Hlocs & #HP & Hlv)".
    iSplitR; [by iExists lv|]. iExists lv. by iFrame "#∗".
  - rewrite content_own_link.
    iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj & #Hsnap)".
    iSplitR; [by iExists lp|]. iExists lp, y, j. by iFrame "#∗".
Qed.

(* Every content record owns exactly one field of its underlying records. *)

Lemma content_own_field γ γc γR c ci :
  content_own γ γc γR c ci -∗
  ∃ (lw : locations.loc) (w : val), isBlockLocs (content_loc c) [lw] ∗ lw ↦ w.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b h]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv0 & #H1 & _ & H2)". iExists lv0, v. iFrame "H1 H2".
  - rewrite content_own_link.
    iIntros "(%lp & %y0 & %j0 & #H1 & _ & H2 & _)". iExists lp, #y0. iFrame "H1 H2".
Qed.

(* The same field-ownership fact for a not-yet-installed value: it is what
   makes a fresh value provably unregistered at CAS time. *)

Lemma content_init_field γ γc c ci :
  content_init γ γc c ci -∗
  ∃ (lw : locations.loc) (w : val), isBlockLocs (content_loc c) [lw] ∗ lw ↦ w.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b h]; try (by iIntros "[]").
  - rewrite /content_init /ownRecord /ownBlock /=.
    iIntros "(%ls & #Hlocs & #HP & Hxs)".
    iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv) "[-> Hlv]".
    iEval (rewrite list_z.singleton_unfold) in "Hlocs".
    iExists lv, v. iFrame "Hlocs Hlv".
  - rewrite content_init_link.
    iIntros "(%lp & %y0 & %j0 & #H1 & _ & H2 & _)". iExists lp, #y0. iFrame "H1 H2".
Qed.

Lemma content_own_excl_loc γ γc γR c ci c' ci' :
  content_loc c = content_loc c' →
  content_own γ γc γR c ci -∗ content_own γ γc γR c' ci' -∗ False.
Proof.
  intros Heq.
  iIntros "Hco Hco'".
  iDestruct (content_own_field with "Hco") as (lw w) "[#Hlocs Hlw]".
  iDestruct (content_own_field with "Hco'") as (lw' w') "[#Hlocs' Hlw']".
  iEval (rewrite Heq) in "Hlocs".
  iDestruct (isBlockLocs_valid with "Hlocs' Hlocs") as %[= ->].
  iCombine "Hlw Hlw'" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

Lemma content_own_excl γ γc γR c ci ci' :
  content_own γ γc γR c ci -∗ content_own γ γc γR c ci' -∗ False.
Proof. by apply content_own_excl_loc. Qed.

Lemma content_init_own_excl_loc γ γc γR c ci c' ci' :
  content_loc c = content_loc c' →
  content_init γ γc c ci -∗ content_own γ γc γR c' ci' -∗ False.
Proof.
  intros Heq.
  iIntros "Hci Hco'".
  iDestruct (content_init_field with "Hci") as (lw w) "[#Hlocs Hlw]".
  iDestruct (content_own_field with "Hco'") as (lw' w') "[#Hlocs' Hlw']".
  iEval (rewrite Heq) in "Hlocs".
  iDestruct (isBlockLocs_valid with "Hlocs' Hlocs") as %[= ->].
  iCombine "Hlw Hlw'" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* The registered description's shape always matches the value's own
   tag. *)

Lemma content_own_tag γ γc γR c ci :
  content_own γ γc γR c ci -∗
  ⌜if content_root c then ∃ v, ci = CRoot v else ∃ b h, ci = CLink b h⌝.
Proof.
  destruct c; destruct ci; simpl;
    try (by iIntros "[]"); iIntros "_"; iPureIntro; eauto.
Qed.

(* [content_info γc x c j] is everything a reader of vertex [x]'s content
   cell (a vertex whose identifier is [j]) learns about the loaded value
   [c]: it is registered, with a description whose shape matches [c]'s
   own tag and whose bound (in the link case) is dominated by [j], and
   its underlying record is a mutable single-field block. *)

Definition content_info (γc : gname) (x : elem) (c : content) (j : Z) : iProp Σ :=
  isBlock (content_loc c) DfracDiscarded Mut ∗
  (∃ lv : locations.loc, isBlockLocs (content_loc c) [lv]) ∗
  match c with
  | CtRoot _ => ∃ v, c ↪[γc]□ CRoot v
  | CtLink _ => ∃ b, c ↪[γc]□ CLink b x ∗ ⌜(b ≤ j)%Z⌝
  end.

Global Instance content_info_persistent γc x c j :
  Persistent (content_info γc x c j).
Proof. destruct c; apply _. Qed.

Lemma content_own_info γ γc γR x c ci j :
  (∀ b h, ci = CLink b h → (b ≤ j)%Z ∧ h = x) →
  c ↪[γc]□ ci -∗
  content_own γ γc γR c ci -∗
  content_info γc x c j ∗ content_own γ γc γR c ci.
Proof.
  intros Hbound.
  iIntros "#Hrc Hco".
  iDestruct (content_own_tag with "Hco") as %Htag.
  iDestruct (content_own_mut with "Hco") as "[#HP Hco]".
  iDestruct (content_own_locs with "Hco") as "[#Hlocs Hco]".
  iFrame "Hco". rewrite /content_info. iFrame "HP Hlocs".
  destruct c as [rc|rc]; simpl in Htag.
  - destruct Htag as [v ->]. by iExists v.
  - destruct Htag as (b & h & ->).
    destruct (Hbound b h eq_refl) as [Hb ->].
    iExists b. iFrame "Hrc". by iPureIntro.
Qed.

(* The same argument one level up, for vertices: a registered vertex owns
   its own [content] cell, so a caller still holding that cell — as
   [make] does for the record it has just allocated — knows the vertex is
   not registered yet. *)

Lemma vertex_own_fresh_ne γ γc γn γR F x i li lc w :
  isBlockLocs x [li; lc] -∗ lc ↦ w -∗ vertex_own γ γc γn γR F x i -∗ False.
Proof.
  iIntros "#Hlocs Hlc Hvo".
  iDestruct "Hvo" as (li' lc' rc ci) "(#Hlocs' & Hlc' & _)".
  iDestruct (isBlockLocs_valid with "Hlocs' Hlocs") as %[= -> ->].
  iCombine "Hlc Hlc'" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* [uf_inv_split] singles out one vertex's footprint: given [z]'s
   persistent [vertex] components, it hands back the content cell
   [lzc ↦ cval ci rc] of [z], the description [ci] of the content record
   [rc] it currently holds, and everything else the invariant owns, with
   [z] and [rc] deleted from the two big separating conjunctions.
   [uf_inv_reassemble] is the converse: it rebuilds [uf_inv] from those
   pieces, for a possibly *different* content record — which is exactly
   what a successful CAS produces. *)

Lemma uf_inv_split γ γc γn γR z j lzi lzc :
  z ↪[γ]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ γc γn γR -∗
  ◇ ∃ (M : gmap elem Z) (C : gmap content cinfo) (N : gmap Z unit)
      (R : gset (elem * elem)) F c ci,
      ⌜M !! z = Some j⌝ ∗ ⌜C !! c = Some ci⌝ ∗
      ⌜∀ b h, ci = CLink b h → (b ≤ j)%Z ∧ h = z⌝ ∗
      ⌜if content_root c then Root F z else ¬ Root F z⌝ ∗
      ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
      ⌜DSF F (dom M)⌝ ∗ ⌜id_bounded M F⌝ ∗ ⌜reaches_sound R F⌝ ∗
      ghost_map_auth γ 1 M ∗ ghost_map_auth γc 1 C ∗ ghost_map_auth γn 1 N ∗
      own γR (● R) ∗
      c ↪[γc]□ ci ∗
      ▷ (lzc ↦ #c) ∗ ▷ (j ↪[γn] ()) ∗
      ▷ content_own γ γc γR c ci ∗
      ▷ ([∗ map] x ↦ i ∈ delete z M, vertex_own γ γc γn γR F x i) ∗
      ▷ ([∗ map] c' ↦ ci' ∈ delete c C, content_own γ γc γR c' ci').
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
  iExists M, C, N, R, F, c, ci.
  iModIntro.
  do 8 (iSplitR; first done).
  iFrame "Hauth Hcauth Hnauth HRauth Hrc Hlc Htok Hco HM HC".
Qed.

Lemma uf_inv_reassemble γ γc γn γR (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) (R : gset (elem * elem)) F z j lzi lzc c ci :
  M !! z = Some j →
  C !! c = Some ci →
  (∀ b h, ci = CLink b h → (b ≤ j)%Z ∧ h = z) →
  (if content_root c then Root F z else ¬ Root F z) →
  (∀ x i, M !! x = Some i → representable i) →
  DSF F (dom M) →
  id_bounded M F →
  reaches_sound R F →
  ghost_map_auth γ 1 M -∗
  ghost_map_auth γc 1 C -∗
  ghost_map_auth γn 1 N -∗
  own γR (● R) -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #c -∗
  c ↪[γc]□ ci -∗
  j ↪[γn] () -∗
  content_own γ γc γR c ci -∗
  ([∗ map] x ↦ i ∈ delete z M, vertex_own γ γc γn γR F x i) -∗
  ([∗ map] c' ↦ ci' ∈ delete c C, content_own γ γc γR c' ci') -∗
  uf_inv γ γc γn γR.
Proof.
  intros HMz HCrc Hbound HFz Hrep HdsfF HidF HRs.
  iIntros "Hauth Hcauth Hnauth HRauth #Hzlocs Hlc #Hrc Htok Hco HM HC".
  iExists M, C, N, R, F. iFrame "Hauth Hcauth Hnauth HRauth".
  do 4 (iSplitR; first done).
  iSplitL "HM Hlc Htok".
  { rewrite (big_sepM_delete _ M z j); last exact HMz.
    iSplitL "Hlc Htok".
    { iExists lzi, lzc, c, ci. by iFrame "Hzlocs Hlc Hrc Htok". }
    iApply "HM". }
  rewrite (big_sepM_delete _ C c ci); last exact HCrc.
  iFrame "Hco HC".
Qed.

(* [find] and [update] also reach a content record *directly*, without
   going through a vertex: they re-read a field of a record whose
   registration [rc ↪[γc]□ ci] they already hold. Nothing about the
   invariant changes across such a step, so this one is an ordinary
   accessor — borrow [content_own], hand it back — rather than a
   split/reassemble pair. *)

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

(* The third member of the reassembly family, for [make]: rather than
   putting an existing vertex back, this registers a brand new one — with
   its own brand new content record — extending both authoritative maps.
   Widening [M] is where the pure invariants have to be re-established,
   which is the bulk of the proof: [representable] for the new id, [DSF]
   by covariance in the domain, and [id_bounded] because [F] confines its
   edges to the *old* domain and so has none touching [x] at all. *)

Lemma uf_inv_insert_vertex γ γc γn γR (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) (R : gset (elem * elem)) F x i li lc c v :
  M !! x = None →
  C !! c = None →
  representable i →
  (∀ w iw, M !! w = Some iw → representable iw) →
  DSF F (dom M) →
  id_bounded M F →
  reaches_sound R F →
  ghost_map_auth γ 1 (<[x := i]> M) -∗
  ghost_map_auth γc 1 (<[c := CRoot v]> C) -∗
  ghost_map_auth γn 1 N -∗
  own γR (● R) -∗
  isBlockLocs x [li; lc] -∗
  lc ↦ #c -∗
  c ↪[γc]□ CRoot v -∗
  i ↪[γn] () -∗
  content_own γ γc γR c (CRoot v) -∗
  ([∗ map] w ↦ iw ∈ M, vertex_own γ γc γn γR F w iw) -∗
  ([∗ map] c ↦ ci ∈ C, content_own γ γc γR c ci) -∗
  uf_inv γ γc γn γR.
Proof.
  intros HMx HCrc Hrepi Hrep HdsfF HidF HRs.
  iIntros "Hauth Hcauth Hnauth HRauth #Hxlocs Hlc #Hrc Htok Hco HM HC".
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

(* Identifiers are injective: a vertex exclusively owns its own entry in
   the identifier registry [γn], so two distinct vertices cannot both
   claim the same identifier. *)

Lemma vertex_own_id_ne γ γc γn γR F a w i :
  vertex_own γ γc γn γR F a i -∗ vertex_own γ γc γn γR F w i -∗ False.
Proof.
  iIntros "(% & % & % & % & _ & _ & _ & _ & _ & Htoka)".
  iIntros "(% & % & % & % & _ & _ & _ & _ & _ & Htokw)".
  iCombine "Htoka Htokw" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* What [union]'s [assert (x.id <> y.id)] needs: distinct vertices have
   distinct — and, from [uf_inv]'s own [representable] conjunct, machine-
   comparable — identifiers. The invariant is handed back unchanged. *)

Lemma uf_inv_ids_distinct γ γc γn γR (a w : elem) (ia iw : Z) :
  a ≠ w →
  a ↪[γ]□ ia -∗ w ↪[γ]□ iw -∗ ▷ uf_inv γ γc γn γR -∗
  ◇ (⌜ia ≠ iw ∧ representable ia ∧ representable iw⌝ ∗ ▷ uf_inv γ γc γn γR).
Proof.
  intros Hne.
  iIntros "#Ha #Hw H".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  iDestruct (ghost_map_lookup with "Hauth Ha") as %HMa.
  iDestruct (ghost_map_lookup with "Hauth Hw") as %HMw.
  assert (HMw' : delete a M !! w = Some iw) by (rewrite lookup_delete_ne; done).
  rewrite (big_sepM_delete _ M a ia); last exact HMa.
  iDestruct "HM" as "[Hvoa HM]".
  rewrite (big_sepM_delete _ (delete a M) w iw); last exact HMw'.
  iDestruct "HM" as "[Hvow HM]".
  destruct (decide (ia = iw)) as [->|Hij].
  { iAssert (▷ False)%I with "[Hvoa Hvow]" as ">[]".
    iNext. iApply (vertex_own_id_ne with "Hvoa Hvow"). }
  iModIntro.
  iSplit.
  { iPureIntro. split; [exact Hij | split; [exact (Hrep a ia HMa) | exact (Hrep w iw HMw)]]. }
  iNext.
  iExists M, C, N, R, F. iFrame "Hauth Hcauth Hnauth HRauth HC".
  do 4 (iSplitR; first done).
  rewrite (big_sepM_delete _ M a ia); last exact HMa.
  rewrite (big_sepM_delete _ (delete a M) w iw); last exact HMw'.
  iFrame "Hvoa Hvow HM".
Qed.

(* ------------------------------------------------------------------------ *)
(* Graph-theoretic facts about growing [F] by one edge. These feed the
   linking case of the CAS lemma [uf_cas_fupd] below. *)

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

(* In a functional graph every vertex has at most one outgoing edge, so
   the vertices reachable from a common origin are linearly ordered:
   two paths out of [x] cannot diverge. This is what [compress] needs in
   order to relate the vertex it is rerouting *to* against the one it
   currently points at — see [reaches_sibling]. *)

Lemma path_confluent (F : elem -> elem -> Prop) :
  Functional F ->
  forall x y, rtc F x y -> forall z, rtc F x z -> rtc F y z \/ rtc F z y.
Proof.
  intros [Hfun] x y Hxy.
  induction Hxy as [x | x x' y HF Hx'y IH]; intros z Hxz.
  - left. exact Hxz.
  - apply rtc_inv in Hxz as [-> | (x'' & HF' & Hx''z)].
    + right. eapply rtc_l; [exact HF | exact Hx'y].
    + assert (x' = x'') as -> by (eapply Hfun; eassumption).
      exact (IH z Hx''z).
Qed.

(* The generalized edge-addition lemma the linking CAS actually needs:
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
   graph via [link a y']: this is what lets the linking CAS re-close the
   invariant's untouched vertices after registering [a]'s own tag flip
   (the ONLY entry that actually needs [link]'s new edge). *)

Lemma vertex_own_widen_link γ γc γn γR (F0 : elem -> elem -> Prop) (a y' : elem) (M' : gmap elem Z) :
  M' !! a = None ->
  ([∗ map] w ↦ i ∈ M', vertex_own γ γc γn γR F0 w i) -∗
  [∗ map] w ↦ i ∈ M', vertex_own γ γc γn γR (link F0 a y') w i.
Proof.
  iIntros (Ha) "HM".
  iApply (big_sepM_impl with "HM").
  iIntros "!>" (w i Hw) "Hvo".
  iDestruct "Hvo" as (li lc c ci) "(Hlocs & Hlc & Hrc & %Hb & %HF & Htok)".
  iExists li, lc, c, ci. iFrame "Hlocs Hlc Hrc Htok".
  iSplit; first done.
  iPureIntro.
  assert (Hne : w ≠ a) by (intros ->; congruence).
  destruct (content_root c).
  - apply (root_link_ne F0 a y' w Hne). exact HF.
  - intros Hroot. apply HF. apply (root_link_ne F0 a y' w Hne). exact Hroot.
Qed.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API. The lemmas from here to [uf_cas_fupd] are the
   only interface the function proofs use: they speak of [vertex],
   [is_uf], [content_own] and the persistent registration fragments —
   never of block locations or of the invariant's internals. *)

Lemma vertex_frag γ x i : vertex γ x i -∗ x ↪[γ]□ i.
Proof. iIntros "(% & % & $ & _)". Qed.

Lemma vertex_mut γ x i : vertex γ x i -∗ isBlock x DfracDiscarded Mut.
Proof. iIntros "(% & % & _ & _ & $ & _)". Qed.

(* The counterpart of [uf_inv_reassemble] for a successful linking CAS —
   the one place where the abstract graph [F] grows: vertex [z], a root
   with identifier [i], has just had its content cell swung to the brand
   new link value [CtLink rcn], registered with bound [b ≤ i] and holder
   [z] (the cell the value is going into is [z]'s own — that is what
   makes [z] the holder). The new record's [content_init] already carries
   the parent [y] and the strict bound [jy < b], which is everything
   [dsf_link_general] needs to justify widening [F] by the edge [z → y]
   without re-checking [y]'s root-status.

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

Lemma uf_inv_reassemble_link γ γc γn γR (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) (R : gset (elem * elem)) F z i b lzi lzc (rcn : elem) :
  M !! z = Some i →
  C !! CtLink rcn = None →
  Root F z →
  (b ≤ i)%Z →
  (∀ x ix, M !! x = Some ix → representable ix) →
  DSF F (dom M) →
  id_bounded M F →
  reaches_sound R F →
  ghost_map_auth γ 1 M -∗
  ghost_map_auth γc 1 (<[CtLink rcn := CLink b z]> C) -∗
  ghost_map_auth γn 1 N -∗
  own γR (● R) -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #(CtLink rcn) -∗
  CtLink rcn ↪[γc]□ CLink b z -∗
  i ↪[γn] () -∗
  content_init γ γc (CtLink rcn) (CLink b z) -∗
  ([∗ map] x ↦ ix ∈ delete z M, vertex_own γ γc γn γR F x ix) -∗
  ([∗ map] c ↦ ci ∈ C, content_own γ γc γR c ci) -∗
  |==> uf_inv γ γc γn γR.
Proof.
  intros HMz HCr Hroot Hbi Hrep HdsfF HidF HRs.
  iIntros "Hauth Hcauth Hnauth HRauth #Hzlocs Hlc #Hr Htok Hco HM HC".
  (* Peek at the new link's parent [y]: a registered vertex whose
     identifier sits strictly below [b], hence strictly below [i]. *)
  iDestruct "Hco" as (y jy) "(Hrec & #Hy & %Hjy)".
  iDestruct (vertex_frag with "Hy") as "#Hyfrag".
  iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
  assert (Hzy : z ≠ y).
  { intros ->. rewrite HMz in HMy. simplify_eq. lia. }
  pose proof (dsf_link_general M F z y i jy HdsfF HidF HMz HMy Hroot
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
  { rewrite (big_sepM_delete _ M z i); last exact HMz.
    iSplitL "Hlc Htok".
    { iExists lzi, lzc, (CtLink rcn), (CLink b z).
      iFrame "Hzlocs Hlc Hr Htok".
      iSplit.
      { iPureIntro. intros b' h' Hb'. injection Hb' as -> ->. done. }
      iPureIntro. simpl. intros [Hr']. eapply (Hr' y). right. done. }
    iApply (vertex_own_widen_link with "HM").
    rewrite lookup_delete_eq. done. }
  rewrite big_sepM_insert; last exact HCr.
  iSplitL "Hrec".
  { iExists y, jy. by iFrame "Hrec Hy Hzy". }
  iApply "HC".
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

  (* Register the vertex and its content record in the invariant. Neither
     can be registered already: an existing entry would own the very
     field we are still holding. *)
  iInv "Hinv" as "H" "Hclose".
  iDestruct "H" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs &
      HM & HC)".
  destruct (M !! r) as [ix|] eqn:HMx.
  { iDestruct (big_sepM_lookup _ _ r ix with "HM") as "Hvo"; first exact HMx.
    iAssert (▷ False)%I with "[Hlc Hvo]" as ">[]".
    iNext. iApply (vertex_own_fresh_ne with "Hxlocs Hlc Hvo"). }
  destruct (C !! c) as [ci0|] eqn:HCc.
  { iDestruct (big_sepM_lookup _ _ _ ci0 with "HC") as "Hco0"; first exact HCc.
    iAssert (▷ False)%I with "[Hco Hco0]" as ">[]".
    iNext. iApply (content_own_excl γ γc γR c (CRoot v) ci0 with "Hco Hco0"). }
  iMod (ghost_map_insert c (CRoot v) with "Hcauth") as "[Hcauth Hcfrag]";
    first exact HCc.
  iMod (ghost_map_elem_persist with "Hcfrag") as "#Hcfrag".
  iMod (ghost_map_insert r i with "Hauth") as "[Hauth Hxfrag]";
    first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth Hlc Htok Hco HM HC]") as "_".
  { iNext.
    iApply (uf_inv_insert_vertex
              with "Hauth Hcauth Hnauth HRauth Hxlocs Hlc Hcfrag Htok Hco HM HC");
      try done. }
  iModIntro.
  iExists li, lc. iFrame "Hxfrag Hxlocs HxP Hli".
Qed.

(* Atomically reading a vertex's content cell: the caller supplies a
   proof that the scrutinee evaluates to the vertex and receives the
   loaded value's [content_info] snapshot. *)

Lemma read_vertex {ζ : exn → iProp Σ} {Ψ η} γ γc γn γR z j e :
  is_uf γ γc γn γR -∗
  vertex γ z j -∗
  imp (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ z' : elem, ⌜z' = z⌝ }} -∗
  imp (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ λ c : content, content_info γc z c j }}.
Proof.
  iIntros "#Hinv #Hz He".
  iDestruct "Hz" as (lzi lzc) "(#Hzfrag & #Hzlocs & #HzP & #Hzli)".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lzi; lzc] z
            with "Hzlocs He []").
  { list_z.length; lia. }
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (M C N R F c ci)
    "(%HMz & %HCc & %Hbound & %HFz & %Hrep & %HdsfF & %HidF & %HRs &
      Hauth & Hcauth & Hnauth & HRauth & #Hrc & Hlc & Htok & Hco & HM & HC)".
  iModIntro.
  iExists c.
  iSplitL "Hlc"; first by iFrame.
  iIntros "!> Hlc".
  iDestruct (content_own_info with "Hrc Hco") as "[#Hinfo Hco]"; first exact Hbound.
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth Hlc Htok Hco HM HC]") as "_".
  { iNext.
    iApply (uf_inv_reassemble γ γc γn γR M C N R F z j lzi lzc c ci
              with "Hauth Hcauth Hnauth HRauth Hzlocs Hlc Hrc Htok Hco HM HC");
      done. }
  iModIntro. iExact "Hinfo".
Qed.

(* Reading a vertex's immutable [id] field, through the persistent
   points-to that [vertex] carries. *)

Lemma read_vertex_id {ζ : exn → iProp Σ} {Ψ η} γ z i e :
  vertex γ z i -∗
  imp (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ z' : elem, ⌜z' = z⌝ }} -∗
  imp (eval η (ERecordAccess e id_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ λ n : Z, ⌜n = i⌝ }}.
Proof.
  iIntros "#Hz He".
  iDestruct "Hz" as (li lc) "(_ & #Hlocs & _ & #Hli)".
  iApply (imp_ERecordAccess_pers id_field _ [li; lc] _ i with "Hlocs He [] []").
  { by vm_compute. }
  { iExact "Hli". }
  { iIntros "!> _". done. }
Qed.

(* The location of a vertex's content cell, as a first-class value —
   this is the [Atomic.Loc.t] handed to the CAS. The postcondition is
   exactly the shape [uf_cas_fupd] wants back. *)

Lemma vertex_content_ptr {ζ : exn → iProp Σ} {Ψ η} γ z i e :
  vertex γ z i -∗
  imp (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ z' : elem, ⌜z' = z⌝ }} -∗
  imp (eval η (EAtomicLoc e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ λ l : locations.loc, ∃ li, isBlockLocs z [li; l] }}.
Proof.
  iIntros "#Hz He".
  iDestruct "Hz" as (li lc) "(_ & #Hlocs & _ & _)".
  iApply (imp_EAtomicLoc content_field z [li; lc] with "Hlocs He []").
  { list_z.length; lia. }
  iNext. iExists li. iExact "Hlocs".
Qed.

(* Distinct vertices have distinct — and machine-comparable —
   identifiers; the folded, vertex-level form of [uf_inv_ids_distinct]. *)

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
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ids_distinct with "Hafrag Hwfrag H") as "[%Hids H]"; first exact Hne.
  iMod ("Hclose" with "H") as "_".
  by iModIntro.
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
  iInv "Hinv" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs & HM & HC)"
    "Hclose".
  iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth HM HC]") as "_".
  { iNext. iExists M, C, N, R, F. by iFrame. }
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
  iInv "Hinv" as (M C N R F)
    "(>Hauth & >Hcauth & >Hnauth & >HRauth & >%Hrep & >%HdsfF & >%HidF & >%HRs & HM & HC)"
    "Hclose".
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
  iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth HM HC]") as "_".
  { iNext. iExists M, C, N, R', F. by iFrame. }
  by iModIntro.
Qed.

(* Re-reading the single field of an already-registered content record,
   without going through any vertex: these accessors produce exactly the
   mask-changing fupd that the atomic rules ([ipat_PRecord_var_atomic],
   [imp_ERecordAccess_atomic]) consume. For a [Root] record the field's
   value is pinned by the registration itself; for a [Link] record the
   caller learns that the loaded parent is a vertex strictly below the
   registered bound — even if the record's erstwhile vertex has moved
   on. *)

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

Lemma uf_link_parent_acc γ γc γn γR rc b h lp (Φ : val → iProp Σ) :
  is_uf γ γc γn γR -∗
  CtLink rc ↪[γc]□ CLink b h -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < b)%Z⌝ -∗ reaches γR h y -∗ vertex γ y j -∗ Φ #y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ w -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ w).
Proof.
  iIntros "#Hinv #Hrc #Hlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_link) in "Hco".
  iDestruct "Hco" as (lp' y j) "(#Hlocs' & #HP & Hlp & #Hy & >%Hj & #Hsnap)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hclose" with "[Hback Hlp]") as "_".
  { iApply "Hback". iNext. rewrite content_own_link.
    iExists lp', y, j. by iFrame "Hlocs' HP Hlp Hy Hsnap". }
  iModIntro. iApply ("HΦ" with "[//] Hsnap Hy").
Qed.

(* The same accessor, with the loaded parent existentially quantified at
   [elem] rather than at [val]. [ipat_PRecord_var_atomic] — the rule
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
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_link) in "Hco".
  iDestruct "Hco" as (lp' y j) "(#Hlocs' & #HP & Hlp & #Hy & >%Hj & #Hsnap)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hclose" with "[Hback Hlp]") as "_".
  { iApply "Hback". iNext. rewrite content_own_link.
    iExists lp', y, j. by iFrame "Hlocs' HP Hlp Hy Hsnap". }
  iModIntro. iApply ("HΦ" with "[//] Hsnap Hy").
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
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_link) in "Hco".
  iDestruct "Hco" as (lp' y j) "(#Hlocs' & #HP & Hlp & #Hy & >%Hj & #Hsnap)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hclose" with "[Hback Hlp]") as "_".
  { iApply "Hback". iNext. rewrite content_own_link.
    iExists lp', z, k. by iFrame "Hlocs' HP Hlp Hz Hhz". }
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
   untouched [content_own] comes back, ready for another attempt. *)

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
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (M C N R F c0 ci0)
    "(%HMz & %HCc0 & %Hbound0 & %HFz & %Hrep & %HdsfF & %HidF & %HRs &
      Hauth & Hcauth & Hnauth & HRauth & #Hc0 & Hlc & Htok & Hco0 & HM & HC)".
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
    iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth Hlc' Htok Hco0 HM HC]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn γR M C N R F z i lzi lzc c0 ci0
                with "Hauth Hcauth Hnauth HRauth Hzlocs Hlc' Hc0 Htok Hco0 HM HC");
        done. }
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
  simpl in HFz.

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
    iMod ("Hclose" with "[Hauth Hcauth Hnauth HRauth Hlc' Htok Hco' HM HC]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn γR M (<[CtRoot rcn := CRoot v']> C) N R F z i
                lzi lzc (CtRoot rcn) (CRoot v')
                with "Hauth Hcauth Hnauth HRauth Hzlocs Hlc' Hnewfrag Htok Hco' HM HC");
        first [ done | apply lookup_insert_eq | discriminate | assumption ]. }
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
  iMod (uf_inv_reassemble_link γ γc γn γR M C N R F z i b lzi lzc rcn
          HMz HCnew HFz Hbi Hrep HdsfF HidF HRs
          with "Hauth Hcauth Hnauth HRauth Hzlocs Hlc' Hnewfrag Htok Hco' HM HC")
    as "Hufinv".
  iMod ("Hclose" with "[Hufinv]") as "_"; first by iNext.
  iModIntro. iApply ("HΦ" $! true with "Hnewfrag").
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
    {{ λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec }}.
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

Definition fresh_spec (γ γc γn γR : gname) (u : unit) (m : microvx) : iProp Σ :=
  is_uf γ γc γn γR -∗
  imp m {{ λ i : Z, i ↪[γn] () ∗ ⌜representable i⌝ }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [make]. *)

(* [make v] returns a fresh vertex of the structure. *)

Definition make_spec (γ γc γn γR : gname) (v : val) (m : microvx) : iProp Σ :=
  is_uf γ γc γn γR -∗
  imp m {{ λ x : elem, ∃ i, vertex γ x i }}.

(* [record]/[ERecord] allocations must fit within [max_array_length]. *)
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof γ γc γn γR η :
  path_spec ["G"; "fresh"] (λ fresh, □ iSpec τ[unit] fresh (fresh_spec γ γc γn γR))%I η -∗
  imp (eval η (EAnonFun __make)) {{ λ c, □ iSpec τ[val] c (make_spec γ γc γn γR) }}.
Proof.
  iIntros "#HG".
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  iIntros "#Hinv".
  iApply imp_please; iNext.

  (* Goal: [ let id = G.fresh() and content = Root { value = v } in ... ] *)
  imp_let $! (λ i : Z, i ↪[γn] () ∗ ⌜representable i⌝)%I
          $! (λ r : content, content_own γ γc γR r (CRoot v))%I.
  { (* [G.fresh ()], through the [fresh_spec] hypothesis. *)
    imp_app τ[unit].
    iIntros "Hm".
    unfold fresh_spec.
    iApply ("Hm" with "Hinv"). }
  { (* [Root { value = v }]: allocating the content record produces
       exactly the invariant's own [content_own] for it, so there is
       nothing to unfold. [A] is given explicitly ([root_fields], not
       [link_fields]): both are single-field [RecordRepr] instances, so
       leaving it to bare [imp_record]'s typeclass search is ambiguous. *)
    imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (a rc) "[Htok %Hrepa] Hco".
  simpl.

  (* Goal: [ { id; content } ]. Allocate the vertex, then register it (and
     its content record) in the invariant; this last step is a pure ghost
     update, performed under [imp_fupd]. *)
  iApply imp_fupd.
  iApply (imp_wand with "[]").
  { imp_record. }
  rewrite -encode_encode'.
  simpl. iIntros (x) "H".
  iDestruct "H" as (i c) "(Hown & -> & ->)".
  iMod (register_vertex with "Hinv Htok Hco Hown") as "#Hv"; first exact Hrepa.
  iModIntro. iExists a. iExact "Hv".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [find]. *)

(* [find x] returns a vertex [z] of the structure that lies in the same
   equivalence class as [x] — [reaches γR x z] — and whose identifier is
   at most [x]'s.

   The class guarantee is what makes the result usable: without it,
   [find] could return any vertex at all and still meet the identifier
   bound. It does NOT come from a linearizability argument; it is
   assembled out of facts each individual read can honestly establish,
   exactly as in [set]/[update]/[union]:

   - the [Root] case returns [x] itself, and [reaches] is reflexive;
   - the [Link] case reads [x]'s content cell, learns from the
     registration [CtLink rc ↪[γc]□ CLink b x] that the link value it
     loaded is one that was installed into *[x]'s own* cell (that is the
     holder component), and therefore that the parent [y] it then
     re-reads satisfies [reaches γR x y]; the recursive call's own
     [reaches γR y z] composes with it by [reaches_trans].

   Note where the racy re-read is absorbed: the parent field is read a
   second time, and by then a concurrent path compression may have
   swung it to a *different* vertex than the one seen a moment earlier.
   That is harmless precisely because [content_own] carries
   [reaches γR h y] for whatever parent [y] the field currently holds —
   the fact is about the record's present contents, re-established by
   whoever wrote them, not a stale observation of ours. *)

Definition find_spec (γ γc γn γR : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    imp m {{ λ z : elem, ∃ j, vertex γ z j ∗ ⌜(j ≤ i)%Z⌝ ∗ reaches γR x z }}.

(* Proof outline:
   1. Read [x.content] through [read_vertex], obtaining the loaded
      value's persistent [content_info] snapshot — including, in the
      link case, that [x] is the registered holder.
   2. Case on the loaded value:
      - [CtRoot]: the first branch matches with a wildcard sub-pattern
        (no field read) and returns [x]; conclude with [j := i] and
        [reaches_refl].
      - [CtLink]: the first branch is refuted; the second branch
        pattern-matches [{ parent = y }] against the link record,
        *re-reading* the racy [parent] field. [ipat_PRecord_var_atomic]
        performs this single field load under [uf_inv], with
        [uf_link_parent_acc] supplying its fupd: even if [x] has moved
        on, the registration [CtLink rc ↪[γc]□ CLink b x] guarantees the
        field holds some [y] with
        [vertex γ y j ∗ j < b ∗ reaches γR x y]. Recurse through the
        [in_env "find"] hypothesis and conclude by transitivity
        ([j < b ≤ i]) and [reaches_trans]. *)

Lemma find_proof γ γc γn γR η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))))
    {{ λ c, □ iSpec τ[elem] c (find_spec γ γc γn γR) }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_spec.
  iIntros (i) "#Hinv #Hx".
  (* [reaches γR x x], minted up front: the [Root] branch needs it, and
     that branch's postcondition is a bare assertion with no fancy update
     left to run a ghost step under. *)
  iMod (reaches_refl with "Hinv") as "#Hxx".
  iApply imp_please; iNext.

  (* Goal: [ match x.content with ... ]. The scrutinee is read atomically
     through [read_vertex]; every branch receives the loaded value's
     [content_info] snapshot. *)
  imp_match content.
  { iApply (read_vertex with "Hinv Hx"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]: no field read; [x] is returned, with [j := i] and
       reflexivity of [reaches] (framed by [imp_path] from the
       intuitionistic context). *)
    rewrite (@encode_encode' content).
    next_branch.
    imp_path.
    iPureIntro; lia. }

  (* [Link { parent = y } -> find y]: the [Root] branch is refuted; the
     [Link] record pattern re-reads the racy [parent] field atomically.
     Only the link record's own content is touched — a plain borrow. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & (%b & #Hrc & %Hb))".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lp with "Hlocs []").
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hrc Hlocs []").
  iNext.
  iIntros (y j Hj) "#Hsnap #Hy".

  (* Recurse on the parent: [j < b ≤ i], and this call's own hop
     [reaches γR x y] composes with the recursive call's [reaches γR y z].
     Composing is a ghost step, so the postcondition is first opened up
     to a fancy update with [imp_fupd]. *)
  imp_app τ[elem].
  iIntros "Hm".
  iSpecialize ("Hm" $! j with "Hinv Hy").
  iApply imp_fupd.
  iApply (imp_wand with "Hm").
  iIntros (z) "(%j0 & #Hz & %Hj0 & #Hev)".
  iMod (reaches_trans with "Hinv Hsnap Hev") as "#Hxz".
  iModIntro.
  iExists j0. iFrame "Hz Hxz". iPureIntro. lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [compress]. *)

(* [compress x z] walks the path out of [x], rerouting each link it
   passes to point directly at [z], and returns [z].

   The precondition is [reaches γR x z]: [z] must already be in [x]'s
   equivalence class. That is exactly the obligation the rerouting write
   incurs — [content_own]'s link conjunct demands that a link's parent be
   reachable from its holder — and it is also all the caller has, since
   [findc] obtains [z] by running [find] on [x]'s parent.

   The postcondition is just [⌜w = z⌝]. Compression is a pure
   optimization: it moves no vertex between classes and reports nothing.
   Callers recover reachability of the result from their own
   precondition, which is why [findc] can be specified identically to
   [find].

   Two things carry the proof.

   First, the write is justified without re-reading anything: the
   registration [CtLink rc ↪[γc]□ CLink b x] fixes the *bound* [b] and
   the *holder* [x] permanently, and identifiers never change, so
   [k < jy < b] survives the race even though the parent field may have
   moved on since [y] was read.

   Second — the crux — the recursive call [compress y z] needs
   [reaches γR y z], while the caller only has [reaches γR x y] (from the
   parent read) and [reaches γR x z] (its own precondition). Deriving one
   from the other is [reaches_sibling], and it is precisely what the
   [y.id > z.id] guard exists to enable: see that lemma. This is also the
   step that no per-open, self-quantified notion of reachability could
   ever justify, since it must compare two facts inside a single [F]. *)

Definition compress_spec (γ γc γn γR : gname) (x z : elem) (m : microvx) : iProp Σ :=
  ∀ i k,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    vertex γ z k -∗
    reaches γR x z -∗
    imp m {{ λ w : elem, ⌜w = z⌝ }}.

Lemma compress_proof γ γc γn γR η :
  ▷ in_env "compress" (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __compress_fun))))
    {{ λ c, □ iSpec τ[elem; elem] c (compress_spec γ γc γn γR) }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x z).
  unfold compress_spec.
  iIntros (i k) "#Hinv #Hx #Hz #Hxz".
  (* Both identifiers are compared by machine instructions below. *)
  iMod (vertex_representable with "Hinv Hx") as %Hrepi.
  iMod (vertex_representable with "Hinv Hz") as %Hrepk.
  iApply imp_please; iNext.

  (* [match x.content with ...], read atomically. *)
  imp_match content.
  { iApply (read_vertex with "Hinv Hx"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> z]: [x] is a root, nothing to compress. *)
    rewrite (@encode_encode' content).
    next_branch.
    imp_path. }

  (* [Link link -> ...]. The registration pins the bound [b] and names
     [x] as the holder — both permanent, which is what makes the racy
     re-reads below harmless. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & (%b & #Hrc & %Hb))".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.

  (* [let y = link.parent in ...]: an ordinary field read, so it goes
     through [imp_ERecordAccess_atomic] rather than the pattern rule
     [find] uses; [uf_link_parent_acc_elem] supplies its fupd. *)
  iApply (imp_ELet_var (B:=elem)
    (λ y : elem, ∃ jy, ⌜(jy < b)%Z⌝ ∗ reaches γR x y ∗ vertex γ y jy)%I).
  { iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lp] rc with "Hlocs [] []").
    { list_z.length; lia. }
    { imp_path. }
    iNext.
    iApply (uf_link_parent_acc_elem with "Hinv Hrc Hlocs []").
    iNext.
    iIntros (y jy Hjy) "#Hsnap #Hy".
    iExists jy. iFrame "Hsnap Hy". done. }
  iIntros (y) "(%jy & %Hjy & #Hsxy & #Hy)".
  iMod (vertex_representable with "Hinv Hy") as %Hrepjy.

  (* [assert (x.id > y.id)]: discharged by the rank bound alone,
     [jy < b ≤ i]. *)
  iApply (imp_ESeq (λ _ : unit, True)%I).
  { iApply (imp_EAssert (R:=True%I)).
    iSplit; first done.
    iApply (imp_wand _ _ _ _ _ (λ b0 : bool, ⌜b0 = true⌝ ∗ True)%I with "[]").
    { iApply (imp_EOpGt_Z _ _ _ i jy); try assumption.
      { iApply (read_vertex_id with "Hx"). imp_path. }
      { iApply (read_vertex_id with "Hy"). imp_path. } }
    iIntros (b0) "->". iSplit; last done. iPureIntro. apply Z.gtb_lt. lia. }
  iIntros "_".

  (* [if y.id > z.id then <reroute and recurse> else z]. *)
  imp_if.
  { iApply (imp_EOpGt_Z _ _ _ jy k); try assumption.
    { iApply (read_vertex_id with "Hy"). imp_path. }
    { iApply (read_vertex_id with "Hz"). imp_path. } }

  { iIntros "%Hcmp".
    (* The guard, at the [Z] level. Everything downstream — the second
       assert, the write's bound obligation, and [reaches_sibling] —
       rests on it. *)
    assert (Hkjy : (k < jy)%Z).
    { pose proof (Zgt_cases jy k) as Hgt. rewrite <- Hcmp in Hgt. lia. }

    (* [assert (x.id > z.id)]: chains the two guards, [k < jy < b ≤ i]. *)
    imp_match unit with "[]".
    { iApply (imp_EAssert (R:=True%I)).
      iSplit; first done.
      iApply (imp_wand _ _ _ _ _ (λ b0 : bool, ⌜b0 = true⌝ ∗ True)%I with "[]").
      { iApply (imp_EOpGt_Z _ _ _ i k); try assumption.
        { iApply (read_vertex_id with "Hx"). imp_path. }
        { iApply (read_vertex_id with "Hz"). imp_path. } }
      iIntros (b0) "->". iSplit; last done. iPureIntro. apply Z.gtb_lt. lia. }
    iIntros "_".
    destruct a. simpl.
    next_branch.

    (* [link.parent <- z]: the compression write. The invariant's link
       conjunct is re-established from [vertex γ z k], the bound
       [k < jy < b], and the caller's [reaches γR x z]. *)
    iApply (imp_ESeq (λ _ : unit, True)%I).
    { iApply (imp_ERecordSet_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ _ [lp] rc (λ w : elem, ⌜w = z⌝)%I
                with "Hlocs [] [] []").
      { list_z.length; lia. }
      { imp_path. }
      { imp_path. }
      iNext.
      iIntros (a) "->".
      iApply (uf_link_parent_set with "Hinv Hrc Hlocs Hz Hxz []").
      { lia. }
      done. }
    iIntros "_".

    (* [compress y z]: the recursive call's precondition [reaches γR y z]
       comes from [reaches_sibling], using the guard [k < jy]. *)
    iMod (reaches_sibling with "Hinv Hy Hz Hsxy Hxz") as "#Hyz"; first lia.
    imp_app τ[elem; elem].
    iIntros "Hm".
    unfold compress_spec.
    iApply ("Hm" $! jy k with "Hinv Hy Hz Hyz"). }

  (* [else z]: compression would not lower the identifier, so stop. *)
  { iIntros "%Hcmp". imp_path. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [findc]. *)

(* [findc] has the same observable contract as [find] — literally so:
   [findc_spec] below is [find_spec]'s postcondition, verbatim. That
   equality is the specification's real content, namely that the
   [compress] calls [findc] makes along the way are pure path-compression
   optimizations, invisible to callers.

   The reachability conjunct is [reaches γR x z], not a self-quantified
   [∃ D F, DSF F D ∗ ⌜x ∈ D⌝ ∗ ⌜Repr F x z⌝]. The latter is what this
   definition used to say, and it was worse than weak — it was vacuous,
   provable for any two vertices (see [reaches]'s comment for the
   counterexample). *)

Definition findc_spec (γ γc γn γR : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    imp m {{ λ z : elem, ∃ j, vertex γ z j ∗ ⌜(j ≤ i)%Z⌝ ∗ reaches γR x z }}.

(* [findc] is not recursive: it is [x] itself when [x] is a root, and
   otherwise [compress x (find y)] for [x]'s parent [y]. So the proof is
   pure composition, and the only step with any content is threading the
   reachability facts together — [reaches γR x y] from the parent read,
   [reaches γR y z] from [find], joined by [reaches_trans] into the
   [reaches γR x z] that is exactly [compress]'s precondition.

   The identifier bound composes just as directly: [j0 ≤ jy] from [find],
   [jy < b] from the link's registered bound, and [b ≤ i] from [x]'s own
   entry, giving [j0 ≤ i]. *)

Lemma findc_proof γ γc γn γR η :
  in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ γc γn γR)) η -∗
  in_env "compress" (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun __findc))
    {{ λ c, □ iSpec τ[elem] c (findc_spec γ γc γn γR) }}.
Proof.
  iIntros "#IFind #ICompress".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold findc_spec.
  iIntros (i) "#Hinv #Hx".
  (* As in [find_proof]: the [Root] branch's postcondition is a bare
     assertion, so [reaches γR x x] is minted up front. *)
  iMod (reaches_refl with "Hinv") as "#Hxx".
  iApply imp_please; iNext.

  imp_match content.
  { iApply (read_vertex with "Hinv Hx"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]. *)
    rewrite (@encode_encode' content).
    next_branch.
    imp_path.
    iPureIntro; lia. }

  (* [Link { parent = y } -> let z = find y in compress x z]. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & (%b & #Hrc & %Hb))".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lp with "Hlocs []").
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hrc Hlocs []").
  iNext.
  iIntros (y jy Hjy) "#Hsxy #Hy".

  (* [let z = find y in ...]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ w : elem, ∃ j0, vertex γ w j0 ∗ ⌜(j0 ≤ jy)%Z⌝ ∗ reaches γR y w)%I).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold find_spec.
    iApply ("Hm" $! jy with "Hinv Hy"). }
  iIntros (z) "(%j0 & #Hz & %Hj0 & #Hyz)".

  (* [compress x z]: its precondition is the composed chain. *)
  iMod (reaches_trans with "Hinv Hsxy Hyz") as "#Hxz".
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold compress_spec.
  iSpecialize ("Hm" $! i j0 with "Hinv Hx Hz Hxz").
  iApply (imp_wand with "Hm").
  iIntros (w) "->".
  iExists j0. iFrame "Hz Hxz". iPureIntro. lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [get]. *)

(* [get x] chases [x] to a root and returns the value stored there,
   retrying if the vertex it reached has meanwhile been linked away.

   The result is described in the same style as [set] and [union]'s
   [Some] case, and for the same reason: the *value* on its own would be
   an unconstrained [val], so what makes the postcondition meaningful is
   the persistent receipt [CtRoot rc ↪[γc]□ CRoot v]. That fragment says
   [v] really was the payload of a genuine, registered [Root] record —
   and since a registration never changes (see [cinfo]), it stays true
   forever, even after that record has been absorbed by a later [union].
   Alongside it, [reaches γR x z] places the vertex the value was read
   from in [x]'s own equivalence class.

   The [Root] branch is where the racy read is discharged for free: a
   [Root] record's [value] field is never written after allocation, so
   [uf_root_value_acc] pins the loaded value to the one in the
   registration rather than merely bounding it. Contrast the [Link]
   case's [parent] field, which compression does rewrite and which
   therefore only yields a class membership (see [uf_link_parent_acc]).

   The retry branch composes exactly like [find]'s: [reaches γR x z]
   from this attempt's [findc], [reaches γR z z'] from the recursive
   call, joined by [reaches_trans]. *)

Definition get_spec (γ γc γn γR : gname) (x : elem) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    imp m {{ λ v : val, ∃ z (rc : elem), reaches γR x z ∗ CtRoot rc ↪[γc]□ CRoot v }}.

Lemma get_proof γ γc γn γR η :
  ▷ in_env "get" (λ get, □ iSpec τ[elem] get (get_spec γ γc γn γR)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun (AnonFun "x"
        (ELet [Binding (PVar "x") (EApp (EPath ["findc"]) (EPath ["x"]))] __get_exp))))
    {{ λ c, □ iSpec τ[elem] c (get_spec γ γc γn γR) }}.
Proof.
  iIntros "#IGet #IFindc".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold get_spec.
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: the binding shadows [x], so everything
     below is about [z], and [x]'s own claim is recovered at the end by
     composing with this call's [reaches γR x z]. *)
  iApply (imp_ELet_var (B:=elem)).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (z) "(%j & #Hz & %Hj & #Hxz)".

  imp_match content.
  { iApply (read_vertex with "Hinv Hz"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root root -> root.value]: an ordinary field read, so it goes
       through [imp_ERecordAccess_atomic] (at [A := val], the payload
       being untyped) with [uf_root_value_acc] supplying its fupd. That
       accessor returns the value fixed by the registration, so the
       receipt is in hand without any further work. *)
    iDestruct "Hc" as "(#HrcP & (%lv & #Hrclocs) & (%v & #Hrc))".
    rewrite (@encode_encode' content).
    next_branch.
    iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lv] rc with "Hrclocs [] []").
    { list_z.length; lia. }
    { imp_path. }
    iNext.
    iApply (uf_root_value_acc with "Hinv Hrc Hrclocs").
    iNext.
    iExists z, rc. iFrame "Hxz Hrc". }

  (* [Link _ -> get x]: [z] was linked away between [findc] and the read,
     so retry from [z] and prepend this attempt's reachability. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem].
  iIntros "Hm".
  unfold get_spec.
  iApply imp_fupd.
  iApply (imp_wand with "[Hm]").
  { iApply ("Hm" $! j with "Hinv Hz"). }
  iIntros (v) "(%z' & %rc' & #Hzz' & #Hrc')".
  iMod (reaches_trans with "Hinv Hxz Hzz'") as "#Hxz'".
  iModIntro. iExists z', rc'. by iFrame "Hxz' Hrc'".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [set]. *)

(* [set x cx'] is the internal, two-argument recursive helper (the public,
   one-argument [set x v] wraps [Root {value = v}] and calls it). The
   caller supplies ownership of the freshly-allocated record underlying
   [cx'] — it must be a not-yet-registered [Root] record — which [set]
   consumes when its CAS succeeds, registering it in the content-record
   registry [γc].

   The functional contract mirrors [union_post]'s style: [set] terminates
   only through a successful CAS, at which point [cx'] became the content
   of some vertex [z] in [x]'s own equivalence class ([reaches γR x z]).
   The caller keeps the CAS's persistent receipt [cx' ↪[γc]□ CRoot v]:
   [cx'] is registered — forever a [Root] holding exactly [v] (a
   [Root]'s registration never changes; see [cinfo]'s comment). *)

Definition set_content_spec (γ γc γn γR : gname) (x : elem) (cx' : content) (m : microvx) : iProp Σ :=
  ∀ i v,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    content_init γ γc cx' (CRoot v) -∗
    imp m {{ λ _ : unit, ∃ z, reaches γR x z ∗ cx' ↪[γc]□ CRoot v }}.

Lemma set_proof γ γc γn γR η :
  ▷ in_env "set" (λ set, □ iSpec τ[elem; content] set (set_content_spec γ γc γn γR)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn γR)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __set_fun))))
    {{ λ c, □ iSpec τ[elem; content] c (set_content_spec γ γc γn γR) }}.
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x cx' i v).
  iIntros "#Hinv #Hx Hcx'".
  iApply imp_please; iNext.

  (* [let z = findc x in ...]: chase [x] to a root [z], whose identifier
     [j] is at most [x]'s, and which [findc] reports as reachable from
     [x] — the chain [set] prepends its own results to. *)
  imp_let.
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (z) "(%j & #Hz & %Hj & #Hsz)".
  subst imp_let_B imp_let_HB.

  (* [let cx = z.content in ...]: read [z]'s content cell through
     [read_vertex], remembering the loaded value's snapshot. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc z c j)%I).
  { iApply (read_vertex with "Hinv Hz"). imp_path. }
  iIntros (cx) "#Hcx".

  (* Re-match on the already-loaded [cx]: a plain path lookup, closed
     automatically by [imp_match]'s own scrutinee handling. *)
  imp_match content with "[]".
  destruct cx as [rc|rc]; simpl.

  { (* [Root _ -> if cas z.content cx cx' then () else set x cx']: [z]
       was a root when we read it, so try to swing its content cell from
       [cx] to the caller's fresh content [cx']. *)
    iDestruct "Hcx" as "(#HrcP & _ & (%vz & #Hrc))".
    rewrite (@encode_encode' content).
    next_branch.
    rewrite -encode_encode'.
    iApply (imp_EIfThenElse _ _ _ _
              (λ b : bool, if b then cx' ↪[γc]□ CRoot v
                           else content_init γ γc cx' (CRoot v))%I
              with "[Hcx'] []").

    { (* The CAS, through [uf_cas_fupd]. On success the caller's fresh
         content is registered — its persistent receipt comes back. *)
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hz"). imp_path. }
      iIntros "Hptr Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_fupd
               (λ b, if b then cx' ↪[γc]□ CRoot v
                     else content_init γ γc cx' (CRoot v))%I
               with "Hinv [] Hptr Hrc HrcP Hcx'").
      { discriminate. }
      { iApply (vertex_frag with "Hz"). }
      { iNext. iIntros ([|]) "H"; iExact "H". } }

    (* The two branches: on success [z] — reached from [x] — is the
       witness; on failure the caller's content comes back and [set]
       retries from [z] (whose identifier [j] is a valid decreasing
       measure), prepending this attempt's chain to the recursive
       result. *)
    iIntros ([|]) "HΦb".
    { iApply imp_EUnit.
      iExists z. by iFrame "HΦb Hsz". }
    imp_app τ[elem; content].
    iIntros "Hm".
    unfold set_content_spec.
    iSpecialize ("Hm" $! j v with "Hinv Hz HΦb").
    iApply imp_fupd.
    iApply (imp_wand with "Hm").
    iIntros (u) "(%z' & #Hz' & #Hfrag)".
    iMod (reaches_trans with "Hinv Hsz Hz'") as "#Hxz'".
    iModIntro. iExists z'. by iFrame "Hfrag Hxz'". }

  (* [Link _ -> set x cx']: [z] is no longer a root, so restart from
     [z] — again with the strictly smaller identifier [j]. *)
  rewrite {2}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; content].
  iIntros "Hm".
  unfold set_content_spec.
  iSpecialize ("Hm" $! j v with "Hinv Hz Hcx'").
  iApply imp_fupd.
  iApply (imp_wand with "Hm").
  iIntros (u) "(%z' & #Hz' & #Hfrag)".
  iMod (reaches_trans with "Hinv Hsz Hz'") as "#Hxz'".
  iModIntro. iExists z'. by iFrame "Hfrag Hxz'".
Qed.

(* The public, one-argument [set x v]: allocates the fresh [Root {value =
   v}] record and calls the internal, two-argument [set] above. *)

(* [set x v] wrote [v] at some vertex [z] in [x]'s equivalence class,
   through a fresh root record [rc] whose registration
   [CtRoot rc ↪[γc]□ CRoot v] is the caller's persistent receipt. *)

Definition set_spec (γ γc γn γR : gname) (x : elem) (v : val) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    imp m {{ λ _ : unit,
      ∃ z (rc : elem), reaches γR x z ∗ CtRoot rc ↪[γc]□ CRoot v }}.

Lemma set_wrapper_proof γ γc γn γR η :
  in_env "set" (λ setv, □ iSpec τ[elem; content] setv (set_content_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun __set)) {{ λ c, □ iSpec τ[elem; val] c (set_spec γ γc γn γR) }}.
Proof.
  iIntros "#ISet".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x v).
  unfold set_spec.
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.

  (* [let cx' = Root { value = v } in set x cx']. [A] pinned explicitly
     ([root_fields]): both it and [link_fields] are single-field
     [RecordRepr] instances, so bare [imp_record] cannot disambiguate
     between them. Allocation yields the fresh content's [content_own]
     directly, which is exactly what the internal [set] consumes. *)
  iApply (imp_ELet_var (B:=content)
      (λ c : content, content_init γ γc c (CRoot v))%I).
  { imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (cx') "Hco".
  (* The allocated content is a [Root]: read its tag off the diagonal
     [content_init] to expose the underlying record [rc]. *)
  destruct cx' as [rc|rc]; last first.
  { iDestruct "Hco" as "[]". }
  imp_app τ[elem; content].
  iIntros "Hm".
  unfold set_content_spec.
  iSpecialize ("Hm" $! i v with "Hinv Hx Hco").
  iApply (imp_wand with "Hm").
  iIntros (u) "(%z & #Hz & #Hfrag)".
  iExists z, rc. by iFrame "Hfrag Hz".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [update]. *)

(* [update x f] repeatedly reads the root's current value and CASes in
   [Root {value = f v}], retrying on failure. Unlike [set], each retry
   allocates its own fresh record internally (there is no externally
   supplied [cx'] to thread through failed attempts), so the proof does
   not need [set_content_spec]'s ownership hand-back trick.

   The caller describes [f] by an arbitrary input/output relation [Φf],
   packaged as an [iSpec] — the same shape as e.g. [Array.init]'s
   function argument. The □ makes it reusable across retries: each
   attempt calls [f] afresh on that attempt's root value.

   [update]'s own functional contract is then the successful attempt's
   linearization snapshot: some vertex [z] reachable from [x] had its
   root swung from a record [rc] registered with value [v] (the receipt
   [CtRoot rc ↪[γc]□ CRoot v] of the CAS's "seen" side) to a fresh
   record [rc'] registered with value [w] (the receipt of its "new"
   side), where [Φf v w] came out of the [f v] call of that same
   attempt. *)

Definition update_post (γc γR : gname) (Φf : val → val → iProp Σ) (x : elem)
    (_ : unit) : iProp Σ :=
  ∃ z (rc rc' : elem) (v w : val),
    reaches γR x z ∗
    CtRoot rc ↪[γc]□ CRoot v ∗
    CtRoot rc' ↪[γc]□ CRoot w ∗
    Φf v w.

Definition update_spec (γ γc γn γR : gname) (x : elem) (f : val) (m : microvx) : iProp Σ :=
  ∀ (Φf : val → val → iProp Σ),
    □ iSpec τ[val] f (λ v m', imp m' {{ λ w, Φf v w }}) -∗
    ∀ i,
      is_uf γ γc γn γR -∗
      vertex γ x i -∗
      imp m {{ update_post γc γR Φf x }}.

(* The retry sites' chaining step, as in [union_post_extend]. Composing
   the two reachability facts is a ghost step, so this is a fancy update
   rather than a plain entailment. *)

Lemma update_post_extend γ γc γn γR Φf (x z : elem) u :
  is_uf γ γc γn γR -∗
  reaches γR x z -∗
  update_post γc γR Φf z u ={⊤}=∗ update_post γc γR Φf x u.
Proof.
  iIntros "#Hinv #Hsz (%z' & %rc & %rc' & %v & %w & #Hz' & Hrc & Hrc' & HΦ)".
  iMod (reaches_trans with "Hinv Hsz Hz'") as "#Hxz'".
  iModIntro. iExists z', rc, rc', v, w. by iFrame.
Qed.


Lemma update_proof γ γc γn γR η :
  ▷ in_env "update" (λ update, □ iSpec τ[elem; val] update (update_spec γ γc γn γR)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn γR)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __update_fun))))
    {{ λ c, □ iSpec τ[elem; val] c (update_spec γ γc γn γR) }}.
Proof.
  iIntros "#IUpdate #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x f).
  unfold update_spec.
  iIntros (Φf) "#Hf".
  iIntros (i) "#Hinv #Hx".
  iApply imp_please; iNext.

  (* [let z = findc x in ...]: chase [x] to a root [z], reachable from
     [x] — this attempt's chain. *)
  iApply (imp_ELet_var (B:=elem)).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (z) "(%j & #Hz & %Hj & #Hsz)".

  (* [let cx = z.content in ...]: read [z]'s content cell through
     [read_vertex]. The snapshot includes the record's field location,
     which the [Root] branch immediately re-reads. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc z c j)%I).
  { iApply (read_vertex with "Hinv Hz"). imp_path. }
  iIntros (cx) "#Hcx".

  (* Re-match on the already-loaded [cx]: a plain path lookup, closed
     automatically by [imp_match]'s own scrutinee handling. *)
  imp_match content with "[]".
  destruct cx as [rc|rc]; simpl.

  { (* [Root { value = v } -> if cas z.content cx (Root {value = f v})
       then () else update x f]. *)
    iDestruct "Hcx" as "(#HrcP & (%lv & #Hrclocs) & (%v & #Hrc))".
    rewrite {2}(@encode_encode' content).
    next_branch.
    rewrite -encode_encode'.

    (* Read the root's current value — pinned to [v] by the
       registration. This borrows only [rc]'s own content. *)
    iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
    iNext.
    iApply (uf_root_value_acc with "Hinv Hrc Hrclocs").
    iNext.

    iApply (imp_EIfThenElse _ _ _ _
              (λ b : bool, if b then update_post γc γR Φf x () else True)%I).

    { (* The CAS. Unlike [set]'s, the "new value" argument is built here:
         a freshly allocated [Root { value = f v }] record, whose
         ownership this attempt consumes (each retry allocates its own),
         together with [Φf v w] from this attempt's [f v] call. *)
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hz"). imp_path. }
      { (* Allocate [Root { value = f v }], already typed as a [content],
           calling [f] through its [iSpec]. *)
        set_postcondition
          (λ c : content, ∃ (rc' : elem) (w : val),
             ⌜c = CtRoot rc'⌝ ∗ content_init γ γc c (CRoot w) ∗ Φf v w)%I.
        imp_record $! root_fields.
        { imp_app τ[val].
          iIntros "Hm".
          iApply "Hm". }
        iIntros (c) "(%r & -> & %xs & Hown & HΦf)".
        iExists r, xs. iSplit; first done. iFrame "HΦf". iApply "Hown". }
      iIntros "Hptr (%rc' & %w & -> & Hco' & HΦf) Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_fupd
                (λ b, if b then update_post γc γR Φf x () else True)%I
                with "Hinv [] Hptr Hrc HrcP Hco' [HΦf]").
      { discriminate. }
      { iApply (vertex_frag with "Hz"). }
      { (* On success both receipts are in hand: the absorbed root's
           [Hrc] and the fresh record's registration. *)
        iNext. iIntros ([|]) "Hfrag"; last done.
        iExists z, rc, rc', v, w.
        by iFrame "Hrc Hfrag HΦf Hsz". } }

    (* Both branches: on success the CAS's snapshot is the result; on
       failure [update] retries from [z], prepending this attempt's
       own chain. *)
    iIntros ([|]) "HΦb".
    { iApply imp_EUnit. iExact "HΦb". }
    imp_app τ[elem; val].
    iIntros "Hm3".
    unfold update_spec.
    iSpecialize ("Hm3" $! Φf with "Hf Hinv Hz").
    iApply imp_fupd.
    iApply (imp_wand with "Hm3").
    iIntros (u) "Hpost".
    iApply (update_post_extend with "Hinv Hsz Hpost"). }

  (* [Link _ -> update x f]: [z] is no longer a root — restart from [z]. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; val].
  iIntros "Hm3".
  unfold update_spec.
  iSpecialize ("Hm3" $! Φf with "Hf Hinv Hz").
  iApply imp_fupd.
  iApply (imp_wand with "Hm3").
  iIntros (u) "Hpost".
  iApply (update_post_extend with "Hinv Hsz Hpost").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [union]. *)

(* A full functional specification, mirroring the sequential union-find's
   own [union_spec] (see [UnionFind.v]) but adapted to the concurrent
   setting. The sequential version's caller-owned [D R V] resource,
   returned updated, is impossible here: [is_uf] is a shared invariant,
   not something a single caller can hold exclusively. Every fact is
   instead a persistent ghost assertion about the abstract graph.

   - [None]: [x] and [y] are in the same class — [same_class γR x y]
     below, unfolding to [∃ z, reaches γR x z ∗ reaches γR y z]. The two
     halves come from [union]'s two [findc] calls, which happen at
     different times and open the invariant independently; they compose
     because [reaches] survives across opens (see its comment).
   - [Some r]: [x] and [y] turned out distinct, and [rc ↪[γc]□ CRoot r] is
     the PERSISTENT registration of whichever root's content record ([rc])
     got absorbed — [r] is exactly the value that was stored there. Since
     a content record's [cinfo] tag never changes once registered (see
     [cinfo]'s own comment), this fact survives forever, even though the
     vertex [z] whose content [rc] used to be has since become a [Link]:
     the caller gets back a genuine, checkable fact about [r]'s provenance,
     not just an unconstrained value.

   Both halves are real, checkable characterizations rather than
   restatements of the returned pointer. It is worth being explicit that
   this depends entirely on [reaches] being ghost-anchored: the earlier
   version of this specification phrased the same claims over a
   *self-quantified* graph, and every one of them was vacuous. See
   [reaches].

   The return value's TYPE is [option val], not [option elem]: [Root]'s
   "value" field ([content_own]'s CRoot case) is untyped ([lv ↦ v] for an
   arbitrary [v : val], mirroring [set]/[update]'s own genericity). *)

(* [x] and [y] have become equivalent: they reach a common vertex in the
   abstract graph. Naming this separately (rather than inlining the
   existential in [union_spec]) is what lets the [None] case read, at a
   glance, as "x and y are equal". *)

Definition same_class (γR : gname) (x y : elem) : iProp Σ :=
  ∃ z, reaches γR x z ∗ reaches γR y z.

(* [find]'s postcondition, read as an equivalence-class statement: a
   vertex [x] reaches is in particular in [x]'s class, the common
   vertex being [z] itself. *)

Lemma reaches_same_class γ γc γn γR (x z : elem) :
  is_uf γ γc γn γR -∗ reaches γR x z ={⊤}=∗ same_class γR x z.
Proof.
  iIntros "#Hinv #Hxz".
  iMod (reaches_refl _ _ _ _ z with "Hinv") as "#Hzz".
  iModIntro. iExists z. by iFrame "Hxz Hzz".
Qed.

Definition union_post (γc γR : gname) (x y : elem) (ov : option val) : iProp Σ :=
  match ov with
  | None => same_class γR x y
  | Some r => ∃ z (rc : elem),
      (reaches γR x z ∨ reaches γR y z) ∗ CtRoot rc ↪[γc]□ CRoot r
  end.

Definition union_spec (γ γc γn γR : gname) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ i j,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    vertex γ y j -∗
    imp m {{ union_post γc γR x y }}.

(* Every recursive [union x y] call happens after [findc] has replaced
   [x]/[y] by their representatives [a]/[y'], so its result is stated
   about [a]/[y']. This prepends the caller's own [findc] reachability
   facts to both sides of that result, which is all it takes to turn it
   back into a statement about [x]/[y]. Used at all four sites that fall
   through to the recursive call. *)

Lemma union_post_extend γ γc γn γR (x y a y' : elem) ov :
  is_uf γ γc γn γR -∗
  reaches γR x a -∗
  reaches γR y y' -∗
  union_post γc γR a y' ov ={⊤}=∗ union_post γc γR x y ov.
Proof.
  iIntros "#Hinv #Hsx #Hsy".
  destruct ov as [r|]; simpl.
  - iIntros "(%z & %rc & [#Hz|#Hz] & #Hrc)".
    + iMod (reaches_trans with "Hinv Hsx Hz") as "#Hxz".
      iModIntro. iExists z, rc. iFrame "Hrc". iLeft. iExact "Hxz".
    + iMod (reaches_trans with "Hinv Hsy Hz") as "#Hyz".
      iModIntro. iExists z, rc. iFrame "Hrc". iRight. iExact "Hyz".
  - iIntros "(%z & #Hza & #Hzy)".
    iMod (reaches_trans with "Hinv Hsx Hza") as "#Hxz".
    iMod (reaches_trans with "Hinv Hsy Hzy") as "#Hyz".
    iModIntro. iExists z. by iFrame "Hxz Hyz".
Qed.

(* Proof outline for the internal (2-arg, recursive) [union]:
   1. Call [findc] on both [x] and [y] (through [imp_let]'s two-binding
      form), obtaining vertices [a], [y'] with ids [i'], [j'].
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
      [imp_record] — which, seeing a [content]-typed postcondition, types
      it as a [content] on the spot, so the "seen"/"new" arguments share
      one [Encode content] despite carrying different tags — CAS it in
      via the polymorphic [compare_and_set_spec] at [A := content], and
      on success
      register the new content record as [CLink i' a] (resp.
      [CLink j' y']) in [γc] — needs the parent's id strictly below the
      bound, i.e. [j' < i'] (resp. [i' < j']), from the branch guard.
      The holder component is forced to be the CASed vertex itself; see
      [uf_cas_fupd].
   5. The graph [F] (see [uf_inv]) only changes at step 4's successful
      CAS, via [UnionFind03Link.link] — literally the same primitive the
      sequential proof's own [Inv_link] uses. [None] (step 2's true
      branch) needs only [same_class γR x y], which is the two [findc]
      results [reaches γR x a] and [reaches γR y y'] meeting at the
      common vertex [a = y'] that step 2 has just tested for — no
      appeal to [a]/[y']'s current root-ness is needed for it. *)

Lemma union_proof γ γc γn γR η :
  ▷ in_env "union" (λ union, □ iSpec τ[elem; elem] union (union_spec γ γc γn γR)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn γR)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __union_fun))))
    {{ λ c, □ iSpec τ[elem; elem] c (union_spec γ γc γn γR) }}.
Proof.
  iIntros "#IUnion #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold union_spec.
  iIntros (i j) "#Hinv #Hx #Hy".
  iApply imp_please; iNext.

  (* [let x = findc x and y = findc y in ...]: chase both arguments to
     their (possibly already stale) roots [a] and [y']. *)
  imp_let $! (λ z : elem, ∃ i', vertex γ z i' ∗ ⌜(i' ≤ i)%Z⌝ ∗ reaches γR x z)%I
          $! (λ z : elem, ∃ j', vertex γ z j' ∗ ⌜(j' ≤ j)%Z⌝ ∗ reaches γR y z)%I.
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! j with "Hinv Hy"). }
  (* The two reachability chains are all the rest of the proof ever needs
     from [findc]; [union_post_extend] prepends them to whatever a
     recursive call returns. *)
  iIntros (a y') "(%i' & #Hav & %Hi' & #Hsx) (%j' & #Hy'v & %Hj' & #Hsy)".
  iDestruct (vertex_mut with "Hav") as "#HaP".
  iDestruct (vertex_mut with "Hy'v") as "#HyP".

  (* [if x == y then None else ...]: physical equality on two non-inline
     records, which needs at least one operand to be a mutable block —
     supplied by [vertex_mut]. *)
  imp_if.
  { set_postcondition
    (λ b : bool, if b then ⌜a = y'⌝ else ⌜a ≠ y'⌝)%I.
    iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I
                                       (λ l : record, ⌜l = y'⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec a y') as [->|Hneq]. } }

  { iIntros "->". (* [a = y']: the two sides already share a representative. *)
    iApply (imp_wand with "[]").
    { imp_constant. }
    iIntros (v) "->".
    simpl.
    iExists y'. by iFrame "Hsx Hsy". }

  iIntros "%Heq".
  (* [assert (x.id <> y.id)]: a real obligation, discharged from the
     id-uniqueness registry [γn] through [vertex_ids_ne] (a same-mask
     fancy update, [iMod]-able straight into the [imp] proof). *)
  iMod (vertex_ids_ne with "Hinv Hav Hy'v") as %(Hij & Hrepi & Hrepj);
    first exact Heq.

  imp_match unit with "[]".
  { iApply (imp_EAssert (R:=⌜i' ≠ j'⌝%I)).
    iSplit; first done.
    iApply (imp_EOpNe (A1:=Z) (A2:=Z)).
    { set_postcondition (λ n, ⌜n=i'⌝)%I.
      iApply (read_vertex_id with "Hav"). imp_path. }
    { set_postcondition (λ n, ⌜n=j'⌝)%I.
      iApply (read_vertex_id with "Hy'v"). imp_path. }
    { (* Bridge the machine-level [int.eq] back to [i' ≠ j' : Z]. *)
      iIntros "!>" (v1 v2) "-> ->".
      rewrite /ne_val /eq_val /=.
      iApply imp_ret; first reflexivity.
      iSplit; [iPureIntro|done].
      rewrite eq_repr_repr; try assumption.
      by destruct (Z.eqb_spec i' j') as [Habs|_]; [exfalso; exact (Hij Habs)|]. } }
  iIntros "%HR".
  destruct a0. simpl.
  next_branch.

  (* [if x.id > y.id then <link x to y> else <link y to x>]. *)
  imp_if.
  { iApply (imp_EOpGt_Z _ _ _ i' j'); try assumption.
    { iApply (read_vertex_id with "Hav"). imp_path. }
    { iApply (read_vertex_id with "Hy'v"). imp_path. } }

  { iIntros "%Hcmp2".
    (* [x.id > y.id]: CAS [Link { parent = y }] into [x]'s content cell.
       Structurally this mirrors [update_proof] — content read, match,
       field read, allocate, CAS — with a [Link] in place of the fresh
       [Root]. *)
    (* The branch guard, in the form [content_own]'s [CLink] case wants.
       It is needed already at allocation time, to build the new record's
       [content_own] on the spot. *)
    assert (Hlt : (j' < i')%Z).
    { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc a c i')%I).
    { iApply (read_vertex with "Hinv Hav"). imp_path. }
    iIntros (cx) "#Hcx".

    (* Re-match on the already-loaded [cx]: a plain path lookup, closed
       automatically by [imp_match]'s own scrutinee handling. *)
    imp_match content with "[]".
    destruct cx as [rc|rc]; simpl.

    { (* [Root {v} -> if cas x.content cx (Link {parent = y}) then Some v
         else union x y]. *)
      iDestruct "Hcx" as "(#HrcP & (%lv & #Hrclocs) & (%v & #Hrc))".
      rewrite (@encode_encode' content).
      next_branch.

      (* Read the absorbed root's value — pinned to [v] by the
         registration; a borrow of the invariant that changes nothing. *)
      iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
      iNext.
      iApply (uf_root_value_acc with "Hinv Hrc Hrclocs").
      iNext.

      imp_if.
      { set_postcondition (λ b, True)%I.
        (* The CAS is instantiated at [A := content]. The "seen" value is
           [CtRoot rc] and the "new" one [CtLink _]: two different
           constructor tags under one [Encode content] instance. *)
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hav"). imp_path. }
        { (* The "seen" value, read back from the environment at
             [content]. [imp_path] cannot guess which constructor the
             stored value belongs to, so it is written out. *)
          set_postcondition (λ c : content, ⌜c = CtRoot rc⌝)%I.
          iApply (imp_EPath (A:=content) (CtRoot rc)); first reflexivity.
          done. }
        { (* The "new" value: because the postcondition is at [content]
             rather than [record], [imp_record] allocates
             [Link { parent = y }] and hands it back already typed as a
             [content]. Adding [y']'s vertex and the branch guard's
             [j' < i'] turns it into the invariant's own [content_own]. *)
          set_postcondition
            (λ c : content, content_init γ γc c (CLink i' a))%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists y', j'. iFrame "Hown Hy'v". iPureIntro. exact Hlt. }
        iIntros "-> Hptr Hco' Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_fupd (λ _, True)%I γ γc γn γR a i'
                  with "Hinv [] Hptr Hrc HrcP Hco' []").
        { intros b0 h0 Hb0. injection Hb0 as -> ->. split; [lia | reflexivity]. }
        { iApply (vertex_frag with "Hav"). }
        { iNext. iIntros ([|]) "_"; done. } }

      { iIntros "_".
        (* CAS succeeded: return [Some v], where [v] is the absorbed
           root's value — still described by the persistent
           [Hrc : CtRoot rc ↪[γc]□ CRoot v]. *)
        imp_data.
        iIntros (? ->). simpl.
        iExists a, rc. iFrame "Hrc". iLeft. iExact "Hsx". }
      { iIntros "_".
        (* CAS failed: retry from [a]/[y'] and chain this call's own
           reachability facts onto the recursive result. *)
        imp_app τ[elem; elem].
        iIntros "Hm3".
        unfold union_spec.
        iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
        iApply imp_fupd.
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        iApply (union_post_extend with "Hinv Hsx Hsy Hov"). } }

    { (* [_ -> union x y]: [x.content] raced ahead of us (already a
         [Link], not a [Root]) — retry via the recursive call. *)
      rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      unfold union_spec.
      iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
      iApply imp_fupd.
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      iApply (union_post_extend with "Hinv Hsx Hsy Hov"). } }

  { iIntros "%Hcmp2".
    (* [x.id <= y.id]: the mirror image — CAS [Link { parent = x }] into
       [y]'s content cell, registering it as [CLink j'] (which needs
       [i' < j'], from [Hcmp2] together with [Hij]). Every step below is
       the previous branch's with [a]/[i'] and [y']/[j'] exchanged. *)
    assert (Hlt : (i' < j')%Z).
    { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc y' c j')%I).
    { iApply (read_vertex with "Hinv Hy'v"). imp_path. }
    iIntros (cy) "#Hcy".

    imp_match content with "[]".
    destruct cy as [rc|rc]; simpl.

    { iDestruct "Hcy" as "(#HrcP & (%lv & #Hrclocs) & (%v & #Hrc))".
      rewrite (@encode_encode' content).
      next_branch.

      iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lv with "Hrclocs []").
      iNext.
      iApply (uf_root_value_acc with "Hinv Hrc Hrclocs").
      iNext.

      imp_if.
      { set_postcondition (λ _, True)%I.
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hy'v"). imp_path. }
        { set_postcondition (λ c : content, ⌜c = CtRoot rc⌝)%I.
          iApply (imp_EPath (A:=content) (CtRoot rc)); first reflexivity.
          done. }
        { set_postcondition
            (λ c : content, content_init γ γc c (CLink j' y'))%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists a, i'. iFrame "Hown Hav". iPureIntro. exact Hlt. }
        iIntros "-> Hptr Hco' Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_fupd (λ _, True)%I γ γc γn γR y' j'
                  with "Hinv [] Hptr Hrc HrcP Hco' []").
        { intros b0 h0 Hb0. injection Hb0 as -> ->. split; [lia | reflexivity]. }
        { iApply (vertex_frag with "Hy'v"). }
        { iNext. iIntros ([|]) "_"; done. } }

      { iIntros "_".
        imp_data.
        iIntros (? ->). simpl.
        iExists y', rc. iFrame "Hrc". iRight. iExact "Hsy". }
      { iIntros "_".
        imp_app τ[elem; elem].
        iIntros "Hm3".
        unfold union_spec.
        iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
        iApply imp_fupd.
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        iApply (union_post_extend with "Hinv Hsx Hsy Hov"). } }

    { rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      unfold union_spec.
      iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
      iApply imp_fupd.
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      iApply (union_post_extend with "Hinv Hsx Hsy Hov"). } }
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [eq]. *)

(* [eq x y] decides whether [x] and [y] are in the same equivalence class,
   following Anderson and Woll's algorithm.

   What is proved is the *sound* half:

       if the answer is [true], then [x] and [y] really are equivalent.

   The [false] case is [True] — it says nothing — and that is a
   deliberate choice rather than unfinished work. The reasoning is worth
   recording, because "complete the specification" looks like an obvious
   improvement and is not one.

   A [false] answer is the only *negative* claim anywhere in this
   development, and negative class facts are not monotone: classes only
   ever merge, so a disequality true now is false a moment later. It
   cannot be stated as a persistent fact about the current graph the way
   [reaches] is. The honest form is a linearization statement — "there
   was an instant during this call at which [x] and [y] were in
   different classes" — which needs a time-indexed history of the graph
   (a monotone list of past [F]s, say).

   The decisive objection is not the cost of that history but that no
   client could use the result. [is_uf] is a shared invariant, so anyone
   holding it must assume concurrent [union]s, and "different at instant
   [t]" can never be strengthened to "different now". The one setting
   where it would pay — a quiescent phase with no concurrent writers —
   needs an ownership discipline (exclusive or fractional control of the
   structure) that [is_uf] does not provide. The machinery would be
   large and its conclusion unusable through this API.

   The corresponding cost, stated plainly: this specification is
   satisfied by [fun _ _ -> false]. It certifies that a [true] answer is
   trustworthy, not that the implementation does anything. That is a
   safety contract, not an effectiveness one — the same is true of
   [find_spec], which [fun x -> x] satisfies. ([union] is the exception:
   its [None] case demands a positive [same_class] proof.) Anyone wanting
   effectiveness should read that as the axis to revisit, and it is a
   different project from linearizability.

   For the record, since it is the part that would be easy to lose: the
   algorithm's own justification, quoted in the OCaml source, rests on
   root-ness being *anti*-monotone — a vertex's content goes
   [Root → Link] and never back, since every CAS swings a [Root] out. So
   [a] being a root now means it was a root at every earlier instant, in
   particular when [b = findc y] was found; if [findc] also reported [b]
   root at its own linearization instant, the two were distinct roots
   simultaneously and the call linearizes there. Both ingredients are
   absent here: [findc_spec] does not report root-ness (dropped with the
   vacuous [Repr] conjunct, see [reaches]), and instants cannot be
   compared.

   What IS proved composes exactly like the rest of the file: each
   iteration turns [x] into its representative [a] and then into [a]'s
   parent, and the [reaches] facts for those hops are chained onto the
   recursive call's result with [reaches_trans]. *)

Definition eq_spec (γ γc γn γR : gname) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ i j,
    is_uf γ γc γn γR -∗
    vertex γ x i -∗
    vertex γ y j -∗
    imp m {{ λ b : bool, if b then same_class γR x y else True }}.

(* The internal, recursive [eq]. Since the two mutually recursive
   functions were merged into one, both [findc] calls happen at the top
   of every iteration rather than only on the retry path. *)

Lemma eq_proof γ γc γn γR η :
  ▷ in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ γc γn γR)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __eq_fun))))
    {{ λ c, □ iSpec τ[elem; elem] c (eq_spec γ γc γn γR) }}.
Proof.
  iIntros "#IEq #IFindc".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold eq_spec.
  iIntros (i j) "#Hinv #Hx #Hy".
  iApply imp_please; iNext.

  (* [let x = findc x in let y = findc y in ...]. The order matters for
     the linearization argument the [false] case would need; it is
     irrelevant to the sound half proved here. *)
  iApply (imp_ELet_var (B:=elem)).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (a) "(%i' & #Hav & %Hi' & #Hxa)".
  iApply (imp_ELet_var (B:=elem)).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! j with "Hinv Hy"). }
  iIntros (b) "(%j' & #Hbv & %Hj' & #Hyb)".

  (* [x == y || ...]: physical equality of two non-inline records, so at
     least one operand must be a mutable block ([vertex_mut]). The
     short-circuit means the match is only reached when [a ≠ b]. *)
  iDestruct (vertex_mut with "Hav") as "#HaP".
  iDestruct (vertex_mut with "Hbv") as "#HbP".
  iApply (imp_EBoolDisj _ (λ bb : bool, if bb then ⌜a = b⌝ else ⌜a ≠ b⌝)%I).
  { iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I
                                       (λ l : record, ⌜l = b⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec a b) as [->|Hneq]. } }
  iIntros ([|]) "Hcmp".

  { (* [a = b]: the two chains meet, so [x] and [y] are equivalent. *)
    iDestruct "Hcmp" as %->.
    iExists b. by iFrame "Hxa Hyb". }

  iDestruct "Hcmp" as %Hne.
  imp_match content.
  { iApply (read_vertex with "Hinv Hav"). imp_path. }
  iIntros "#Hc".
  destruct a0 as [rc|rc]; simpl.

  { (* [Root _ -> false]: the answer is [false] and the specification
       asks nothing of it. This is the gap documented above. *)
    rewrite (@encode_encode' content).
    next_branch.
    iApply (imp_wand with "[]").
    { imp_constant. }
    iIntros (v) "->". simpl. done. }

  (* [Link { parent = x } -> eq x y]: interference, so retry from [a]'s
     parent, chaining [x ⟶ a ⟶ x'] onto whatever the recursive call
     returns. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & (%b0 & #Hrc & %Hb0))".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_var_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ rc lp with "Hlocs []").
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hrc Hlocs []").
  iNext.
  iIntros (x' jx' Hjx') "#Hax' #Hx'v".
  iMod (reaches_trans with "Hinv Hxa Hax'") as "#Hxx'".
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold eq_spec.
  iSpecialize ("Hm" $! jx' j' with "Hinv Hx'v Hbv").
  iApply imp_fupd.
  iApply (imp_wand with "Hm").
  iIntros ([|]) "Hres".
  { iDestruct "Hres" as (w) "[#Hx'w #Hbw]".
    iMod (reaches_trans with "Hinv Hxx' Hx'w") as "#Hxw".
    iMod (reaches_trans with "Hinv Hyb Hbw") as "#Hyw".
    iModIntro. iExists w. by iFrame "Hxw Hyw". }
  { by iModIntro. }
Qed.

(* The public [eq x y = x == y || eq x y]: a fast path for the physically
   identical case, which needs only reflexivity of [reaches]. *)

Lemma eq_wrapper_proof γ γc γn γR η :
  in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ γc γn γR)) η -∗
  imp (eval η (EAnonFun __eq)) {{ λ c, □ iSpec τ[elem; elem] c (eq_spec γ γc γn γR) }}.
Proof.
  iIntros "#IEq".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold eq_spec.
  iIntros (i j) "#Hinv #Hx #Hy".
  (* The [x == y] branch's postcondition is a bare assertion, so the
     reflexivity fact is minted up front (as in [find_proof]). *)
  iMod (reaches_refl _ _ _ _ x with "Hinv") as "#Hxx".
  iApply imp_please; iNext.
  iDestruct (vertex_mut with "Hx") as "#HxP".
  iDestruct (vertex_mut with "Hy") as "#HyP".
  iApply (imp_EBoolDisj _ (λ bb : bool, if bb then ⌜x = y⌝ else ⌜x ≠ y⌝)%I).
  { iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = x⌝)%I
                                       (λ l : record, ⌜l = y⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec x y) as [->|Hneq]. } }
  iIntros ([|]) "Hcmp".
  { iDestruct "Hcmp" as %<-.
    iExists x. by iFrame "Hxx". }
  iDestruct "Hcmp" as %Hne.
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold eq_spec.
  iApply ("Hm" $! i j with "Hinv Hx Hy").
Qed.

End ConcurrentUnionFind.
