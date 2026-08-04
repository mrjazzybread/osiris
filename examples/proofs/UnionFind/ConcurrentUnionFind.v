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
   fragment [CtRoot rc ↪[γc]□ CRoot r]) instead of an unconstrained
   existential. *)
Inductive cinfo :=
| CRoot (v : val)
| CLink (b : Z).

Section ConcurrentUnionFind.

(* [content] is the OCaml type of a vertex's [content] field: the
   two-constructor variant whose payloads are the inline records
   [Root {value}] and [Link {parent}]. It is the *key* of the content
   registry [γc]: the registry maps each content value ever stored in a
   vertex's content cell to its static description [cinfo]. Keying by
   the typed value (rather than by the bare record location) means the
   registration fragment [c ↪[γc]□ ci] pins down the value's tag as
   well as its record, so clients never fall back to the [val] level. *)

Inductive content := CtRoot (r : record) | CtLink (r : record).

Definition content_loc (c : content) : record :=
  match c with CtRoot rc | CtLink rc => rc end.

Definition content_root (c : content) : bool :=
  match c with CtRoot _ => true | CtLink _ => false end.

Definition content_tag (c : content) :=
  match c with CtRoot _ => "Root" | CtLink _ => "Link" end.

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
          !ghost_mapG Σ Z unit}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.

(* ------------------------------------------------------------------------ *)
(* [isBlockP], its persistence instances and [isBlock_persist] now live
   in [program_logic/ewp.v], next to [isBlock] — [ownBlock] holds the
   mutability tag in exactly this persistent form. *)

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

(* [content] is the OCaml type of a vertex's [content] field: the
   two-constructor variant whose payloads are the inline records
   [Root {value}] and [Link {parent}].

   Naming it, rather than working with the underlying [VInline ...]
   values, is what keeps [val] out of the proofs. It matters because
   [compare_and_set_spec] types its "seen" and "new" arguments by a
   *single* [Encode A]: swinging a [Root]-tagged record for a
   [Link]-tagged one has no common [Encode record] instance (there is one
   per tag, [encode_record c]), so without this type every such CAS has
   to be instantiated at [A := val] with the identity encoding. With it,
   all three CAS sites in this file instantiate at [A := content]. *)

Global Instance Encode_content : Encode content :=
  {| encode' c := match c with
                  | CtRoot r => VInline "Root" r
                  | CtLink r => VInline "Link" r
                  end |}.

(* Registering the two constructors lets [imp_path] recover a [content]
   from a stored [VInline c r], which its encoding — a [match] on
   constructors — gives unification no way to invert. *)

Global Instance Inline_content_Root : Inline "Root" content :=
  {| inline_apply := CtRoot; inline_encode := λ _, eq_refl |}.

Global Instance Inline_content_Link : Inline "Link" content :=
  {| inline_apply := CtLink; inline_encode := λ _, eq_refl |}.

(* The stored shape of a [content] value, for the rules (notably the
   CAS) that inspect the raw [VInline] representation. *)

Lemma content_encode_inline c :
  #c = VInline (content_tag c) (content_loc c).
Proof. rewrite encode_encode'. by destruct c. Qed.

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

(* [content_own γ γc c ci] is the invariant-owned footprint of the
   content value [c] — the record [content_loc c] wrapped in [c]'s own
   constructor — as described by [ci]. The description is *diagonal*: a
   [CtRoot] value is only ever registered as [CRoot v], and a [CtLink]
   value as [CLink b], so a mismatched pair is simply [False]. Clients
   that learn a value's shape (say, in a match branch) therefore recover
   the shape of its registered description for free. *)

Definition content_own (γ γc : gname) (c : content) (ci : cinfo) : iProp Σ :=
  match c, ci with
  | CtRoot rc, CRoot v => rc ⤇ {| root_value := v |}
  | CtLink rc, CLink b =>
      ∃ (y : elem) j, rc ⤇ {| link_parent := y |} ∗ vertex γ y j ∗ ⌜(j < b)%Z⌝
  | _, _ => False
  end.

(* The field-level view of a content record. [ownRecord] is the right
   *statement* of the ownership — it says "this is a [Root {value}]" —
   but the rules that actually touch these records are the atomic ones
   ([imp_ERecordAccess_atomic], [ipat_PRecord_var_atomic], the CAS),
   which consume a single field's points-to because the record lives in
   a shared invariant. These two equations bridge between the two views,
   and are the only place the bridging happens. *)

Lemma content_own_root γ γc rc v :
  content_own γ γc (CtRoot rc) (CRoot v) ⊣⊢
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

Lemma content_own_link γ γc rc b :
  content_own γ γc (CtLink rc) (CLink b) ⊣⊢
  ∃ (lp : locations.loc) (y : elem) j,
    isBlockLocs rc [lp] ∗ isBlock rc DfracDiscarded Mut ∗ lp ↦ #y ∗ vertex γ y j ∗ ⌜(j < b)%Z⌝.
Proof.
  rewrite /content_own /ownRecord /ownBlock /=.
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
  ∃ (li lc : locations.loc) (c : content) (ci : cinfo),
    isBlockLocs x [li; lc] ∗
    lc ↦ #c ∗
    c ↪[γc]□ ci ∗
    ⌜∀ b, ci = CLink b → (b ≤ i)%Z⌝ ∗
    ⌜if content_root c then Root F x else ¬ Root F x⌝ ∗
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
  ∃ (M : gmap elem Z) (C : gmap content cinfo) (N : gmap Z unit)
    (F : elem → elem → Prop),
    ghost_map_auth γ 1 M ∗
    ghost_map_auth γc 1 C ∗
    ghost_map_auth γn 1 N ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜DSF F (dom M)⌝ ∗
    ⌜id_bounded M F⌝ ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ γc γn F x i) ∗
    ([∗ map] c ↦ ci ∈ C, content_own γ γc c ci).

Definition is_uf (γ γc γn : gname) : iProp Σ :=
  inv ufN (uf_inv γ γc γn).

(* An empty structure can always be created; the empty graph is trivially a
   disjoint set forest over the empty domain ([is_dsf_empty],
   [UnionFind02EmptyCreate.v]). *)

Lemma uf_alloc E :
  ⊢ |={E}=> ∃ γ γc γn, is_uf γ γc γn.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γ) "Hγ".
  iMod (ghost_map_alloc_empty (K:=content) (V:=cinfo)) as (γc) "Hγc".
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
(* Working with the invariant. *)

Instance inhabited_elem : Inhabited elem.
Proof. by (unfold elem, record; simpl; apply _). Qed.

Instance inhabited_cinfo : Inhabited cinfo.
Proof. exact (populate (CLink 0%Z)). Qed.

(* Every content record is a mutable block. This fact is persistent, so
   it can be read off [content_own] without giving it up. *)

Lemma content_own_mut γ γc c ci :
  content_own γ γc c ci -∗
  isBlock (content_loc c) DfracDiscarded Mut ∗ content_own γ γc c ci.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv & #Hlocs & #HP & Hlv)".
    iSplitR; [iExact "HP"|]. iExists lv. by iFrame "#∗".
  - rewrite content_own_link.
    iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj)".
    iSplitR; [iExact "HP"|]. iExists lp, y, j. by iFrame "#∗".
Qed.

(* Likewise, every content record has exactly one field, whichever tag
   it carries — [Root]'s [value] or [Link]'s [parent]. Callers that go
   on to read that field atomically need its location. *)

Lemma content_own_locs γ γc c ci :
  content_own γ γc c ci -∗
  (∃ lv : locations.loc, isBlockLocs (content_loc c) [lv]) ∗ content_own γ γc c ci.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv & #Hlocs & #HP & Hlv)".
    iSplitR; [by iExists lv|]. iExists lv. by iFrame "#∗".
  - rewrite content_own_link.
    iIntros "(%lp & %y & %j & #Hlocs & #HP & Hlp & #Hy & %Hj)".
    iSplitR; [by iExists lp|]. iExists lp, y, j. by iFrame "#∗".
Qed.

(* Whatever its tag, a registered content value owns exactly one field
   of its underlying record, outright. Consequently two [content_own]s
   over the same underlying record — whether for the same content value
   or for differently-tagged views of it — cannot coexist. This is the
   form the registration sites use to establish freshness, and how the
   CAS identifies the current content value from its bare location. *)

Lemma content_own_field γ γc c ci :
  content_own γ γc c ci -∗
  ∃ (lw : locations.loc) (w : val), isBlockLocs (content_loc c) [lw] ∗ lw ↦ w.
Proof.
  destruct c as [rc|rc]; destruct ci as [v|b]; try (by iIntros "[]").
  - rewrite content_own_root.
    iIntros "(%lv0 & #H1 & _ & H2)". iExists lv0, v. iFrame "H1 H2".
  - rewrite content_own_link.
    iIntros "(%lp & %y0 & %j0 & #H1 & _ & H2 & _)". iExists lp, #y0. iFrame "H1 H2".
Qed.

Lemma content_own_excl_loc γ γc c ci c' ci' :
  content_loc c = content_loc c' →
  content_own γ γc c ci -∗ content_own γ γc c' ci' -∗ False.
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

Lemma content_own_excl γ γc c ci ci' :
  content_own γ γc c ci -∗ content_own γ γc c ci' -∗ False.
Proof. by apply content_own_excl_loc. Qed.

(* The registered description's shape always matches the value's own
   tag — [content_own] is diagonal. *)

Lemma content_own_tag γ γc c ci :
  content_own γ γc c ci -∗
  ⌜if content_root c then ∃ v, ci = CRoot v else ∃ b, ci = CLink b⌝.
Proof.
  destruct c; destruct ci; simpl;
    try (by iIntros "[]"); iIntros "_"; iPureIntro; eauto.
Qed.

(* [content_info γc c j] is everything a reader of a vertex's content
   cell (a vertex whose identifier is [j]) learns about the loaded value
   [c]: it is registered, with a description whose shape matches [c]'s
   own tag and whose bound (in the link case) is dominated by [j], and
   its underlying record is a mutable single-field block. All of it is
   persistent — a snapshot that outlives the read. *)

Definition content_info (γc : gname) (c : content) (j : Z) : iProp Σ :=
  isBlock (content_loc c) DfracDiscarded Mut ∗
  (∃ lv : locations.loc, isBlockLocs (content_loc c) [lv]) ∗
  match c with
  | CtRoot _ => ∃ v, c ↪[γc]□ CRoot v
  | CtLink _ => ∃ b, c ↪[γc]□ CLink b ∗ ⌜(b ≤ j)%Z⌝
  end.

Global Instance content_info_persistent γc c j :
  Persistent (content_info γc c j).
Proof. destruct c; apply _. Qed.

Lemma content_own_info γ γc c ci j :
  (∀ b, ci = CLink b → (b ≤ j)%Z) →
  c ↪[γc]□ ci -∗
  content_own γ γc c ci -∗
  content_info γc c j ∗ content_own γ γc c ci.
Proof.
  intros Hbound.
  iIntros "#Hrc Hco".
  iDestruct (content_own_tag with "Hco") as %Htag.
  iDestruct (content_own_mut with "Hco") as "[#HP Hco]".
  iDestruct (content_own_locs with "Hco") as "[#Hlocs Hco]".
  iFrame "Hco". rewrite /content_info. iFrame "HP Hlocs".
  destruct c as [rc|rc]; simpl in Htag.
  - destruct Htag as [v ->]. by iExists v.
  - destruct Htag as [b ->]. iExists b. iFrame "Hrc". iPureIntro. by apply Hbound.
Qed.

(* The same argument one level up, for vertices: a registered vertex owns
   its own [content] cell, so a caller still holding that cell — as
   [make] does for the record it has just allocated — knows the vertex is
   not registered yet. *)

Lemma vertex_own_fresh_ne γ γc γn F x i li lc w :
  isBlockLocs x [li; lc] -∗ lc ↦ w -∗ vertex_own γ γc γn F x i -∗ False.
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
   what a successful CAS produces.

   Together they replace the ~15-line [iInv]/[ghost_map_lookup]/
   [big_sepM_delete] preamble (and its mirror image at closing time) that
   every atomic step in [set], [update] and [union] would otherwise
   repeat verbatim. *)

Lemma uf_inv_split γ γc γn z j lzi lzc :
  z ↪[γ]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ γc γn -∗
  ◇ ∃ (M : gmap elem Z) (C : gmap content cinfo) (N : gmap Z unit) F c ci,
      ⌜M !! z = Some j⌝ ∗ ⌜C !! c = Some ci⌝ ∗
      ⌜∀ b, ci = CLink b → (b ≤ j)%Z⌝ ∗
      ⌜if content_root c then Root F z else ¬ Root F z⌝ ∗
      ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
      ⌜DSF F (dom M)⌝ ∗ ⌜id_bounded M F⌝ ∗
      ghost_map_auth γ 1 M ∗ ghost_map_auth γc 1 C ∗ ghost_map_auth γn 1 N ∗
      c ↪[γc]□ ci ∗
      ▷ (lzc ↦ #c) ∗ ▷ (j ↪[γn] ()) ∗
      ▷ content_own γ γc c ci ∗
      ▷ ([∗ map] x ↦ i ∈ delete z M, vertex_own γ γc γn F x i) ∗
      ▷ ([∗ map] c' ↦ ci' ∈ delete c C, content_own γ γc c' ci').
Proof.
  iIntros "#Hzfrag #Hzlocs H".
  iDestruct "H" as (M C N F)
    "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
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
  iExists M, C, N, F, c, ci.
  iModIntro.
  do 7 (iSplitR; first done).
  iFrame "Hauth Hcauth Hnauth Hrc Hlc Htok Hco HM HC".
Qed.

Lemma uf_inv_reassemble γ γc γn (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) F z j lzi lzc c ci :
  M !! z = Some j →
  C !! c = Some ci →
  (∀ b, ci = CLink b → (b ≤ j)%Z) →
  (if content_root c then Root F z else ¬ Root F z) →
  (∀ x i, M !! x = Some i → representable i) →
  DSF F (dom M) →
  id_bounded M F →
  ghost_map_auth γ 1 M -∗
  ghost_map_auth γc 1 C -∗
  ghost_map_auth γn 1 N -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #c -∗
  c ↪[γc]□ ci -∗
  j ↪[γn] () -∗
  content_own γ γc c ci -∗
  ([∗ map] x ↦ i ∈ delete z M, vertex_own γ γc γn F x i) -∗
  ([∗ map] c' ↦ ci' ∈ delete c C, content_own γ γc c' ci') -∗
  uf_inv γ γc γn.
Proof.
  intros HMz HCrc Hbound HFz Hrep HdsfF HidF.
  iIntros "Hauth Hcauth Hnauth #Hzlocs Hlc #Hrc Htok Hco HM HC".
  iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth".
  do 3 (iSplitR; first done).
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

Lemma uf_inv_content_acc γ γc γn c ci :
  c ↪[γc]□ ci -∗
  ▷ uf_inv γ γc γn -∗
  ◇ (▷ content_own γ γc c ci ∗
     (▷ content_own γ γc c ci -∗ ▷ uf_inv γ γc γn)).
Proof.
  iIntros "#Hrc H".
  iDestruct "H" as (M C N F)
    "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  iDestruct (ghost_map_lookup with "Hcauth Hrc") as %HCrc.
  rewrite (big_sepM_delete _ C c ci); last exact HCrc.
  iDestruct "HC" as "[Hco HC]".
  iModIntro. iFrame "Hco".
  iIntros "Hco". iNext.
  iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth HM".
  do 3 (iSplitR; first done).
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

Lemma uf_inv_insert_vertex γ γc γn (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) F x i li lc c v :
  M !! x = None →
  C !! c = None →
  representable i →
  (∀ w iw, M !! w = Some iw → representable iw) →
  DSF F (dom M) →
  id_bounded M F →
  ghost_map_auth γ 1 (<[x := i]> M) -∗
  ghost_map_auth γc 1 (<[c := CRoot v]> C) -∗
  ghost_map_auth γn 1 N -∗
  isBlockLocs x [li; lc] -∗
  lc ↦ #c -∗
  c ↪[γc]□ CRoot v -∗
  i ↪[γn] () -∗
  content_own γ γc c (CRoot v) -∗
  ([∗ map] w ↦ iw ∈ M, vertex_own γ γc γn F w iw) -∗
  ([∗ map] c ↦ ci ∈ C, content_own γ γc c ci) -∗
  uf_inv γ γc γn.
Proof.
  intros HMx HCrc Hrepi Hrep HdsfF HidF.
  iIntros "Hauth Hcauth Hnauth #Hxlocs Hlc #Hrc Htok Hco HM HC".
  destruct c as [rc|rc]; last by iDestruct "Hco" as "[]".
  iExists (<[x := i]> M), (<[CtRoot rc := CRoot v]> C), N, F.
  iFrame "Hauth Hcauth Hnauth".
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
  iSplitL "HM Hlc Htok".
  { rewrite big_sepM_insert; last exact HMx.
    iSplitL "Hlc Htok".
    { iExists li, lc, (CtRoot rc), (CRoot v). iFrame "Hxlocs Hlc Hrc Htok".
      iSplit.
      { iPureIntro. intros b Hb. discriminate. }
      iPureIntro. simpl. eapply only_roots_outside_D; [exact HdsfF|].
      apply not_elem_of_dom. exact HMx. }
    iApply "HM". }
  rewrite big_sepM_insert; last exact HCrc.
  iFrame "Hco HC".
Qed.

(* Identifiers are injective: a vertex exclusively owns its own entry in
   the identifier registry [γn], so two distinct vertices cannot both
   claim the same identifier. *)

Lemma vertex_own_id_ne γ γc γn F a w i :
  vertex_own γ γc γn F a i -∗ vertex_own γ γc γn F w i -∗ False.
Proof.
  iIntros "(% & % & % & % & _ & _ & _ & _ & _ & Htoka)".
  iIntros "(% & % & % & % & _ & _ & _ & _ & _ & Htokw)".
  iCombine "Htoka Htokw" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* What [union]'s [assert (x.id <> y.id)] needs: distinct vertices have
   distinct — and, from [uf_inv]'s own [representable] conjunct, machine-
   comparable — identifiers. The invariant is handed back unchanged. *)

Lemma uf_inv_ids_distinct γ γc γn (a w : elem) (ia iw : Z) :
  a ≠ w →
  a ↪[γ]□ ia -∗ w ↪[γ]□ iw -∗ ▷ uf_inv γ γc γn -∗
  ◇ (⌜ia ≠ iw ∧ representable ia ∧ representable iw⌝ ∗ ▷ uf_inv γ γc γn).
Proof.
  intros Hne.
  iIntros "#Ha #Hw H".
  iDestruct "H" as (M C N F)
    "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
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
  iExists M, C, N, F. iFrame "Hauth Hcauth Hnauth HC".
  do 3 (iSplitR; first done).
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

Lemma vertex_own_widen_link γ γc γn (F0 : elem -> elem -> Prop) (a y' : elem) (M' : gmap elem Z) :
  M' !! a = None ->
  ([∗ map] w ↦ i ∈ M', vertex_own γ γc γn F0 w i) -∗
  [∗ map] w ↦ i ∈ M', vertex_own γ γc γn (link F0 a y') w i.
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
   new link value [CtLink rcn], registered with bound [b ≤ i]. The new
   record's [content_own] already carries the parent [y] and the strict
   bound [jy < b], which is everything [dsf_link_general] needs to
   justify widening [F] by the edge [z → y] without re-checking [y]'s
   root-status. *)

Lemma uf_inv_reassemble_link γ γc γn (M : gmap elem Z) (C : gmap content cinfo)
    (N : gmap Z unit) F z i b lzi lzc (rcn : elem) :
  M !! z = Some i →
  C !! CtLink rcn = None →
  Root F z →
  (b ≤ i)%Z →
  (∀ x ix, M !! x = Some ix → representable ix) →
  DSF F (dom M) →
  id_bounded M F →
  ghost_map_auth γ 1 M -∗
  ghost_map_auth γc 1 (<[CtLink rcn := CLink b]> C) -∗
  ghost_map_auth γn 1 N -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #(CtLink rcn) -∗
  CtLink rcn ↪[γc]□ CLink b -∗
  i ↪[γn] () -∗
  content_own γ γc (CtLink rcn) (CLink b) -∗
  ([∗ map] x ↦ ix ∈ delete z M, vertex_own γ γc γn F x ix) -∗
  ([∗ map] c ↦ ci ∈ C, content_own γ γc c ci) -∗
  uf_inv γ γc γn.
Proof.
  intros HMz HCr Hroot Hbi Hrep HdsfF HidF.
  iIntros "Hauth Hcauth Hnauth #Hzlocs Hlc #Hr Htok Hco HM HC".
  (* Peek at the new link's parent [y]: a registered vertex whose
     identifier sits strictly below [b], hence strictly below [i]. *)
  iDestruct "Hco" as (y jy) "(Hrec & #Hy & %Hjy)".
  iDestruct (vertex_frag with "Hy") as "#Hyfrag".
  iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
  assert (Hzy : z ≠ y).
  { intros ->. rewrite HMz in HMy. simplify_eq. lia. }
  pose proof (dsf_link_general M F z y i jy HdsfF HidF HMz HMy Hroot
                ltac:(lia) Hzy) as [HdsfF' HidF'].
  iExists M, (<[CtLink rcn := CLink b]> C), N, (link F z y).
  iFrame "Hauth Hcauth Hnauth".
  do 3 (iSplitR; first done).
  iSplitL "HM Hlc Htok".
  { rewrite (big_sepM_delete _ M z i); last exact HMz.
    iSplitL "Hlc Htok".
    { iExists lzi, lzc, (CtLink rcn), (CLink b).
      iFrame "Hzlocs Hlc Hr Htok".
      iSplit.
      { iPureIntro. intros b' Hb'. injection Hb' as ->. exact Hbi. }
      iPureIntro. simpl. intros [Hr']. eapply (Hr' y). right. done. }
    iApply (vertex_own_widen_link with "HM").
    rewrite lookup_delete_eq. done. }
  rewrite big_sepM_insert; last exact HCr.
  iSplitL "Hrec".
  { iExists y, jy. iFrame "Hrec Hy". iPureIntro. exact Hjy. }
  iApply "HC".
Qed.

(* Registering a fresh vertex: the caller owns the vertex record — its
   [id] field holding a fresh identifier, its [content] cell a fresh,
   unregistered [Root] content — and trades all of it for the persistent
   [vertex] fact. *)

Lemma register_vertex γ γc γn i (c : content) v r :
  representable i →
  is_uf γ γc γn -∗
  i ↪[γn] () -∗
  content_own γ γc c (CRoot v) -∗
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
  iDestruct "H" as (M C N F)
    "(>Hauth & >Hcauth & >Hnauth & >%Hrep & >%HdsfF & >%HidF & HM & HC)".
  destruct (M !! r) as [ix|] eqn:HMx.
  { iDestruct (big_sepM_lookup _ _ r ix with "HM") as "Hvo"; first exact HMx.
    iAssert (▷ False)%I with "[Hlc Hvo]" as ">[]".
    iNext. iApply (vertex_own_fresh_ne with "Hxlocs Hlc Hvo"). }
  destruct (C !! c) as [ci0|] eqn:HCc.
  { iDestruct (big_sepM_lookup _ _ _ ci0 with "HC") as "Hco0"; first exact HCc.
    iAssert (▷ False)%I with "[Hco Hco0]" as ">[]".
    iNext. iApply (content_own_excl γ γc c (CRoot v) ci0 with "Hco Hco0"). }
  iMod (ghost_map_insert c (CRoot v) with "Hcauth") as "[Hcauth Hcfrag]";
    first exact HCc.
  iMod (ghost_map_elem_persist with "Hcfrag") as "#Hcfrag".
  iMod (ghost_map_insert r i with "Hauth") as "[Hauth Hxfrag]";
    first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth Hlc Htok Hco HM HC]") as "_".
  { iNext.
    iApply (uf_inv_insert_vertex
              with "Hauth Hcauth Hnauth Hxlocs Hlc Hcfrag Htok Hco HM HC"); try done. }
  iModIntro.
  iExists li, lc. iFrame "Hxfrag Hxlocs HxP Hli".
Qed.

(* Atomically reading a vertex's content cell: the caller supplies a
   proof that the scrutinee evaluates to the vertex and receives the
   loaded value's [content_info] snapshot. *)

Lemma read_vertex {ζ : exn → iProp Σ} {Ψ η} γ γc γn z j e :
  is_uf γ γc γn -∗
  vertex γ z j -∗
  imp (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ z' : elem, ⌜z' = z⌝ }} -∗
  imp (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ λ c : content, content_info γc c j }}.
Proof.
  iIntros "#Hinv #Hz He".
  iDestruct "Hz" as (lzi lzc) "(#Hzfrag & #Hzlocs & #HzP & #Hzli)".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lzi; lzc] z
            with "Hzlocs He []").
  { list_z.length; lia. }
  iNext.
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (M C N F c ci)
    "(%HMz & %HCc & %Hbound & %HFz & %Hrep & %HdsfF & %HidF &
      Hauth & Hcauth & Hnauth & #Hrc & Hlc & Htok & Hco & HM & HC)".
  iModIntro.
  iExists c.
  iSplitL "Hlc"; first by iFrame.
  iIntros "!> Hlc".
  iDestruct (content_own_info with "Hrc Hco") as "[#Hinfo Hco]"; first exact Hbound.
  iMod ("Hclose" with "[Hauth Hcauth Hnauth Hlc Htok Hco HM HC]") as "_".
  { iNext.
    iApply (uf_inv_reassemble γ γc γn M C N F z j lzi lzc c ci
              with "Hauth Hcauth Hnauth Hzlocs Hlc Hrc Htok Hco HM HC"); done. }
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

Lemma vertex_ids_ne γ γc γn (a w : elem) ia iw :
  a ≠ w →
  is_uf γ γc γn -∗
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

(* Re-reading the single field of an already-registered content record,
   without going through any vertex: these accessors produce exactly the
   mask-changing fupd that the atomic rules ([ipat_PRecord_var_atomic],
   [imp_ERecordAccess_atomic]) consume. For a [Root] record the field's
   value is pinned by the registration itself; for a [Link] record the
   caller learns that the loaded parent is a vertex strictly below the
   registered bound — even if the record's erstwhile vertex has moved
   on. *)

Lemma uf_root_value_acc γ γc γn rc v lp (Φ : val → iProp Σ) :
  is_uf γ γc γn -∗
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

Lemma uf_link_parent_acc γ γc γn rc b lp (Φ : val → iProp Σ) :
  is_uf γ γc γn -∗
  CtLink rc ↪[γc]□ CLink b -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < b)%Z⌝ -∗ vertex γ y j -∗ Φ #y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ w -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ w).
Proof.
  iIntros "#Hinv #Hrc #Hlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_content_acc with "Hrc H") as "[Hco Hback]".
  iEval (rewrite content_own_link) in "Hco".
  iDestruct "Hco" as (lp' y j) "(#Hlocs' & #HP & Hlp & #Hy & >%Hj)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hclose" with "[Hback Hlp]") as "_".
  { iApply "Hback". iNext. rewrite content_own_link.
    iExists lp', y, j. iFrame "Hlocs' HP Hlp Hy". done. }
  iModIntro. iApply ("HΦ" with "[//] Hy").
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
      γ γc γn z i lzc (rce : elem) vexp (cnew : content) cinew :
  (∀ b, cinew = CLink b → (b ≤ i)%Z) →
  is_uf γ γc γn -∗
  z ↪[γ]□ i -∗
  (∃ li, isBlockLocs z [li; lzc]) -∗
  CtRoot rce ↪[γc]□ CRoot vexp -∗
  isBlock rce DfracDiscarded Mut -∗
  content_own γ γc cnew cinew -∗
  ▷ (∀ b : bool,
       (if b then cnew ↪[γc]□ cinew else content_own γ γc cnew cinew) -∗ Φ b) -∗
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
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (M C N F c0 ci0)
    "(%HMz & %HCc0 & %Hbound0 & %HFz & %Hrep & %HdsfF & %HidF &
      Hauth & Hcauth & Hnauth & #Hc0 & Hlc & Htok & Hco0 & HM & HC)".
  iAssert (▷ (isBlock (content_loc c0) DfracDiscarded Mut ∗ content_own γ γc c0 ci0))%I
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
    iMod ("Hclose" with "[Hauth Hcauth Hnauth Hlc' Htok Hco0 HM HC]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn M C N F z i lzi lzc c0 ci0
                with "Hauth Hcauth Hnauth Hzlocs Hlc' Hc0 Htok Hco0 HM HC"); done. }
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
    - iApply (content_own_excl with "Hco' Hco0").
    - iDestruct (big_sepM_lookup _ _ cnew ci1 with "HC") as "Hco1".
      { rewrite lookup_delete_ne; done. }
      iApply (content_own_excl with "Hco' Hco1"). }
  iMod (ghost_map_insert cnew cinew with "Hcauth") as "[Hcauth Hnewfrag]";
    first exact HCnew.
  iMod (ghost_map_elem_persist with "Hnewfrag") as "#Hnewfrag".

  (* The absorbed [Root] value goes back into the registry's big star as
     an ordinary (now unreachable) entry. *)
  iAssert ([∗ map] c' ↦ ci' ∈ C, content_own γ γc c' ci')%I
    with "[Hco0 HC]" as "HC".
  { rewrite (big_sepM_delete _ C (CtRoot rce) (CRoot vexp)); last exact HCe.
    iFrame "Hco0 HC". }

  destruct cinew as [v'|b].

  { (* The new content is a [Root]: [z] stays a root, [F] is unchanged. *)
    destruct cnew as [rcn|rcn]; last by iDestruct "Hco'" as "[]".
    iAssert ([∗ map] c' ↦ ci' ∈ delete (CtRoot rcn) (<[CtRoot rcn := CRoot v']> C),
               content_own γ γc c' ci')%I with "[HC]" as "HC".
    { rewrite delete_insert_eq (delete_id _ _ HCnew). iApply "HC". }
    iMod ("Hclose" with "[Hauth Hcauth Hnauth Hlc' Htok Hco' HM HC]") as "_".
    { iNext.
      iApply (uf_inv_reassemble γ γc γn M (<[CtRoot rcn := CRoot v']> C) N F z i
                lzi lzc (CtRoot rcn) (CRoot v')
                with "Hauth Hcauth Hnauth Hzlocs Hlc' Hnewfrag Htok Hco' HM HC");
        first [ done | apply lookup_insert_eq | discriminate | assumption ]. }
    iModIntro. iApply ("HΦ" $! true with "Hnewfrag"). }

  (* The new content is a [Link]: [z] stops being a root and [F] grows
     by the new edge. *)
  destruct cnew as [rcn|rcn]; first by iDestruct "Hco'" as "[]".
  iMod ("Hclose" with "[Hauth Hcauth Hnauth Hlc' Htok Hco' HM HC]") as "_".
  { iNext.
    iApply (uf_inv_reassemble_link γ γc γn M C N F z i b lzi lzc rcn
              with "Hauth Hcauth Hnauth Hzlocs Hlc' Hnewfrag Htok Hco' HM HC");
      first [ done | exact HFz | (apply Hbound; reflexivity) ]. }
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
  iIntros "#HG".
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  iIntros "#Hinv".
  iApply imp_please; iNext.

  (* Goal: [ let id = G.fresh() and content = Root { value = v } in ... ] *)
  imp_let $! (λ i : Z, i ↪[γn] () ∗ ⌜representable i⌝)%I
          $! (λ r : content, content_own γ γc r (CRoot v))%I.
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
   1. Read [x.content] through [read_vertex], obtaining the loaded
      value's persistent [content_info] snapshot.
   2. Case on the loaded value:
      - [CtRoot]: the first branch matches with a wildcard sub-pattern
        (no field read) and returns [x]; conclude with [j := i].
      - [CtLink]: the first branch is refuted; the second branch
        pattern-matches [{ parent = y }] against the link record,
        *re-reading* the racy [parent] field. [ipat_PRecord_var_atomic]
        performs this single field load under [uf_inv], with
        [uf_link_parent_acc] supplying its fupd: even if [x] has moved
        on, the registration [CtLink rc ↪[γc]□ CLink b] guarantees the
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

  (* Goal: [ match x.content with ... ]. The scrutinee is read atomically
     through [read_vertex]; every branch receives the loaded value's
     [content_info] snapshot. *)
  imp_match content.
  { iApply (read_vertex with "Hinv Hx"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]: no field read; [x] is returned, with [j := i]. *)
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
  iIntros (y j Hj) "#Hy".

  (* Recurse on the parent: [j < b ≤ i]. *)
  imp_app τ[elem].
  iIntros "Hm".
  iSpecialize ("Hm" $! j with "Hinv Hy").
  iApply (imp_wand with "Hm").
  iIntros (z) "(%j0 & #Hz & %Hj0)".
  iExists j0. iFrame "Hz". iPureIntro. lia.
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

Definition set_content_spec (γ γc γn : gname) (x : elem) (cx' : content) (m : microvx) : iProp Σ :=
  ∀ i v,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    content_own γ γc cx' (CRoot v) -∗
    imp m {{ λ _ : unit, True }}.

Lemma set_proof γ γc γn η :
  ▷ in_env "set" (λ set, □ iSpec τ[elem; content] set (set_content_spec γ γc γn)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  imp (eval η (EAnonFun (AnonFun "x" (EAnonFun __set_fun))))
    {{ λ c, □ iSpec τ[elem; content] c (set_content_spec γ γc γn) }}.
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x cx' i v).
  iIntros "#Hinv #Hx Hcx'".
  iApply imp_please; iNext.

  (* [let z = findc x in ...]: chase [x] to a root [z], whose identifier
     [j] is at most [x]'s. The reachability snapshot [findc] also returns
     is irrelevant here (only [union] consumes it). *)
  imp_let.
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (z) "(%j & #Hz & %Hj & _)".
  subst imp_let_B imp_let_HB.

  (* [let cx = z.content in ...]: read [z]'s content cell through
     [read_vertex], remembering the loaded value's snapshot. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc c j)%I).
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
              (λ b : bool, if b then True else content_own γ γc cx' (CRoot v))%I
              with "[Hcx'] []").

    { (* The CAS, through [uf_cas_fupd]. *)
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hz"). imp_path. }
      iIntros "Hptr Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_fupd
               (λ b, if b then True else content_own γ γc cx' (CRoot v))%I
               with "Hinv [] Hptr Hrc HrcP Hcx'").
      { discriminate. }
      { iApply (vertex_frag with "Hz"). }
      { iNext. iIntros ([|]) "H"; [done | iExact "H"]. } }

    (* The two branches: on success there is nothing left to do; on
       failure the caller's content comes back and [set] retries from [z]
       (whose identifier [j] is a valid decreasing measure). *)
    iIntros ([|]) "HΦb".
    { iApply imp_EUnit. done. }
    imp_app τ[elem; content].
    iIntros "Hm".
    unfold set_content_spec.
    iApply ("Hm" $! j v with "Hinv Hz HΦb"). }

  (* [Link _ -> set x cx']: [z] is no longer a root, so restart from
     [z] — again with the strictly smaller identifier [j]. *)
  rewrite {2}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; content].
  iIntros "Hm".
  unfold set_content_spec.
  iApply ("Hm" $! j v with "Hinv Hz Hcx'").
Qed.

(* The public, one-argument [set x v]: allocates the fresh [Root {value =
   v}] record and calls the internal, two-argument [set] above. *)

Definition set_spec (γ γc γn : gname) (x : elem) (v : val) (m : microvx) : iProp Σ :=
  ∀ i,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    imp m {{ λ _ : unit, True }}.

Lemma set_wrapper_proof γ γc γn η :
  in_env "set" (λ setv, □ iSpec τ[elem; content] setv (set_content_spec γ γc γn)) η -∗
  imp (eval η (EAnonFun __set)) {{ λ c, □ iSpec τ[elem; val] c (set_spec γ γc γn) }}.
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
      (λ c : content, content_own γ γc c (CRoot v))%I).
  { imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (cx') "Hco".
  imp_app τ[elem; content].
  iIntros "Hm".
  unfold set_content_spec.
  iApply ("Hm" $! i v with "Hinv Hx Hco").
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


Lemma update_proof γ γc γn η :
  ▷ in_env "update" (λ update, □ iSpec τ[elem; val] update (update_spec γ γc γn)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γc γn)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
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

  (* [let z = findc x in ...]: chase [x] to a root [z]. *)
  iApply (imp_ELet_var (B:=elem)).
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  iIntros (z) "(%j & #Hz & %Hj & _)".

  (* [let cx = z.content in ...]: read [z]'s content cell through
     [read_vertex]. The snapshot includes the record's field location,
     which the [Root] branch immediately re-reads. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc c j)%I).
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

    iApply (imp_EIfThenElse _ _ _ _ (λ _ : bool, True)%I).

    { (* The CAS. Unlike [set]'s, the "new value" argument is built here:
         a freshly allocated [Root { value = f v }] record, whose
         ownership this attempt consumes (each retry allocates its own). *)
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hz"). imp_path. }
      { (* Allocate [Root { value = f v }], already typed as a [content].
           [f] is only known to be safe, so nothing is remembered about
           the stored value. *)
        set_postcondition
          (λ c : content, ∃ w : val, content_own γ γc c (CRoot w))%I.
        imp_record $! root_fields.
        { iApply (imp_EApp' (B:=val)).
          { imp_path. }
          { imp_path. }
          iIntros "!>" (f0 w0) "-> ->".
          iApply "Hf". }
        iIntros (c) "(%r & -> & %xs & Hown & _)".
        iExists xs. iApply "Hown". }
      iIntros "Hptr (%w & Hco') Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_fupd (λ b, True)%I with "Hinv [] Hptr Hrc HrcP Hco' []").
      { discriminate. }
      { iApply (vertex_frag with "Hz"). }
      { iNext. iIntros ([|]) "_"; done. } }

    (* Both branches: on success there is nothing left to do; on failure
       [update] retries from [z]. *)
    iIntros ([|]) "_".
    { iApply imp_EUnit. done. }
    imp_app τ[elem; val].
    iIntros "Hm3".
    unfold update_spec.
    iApply ("Hm3" with "Hf Hinv Hz"). }

  (* [Link _ -> update x f]: [z] is no longer a root — restart from [z]. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; val].
  iIntros "Hm3".
  unfold update_spec.
  iApply ("Hm3" with "Hf Hinv Hz").
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

Definition union_post (γc : gname) (x y : elem) (ov : option val) : iProp Σ :=
  match ov with
  | None => ⌜same_class x y⌝
  | Some r => ∃ z (rc : elem),
      (⌜ev_reaches x z⌝ ∨ ⌜ev_reaches y z⌝) ∗ CtRoot rc ↪[γc]□ CRoot r
  end.

Definition union_spec (γ γc γn : gname) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ i j,
    is_uf γ γc γn -∗
    vertex γ x i -∗
    vertex γ y j -∗
    imp m {{ union_post γc x y }}.

(* Every recursive [union x y] call happens after [findc] has replaced
   [x]/[y] by their representatives [a]/[y'], so its result is stated
   about [a]/[y']. This prepends the caller's own one-hop snapshots to
   both sides of that result, which is all it takes to turn it back into
   a statement about [x]/[y] — no shared graph history required, since
   [ev_reaches] is a chain of independently-witnessed hops. Used at all
   four sites that fall through to the recursive call. *)

Lemma union_post_extend γc (x y a y' : elem) ov :
  snap_reaches x a →
  snap_reaches y y' →
  union_post γc a y' ov -∗ union_post γc x y ov.
Proof.
  intros Hsx Hsy.
  destruct ov as [r|]; simpl.
  - iIntros "(%z & %rc & [%Hz|%Hz] & #Hrc)"; iExists z, rc; iFrame "Hrc".
    + iLeft. iPureIntro. eapply rtc_l; [exact Hsx | exact Hz].
    + iRight. iPureIntro. eapply rtc_l; [exact Hsy | exact Hz].
  - iIntros "%Hsc". destruct Hsc as (z & Hza & Hzy).
    iPureIntro. exists z.
    split; (eapply rtc_l; [eassumption | assumption]).
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
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
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

  (* [let x = findc x and y = findc y in ...]: chase both arguments to
     their (possibly already stale) roots [a] and [y']. *)
  imp_let $! (λ z : elem, ∃ i', vertex γ z i' ∗ ⌜(i' ≤ i)%Z⌝ ∗
                ∃ Dx Fx, ⌜DSF Fx Dx⌝ ∗ ⌜x ∈ Dx⌝ ∗ ⌜Repr Fx x z⌝)%I
          $! (λ z : elem, ∃ j', vertex γ z j' ∗ ⌜(j' ≤ j)%Z⌝ ∗
                ∃ Dy Fy, ⌜DSF Fy Dy⌝ ∗ ⌜y ∈ Dy⌝ ∗ ⌜Repr Fy y z⌝)%I.
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! i with "Hinv Hx"). }
  { imp_app τ[elem].
    iIntros "Hm".
    unfold findc_spec.
    iApply ("Hm" $! j with "Hinv Hy"). }
  iIntros (a y') "(%i' & #Hav & %Hi' & %Dx & %Fx & %HdsfFx & %HxDx & %HReprXa)
                  (%j' & #Hy'v & %Hj' & %Dy & %Fy & %HdsfFy & %HyDy & %HReprYy')".
  (* The single-snapshot reachability facts are all the rest of the proof
     ever needs from [findc]'s two graphs; [union_post_extend] chains
     them onto whatever a recursive call returns. *)
  assert (Hsx : snap_reaches x a) by (exists Dx, Fx; auto).
  assert (Hsy : snap_reaches y y') by (exists Dy, Fy; auto).
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
    iPureIntro. eexists.
    split.
    { apply rtc_once. exact Hsx. }
    { apply rtc_once. exact Hsy. } }

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
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc c i')%I).
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
            (λ c : content, content_own γ γc c (CLink i'))%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists y', j'. iFrame "Hown Hy'v". iPureIntro. exact Hlt. }
        iIntros "-> Hptr Hco' Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_fupd (λ _, True)%I γ γc γn a i'
                  with "Hinv [] Hptr Hrc HrcP Hco' []").
        { intros b0 Hb0. injection Hb0 as ->. lia. }
        { iApply (vertex_frag with "Hav"). }
        { iNext. iIntros ([|]) "_"; done. } }

      { iIntros "_".
        (* CAS succeeded: return [Some v], where [v] is the absorbed
           root's value — still described by the persistent
           [Hrc : CtRoot rc ↪[γc]□ CRoot v]. *)
        imp_data.
        iIntros (? ->). simpl.
        iExists a, rc. iFrame "Hrc". iLeft. iPureIntro.
        by apply rtc_once. }
      { iIntros "_".
        (* CAS failed: retry from [a]/[y'] and chain this call's own
           one-hop snapshots onto the recursive result. *)
        imp_app τ[elem; elem].
        iIntros "Hm3".
        unfold union_spec.
        iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        iApply (union_post_extend with "Hov"); [exact Hsx | exact Hsy]. } }

    { (* [_ -> union x y]: [x.content] raced ahead of us (already a
         [Link], not a [Root]) — retry via the recursive call. *)
      rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      unfold union_spec.
      iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      iApply (union_post_extend with "Hov"); [exact Hsx | exact Hsy]. } }

  { iIntros "%Hcmp2".
    (* [x.id <= y.id]: the mirror image — CAS [Link { parent = x }] into
       [y]'s content cell, registering it as [CLink j'] (which needs
       [i' < j'], from [Hcmp2] together with [Hij]). Every step below is
       the previous branch's with [a]/[i'] and [y']/[j'] exchanged. *)
    assert (Hlt : (i' < j')%Z).
    { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γc c j')%I).
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
            (λ c : content, content_own γ γc c (CLink j'))%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists a, i'. iFrame "Hown Hav". iPureIntro. exact Hlt. }
        iIntros "-> Hptr Hco' Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_fupd (λ _, True)%I γ γc γn y' j'
                  with "Hinv [] Hptr Hrc HrcP Hco' []").
        { intros b0 Hb0. injection Hb0 as ->. lia. }
        { iApply (vertex_frag with "Hy'v"). }
        { iNext. iIntros ([|]) "_"; done. } }

      { iIntros "_".
        imp_data.
        iIntros (? ->). simpl.
        iExists y', rc. iFrame "Hrc". iRight. iPureIntro.
        by apply rtc_once. }
      { iIntros "_".
        imp_app τ[elem; elem].
        iIntros "Hm3".
        unfold union_spec.
        iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
        iApply (imp_wand with "Hm3").
        iIntros (ov) "Hov".
        iApply (union_post_extend with "Hov"); [exact Hsx | exact Hsy]. } }

    { rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      unfold union_spec.
      iSpecialize ("Hm3" $! i' j' with "Hinv Hav Hy'v").
      iApply (imp_wand with "Hm3").
      iIntros (ov) "Hov".
      iApply (union_post_extend with "Hov"); [exact Hsx | exact Hsy]. } }
Qed.

End ConcurrentUnionFind.
