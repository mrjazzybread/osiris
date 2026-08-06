From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From osiris Require Import osiris.

Require Import UnionFind01Data UnionFind03Link UnionFind08DataConc UnionFind09Reaches.

(* ------------------------------------------------------------------------ *)
(* Representation predicates. *)
Section repr.
Local Notation elem := record.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.
(* [vertex γ x i] is the persistent knowledge that [x] is a vertex of the
   structure with identifier [i]. *)
Definition vertex (γ : gname) (x : elem) (i : Z) : iProp Σ :=
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
   [imp_ERecordAccess_atomic], [ipat_PRecord_atomic], and the CAS
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
End repr.
(* ------------------------------------------------------------------------ *)
(* Working with the predicates. *)
Section repr_api.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ content cinfo,
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.
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
  assert (Hne : w ≠ a) by (intros ->; by rewrite Ha in Hw).
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

End repr_api.
