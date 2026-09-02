From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From osiris Require Import osiris.

Require Import UnionFind08DataConc UnionFind09SameClass.

(* ------------------------------------------------------------------------ *)
(* Representation predicates. *)
Section repr.
Local Abbreviation elem := record.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* [vertex γ x i] is the persistent knowledge that [x] is a vertex of the
   structure with identifier [i]. *)
Definition vertex (γ : uf_names) (x : elem) (i : Z) : iProp Σ :=
  ∃ (li lc : locations.loc),
    x ↪[γ.(uf_vert)]□ i ∗
    isBlockLocs x [li; lc] ∗
    isBlock x DfracDiscarded Mut ∗
    li ↦□ #i.
Global Instance vertex_persistent γ x i : Persistent (vertex γ x i).
Proof. apply _. Qed.

(* ------------------------------------------------------------------------ *)
(* The two shapes of content record. *)

(* A [Root] record, entirely persistently: its single [value] field holds
   [v] and always will. The field is never written after allocation, so
   rather than keeping it in the invariant and lending it out for each
   read, the invariant discards its fraction once and hands the result to
   anyone who loads the record. A reader of [root.value] therefore needs
   no accessor and no open at all — an ordinary persistent field read. *)

Definition root_val (rc : record) (v : val) : iProp Σ :=
  ∃ lv : locations.loc,
    isBlockLocs rc [lv] ∗ isBlock rc DfracDiscarded Mut ∗ lv ↦□ v.

Global Instance root_val_persistent rc v : Persistent (root_val rc v).
Proof. apply _. Qed.

(* Turning a freshly allocated [Root] record into the persistent form the
   invariant keeps. This is a one-way step, and it is where the decision
   that a payload is immutable is actually taken: [set] and [update] CAS a
   whole new record in rather than writing the field, so nothing ever
   needs the exclusive points-to back. *)

Lemma root_val_alloc rc (v : val) :
  rc ⤇ {| root_value := v |} ==∗ root_val rc v.
Proof.
  iIntros "Hrec".
  rewrite /ownRecord /ownBlock /=.
  iDestruct "Hrec" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv) "[-> Hlv]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs".
  iMod (gen_heap.pointsto_persist with "Hlv") as "#Hlv".
  iModIntro. iExists lv. by iFrame "Hlocs HP Hlv".
Qed.

(* A [Link] record held by vertex [h], whose identifier is [i]. Its
   [parent] field IS written — that is what path compression does — so
   this one stays in the invariant, owned by [h]'s own entry.

   All it says about the vertex [y] the field currently holds is that [y]
   is a registered vertex of a strictly smaller identifier, and that
   following the pointer stays inside [h]'s class. Nothing says it is an
   edge of anything: compression reroutes it freely, and this is exactly
   the property compression preserves. *)

Definition link_field (γ : uf_names) (rc : record) (lp : locations.loc)
    (h : elem) (i : Z) : iProp Σ :=
  ∃ (y : elem) jy,
    isBlock rc DfracDiscarded Mut ∗ lp ↦ #y ∗
    vertex γ y jy ∗ ⌜(jy < i)%Z⌝ ∗ same_class γ h y.

(* [linked γ x rc lp]: [x] holds the link record [rc], whose [parent] field
   lives at [lp]. *)

Definition linked (γ : uf_names) (x : elem) (rc : record)
    (lp : locations.loc) : iProp Σ :=
  x ↪[γ.(uf_link)]□ Some rc ∗ isBlockLocs rc [lp].

Global Instance linked_persistent γ x rc lp : Persistent (linked γ x rc lp).
Proof. apply _. Qed.

(* [linked]'s negation is a resource: a vertex that is still a root
   owns [x ↪[γ.(uf_link)] None] exclusively. *)

Lemma linked_not_root γ x rc lp :
  linked γ x rc lp -∗ x ↪[γ.(uf_link)] None -∗ False.
Proof.
  iIntros "[H1 _] H2".
  by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hbad _].
Qed.

(* Both halves are timeless, but the [record = loc] identification puts
   several [ghost_mapG]s in scope at the same key type, and resolution
   picks the wrong one for the array map. Hence the explicit instance. *)

Global Instance linked_timeless γ x rc lp : Timeless (linked γ x rc lp).
Proof.
  rewrite /linked /isBlockLocs. apply bi.sep_timeless; first apply _.
  apply bi.sep_timeless; last apply _.
  apply (ghost_map_elem_timeless (V := list loc)).
Qed.

Lemma linked_locs γ x rc lp : linked γ x rc lp -∗ isBlockLocs rc [lp].
Proof. by iIntros "[_ $]". Qed.

Lemma linked_agree γ x rc rc' lp lp' :
  linked γ x rc lp -∗ linked γ x rc' lp' -∗ ⌜rc = rc' ∧ lp = lp'⌝.
Proof.
  iIntros "[H1 #Hl1] [H2 #Hl2]".
  iDestruct (ghost_map_elem_agree with "H1 H2") as %[= ->].
  iDestruct (isBlockLocs_valid with "Hl1 Hl2") as %[= ->].
  done.
Qed.

(* ------------------------------------------------------------------------ *)

(* [cell_own γ R V x i c] is what the invariant owns and knows about
   vertex [x]'s content cell, given that it currently holds [c].

   The tag of [c] is [x]'s root-status: a cell holds a [Root] iff its
   vertex is its own representative. That equivalence is the entire
   coupling between the structure and its abstract state, and it is what
   makes an atomic read of a content cell a linearization point. *)

Definition cell_own (γ : uf_names) (R : elem → elem) (V : elem → val)
    (x : elem) (i : Z) (c : content) : iProp Σ :=
  match c with
  | CtRoot rc => ⌜R x = x⌝ ∗ x ↪[γ.(uf_link)] None ∗ root_val rc (V x)
  | CtLink rc =>
      ∃ lp, ⌜R x ≠ x⌝ ∗ linked γ x rc lp ∗ link_field γ rc lp x i
  end.

(* Root-ness is ANTI-monotone, and this is where that is recorded.

   Every CAS in the implementation swings a [Root] value OUT of a cell, so
   a vertex that has been linked away never becomes a root again. [linked]
   is the persistent witness of having been linked; a root's cell owns the
   [x ↪[γ.(uf_link)] None] that contradicts it. So a [linked] obtained at
   ONE instant refutes root-ness at EVERY LATER one — the fact holds
   against whatever [cell_own] the invariant happens to hold now, not just
   against the one it was minted from.

   This is what the [false] case of [eq] turns on. That case has to know,
   while it is still inside [findc y], how a LATER read of [x.content]
   will turn out; being able to rule out [Root] from a [linked] observed
   earlier is exactly the half of that argument which is about the
   structure rather than about prophecy.

   Note the shape: [linked]'s negation is a RESOURCE living in the
   invariant, not a proposition a reader can carry away, so the refutation
   has to be stated against a [cell_own] and cannot be a fact about
   [content_info] alone. *)

Lemma cell_own_linked γ R V x i c rc lp :
  linked γ x rc lp -∗ cell_own γ R V x i c -∗
  ⌜c = CtLink rc⌝ ∗ cell_own γ R V x i c.
Proof.
  iIntros "#Hlk Hcell". destruct c as [rc'|rc'].
  - (* A root's cell owns the token [linked] refutes. *)
    iDestruct "Hcell" as "(%Hr & Htok & Hval)".
    iDestruct (linked_not_root with "Hlk Htok") as "[]".
  - iDestruct "Hcell" as "(%lp' & %Hr & #Hlk' & Hlf)".
    iDestruct (linked_agree with "Hlk' Hlk") as %[-> ->].
    iSplitR; first done. iExists lp. by iFrame "Hlk' Hlf".
Qed.

(* [vertex_own γ R V x i] is the invariant-owned footprint of the
   vertex [x]: its content cell, together with whatever that cell's
   current content owns.

   What is deliberately NOT here is the identifier registry token. It used
   to be, so that its exclusivity would make identifiers injective — but
   no step on a vertex's cell ever reads or moves it, so keeping it in the
   per-vertex footprint meant every accessor had to carry it in and out
   for nothing. It now sits in [uf_inv] as one [id_tokens] conjunct
   (below), which is also the shape the argument actually wants: a single
   map from which injectivity is read off. *)

Definition vertex_own (γ : uf_names) (R : elem → elem) (V : elem → val)
    x i : iProp Σ :=
  ∃ (li lc : locations.loc) (c : content),
    isBlockLocs x [li; lc] ∗
    lc ↦ #c ∗
    cell_own γ R V x i c.

End repr.

(* ------------------------------------------------------------------------ *)
(* Working with the predicates. *)
Section repr_api.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* [content_info γ x c] is everything a reader of vertex [x]'s content
   cell learns about the loaded value [c], and it is entirely persistent:
   the record is a mutable single-field block, and — this is the part that
   has to outlive the read — a [Root]'s payload is pinned by a persistent
   points-to, while a [Link] is pinned to [x] by [linked]. Either way the
   reader may come back to the record later, when [x]'s cell may well hold
   something else. *)

Definition content_info (γ : uf_names) (x : elem) (c : content) : iProp Σ :=
  isBlock (content_loc c) DfracDiscarded Mut ∗
  match c with
  | CtRoot rc => ∃ v, root_val rc v
  | CtLink rc => ∃ lp : locations.loc, linked γ x rc lp
  end.

Global Instance content_info_persistent γ x c : Persistent (content_info γ x c).
Proof. destruct c; apply _. Qed.

(* The one thing a reader of a content cell learns that [content_info]
   cannot state on its own, because it mentions the abstract state: if the
   loaded value is a [Root], its payload is [x]'s value *in the state at
   the instant of the read*. It is therefore available only where that
   state is — at a linearization point — but, being persistent, it outlives
   the open, which is exactly what [get] needs: [get] commits at the
   content read and only afterwards performs the field access that
   actually produces the value. *)

Definition content_val (V : elem → val) (x : elem) (c : content) : iProp Σ :=
  match c with
  | CtRoot rc => root_val rc (V x)
  | CtLink _ => True
  end.

Global Instance content_val_persistent V x c : Persistent (content_val V x c).
Proof. destruct c; apply _. Qed.

(* Reading it all off the cell's own resources, which are handed straight
   back: everything [content_info] and [content_val] hold is persistent.
   The reader also learns the tag's meaning — a cell holds a [Root]
   exactly when its vertex is its own representative — which is the fact
   that makes an atomic read of a content cell a linearization point. *)

Lemma cell_own_info γ R V x i c :
  cell_own γ R V x i c -∗
  ⌜content_root c = true ↔ R x = x⌝ ∗
  content_info γ x c ∗
  content_val V x c ∗
  cell_own γ R V x i c.
Proof.
  rewrite /content_info /content_val /cell_own.
  destruct c as [rc|rc]; simpl.
  - iIntros "(%Hroot & Htok & #Hrv)".
    iAssert (isBlock rc DfracDiscarded Mut) as "#HP".
    { by iDestruct "Hrv" as (lv) "(_ & $ & _)". }
    iSplitR; first by iPureIntro; split.
    iSplitR; [iSplitR; [iExact "HP" | by iExists (V x)] | ].
    iSplitR; first iExact "Hrv".
    by iFrame "Htok Hrv".
  - iIntros "(%lp & %Hroot & #Hlk & Hlf)".
    iDestruct "Hlf" as (y jy) "(#HP & Hlp & #Hy & %Hjy & #Hsc)".
    iSplitR; first by iPureIntro; split; [discriminate | done].
    iSplitR.
    { iFrame "HP". by iExists lp. }
    iSplitR; first done.
    iExists lp. iSplit; first done. iFrame "Hlk".
    iExists y, jy. by iFrame "HP Hlp Hy Hsc".
Qed.

(* Building a link field out of a freshly allocated record: this is what a
   successful linking CAS installs. The obligations are the field's own —
   the new parent is a registered vertex, of a strictly smaller
   identifier, inside the holder's class. *)

(* A freshly allocated link record, taken apart into the pieces its two
   consumers need: [linked] wants the field's location, [link_field] wants
   the field itself. The CAS that installs the record mints the first
   before its hook runs and builds the second after, so the split has to
   happen once, up front. *)

Lemma link_record_split rc (y : elem) :
  rc ⤇ {| link_parent := y |} -∗
  ∃ lp, isBlockLocs rc [lp] ∗ isBlock rc DfracDiscarded Mut ∗ lp ↦ #y.
Proof.
  iIntros "Hrec".
  rewrite /ownRecord /ownBlock /=.
  iDestruct "Hrec" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lp) "[-> Hlp]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs".
  iExists lp. by iFrame "Hlocs HP Hlp".
Qed.

Lemma link_field_intro γ rc lp (h y : elem) i j :
  (j < i)%Z →
  isBlock rc DfracDiscarded Mut -∗
  lp ↦ #y -∗
  vertex γ y j -∗
  same_class γ h y -∗
  link_field γ rc lp h i.
Proof.
  iIntros (Hj) "#HP Hlp #Hy #Hsc".
  iExists y, j. by iFrame "HP Hlp Hy Hsc".
Qed.

(* Its dual, for the ABA argument at the CAS: a link record's field is
   owned exclusively by its holder, so a persistent points-to for the same
   record — which is what a [Root] record hands out — cannot exist. This
   is what rules out a [Link] value having reused the block of the [Root]
   value a CAS is comparing against. *)

Lemma link_field_root_val_excl γ rc lp h i v :
  isBlockLocs rc [lp] -∗ link_field γ rc lp h i -∗ root_val rc v -∗ False.
Proof.
  iIntros "#Hlocs Hlf (%lv & #Hlocs' & _ & #Hlv)".
  iDestruct "Hlf" as (y jy) "(_ & Hlp & _)".
  iDestruct (isBlockLocs_valid with "Hlocs' Hlocs") as %[= ->].
  by iCombine "Hlp Hlv" gives %[Hbad _].
Qed.

(* A registered vertex owns its own [content] cell, so a caller still
   holding that cell — as [make] does for the record it has just
   allocated — knows the vertex is not registered yet. *)

Lemma vertex_own_fresh_ne γ R V x i li lc w :
  isBlockLocs x [li; lc] -∗ lc ↦ w -∗ vertex_own γ R V x i -∗ False.
Proof.
  iIntros "#Hlocs Hlc Hvo".
  iDestruct "Hvo" as (li' lc' c) "(#Hlocs' & Hlc' & _)".
  iDestruct (isBlockLocs_valid with "Hlocs' Hlocs") as %[= -> ->].
  iCombine "Hlc Hlc'" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* ------------------------------------------------------------------------ *)
(* The identifier registry. *)

(* One exclusive token per registered vertex, held for that vertex's
   identifier. Its only purpose is the lemma below — identifiers are
   injective — and the only operation that touches it is [make], which
   spends the token [G.fresh] hands it to extend the map.

   That injectivity is not a decoration: it is what makes [union]'s
   [x.id > y.id] test a total order on the two roots. When the test fails,
   what the proof needs is [ib < ia] STRICTLY, since [uf_cas_link_fupd]
   rests on the absorbed root's identifier being strictly above the one it
   is linked into ([repr_id_le] only gives [≤]). Without injectivity a
   tie would let two domains link each vertex into the other. *)

Definition id_tokens (γ : uf_names) (M : gmap elem Z) : iProp Σ :=
  [∗ map] x ↦ i ∈ M, i ↪[γ.(uf_ids)] ().

Lemma id_tokens_injective γ M a w ia iw :
  a ≠ w →
  M !! a = Some ia →
  M !! w = Some iw →
  id_tokens γ M -∗ ⌜ia ≠ iw⌝.
Proof.
  iIntros (Hne HMa HMw) "HM".
  rewrite /id_tokens (big_sepM_delete _ M a ia) //.
  iDestruct "HM" as "[Ha HM]".
  rewrite (big_sepM_delete _ (delete a M) w iw);
    last by rewrite lookup_delete_ne.
  iDestruct "HM" as "[Hw _]".
  destruct (decide (ia = iw)) as [->|Hne']; last by iPureIntro.
  iCombine "Ha Hw" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* [uf_inv]'s big [∗ map] of [vertex_own]s is indexed by the abstract
   state, but all it reads off it is which vertices are their own
   representative, and what value each of THOSE holds. So an operation
   that moves the state — [union] is the only one that moves [R] — may
   re-close the untouched vertices as soon as it has shown that it
   changed nobody else's root-status, and changed no surviving root's
   value. (It hasn't: linking [a] away unseats [a] alone, and the vertices
   whose value moves with it are exactly the ones [a] represented, none of
   which is a root.) *)

Lemma vertex_own_reindex γ (R R' : elem → elem) (V V' : elem → val)
    (M' : gmap elem Z) :
  (∀ w i, M' !! w = Some i → (R' w = w ↔ R w = w)) →
  (∀ w i, M' !! w = Some i → R w = w → V' w = V w) →
  ([∗ map] w ↦ i ∈ M', vertex_own γ R V w i) -∗
  [∗ map] w ↦ i ∈ M', vertex_own γ R' V' w i.
Proof.
  iIntros (HR HV) "HM".
  iApply (big_sepM_impl with "HM").
  iIntros "!>" (w i Hw) "Hvo".
  iDestruct "Hvo" as (li lc c) "(Hlocs & Hlc & Hcell)".
  iExists li, lc, c. iFrame "Hlocs Hlc".
  destruct (HR w i Hw) as [Hfwd Hbwd].
  destruct c as [rc|rc]; simpl.
  - iDestruct "Hcell" as "(%Hroot & $ & Hrv)".
    rewrite (HV w i Hw Hroot). iFrame "Hrv". iPureIntro. by apply Hbwd.
  - iDestruct "Hcell" as "(%lp & %Hroot & Hlk & Hlf)".
    iExists lp. iFrame "Hlk Hlf". iPureIntro. by intros ?%Hfwd.
Qed.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API: the function proofs speak of [vertex], [is_uf],
   [content_info] and [linked] — never of block locations or of the
   invariant's internals. *)

Lemma vertex_frag γ x i : vertex γ x i -∗ x ↪[γ.(uf_vert)]□ i.
Proof. iIntros "(% & % & $ & _)". Qed.

Lemma vertex_mut γ x i : vertex γ x i -∗ isBlock x DfracDiscarded Mut.
Proof. iIntros "(% & % & _ & _ & $ & _)". Qed.

Lemma vertex_locs γ x i : vertex γ x i -∗ ∃ li lc, isBlockLocs x [li; lc].
Proof.
  iIntros "(%li & %lc & _ & Hlocs & _ & _)". iExists li, lc. iExact "Hlocs".
Qed.

End repr_api.
