From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var.
From stdpp Require Import relations.

From osiris Require Import osiris.

Require Export UnionFind08DataConc UnionFind09SameClass UnionFind10ReprPred.

Local Notation elem := record.

Definition ufN : namespace := nroot .@ "concurrent_uf".

(* The abstract state of the structure, as the client sees it: a domain, a
   representative function, and a value function — the sequential
   development's [D], [R] and [V] (see [UnionFind.v]). *)

Definition uf_state : Type := gset elem * (elem → elem) * (elem → val).

(* ------------------------------------------------------------------------ *)
(* What it means for [R] to be a representative function. *)

(* The sequential development says this by exhibiting a disjoint set forest
   [F] and asking that [R] pick out the root of each tree
   ([rel_incl R (Repr F)], see [UnionFind.v]'s [Inv]). The concurrent
   structure cannot use that formulation, and does not need it.

   It cannot, because there is no single graph to point at: path
   compression rewrites parent pointers concurrently with everything else,
   so the pointers do not form a stable forest, and the "abstract graph"
   the previous version of this invariant existentially quantified over
   was a fiction maintained alongside them, tied to the pointers by
   nothing at all.

   It does not need to, because a forest is a *witness* for four
   elementary properties of [R], and those four properties are all any
   proof here ever used:

   - [repr_idem]: a representative is its own representative. This is what
     makes the fibres of [R] a partition, i.e. what makes "same class"
     mean anything.
   - [repr_dom] / [repr_out]: [R] maps the structure into itself, and is
     the identity on everything else — so a vertex that has never been
     registered is trivially its own class.
   - [repr_id_le]: a representative's identifier is at most its own
     vertex's. This is the acyclicity argument, in the only form the code
     uses it: it is what shows that the vertex a linking CAS points into
     cannot already be represented by the vertex being linked away, i.e.
     that [union] cannot create a cycle. In the forest formulation this
     was [path_id_decrease] over [id_bounded].

   [uf_inv] pairs these with [vertex_own]'s tag conjunct — a cell holds a
   [Root] iff [R x = x] — and that is the entire coupling between the
   structure and its abstract state. *)

Record uf_repr (M : gmap elem Z) (R : elem → elem) : Prop := {
  repr_idem : ∀ x, R (R x) = R x;
  repr_out : ∀ x, x ∉ dom M → R x = x;
  repr_dom : ∀ x, x ∈ dom M → R x ∈ dom M;
  repr_id_le : ∀ x i j, M !! x = Some i → M !! (R x) = Some j → (j ≤ i)%Z;
}.

(* ------------------------------------------------------------------------ *)
(* The abstract state transitions. *)

(* There is only one, [update_class] (UnionFind00Update.v), shared with the
   sequential development: an update to a whole equivalence class. It has
   to be a whole class rather than a point, because the abstract state is
   constrained by [V u = V (R u)] and has no notion of "where the value is
   stored". Every transition either operation makes is an instance:

     make    [V.[x -/R/> v]]                     (the class of [x] is [x])
     set     [V.[x -/R/> v]]
     union   [R.[x -/R/> R y]] and [V.[x -/R/> V y]]

   [union] is the only one that moves [R] at all — [make] extends the
   domain, [set] and [update] move [V] alone, and compression moves
   nothing. Linking absorbs [x]'s whole class into [y]'s: every vertex
   that [R x] represented now has [R y] as its representative, and takes
   [y]'s value.

   The section below collects what that transition preserves, for the one
   shape the implementation produces it in: a root [a] linked into a
   vertex whose representative is [z], with [z]'s identifier strictly
   below [a]'s. *)

Section link_state.

(* [a] is a root about to be linked away; [z] is the representative of the
   class it is joining. The identifier ordering is the whole reason the
   two are distinct classes — [z]'s identifier is below [a]'s, so [z]
   cannot be represented by [a] — and it is what makes the result a
   representative function again rather than a cycle. *)

Context (M : gmap elem Z) (R : elem → elem) (a z : elem) (ia iz : Z).
Context (HR : uf_repr M R) (Hroot : R a = a) (Hz : R z = z).
Context (HMa : M !! a = Some ia) (HMz : M !! z = Some iz) (Hlt : (iz < ia)%Z).

Local Lemma link_z_ne_a : z ≠ a.
Proof.
  intros Heq. assert (Some iz = Some ia) as [= ?].
  { rewrite -HMz -HMa. by f_equal. }
  lia.
Qed.

(* [a] is a root, so naming its class by [a] is naming it by [R a]: the
   two forms of the update coincide, and this is what lets the proofs
   below case on [R u = a] directly. *)
Local Lemma link_unfold {B : Type} (f : elem → B) (b : B) u :
  f.[a -/R/> b] u = if decide (R u = a) then b else f u.
Proof. rewrite /update_class /fcupdate Hroot //. Qed.

(* Nobody's root-status changes except [a]'s. *)
Lemma uf_link_root_iff w : w ≠ a → (R.[a -/R/> z] w = w ↔ R w = w).
Proof.
  intros Hw. rewrite link_unfold. case_decide as Hcase; last done.
  split.
  - intros <-. exfalso. apply link_z_ne_a. by rewrite -Hcase Hz.
  - intros Hww. exfalso. apply Hw. by rewrite -Hww Hcase.
Qed.

Lemma uf_repr_link : uf_repr M R.[a -/R/> z].
Proof.
  destruct HR as [Hidem Hout Hdom Hle].
  pose proof link_z_ne_a as Hza.
  split; intros u; rewrite !link_unfold.
  - destruct (decide (R u = a)) as [Hu|Hu].
    + rewrite Hz. by destruct (decide (z = a)).
    + rewrite Hidem. by rewrite decide_False.
  - intros Hu. rewrite decide_False; first by apply Hout.
    rewrite Hout //. intros ->. apply Hu, elem_of_dom. by eexists.
  - intros Hu. case_decide; [by apply elem_of_dom; eexists | by apply Hdom].
  - intros iu j Hu. case_decide as Hcase.
    + rewrite HMz. intros [= <-].
      transitivity ia; first lia. by eapply Hle; [exact Hu | rewrite Hcase].
    + by eapply Hle.
Qed.

(* Values are still read through representatives afterwards — with the NEW
   representative function, which is what distinguishes this from
   [lookup_class_root] (the [set]/[make] case, where [R] does not move). *)
Lemma uf_link_value_coherent (V : elem → val) :
  (∀ u, V u = V (R u)) →
  ∀ u, V.[a -/R/> V z] u = V.[a -/R/> V z] (R.[a -/R/> z] u).
Proof.
  intros HV u. pose proof link_z_ne_a as Hza.
  destruct HR as [Hidem _ _ _].
  rewrite (link_unfold V (V z) u) (link_unfold R z u).
  destruct (decide (R u = a)) as [Hu|Hu].
  - rewrite (link_unfold V (V z) z) decide_False; [done | by rewrite Hz].
  - rewrite (link_unfold V (V z) (R u)) decide_False;
      [by apply HV | by rewrite Hidem].
Qed.

End link_state.

Section uf_inv.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* ------------------------------------------------------------------------ *)
(* The abstract state. *)

(* A client of the structure sees exactly what a client of the SEQUENTIAL
   union-find sees (see [UnionFind.v]): a domain [Dp], a representative
   function [Rp] mapping every vertex to the root of its tree (and every
   non-vertex to itself), and a value function [Vp]. The concurrent
   [UF γ Dp Rp Vp] plays the role of the sequential [UF Dp Rp Vp]: it is
   the client's exclusive handle on the state, and it is what a logically
   atomic specification quantifies over.

   It is half of a ghost variable whose other half lives in the invariant,
   so the two are forced to agree and neither side can move the state
   alone. At its linearization point an operation opens the invariant,
   takes [UF] out of the client's atomic update, and either reads it (a
   pure observer like [find]) or updates both halves at once.

   Note what is NOT in the abstract state: the parent pointers. Path
   compression rewrites them constantly, and it is exactly the point of
   this abstraction that this is invisible — compression changes no [Rp].
   The [same_class] ghost state is likewise invisible to the client.

   [UF] does, however, carry HALF the authority over the recorded class
   pairs, alongside the soundness of what is recorded against this very
   [Rp]. That is not information for the client — the set is existentially
   hidden — it is a CAPABILITY: whoever holds a [UF] can turn a
   [same_class] fact into the equation [R u = R w] on the spot
   ([UF_same_class_eq]), with no fupd and no invariant open, and therefore
   at ANY mask. That is what lets an operation reason about classes inside
   an atomic update's access, where nothing can be opened.

   The other half lives in the invariant's own [UF], so the two are forced
   to agree. And since changing the recorded set needs both halves at
   once, it can only happen where they meet — which is exactly a
   linearization point, and exactly where a new equivalence is born.

   [UF] also carries [uf_val_congr], the one well-formedness fact about
   the state that is not derivable from the two functions alone: the value
   function is constant on classes. Like the class authority this is a
   capability rather than information — it is what lets a holder of [UF]
   re-state a transition in terms of ANY member of a class instead of the
   one it happens to be holding a name for. [union]'s retry is the reason
   it is here: after a lost CAS the call restarts on the vertices its
   traversals reached, and its client's hook, which speaks of the original
   arguments, has to be re-based onto them — [same_class] gives the
   representatives are equal, and this gives the values are too. *)

Definition uf_val_congr (Rp : elem → elem) (Vp : elem → val) : Prop :=
  ∀ u w, Rp u = Rp w → Vp u = Vp w.

(* It survives both shapes of transition the structure ever makes: giving
   one class a new value ([make], [set]), and merging two ([union]). *)

Lemma uf_val_congr_set R V x v :
  uf_val_congr R V → uf_val_congr R V.[x -/R/> v].
Proof.
  intros HV u w Huw. unfold update_class, fcupdate.
  rewrite Huw. case_decide; [done | by apply HV].
Qed.

Lemma uf_val_congr_link R V b c :
  uf_val_congr R V → uf_val_congr R.[b -/R/> R c] V.[b -/R/> V c].
Proof.
  intros HV u w. unfold update_class, fcupdate.
  repeat case_decide; [done | by intros <-%HV | by intros ->%HV | by apply HV].
Qed.

Definition UF (γ : uf_names) (Dp : gset elem) (Rp : elem → elem)
    (Vp : elem → val) : iProp Σ :=
  ⌜uf_val_congr Rp Vp⌝ ∗
  ghost_var γ.(uf_abs) (1/2) (Dp, Rp, Vp) ∗
  ∃ S, ⌜same_class_sound S Rp⌝ ∗ own γ.(uf_class) (●{#1/2} S).

Global Instance UF_timeless γ Dp Rp Vp : Timeless (UF γ Dp Rp Vp).
Proof. apply _. Qed.

Lemma UF_agree γ Dp Rp Vp Dp' Rp' Vp' :
  UF γ Dp Rp Vp -∗ UF γ Dp' Rp' Vp' -∗ ⌜Dp = Dp' ∧ Rp = Rp' ∧ Vp = Vp'⌝.
Proof.
  iIntros "(_ & H1 & _) (_ & H2 & _)".
  by iDestruct (ghost_var_agree with "H1 H2") as %[= -> -> ->].
Qed.

Lemma UF_val_congr γ Dp Rp Vp : UF γ Dp Rp Vp -∗ ⌜uf_val_congr Rp Vp⌝.
Proof. by iIntros "($ & _)". Qed.

(* Reading a class fact against the state, from a handle alone. *)

Lemma UF_same_class_eq γ D R V u w :
  UF γ D R V -∗ same_class γ u w -∗ ⌜R u = R w⌝ ∗ UF γ D R V.
Proof.
  iIntros "(%Hcongr & Hvar & (%S & %HS & HSauth)) #Hsc".
  iDestruct (same_class_eq with "HSauth Hsc") as %Heq; first exact HS.
  iFrame "Hvar". iSplitR; first done. iSplitR; first done.
  iExists S. by iFrame "HSauth".
Qed.

(* Moving the state. Both halves are needed, which is the point: the
   recorded pairs are sound against [Rp], so the transition must carry
   them along, and coarsening [Rp] is exactly what keeps them sound
   ([same_class_sound_coarsen]). *)

Lemma UF_update_2 γ D R V D' R' V' :
  (∀ u w, R u = R w → R' u = R' w) →
  uf_val_congr R' V' →
  UF γ D R V -∗ UF γ D R V ==∗ UF γ D' R' V' ∗ UF γ D' R' V'.
Proof.
  iIntros (Hmono Hcongr) "(_ & Hv1 & (%S1 & %HS1 & Ha1))
                          (_ & Hv2 & (%S2 & %HS2 & Ha2))".
  iMod (ghost_var_update_halves (D', R', V') with "Hv1 Hv2") as "[Hv1 Hv2]".
  iCombine "Ha1 Ha2" gives %[_ [->%leibniz_equiv _]]%auth_auth_dfrac_op_valid.
  iModIntro.
  iSplitL "Hv1 Ha1".
  - iSplitR; first done. iFrame "Hv1". iExists S2. iFrame "Ha1".
    iPureIntro. by eapply same_class_sound_coarsen.
  - iSplitR; first done. iFrame "Hv2". iExists S2. iFrame "Ha2".
    iPureIntro. by eapply same_class_sound_coarsen.
Qed.

(* Recording a new pair — the only operation that mints a class fact, and
   the only one that needs the full authority. *)

Lemma UF_same_class_update γ D R V u w :
  R u = R w →
  UF γ D R V -∗ UF γ D R V ==∗
  UF γ D R V ∗ UF γ D R V ∗ same_class γ u w.
Proof.
  iIntros (Huw) "($ & $ & (%S1 & %HS1 & Ha1)) ($ & $ & (%S2 & %HS2 & Ha2))".
  iCombine "Ha1 Ha2" gives %[_ [->%leibniz_equiv _]]%auth_auth_dfrac_op_valid.
  iCombine "Ha1 Ha2" as "Ha".
  iMod (same_class_update _ _ R u w with "Ha") as (S') "(Ha & #Hsc & %HS' & _)";
    [exact HS2 | exact Huw |].
  iModIntro. iFrame "Hsc".
  iDestruct "Ha" as "[Ha1 Ha2]".
  iSplitL "Ha1"; iExists S'; by iFrame.
Qed.

(* [in_uf γ x]: [x] is a vertex of the structure. This is the persistent
   right to name [x] in a specification — the counterpart of the
   sequential development's [⌜e ∈ D⌝] precondition, which cannot be stated
   as a pure side condition here because [D] is only known at the
   linearization point. Membership never expires, so this is persistent,
   and at the linearization point the invariant turns it back into the
   pure [x ∈ Dp] the sequential proofs use. *)

Definition in_uf (γ : uf_names) (x : elem) : iProp Σ := ∃ i, vertex γ x i.

Global Instance in_uf_persistent γ x : Persistent (in_uf γ x).
Proof. apply _. Qed.
(* ------------------------------------------------------------------------ *)

(* The global invariant: the authoritative map of vertices with their
   physical footprints, the two registries (identifiers, and which
   vertices have been linked away), and the invariant's half of the
   abstract state.

   The conjuncts that tie the two levels together are [uf_repr M Rp] — the
   four properties above, standing in for the sequential development's
   [DSF F Dp ∧ rel_incl Rp (Repr F)] — and [Vp x = Vp (Rp x)], which is
   [Inv]'s third component verbatim. Everything an atomically specified
   operation reports about the abstract state is read off them, together
   with [cell_own]'s [Root]-tag conjunct.

   [S] is the set of pairs ever recorded as equivalent, coupled to the
   abstract state by [same_class_sound S Rp]: what a traversal needs to
   carry across invariant opens is that two vertices are in the same
   class, and it is the partition — not any pointer structure — that only
   ever coarsens.

   [id_tokens γ M] is what makes identifiers injective. It sits here
   rather than inside [vertex_own] because no step on a vertex's cell ever
   reads or moves it: only [make] touches it, to extend it. Keeping it
   per-vertex meant carrying it in and out of every accessor for nothing.

   Note that content records are no longer tracked here. A [Root] record's
   payload is persistent, so nobody has to own it; a [Link] record's
   parent field is owned by the vertex holding it, inside that vertex's
   own [vertex_own]. The registry that used to map every content value
   ever installed to a description has shrunk to [L], which records which
   vertices have been linked away and with what record — and is never even
   read, since the fragments carry everything (see [linked]).

   [L]'s domain is nevertheless pinned to [M]'s. That is not needed to
   USE the registry — a vertex's own entry always comes out of its
   [cell_own] — but it is what lets [make] put a fresh vertex INTO it:
   inserting into a [ghost_map] needs the key to be absent, and "absent
   from [L]" is exactly what being a fresh vertex has to mean. *)

Definition uf_inv (γ : uf_names) : iProp Σ :=
  ∃ (M : gmap elem Z) (L : gmap elem (option record)) (N : gmap Z unit)
    (Rp : elem → elem) (Vp : elem → val),
    ghost_map_auth γ.(uf_vert) 1 M ∗
    ghost_map_auth γ.(uf_link) 1 L ∗
    ghost_map_auth γ.(uf_ids) 1 N ∗
    UF γ (dom M) Rp Vp ∗
    ⌜dom L = dom M⌝ ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜uf_repr M Rp⌝ ∗
    ⌜∀ x, Vp x = Vp (Rp x)⌝ ∗
    id_tokens γ M ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ Rp Vp x i).

Definition is_uf (γ : uf_names) : iProp Σ :=
  inv ufN (uf_inv γ).

(* An empty structure can always be created; over the empty domain every
   vertex is trivially its own representative. The client receives the
   abstract state it starts in. *)

Lemma uf_alloc E (V0 : elem → val) :
  ⊢ |={E}=> ∃ γ, is_uf γ ∗ UF γ ∅ (λ x, x) V0.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γv) "Hγ".
  iMod (ghost_map_alloc_empty (K:=elem) (V:=option record)) as (γl) "Hγl".
  iMod (ghost_map_alloc_empty (K:=Z) (V:=unit)) as (γn) "Hγn".
  iMod (own_alloc (● (∅ : gset (elem * elem)))) as (γc) "Hγe";
    first by apply auth_auth_valid.
  iMod (ghost_var_alloc (∅ : gset elem, (λ x : elem, x), V0)) as (γa) "[Hγs Hγs']".
  set (γ := UfNames γv γl γn γc γa).
  (* The class authority is split at once: half for the invariant's [UF],
     half for the client's. *)
  iDestruct "Hγe" as "[Hγe Hγe']".
  iAssert (UF γ ∅ (λ x, x) V0) with "[Hγs Hγe]" as "HUF".
  { iSplitR; first by iPureIntro; intros u w ->.
    iFrame "Hγs". iExists ∅. iFrame "Hγe".
    iPureIntro. intros u w Huw. set_solver. }
  iAssert (UF γ ∅ (λ x, x) V0) with "[Hγs' Hγe']" as "HUF'".
  { iSplitR; first by iPureIntro; intros u w ->.
    iFrame "Hγs'". iExists ∅. iFrame "Hγe'".
    iPureIntro. intros u w Huw. set_solver. }
  iMod (inv_alloc ufN _ (uf_inv γ) with "[Hγ Hγl Hγn HUF]") as "#Hinv".
  { iNext. iExists ∅, ∅, ∅, (λ x, x), V0.
    rewrite dom_empty_L. iFrame.
    iSplit; [by rewrite !dom_empty_L|].
    iSplit; [iPureIntro; intros x i; rewrite lookup_empty; discriminate|].
    iSplit; [iPureIntro; split; try done; intros x i j;
             rewrite lookup_empty; discriminate|].
    iSplit; [by iPureIntro|].
    rewrite /id_tokens. by rewrite !big_sepM_empty. }
  iModIntro. iExists γ. by iFrame "Hinv HUF'".
Qed.

(* ------------------------------------------------------------------------ *)
(* Accessing the invariant.

   [uf_inv] is never destructured outside this file, and inside it only by
   the two accessors below. Each hands out exactly the resources its
   callers consume — and a wand to give them back — rather than the whole
   pile of components; the ones a caller does not need it never sees,
   which is what keeps the function proofs free of invariant bookkeeping.

   The first accessor is the purely ghost one. [vertex_representable] reads
   the identifier map [M] and nothing else — no physical footprint, no
   abstract state — so that is all this exposes. It used to also hand out
   the class authority, for [same_class_trans]; with class facts closed
   under composition by construction there is no such caller left. *)

Lemma uf_inv_ghost_acc γ :
  ▷ uf_inv γ -∗
  ◇ ∃ M : gmap elem Z,
      ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
      ghost_map_auth γ.(uf_vert) 1 M ∗
      (ghost_map_auth γ.(uf_vert) 1 M -∗ ▷ uf_inv γ).
Proof.
  iIntros "H".
  iDestruct "H" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & Htoks & HM)".
  iModIntro. iExists M.
  iSplitR; first done.
  iFrame "Hauth".
  iIntros "Hauth". iNext.
  iExists M, L, N, Rp, Vp. by iFrame.
Qed.

(* [uf_frame γ z j D Rp Vp] is everything [uf_inv] owns that a
   step on vertex [z]'s content cell never inspects: the identifier map,
   the two registries, the identifier tokens, and every OTHER vertex's
   footprint. Packaging it under one name is what lets the single accessor
   below expose one vertex's cell and nothing else.

   What it does NOT hold is the abstract state and the recorded pairs:
   those are handed out alongside the cell, because a step on a content
   cell is exactly where they get read (a linearization point) or moved (a
   successful CAS). *)

Definition uf_frame (γ : uf_names) z j
    (D : gset elem) (Rp : elem → elem) (Vp : elem → val) : iProp Σ :=
  ∃ (M : gmap elem Z) (L : gmap elem (option record)) (N : gmap Z unit),
    ⌜M !! z = Some j⌝ ∗ ⌜dom M = D⌝ ∗ ⌜dom L = dom M⌝ ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜uf_repr M Rp⌝ ∗ ⌜∀ x, Vp x = Vp (Rp x)⌝ ∗
    ghost_map_auth γ.(uf_vert) 1 M ∗ ghost_map_auth γ.(uf_link) 1 L ∗
    ghost_map_auth γ.(uf_ids) 1 N ∗
    id_tokens γ M ∗
    ([∗ map] x ↦ i ∈ delete z M, vertex_own γ Rp Vp x i).

(* [uf_inv_split] singles out one vertex's footprint: given [z]'s
   persistent [vertex] components, it hands back the content cell
   [lzc ↦ #c] of [z] and whatever that content owns ([cell_own]), together
   with the abstract state, the recorded pairs, and the frame.
   [uf_inv_reassemble] is the converse — for a possibly DIFFERENT content
   value, which is what a successful CAS installs, and for a possibly
   larger set of recorded pairs. *)

Lemma uf_inv_split γ z j lzi lzc :
  z ↪[γ.(uf_vert)]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ -∗
  ◇ ∃ (c : content) (D : gset elem) (Rp : elem → elem) (Vp : elem → val),
      ⌜z ∈ D⌝ ∗
      UF γ D Rp Vp ∗
      ▷ (lzc ↦ #c) ∗
      ▷ cell_own γ Rp Vp z j c ∗
      ▷ uf_frame γ z j D Rp Vp.
Proof.
  iIntros "#Hzfrag #Hzlocs H".
  iDestruct "H" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & Htoks & HM)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  iDestruct "Hvo" as (li' lc' c) "(#Hzlocs' & Hlc & Hcell)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hzlocs' Hzlocs"). }
  simplify_eq.
  iExists c, (dom M), Rp, Vp.
  iModIntro.
  iSplitR; first by iPureIntro; eapply elem_of_dom_2.
  iFrame "Hcont Hlc Hcell".
  iNext. iExists M, L, N.
  do 6 (iSplitR; first done).
  iFrame "Hauth Hlauth Hnauth Htoks HM".
Qed.

Lemma uf_inv_reassemble γ z j lzi lzc c' D Rp Vp :
  UF γ D Rp Vp -∗
  isBlockLocs z [lzi; lzc] -∗
  lzc ↦ #c' -∗
  cell_own γ Rp Vp z j c' -∗
  uf_frame γ z j D Rp Vp -∗
  uf_inv γ.
Proof.
  iIntros "Hcont #Hzlocs Hlc Hcell Hframe".
  iDestruct "Hframe" as (M L N)
    "(%HMz & %HdomM & %HdomL & %Hrep & %HRp & %HVp &
      Hauth & Hlauth & Hnauth & Htoks & HM)".
  subst D.
  iExists M, L, N, Rp, Vp.
  iFrame "Hauth Hlauth Hnauth Hcont Htoks".
  do 4 (iSplitR; first done).
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iFrame "HM".
  iExists lzi, lzc, c'. iFrame "Hzlocs Hlc Hcell".
Qed.

(* Note that the two state-CHANGING steps do NOT go through
   [uf_inv_reassemble]: they have to put the frame back under a different
   abstract state, and the reassembly of each is spelled out inside its
   own lemma below ([uf_cas_link_fupd], [uf_cas_set_fupd]). *)

(* ------------------------------------------------------------------------ *)
(* The linearization point of [make]: registering a fresh vertex. *)

(* [make] allocates a vertex record and a [Root] content record, and then,
   in one ghost step, declares the result a vertex of the structure. That
   step is the whole of [make]'s dealings with the abstract state, and it
   is its linearization point.

   The state moves in the only way it can here: the domain gains [x], and
   [x]'s class — which is [x] alone — takes the value [v], which is again
   [update_class]. [R] does not move at all: [repr_out] already forced
   [R x = x] for every vertex outside the domain, so the fresh vertex was
   its own representative before it was registered and stays so
   afterwards. That is also why the caller can be handed [⌜R x = x⌝] for
   free — without it the postcondition would not say where [v] went.

   That the allocated record is not ALREADY a registered vertex is read
   off the heap rather than the ghost state: a registered vertex owns its
   content cell exclusively, and the caller is still holding this one
   ([vertex_own_fresh_ne]).

   Nothing here touches [same_class] — a fresh vertex is equivalent to
   nothing but itself, and [same_class] is reflexive by definition — nor
   the identifier authority: the token spent comes from [G.fresh], and
   that is precisely what makes the identifier globally unused. *)

Lemma register_vertex  (Q : iProp Σ) γ (x : elem) i (rc : record)
    (v : val) :
  ⌜representable i⌝ -∗
  is_uf γ -∗
  i ↪[γ.(uf_ids)] () -∗
  x ⤇ {| vertex_id_f := i; vertex_content_f := CtRoot rc |} -∗
  rc ⤇ {| root_value := v |} -∗
  (∀ D (R : elem → elem) (V : elem → val),
     ⌜x ∉ D⌝ -∗ ⌜R x = x⌝ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
     UF γ (D ∪ {[x]}) R V.[x -/R/> v] ∗ Q) -∗
  |={⊤}=> vertex γ x i ∗ Q.
Proof.
  iIntros (Hrep) "#Hinv Htokn Hx Hrc Hhook".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrepr & >%HRp & >%HVp & >Htoks & HM)" "Hclose".

  rewrite {1}/ownRecord /ownBlock /=.
  iDestruct "Hx" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_cons_inv_r with "Hxs")
    as (li ls') "(-> & Hli & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lc) "[-> Hlc]".
  rewrite list_z.singleton_unfold.

  (* The allocated record is not a vertex yet: a vertex owns its content
     cell, and the caller is still holding this one. *)
  destruct (M !! x) as [j|] eqn:HMx.
  { iAssert (▷ False)%I with "[HM Hlc]" as ">[]".
    iNext. rewrite (big_sepM_lookup _ M x j) //.
    iApply (vertex_own_fresh_ne with "Hlocs Hlc HM"). }
  assert (HxD : x ∉ dom M) by (apply not_elem_of_dom; exact HMx).
  assert (HLx : L !! x = None)
    by (apply not_elem_of_dom; rewrite HdomL; exact HxD).
  (* Hence it is already its own representative, by [repr_out]. *)
  assert (Hroot : Rp x = x) by (by apply (repr_out _ _ HRp)).

  iMod (ghost_map_insert x i with "Hauth") as "[Hauth Hxfrag]"; first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod (ghost_map_insert x None with "Hlauth") as "[Hlauth Htokl]";
    first exact HLx.
  iMod (gen_heap.pointsto_persist with "Hli") as "#Hli".
  iMod (root_val_alloc with "Hrc") as "#Hrv".

  (* The linearization point proper. *)
  iMod ("Hhook" $! (dom M) Rp Vp with "[//] [//] Hcont") as "[Hcont HQ]".

  iMod ("Hclose" with "[-HQ]") as "_".
  { iNext.
    iExists (<[x := i]> M), (<[x := None]> L), N, Rp, Vp.[x -/Rp/> v].
    iFrame "Hauth Hlauth Hnauth".
    rewrite dom_insert_L (union_comm_L {[x]} (dom M)). iFrame "Hcont".
    iSplitR; first (iPureIntro; rewrite dom_insert_L HdomL; set_solver).
    iSplitR.
    { iPureIntro. intros y k. destruct (decide (y = x)) as [->|Hne].
      - rewrite lookup_insert_eq. by intros [= <-].
      - rewrite lookup_insert_ne //. apply Hrepr. }
    iSplitR.
    { (* [R] has not moved, so all four properties are the old ones plus
         the new vertex's, and the new vertex is its own class. *)
      iPureIntro. destruct HRp as [Hidem Hout Hdom Hle]. split.
      - exact Hidem.
      - intros u Hu. apply Hout. rewrite dom_insert_L in Hu. set_solver.
      - intros u Hu. rewrite dom_insert_L. rewrite dom_insert_L in Hu.
        apply elem_of_union in Hu as [Hu|Hu].
        + apply elem_of_singleton in Hu as ->. rewrite Hroot. set_solver.
        + apply elem_of_union_r. by apply Hdom.
      - intros u iu ju Hu Hru.
        destruct (decide (u = x)) as [->|Hne].
        + rewrite lookup_insert_eq in Hu. rewrite Hroot lookup_insert_eq in Hru.
          simplify_eq. lia.
        + rewrite lookup_insert_ne // in Hu.
          (* [u]'s representative is an old vertex, so not the fresh one. *)
          assert (Hrux : Rp u ≠ x).
          { intros Habs. apply HxD. rewrite -Habs.
            apply Hdom, elem_of_dom. by eexists. }
          rewrite lookup_insert_ne // in Hru.
          by eapply Hle. }
    iSplitR.
    { iPureIntro.
      assert (Idempotent Rp) by (constructor; apply (repr_idem _ _ HRp)).
      intros u. apply lookup_class_root, HVp. }
    rewrite /id_tokens big_sepM_insert //.
    iFrame "Htokn Htoks".
    rewrite big_sepM_insert //.
    iSplitR "HM".
    - (* The fresh vertex's own footprint: a [Root] cell holding [v]. *)
      iExists li, lc, (CtRoot rc).
      iFrame "Hlocs Hlc".
      iSplitR; first (iPureIntro; exact Hroot).
      iFrame "Htokl".
      rewrite lookup_update_class //.
    - (* Every other vertex: no root-status changed, and no surviving
         root's value did either, the fresh vertex being nobody else's
         representative. *)
      iApply (vertex_own_reindex with "HM"); first done.
      intros w k Hw Hw'. rewrite lookup_update_class_ne //.
      rewrite Hroot Hw'. intros ->. by rewrite HMx in Hw. }
  iModIntro. iSplitR "HQ"; last iExact "HQ".
  iExists li, lc. by iFrame "Hxfrag Hlocs HP Hli".
Qed.

End uf_inv.

Section same_class.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* ------------------------------------------------------------------------ *)
(* The [same_class] API. *)

(* Reflexivity, symmetry and transitivity all hold by definition — see
   [UnionFind09SameClass.v], where a class fact is a CHAIN of recorded
   pairs rather than a single one. None of them is a ghost step, and none
   of them needs an invariant open. What used to live here
   ([same_class_trans], [same_class_sibling]) is now [same_class_trans]
   and [same_class_sym] composed. *)

(* Two vertices in a common class are in each other's. This is what path
   compression needs to hand its recursive call: it holds [x ~ y] (the hop
   it just read) and [x ~ z] (its own precondition), and must produce
   [y ~ z] to reroute [y] as well.

   It is worth pausing on how little there is to prove. Under the previous
   formulation, where the recorded facts were PATHS in an abstract graph,
   the same step needed the two paths out of [x] to be linearly ordered
   ([path_confluent], from a disjoint-set forest being [Functional]) and
   the wrong order to be ruled out by the identifier ordering
   ([path_id_decrease]) — for which [compress]'s [y.id > z.id] guard had
   to be threaded in. Recording class membership instead, the whole thing
   is [Rp y = Rp x = Rp z], and the guard justifies nothing about the
   rerouting: it is only what keeps identifiers decreasing. *)

(* Observing that two vertices are in one class, against the abstract
   state, at a ghost instant.

   [union] needs this for the case where it has nothing to do: it has
   chased both arguments to a common vertex, so they are equivalent —
   permanently, since classes only merge — and it returns [None]. There is
   no physical step left at which to say so (the [==] test is a register
   comparison), and there does not need to be one: nothing about the
   structure changes, so any instant will do, and an invariant open with
   no step in it is exactly such an instant. *)

Lemma uf_same_class_commit γ (u w c : elem) (Q : iProp Σ) :
  is_uf γ -∗
  same_class γ u c -∗
  same_class γ w c -∗
  (∀ D (R : elem → elem) (V : elem → val),
     ⌜R u = R w⌝ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Q) ={⊤}=∗ Q.
Proof.
  iIntros "#Hinv #Huc #Hwc Hk".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & HM)" "Hclose".
  iDestruct (UF_same_class_eq with "Hcont Huc") as "[%Huc Hcont]".
  iDestruct (UF_same_class_eq with "Hcont Hwc") as "[%Hwc Hcont]".
  iMod ("Hk" $! (dom M) Rp Vp with "[%] Hcont") as "[Hcont HQ]".
  { by rewrite Huc Hwc. }
  iMod ("Hclose" with "[-HQ]") as "_".
  { iNext. iExists M, L, N, Rp, Vp.
    iFrame "Hauth Hlauth Hnauth Hcont HM".
    by do 3 (iSplitR; first done). }
  by iModIntro.
Qed.

Lemma same_class_sibling γ x y z :
  same_class γ x y -∗ same_class γ x z -∗ same_class γ y z.
Proof.
  iIntros "#Hxy #Hxz".
  iApply (same_class_trans with "[] Hxz").
  by iApply same_class_sym.
Qed.

End same_class.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API: the only interface the function proofs use. It
   speaks of [vertex], [is_uf], [content_info] and [linked] — never of the
   invariant's components. *)

Section uf_api.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* Reading a vertex's content cell, in the shape the atomic record-access
   rule wants. The reader learns [content_info] — for a [Root], a
   persistent points-to for its payload; for a [Link], that the record is
   [z]'s own and stays so — and gives the cell straight back, unchanged. *)

Lemma uf_vertex_content_acc γ z j lzi lzc (Φ : content → iProp Σ) :
  is_uf γ -∗
  z ↪[γ.(uf_vert)]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ (∀ c : content, content_info γ z c -∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hzfrag #Hzlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (cell_own_info with "Hcell") as "(_ & #Hinfo & _ & Hcell)".
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iNext.
    iApply (uf_inv_reassemble with "Hcont Hzlocs Hlc Hcell Hframe"). }
  iModIntro. iApply ("HΦ" with "Hinfo").
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [find]. *)

(* This is [uf_vertex_content_acc] with the abstract state added: the same
   single atomic read of [z]'s content cell, but the continuation also
   receives the invariant's half of [UF] — so that it can meet the
   client's half, held inside an atomic update, and commit — together with
   the one fact that makes the read a linearization point:

     if the cell holds a [Root], then [z] IS its own representative.

   That fact is read against the open this accessor performs, and does not
   survive it: a moment later [z] may have been linked away and [Rp z]
   moved on. That is exactly why it has to be cashed in at the read, and
   exactly what a logically atomic specification is for. A caller standing
   at some other vertex of the class transports the claim afterwards, with
   the [same_class] fact its traversal accumulated — see [find_proof].

   The continuation also gets [content_val], which pins the loaded [Root]
   record's payload to [V z] in that same state. This is what makes the
   read [get]'s linearization point rather than the field access that
   follows it: [get] commits here, and the payload it reads a step later
   is fixed by a persistent points-to, so the race it looks like it is
   running is not one.

   The state is handed over read-only — the continuation must give back
   the very same [UF] — because neither [find] nor [get] changes it. The
   state-CHANGING operations will want the same accessor with a hook that
   may give back a different one. *)

Lemma uf_find_content_acc γ (z : elem) j lzi lzc
    (Φ : content → iProp Σ) :
  is_uf γ -∗
  z ↪[γ.(uf_vert)]□ j -∗
  isBlockLocs z [lzi; lzc] -∗
  ▷ (∀ (c : content) D (R : elem → elem) (V : elem → val),
       ⌜z ∈ D⌝ -∗
       ⌜content_root c = true → R z = z⌝ -∗
       content_info γ z c -∗
       content_val V z c -∗
       UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hzfrag #Hzlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(%HzD & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (cell_own_info with "Hcell") as "(%Hiff & #Hinfo & #Hval & Hcell)".
  iMod ("HΦ" with "[//] [%] Hinfo Hval Hcont") as "[Hcont HΦ]".
  { by apply Hiff. }
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iNext.
    iApply (uf_inv_reassemble with "Hcont Hzlocs Hlc Hcell Hframe"). }
  by iModIntro.
Qed.

(* What [union]'s [assert (x.id <> y.id)] needs: distinct vertices have
   distinct — and, from [uf_inv]'s own [representable] conjunct, machine-
   comparable — identifiers. Now that the identifier tokens are factored
   out of the per-vertex footprints, this reads both facts straight off
   the invariant and gives everything back untouched: no vertex has to be
   split out at all. *)

Lemma vertex_ids_ne γ (a w : elem) ia iw :
  a ≠ w →
  is_uf γ -∗
  vertex γ a ia -∗
  vertex γ w iw -∗
  |={⊤}=> ⌜ia ≠ iw ∧ representable ia ∧ representable iw⌝.
Proof.
  iIntros (Hne) "#Hinv #Ha #Hw".
  iDestruct (vertex_frag with "Ha") as "#Hafrag".
  iDestruct (vertex_frag with "Hw") as "#Hwfrag".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & >Htoks & HM)" "Hclose".
  iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMa.
  iDestruct (ghost_map_lookup with "Hauth Hwfrag") as %HMw.
  iDestruct (id_tokens_injective with "Htoks") as %Hij; [done..|].
  iMod ("Hclose" with "[Hauth Hlauth Hnauth Hcont Htoks HM]") as "_".
  { iNext. iExists M, L, N, Rp, Vp. by iFrame. }
  iModIntro. iPureIntro.
  split; [exact Hij | split; [exact (Hrep a ia HMa) | exact (Hrep w iw HMw)]].
Qed.

(* A single vertex's identifier is machine-comparable. [vertex_ids_ne]
   yields this too, but only for a pair of vertices already known to be
   distinct; [compress] compares identifiers of vertices it has no
   distinctness fact about. *)

Lemma vertex_representable γ x i :
  is_uf γ -∗ vertex γ x i ={⊤}=∗ ⌜representable i⌝.
Proof.
  iIntros "#Hinv #Hx".
  iDestruct (vertex_frag with "Hx") as "#Hxfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_ghost_acc with "H") as (M) "(%Hrep & Hauth & Hback)".
  iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
  iMod ("Hclose" with "[Hback Hauth]") as "_";
    first by iApply ("Hback" with "Hauth").
  iModIntro. iPureIntro. exact (Hrep _ _ HMx).
Qed.

End uf_api.

(* ------------------------------------------------------------------------ *)
(* Re-reading (and, for [compress], rewriting) the [parent] field of the
   link record a vertex holds.

   A [Root] record needs no counterpart to these: its payload comes with a
   persistent points-to ([root_val], carried by [content_info]), so
   reading it is an ordinary field read that opens nothing.

   These are what produce the mask-changing fupd that the atomic rules
   ([ipat_PRecord_atomic], [imp_ERecordAccess_atomic],
   [imp_ERecordSet_atomic]) consume, and they expose that one field and
   nothing else: the caller learns that the parent it loaded is a
   registered vertex of a strictly smaller identifier, inside the holder's
   class, and may store back any vertex it can establish the same of. *)

Section uf_acc.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* The single primitive the three accessors below are built from. Note how
   the holder is identified: not by a registration recording which vertex
   a record belongs to, but by splitting the invariant at that very vertex
   — [linked γ h rc] says [h]'s cell holds [rc], and the [h ↪[γ.(uf_link)] None]
   that a root's cell owns is what rules out [h] having become one again.

   The reported parent comes with a class fact tying it to the holder [h].
   That is all this needs to say: a traversal that arrived here from
   somewhere else composes the hop with what it already holds afterwards,
   outside the open, since a class fact is now a chain and composing is
   definitional. This accessor used to take an extra [x0] and do that
   composition itself, back when it was a ghost update needing the
   authority. *)

Lemma uf_link_field_acc γ h ih rc lp :
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc -∗
  isBlockLocs rc [lp] -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ (y : elem) jy,
    ▷ (lp ↦ #y) ∗
    ▷ (vertex γ y jy ∗ same_class γ h y ∗ ⌜(jy < ih)%Z⌝) ∗
    (∀ (z : elem) k, ⌜(k < ih)%Z⌝ -∗ vertex γ z k -∗ same_class γ h z -∗
       lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> True).
Proof.
  iIntros "#Hinv #Hh #Hlk #Hlocs".
  iDestruct (vertex_frag with "Hh") as "#Hhfrag".
  iDestruct "Hh" as (lhi lhc) "(_ & #Hhlocs & _ & _)".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hhfrag Hhlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  (* [h] is linked, so its cell holds a [Link] — and the record is [rc],
     since a vertex's link record is fixed once and for all. *)
  destruct c as [rc'|rc'].
  { (* A root's cell owns [h ↪[γ.(uf_link)] None], which [linked] refutes. *)
    iAssert (▷ False)%I with "[Hcell]" as ">[]".
    iNext. iDestruct "Hcell" as "(_ & Htok & _)".
    iApply (linked_not_root with "Hlk Htok"). }
  iDestruct "Hcell" as "(>%Hnr & >#Hlk' & Hlf)".
  iDestruct (linked_agree with "Hlk' Hlk") as %->.
  iDestruct "Hlf" as (lp' y jy) "(#Hlocs' & #HP & Hlp & #Hy & >%Hjy & >#Hsc)".
  iAssert (▷ ⌜[lp] = [lp']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (isBlockLocs_valid with "Hlocs' Hlocs"). }
  simplify_eq.
  iModIntro. iExists y, jy.
  iFrame "Hlp".
  iSplitR; first by iNext; iFrame "Hy Hsc".
  iIntros (z k) "%Hk #Hz #Hhz Hlp".
  iMod ("Hclose" with "[Hcont Hlc Hlp Hframe]") as "_".
  { iNext.
    iApply (uf_inv_reassemble _ _ _ _ _ (CtLink rc)
              with "Hcont [] Hlc [Hlp] Hframe").
    { iExact "Hhlocs". }
    iSplitR; first done. iFrame "Hlk".
    iExists _, z, k. by iFrame "Hlocs' HP Hlp Hz Hhz". }
  by iModIntro.
Qed.

Lemma uf_link_parent_acc γ h ih rc lp (Φ : val → iProp Σ) :
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < ih)%Z⌝ -∗ same_class γ h y -∗ vertex γ y j -∗ Φ #y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ w -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ w).
Proof.
  iIntros "#Hinv #Hh #Hlk #Hlocs HΦ".
  iMod (uf_link_field_acc with "Hinv Hh Hlk Hlocs")
    as (y jy) "(Hlp & Hy & Hback)".
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iDestruct "Hy" as "(#Hyv & #Hhy & %Hjy)".
  iMod ("Hback" $! y jy with "[//] Hyv Hhy Hlp") as "_".
  iModIntro. iApply ("HΦ" with "[//] Hhy Hyv").
Qed.

(* The same accessor, with the loaded parent existentially quantified at
   [elem] rather than at [val]. [ipat_PRecord_atomic] — the rule behind
   [find]'s [Link { parent = y }] pattern — is [val]-shaped, but
   [compress] reads the field through an ordinary [let y = link.parent],
   i.e. [imp_ERecordAccess_atomic], whose loaded value is at the
   postcondition's own type. Only the witness of the existential
   differs. *)

Lemma uf_link_parent_acc_elem γ h ih rc lp (Φ : elem → iProp Σ) :
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc -∗
  isBlockLocs rc [lp] -∗
  ▷ (∀ (y : elem) j, ⌜(j < ih)%Z⌝ -∗ same_class γ h y -∗ vertex γ y j -∗ Φ y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ y : elem, ▷ lp ↦ #y ∗ ▷ (lp ↦ #y -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ y).
Proof.
  iIntros "#Hinv #Hh #Hlk #Hlocs HΦ".
  iMod (uf_link_field_acc with "Hinv Hh Hlk Hlocs")
    as (y jy) "(Hlp & Hy & Hback)".
  iModIntro. iExists y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iDestruct "Hy" as "(#Hyv & #Hhy & %Hjy)".
  iMod ("Hback" $! y jy with "[//] Hyv Hhy Hlp") as "_".
  iModIntro. iApply ("HΦ" with "[//] Hhy Hyv").
Qed.

(* Rerouting a link's [parent] field, which is what path compression does.
   Unlike the CAS this is an ordinary (racy, non-atomic in the source,
   single-store in the semantics) write, so it is a plain accessor: borrow
   the field, hand back a new one. The obligation it levies is the link
   field's own: the caller must show the vertex it is rerouting to is
   registered, sits below the holder's identifier, and is already in the
   holder's class. *)

Lemma uf_link_parent_set γ h ih rc lp (z : elem) k (Φ : iProp Σ) :
  (k < ih)%Z →
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc -∗
  isBlockLocs rc [lp] -∗
  vertex γ z k -∗
  same_class γ h z -∗
  ▷ Φ -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ).
Proof.
  iIntros (Hk) "#Hinv #Hh #Hlk #Hlocs #Hz #Hhz HΦ".
  iMod (uf_link_field_acc with "Hinv Hh Hlk Hlocs")
    as (y jy) "(Hlp & _ & Hback)".
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hback" $! z k with "[//] Hz Hhz Hlp") as "_".
  by iModIntro.
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [union]: the linking CAS. *)

(* Everything the [compare_and_set_spec] premise needs when the CASed cell
   is vertex [a]'s content cell and the value going in is a fresh [Link]
   record pointing at [b], packaged once.

   This is the only step in the whole development that MOVES the abstract
   state, so it is the only one whose hook may hand a different [UF] back:
   [a]'s class is absorbed into [b]'s, which is [update_class] on [R] and
   on [V] at once. The hook is run only if the CAS succeeds, and it is run
   with the three facts that make the transition meaningful, all of them
   read off the state at that instant: [a] is a root, the two classes are
   distinct, and the value the caller read out of [a]'s [Root] record
   really is the value of [a]'s class.

   Everything is reported at [a] and [b] themselves — the vertices the CAS
   links. A caller whose client named other members of the same two
   classes re-bases afterwards ([union_hook_rebase]); that used to happen
   here, through an extra [x0]/[y0] pair, and it does not need an open.

   Note that the transition is nevertheless NOT stated at [R b]: writing
   the update at a representative would leave an [R (R b)] a client has no
   way to collapse. The bridge to the root, which the invariant does need,
   is one [update_class_congr_class] inside the proof.

   Two things carry the proof.

   The identifier ordering [ib < ia] is what makes the result a
   representative function again rather than a cycle: [b]'s representative
   has an identifier at most [b]'s ([repr_id_le]), hence below [a]'s, so
   it cannot be [a] itself.

   And the ABA argument — if the cell's current content sits at the same
   record as the [Root] the caller expects, it must BE that [Root], not a
   [Link] that reused the block — is now one line: the caller holds
   [root_val rce vexp], a PERSISTENT points-to for that record's single
   field, while a link record's field is owned exclusively by its holder's
   [cell_own], and one location cannot carry both
   ([link_field_root_val_excl]). *)

Lemma uf_cas_link_fupd γ (a b : elem) ia ib lac
    (rce rcn : record) (vexp : val) (P Ψ : iProp Σ) (Φ : bool → iProp Σ) :
  (ib < ia)%Z →
  is_uf γ -∗
  vertex γ a ia -∗
  (∃ li, isBlockLocs a [li; lac]) -∗
  root_val rce vexp -∗
  vertex γ b ib -∗
  rcn ⤇ {| link_parent := b |} -∗
  (* The caller's linearization resources. They are spent only if the CAS
     succeeds; a failed CAS hands them straight back, which is what lets
     [union] retry. *)
  P -∗
  (* The hook also YIELDS the class fact born at this instant. Recording a
     new equivalence needs the full authority over the recorded set, and
     the two halves — the invariant's and the client's — meet only here,
     inside the hook, where the client's atomic update is opened. So this
     is the one place it can be minted, and the transition is exactly what
     mints it: [UF_same_class_update] does both at once. *)
  ▷ (∀ D (R : elem → elem) (V : elem → val),
       ⌜R a = a⌝ -∗ ⌜R a ≠ R b⌝ -∗ ⌜V a = vexp⌝ -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R.[a -/R/> R b] V.[a -/R/> V b] ∗ same_class γ a b ∗ Ψ) -∗
  ▷ (∀ res : bool,
       (if res then Ψ else P ∗ rcn ⤇ {| link_parent := b |}) -∗ Φ res) -∗
  |={⊤,⊤ ∖ ↑ufN}=>
    ∃ c cs (r rs : record) dq1 dq2 t,
      ⌜#(CtRoot rce) = VInline cs rs⌝ ∗
      ▷ lac ↦ VInline c r ∗ ▷ isBlock r dq1 t ∗ ▷ isBlock rs dq2 Mut ∗
      ▷ (lac ↦ (if locations.eqb r rs then #(CtLink rcn) else VInline c r) -∗
         isBlock r dq1 t -∗ isBlock rs dq2 Mut -∗
         |={⊤ ∖ ↑ufN,⊤}=> Φ (locations.eqb r rs)).
Proof.
  intros Hab.
  iIntros "#Hinv #Ha (%lai & #Halocs) #Hrv #Hb Hrcn HP Hhook HΦ".
  iDestruct (vertex_frag with "Ha") as "#Hafrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hafrag Halocs H") as (c D Rp Vp)
    "(%HaD & Hcont & Hlc & Hcell & Hframe)".
  iAssert (▷ (isBlock (content_loc c) DfracDiscarded Mut ∗
              cell_own γ Rp Vp a ia c))%I with "[Hcell]" as "[#HcP Hcell]".
  { iNext. iDestruct (cell_own_info with "Hcell") as "(_ & [#Hb1 _] & _ & $)".
    iExact "Hb1". }
  iModIntro.
  iExists (content_tag c), (content_tag (CtRoot rce)), (content_loc c), rce,
          DfracDiscarded, DfracDiscarded, Mut.
  iSplitR; first by rewrite content_encode_inline.
  rewrite -{1}(content_encode_inline c).
  iFrame "Hlc HcP".
  iSplitR; first by iDestruct "Hrv" as (lv) "(_ & $ & _)".
  iNext. iIntros "Hlc' _ _".
  destruct (locations.eqb_spec (content_loc c) rce) as [Heq|Hne]; last first.

  { (* CAS failure: the cell still holds [c]; close untouched and hand the
       fresh record back for the next attempt. *)
    iEval (rewrite -content_encode_inline) in "Hlc'".
    iMod ("Hclose" with "[Hcont Hlc' Hcell Hframe]") as "_".
    { iNext.
      iApply (uf_inv_reassemble with "Hcont Halocs Hlc' Hcell Hframe"). }
    iModIntro. iApply ("HΦ" $! false with "[$HP $Hrcn]"). }

  (* CAS success. The cell's content sits at the very record the expected
     [Root] describes, so it IS that [Root]: a [Link] there would own the
     record's field exclusively, and the caller holds it persistently. *)
  destruct c as [rc0|rc0]; simpl in Heq; subst rc0; last first.
  { iDestruct "Hcell" as "(_ & _ & Hlf)".
    iDestruct (link_field_root_val_excl with "Hlf Hrv") as "[]". }
  iDestruct "Hcell" as "(%Hroot & Htokl & #Hrv0)".
  iAssert ⌜Vp a = vexp⌝%I as %Hval.
  { iDestruct "Hrv" as (lv) "(#Hl1 & _ & #Hp1)".
    iDestruct "Hrv0" as (lv') "(#Hl2 & _ & #Hp2)".
    iDestruct (isBlockLocs_valid with "Hl1 Hl2") as %[= ->].
    by iDestruct (gen_heap.pointsto_agree with "Hp2 Hp1") as %[= ->]. }

  (* Take the frame apart: the identifiers of [b] and of its
     representative are what the transition rests on. *)
  iDestruct "Hframe" as (M L N)
    "(%HMa & %HdomM & %HdomL & %Hrep & %HRp & %HVp &
      Hauth & Hlauth & Hnauth & Htoks & HM)".
  iDestruct (vertex_frag with "Hb") as "#Hbfrag".
  iDestruct (ghost_map_lookup with "Hauth Hbfrag") as %HMb.
  assert (Hbdom : b ∈ dom M) by (apply elem_of_dom; by eexists).
  pose proof (repr_dom _ _ HRp b Hbdom) as Hzdom.
  apply elem_of_dom in Hzdom as [iz HMz].
  assert (Hizb : (iz ≤ ib)%Z) by (eapply (repr_id_le _ _ HRp b); done).
  assert (Hlt : (iz < ia)%Z) by lia.
  pose proof (repr_idem _ _ HRp b) as Hidemb.

  (* The two classes are distinct. *)
  assert (Hne' : Rp b ≠ a).
  { intros Hcontra. rewrite Hcontra HMa in HMz. simplify_eq. lia. }

  (* The linearization point proper. The hook reports the transition at
     [b]; the invariant is re-closed at [b]'s root, and the two namings of
     the same class agree. *)
  assert (HeqV : Vp.[a -/Rp/> Vp b] = Vp.[a -/Rp/> Vp (Rp b)]).
  { by rewrite (HVp b). }
  iMod ("Hhook" $! D Rp Vp with "[%] [%] [%] HP Hcont")
    as "(Hcont & #Hsab & HΨ)".
  { exact Hroot. }
  { rewrite Hroot. by intros ->. }
  { exact Hval. }
  rewrite HeqV.

  (* [a] is linked from now on: its record is fixed. The registry's domain
     does not move — [a] was already in it — and the class fact came out
     of the hook, which is the only place it could be minted. *)
  iDestruct (ghost_map_lookup with "Hlauth Htokl") as %HLa.
  iMod (ghost_map_update (Some rcn) with "Hlauth Htokl") as "[Hlauth Htokl]".
  iMod (ghost_map_elem_persist with "Htokl") as "#Hlk".

  (* Re-close under the merged state. *)
  iMod ("Hclose" with "[- HΨ HΦ]") as "_".
  { iNext.
    iExists M, (<[a := Some rcn]> L), N,
            Rp.[a -/Rp/> Rp b], Vp.[a -/Rp/> Vp (Rp b)].
    iFrame "Hauth Hlauth Hnauth Htoks".
    rewrite HdomM. iFrame "Hcont".
    iSplitR.
    { iPureIntro.
      rewrite dom_insert_lookup_L; [by rewrite HdomL | by eexists]. }
    iSplitR; first done.
    iSplitR.
    { iPureIntro. eapply (uf_repr_link M Rp a (Rp b) ia iz); done. }
    iSplitR.
    { iPureIntro. by eapply (uf_link_value_coherent M Rp a (Rp b) ia iz). }
    rewrite (big_sepM_delete _ M a ia); last exact HMa.
    iSplitR "HM".
    { iExists lai, lac, (CtLink rcn).
      iSplitR; first iExact "Halocs".
      iSplitL "Hlc'"; first iExact "Hlc'".
      iSplitR.
      { iPureIntro. rewrite lookup_update_class. exact Hne'. }
      iSplitR; first iExact "Hlk".
      iApply (link_field_intro with "Hrcn Hb Hsab"). lia. }
    iApply (vertex_own_reindex with "HM").
    { intros w i Hw. eapply (uf_link_root_iff M Rp a (Rp b) ia iz); [done..|].
      intros ->. by rewrite lookup_delete_eq in Hw. }
    { intros w i Hw Hw'. rewrite lookup_update_class_ne //.
      rewrite Hroot Hw'. intros ->. by rewrite lookup_delete_eq in Hw. } }
  iModIntro. iApply ("HΦ" $! true with "HΨ").
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [set]: the value CAS. *)

(* [set] never writes a payload field. It swings the whole content cell to
   a freshly allocated [Root] record, and that is precisely what lets a
   payload be immutable, hence persistent, hence readable with no open at
   all — which is what [get] lives on.

   Abstractly the step moves [V] and nothing else, by [update_class]: the
   whole of [x]'s class takes the new value at once, which is what keeps
   the invariant's [V u = V (R u)] true ([lookup_class_root]). Since [R]
   does not move, no vertex changes root-status and the recorded pairs are
   untouched; the only vertex whose footprint changes at all is [x].

   As in [uf_cas_link_fupd], everything is reported at the vertex the CAS
   acts on; a caller whose client named another member of the class
   re-bases afterwards ([set_hook_rebase]).

   The ABA argument is [uf_cas_link_fupd]'s in mirror image: the expected
   [Root]'s payload points-to is persistent, a [Link]'s field is owned
   exclusively by its holder, and one location cannot be both. *)

Lemma uf_cas_set_fupd γ (x : elem) i lxc
    (rce rcn : record) (vexp v : val) (P Ψ : iProp Σ) (Φ : bool → iProp Σ) :
  is_uf γ -∗
  vertex γ x i -∗
  (∃ li, isBlockLocs x [li; lxc]) -∗
  root_val rce vexp -∗
  rcn ⤇ {| root_value := v |} -∗
  (* The caller's linearization resources, spent only if the CAS
     succeeds; a failed CAS hands them back, which is what lets [set]
     retry. The fresh record comes back with them: it was never
     installed. *)
  P -∗
  ▷ (∀ D (R : elem → elem) (V : elem → val),
       ⌜R x = x⌝ -∗ ⌜V x = vexp⌝ -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R V.[x -/R/> v] ∗ Ψ) -∗
  ▷ (∀ res : bool,
       (if res then Ψ else P ∗ rcn ⤇ {| root_value := v |}) -∗ Φ res) -∗
  |={⊤,⊤ ∖ ↑ufN}=>
    ∃ c cs (r rs : record) dq1 dq2 t,
      ⌜#(CtRoot rce) = VInline cs rs⌝ ∗
      ▷ lxc ↦ VInline c r ∗ ▷ isBlock r dq1 t ∗ ▷ isBlock rs dq2 Mut ∗
      ▷ (lxc ↦ (if locations.eqb r rs then #(CtRoot rcn) else VInline c r) -∗
         isBlock r dq1 t -∗ isBlock rs dq2 Mut -∗
         |={⊤ ∖ ↑ufN,⊤}=> Φ (locations.eqb r rs)).
Proof.
  iIntros "#Hinv #Hx (%lxi & #Hxlocs) #Hrv Hrcn HP Hhook HΦ".
  iDestruct (vertex_frag with "Hx") as "#Hxfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hxfrag Hxlocs H") as (c D Rp Vp)
    "(%HxD & Hcont & Hlc & Hcell & Hframe)".
  iAssert (▷ (isBlock (content_loc c) DfracDiscarded Mut ∗
              cell_own γ Rp Vp x i c))%I with "[Hcell]" as "[#HcP Hcell]".
  { iNext. iDestruct (cell_own_info with "Hcell") as "(_ & [#Hb1 _] & _ & $)".
    iExact "Hb1". }
  iModIntro.
  iExists (content_tag c), (content_tag (CtRoot rce)), (content_loc c), rce,
          DfracDiscarded, DfracDiscarded, Mut.
  iSplitR; first by rewrite content_encode_inline.
  rewrite -{1}(content_encode_inline c).
  iFrame "Hlc HcP".
  iSplitR; first by iDestruct "Hrv" as (lv) "(_ & $ & _)".
  iNext. iIntros "Hlc' _ _".
  destruct (locations.eqb_spec (content_loc c) rce) as [Heq|Hne]; last first.

  { (* CAS failure: the cell still holds [c]; close untouched and hand the
       fresh record back for the next attempt. *)
    iEval (rewrite -content_encode_inline) in "Hlc'".
    iMod ("Hclose" with "[Hcont Hlc' Hcell Hframe]") as "_".
    { iNext.
      iApply (uf_inv_reassemble with "Hcont Hxlocs Hlc' Hcell Hframe"). }
    iModIntro. iApply ("HΦ" $! false with "[$HP $Hrcn]"). }

  (* CAS success. As in the linking case, the cell's content sits at the
     very record the expected [Root] describes, so it IS that [Root]. *)
  destruct c as [rc0|rc0]; simpl in Heq; subst rc0; last first.
  { iDestruct "Hcell" as "(_ & _ & Hlf)".
    iDestruct (link_field_root_val_excl with "Hlf Hrv") as "[]". }
  iDestruct "Hcell" as "(%Hroot & Htokl & #Hrv0)".
  iAssert ⌜Vp x = vexp⌝%I as %Hval.
  { iDestruct "Hrv" as (lv) "(#Hl1 & _ & #Hp1)".
    iDestruct "Hrv0" as (lv') "(#Hl2 & _ & #Hp2)".
    iDestruct (isBlockLocs_valid with "Hl1 Hl2") as %[= ->].
    by iDestruct (gen_heap.pointsto_agree with "Hp2 Hp1") as %[= ->]. }

  (* The linearization point proper: [x] is a root, and its class is what
     moves. *)
  iMod ("Hhook" $! D Rp Vp with "[%] [%] HP Hcont") as "[Hcont HΨ]".
  { exact Hroot. }
  { exact Hval. }

  (* The new record's payload is fixed from now on. *)
  iMod (root_val_alloc with "Hrcn") as "#Hrvn".

  (* Re-close under the new value function. Only [x]'s own footprint
     changes; every other vertex is re-closed by [vertex_own_reindex],
     whose obligation here is that no OTHER root's value moved — which
     holds because [x] is the only root of its class. *)
  iDestruct "Hframe" as (M L N)
    "(%HMx & %HdomM & %HdomL & %Hrep & %HRp & %HVp &
      Hauth & Hlauth & Hnauth & Htoks & HM)".
  iMod ("Hclose" with "[- HΨ HΦ]") as "_".
  { iNext.
    iExists M, L, N, Rp, Vp.[x -/Rp/> v].
    iFrame "Hauth Hlauth Hnauth Htoks".
    rewrite HdomM. iFrame "Hcont".
    iSplitR; first (iPureIntro; by rewrite HdomL).
    do 2 (iSplitR; first done).
    iSplitR.
    { iPureIntro.
      assert (Idempotent Rp) by (constructor; apply (repr_idem _ _ HRp)).
      intros u. apply lookup_class_root, HVp. }
    rewrite (big_sepM_delete _ M x i); last exact HMx.
    iSplitR "HM".
    { iExists lxi, lxc, (CtRoot rcn).
      iFrame "Hxlocs Hlc'".
      iSplitR; first done.
      iFrame "Htokl".
      rewrite lookup_update_class //. }
    iApply (vertex_own_reindex with "HM").
    { by intros w k Hw. }
    { intros w k Hw Hw'. rewrite lookup_update_class_ne //.
      rewrite Hroot Hw'. intros ->. by rewrite lookup_delete_eq in Hw. } }
  iModIntro. iApply ("HΦ" $! true with "HΨ").
Qed.

End uf_acc.
