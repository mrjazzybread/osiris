From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map.
From stdpp Require Import relations.

From osiris Require Import osiris.
From osiris.stdlib.proofs Require Import atomic.
From osiris.examples Require Import og_ConcurrentUnionFind.

Require Import UnionFind12GhostInv.

(** * Concurrent union-find

    This file contains the verification of the concurrent union-find data
    structure. *)

(* A vertex is a two-field record { id; content }. *)
Notation elem := record.

(* Field offsets of the vertex record. *)
Notation id_field := 0%Z (only parsing).
Notation content_field := 1%Z (only parsing).

Section ConcurrentUnionFind.

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
        *re-reading* the racy [parent] field. [ipat_PRecord_atomic]
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
    iMod (reaches_refl with "Hinv") as "#Hreaches_refl".
    imp_path.
    iPureIntro; lia. }

  (* [Link { parent = y } -> find y]: the [Root] branch is refuted; the
     [Link] record pattern re-reads the racy [parent] field atomically.
     Only the link record's own content is touched — a plain borrow. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & (%b & #Hrc & %Hb))".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp] with "Hlocs []"); first done.
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
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp] with "Hlocs []"); first done.
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
    iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lv] with "Hrclocs []"); first done.
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
      iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lv] with "Hrclocs []"); first done.
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

      iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lv] with "Hrclocs []"); first done.
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
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp] with "Hlocs []"); first done.
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
