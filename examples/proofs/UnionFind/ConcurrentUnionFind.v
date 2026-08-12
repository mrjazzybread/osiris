From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var.
From stdpp Require Import relations.

From osiris Require Import osiris.
From osiris.program_logic Require Import atomic.
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

(* Resource algebras used by the [is_uf] invariant. *)
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* ------------------------------------------------------------------------ *)
(* Resoning rules for reading the [id] and [content] fields of an [elem]. *)

(* Atomically reading a vertex's content cell: the caller receives the
   loaded value's [content_info] snapshot. *)

Lemma read_vertex {ζ : exn → iProp Σ} {Ψ η} γ z j e :
  is_uf γ -∗
  vertex γ z j -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content), content_info γ z c }}.
Proof.
  iIntros "#Hinv #Hz He".
  iDestruct "Hz" as (lzi lzc) "(#Hzfrag & #Hzlocs & #HzP & #Hzli)".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lzi; lzc] z
            with "Hzlocs He []").
  { list_z.length; lia. }
  iNext.
  iApply (uf_vertex_content_acc with "Hinv Hzfrag Hzlocs").
  iNext. iIntros (c) "#Hinfo". iExact "Hinfo".
Qed.

(* Reading a vertex's immutable [id] field, through the persistent
   points-to that [vertex] carries. *)

Lemma read_vertex_id {ζ : exn → iProp Σ} {Ψ η} γ z i e :
  vertex γ z i -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e id_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (n : Z), ⌜n = i⌝ }}.
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
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (EAtomicLoc e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (l : locations.loc), ∃ li, isBlockLocs z [li; l] }}.
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
  EWP (eval η (EPath ["Atomic"; "Loc"; "compare_and_set"]))
    {{ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec }}.
Proof.
  iIntros "HAtomic".
  iDestruct (atomic_cas_path_spec with "HAtomic") as (cas Hcas) "#Hspec".
  iApply (imp_EPath (A:=val) cas).
  { exact Hcas. }
  iExact "Hspec".
Qed.

(* The same read, at the one place where it is a linearization point: it
   is [find]'s and [get]'s scrutinee read. The caller hands over a
   resource [P] — in practice the atomic update it is running under —
   together with a hook saying what to do with it if the loaded content
   turns out to be a [Root], which is exactly when [x]'s representative is
   known to be [x] itself. The hook also receives [content_val], which
   pins that [Root] record's payload to [V x]: that is what lets [get]
   linearize here and read the field afterwards. If the content is a
   [Link] instead, nothing has been linearized: [P] comes back untouched,
   along with the loaded value's [content_info], and the traversal moves
   on. *)

Lemma read_vertex_lp {ζ : exn → iProp Σ} {Ψ η} γ (x : elem) i e
    (P : iProp Σ) (Q : content → iProp Σ) :
  is_uf γ -∗
  vertex γ x i -∗
  P -∗
  ▷ (∀ (c : content) D (R : elem → elem) (V : elem → val),
       ⌜content_root c = true⌝ -∗ ⌜R x = x⌝ -∗
       content_info γ x c -∗ content_val V x c -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R V ∗ Q c) -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = x⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content),
         if content_root c then Q c else content_info γ x c ∗ P }}.
Proof.
  iIntros "#Hinv #Hx HP Hhook He".
  iDestruct "Hx" as (lxi lxc) "(#Hxfrag & #Hxlocs & #HxP & #Hxli)".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lxi; lxc] x
            with "Hxlocs He [HP Hhook]").
  { list_z.length; lia. }
  iNext.
  iApply (uf_find_content_acc with "Hinv Hxfrag Hxlocs").
  iNext. iIntros (c D R V) "_ %Hroot #Hinfo #Hval Hst".
  destruct (content_root c) eqn:Hc; last by iFrame "Hst Hinfo HP".
  pose proof (Hroot eq_refl) as HRx.
  iMod ("Hhook" $! c D R V with "[//] [//] Hinfo Hval HP Hst") as "[$ $]". done.
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [G.fresh]. *)

(* [G.fresh]'s specification is strengthened to hand back exclusive
   ownership of the returned identifier [i] in the registry [γ.(uf_ids)]:
   that token is what lets [make_proof] extend [id_tokens], which is what
   keeps identifiers injective, which is in turn what lets [union_proof]
   discharge [assert (x.id <> y.id)] (see [id_tokens_injective]). *)

Definition fresh_spec (γ : uf_names) (u : unit) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  EWP m {{ (i : Z), i ↪[γ.(uf_ids)] () ∗ ⌜representable i⌝ }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [make]. *)

(* Ownership of a freshly allocated, not-yet-installed [Root] record
   holding [v]. Both operations that allocate one need it: [make] installs
   it in the vertex it is creating, and [set] CASes it into an existing
   vertex's cell. The [CtLink] case is [False] rather than a separate
   existential because a caller always knows which it has. *)

Definition fresh_root (cx : content) (v : val) : iProp Σ :=
  match cx with
  | CtRoot rc => rc ⤇ {| root_value := v |}
  | CtLink _ => False
  end.

(* [make v] returns a fresh vertex of the structure, of value [v] and its
   own class.

   This is the sequential [make_spec]'s postcondition (UnionFind.v)
   verbatim — the domain gains [x], and [x]'s class, which is [x] alone,
   takes [v] — with the state quantified atomically, plus the persistent
   [in_uf γ x] every later call on [x] needs.

   Alone among the operations here, [make] states its specification as a
   plain logically atomic triple rather than as a hook. It can afford to:
   nothing in this module calls it, so there is no caller whose own
   linearization point comes later and who would therefore be unable to
   supply an atomic update (contrast [find_spec]'s comment). The single
   ghost step that registers the vertex is the linearization point, and
   the client's update is committed right there, inside
   [register_vertex]. *)

Definition make_spec (γ : uf_names) (v : val) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ x : elem, ⌜x ∉ D ∧ R x = x⌝ ∗ UF γ (D ∪ {[x]}) R V.[x -/R/> v]
    | RET x; in_uf γ x }>>.

(* Records allocated by this module must fit within [max_array_length]:
   two fields for a vertex ([make]), one for a content record ([make],
   [set] and [union]). *)
Hypothesis Hmax1 : (1 ≤ max_array_length)%Z.
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof γ η :
  path_spec ["G"; "fresh"] (λ fresh, □ iSpec τ[unit] fresh (fresh_spec γ))%I η -∗
  EWP (eval η (EAnonFun __make)) {{ c, □ iSpec τ[val] c (make_spec γ) }}.
Proof.
  iIntros "#HG".
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  (* We are proving a logically atomic triple: introduce the atomic
     update [AU] and the abstract postcondition [Φ]. *)
  iIntros "#Hinv" (Φ) "AU".
  iApply imp_please; iNext.

  (* [let id = G.fresh() and content = Root { value = v } in ...].
     We specify the two postconditions upfront. *)
  imp_let $! (λ i : Z, i ↪[γ.(uf_ids)] () ∗ ⌜representable i⌝)%I
          $! (λ c : content, ∃ rc, ⌜c = CtRoot rc⌝ ∗ rc ⤇ {| root_value := v |})%I.
  { (* [G.fresh()]. *)
    imp_app τ[unit].
    iIntros "Hm".
    iApply ("Hm" with "Hinv"). }
  { (* [Root { value = v }]. *)
    imp_record $! root_fields.
    simpl. iIntros (c) "(%r & -> & % & Hown & ->)".
    by iFrame "Hown". }
  iIntros (a cx) "[Htok %Hrepa] (%rc & -> & Hrecord)".

  (* [{ id; content }]. *)
  iApply imp_fupd.
  iApply (imp_wand with "[]").
  { imp_record. }
  iIntros (x) "(%i & %c & Hown & -> & ->) /=".

  (* Establish the postcondition [|={⊤}=> Φ x] with the atomic update *)
  iMod (register_vertex (in_uf γ x -∗ Φ x)%I $! Hrepa
          with "Hinv Htok Hown Hrecord [AU]") as "[#Hv HΦ]".
  { (* The linearization point: commit the atomic update. *)
    iIntros (D R V) "%HxD %Hroot Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iMod (UF_update_2 _ _ _ _ (D ∪ {[x]}) R V.[x -/R/> v]
            with "Hst Hcl") as "[Hst Hcl]";
      [done | by apply uf_val_congr_set |].
    iMod ("Hcommit" $! x with "[$Hcl]") as "HΦ"; first done.
    by iFrame "Hst HΦ". }
  iModIntro. iApply "HΦ". by iExists a.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [find]. *)

(* [find x] returns the representative of [x] as of the instant of its
   own last read.

   Consider the sequential [find_spec] (UnionFind.v):

     ∀ D R V, ⌜e ∈ D⌝ -∗ UF D R V -∗
       EWP m {{ (z : elem), ⌜z = R e⌝ ∗ UF D R V }}

   The concurrent version below is the same statement with the state
   quantified atomically instead of owned by the caller throughout, and
   with the pure precondition [⌜e ∈ D⌝] replaced by the persistent
   [in_uf γ x].

   The private postcondition is what a caller keeps once the atomic claim
   has been spent: the vertex it got back is a vertex of the structure, in
   [x]'s class. Both are permanent; neither says anything about the state
   the caller now sees.

   This specification is about [x] and nothing else — there is no
   generalisation over a third vertex, and the recursion needs none. That
   is worth a note, because it was not always so, and the reason is the
   shape of [UF].

   [find x] tail-calls [find y] on [x]'s parent, so the obligation it
   holds, which is about [R x], must become one about [R y]. Bridging them
   needs [R x = R y] — true only at an instant, with [same_class γ x y] as
   the evidence — and the bridge has to be usable at the moment the CALLEE
   accesses the update, by which time the callee holds [ufN] open. That is
   exactly why the triple's outer mask is [⊤ ∖ ↑ufN]: nothing there can
   open the invariant.

   So the bridge cannot go through the invariant, and it does not: [UF]
   carries half the class authority, and the access hands over a [UF]. See
   [UF_same_class_eq] — a pure elimination, no fupd and no mask side
   condition — and the wrapper in [find_proof]'s [Link] branch. *)

Definition find_spec (γ : uf_names) x (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ z : elem, ⌜z = R x⌝ ∗ UF γ D R V
    | RET z; in_uf γ z ∗ same_class γ x z }>>.

(* ------------------------------------------------------------------------ *)

(* The second specification of the same code, and all that [find]'s own
   callers inside this module want: the traversal landed on a vertex of
   the structure, in [x]'s class. Neither conjunct mentions the abstract
   state.

   This cannot be derived from the triple, and the reason is not an
   artefact of the encoding. To USE a logically atomic triple one must
   hand over an atomic update, i.e. be able to produce [UF γ D R V] at the
   triple's outer mask [⊤ ∖ ↑ufN]. [get], [set] and [union] own no such
   thing: their own client's update is spent at their own, LATER,
   linearization point — the read or CAS that follows the traversal, not
   the traversal — and at that mask they cannot open [ufN] to borrow the
   invariant's half either. They have nothing to give, so they need a
   specification that asks for nothing.

   It is therefore proved separately, from the code, below. Like the
   triple it is about [x] alone: a caller standing at some other vertex of
   the class composes afterwards, which costs nothing. *)

Definition find_observe_spec (γ : uf_names) (x : elem) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗
  EWP m {{ (z : elem), in_uf γ z ∗ same_class γ x z }}.

(* Proof outline:
   1. Read [x.content] atomically, through [read_vertex_lp]. This is the
      only step of the whole call that can be a linearization point, and
      it is one exactly when the loaded value is a [Root]: then the
      accessor reports [R x = x] against the state at that instant, which
      is where the client's atomic update is committed.
   2. Case on the loaded value:
      - [CtRoot]: the branch returns [x], and the atomic update has
        already been committed to it.
      - [CtLink]: the update has not been touched; the branch
        pattern-matches [{ parent = y }] against the link record,
        *re-reading* the racy [parent] field. [ipat_PRecord_atomic]
        performs that single field load under [uf_inv], with
        [uf_link_parent_acc] supplying its fupd: even if [x]'s parent has
        moved on since, whatever vertex [y] the field holds now satisfies
        [same_class γ x y]. Recurse through the [in_env "find"]
        hypothesis — on [y], so the update, which is about [x], has to be
        transported across that class fact. See the [Link] branch. *)

Lemma find_proof γ η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ)) η -∗
  EWP (eval η (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))))
    {{ c, □ iSpec τ[elem] c (find_spec γ) }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_spec.
  iIntros "#Hinv #Hx".
  iIntros (Φ) "AU".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* Goal: [ match x.content with ... ]. The scrutinee read carries the
     atomic update: on a [Root] it is committed there and then, and the
     branch's whole postcondition comes back in its place. *)
  imp_match content with "[AU]".
  { iApply (read_vertex_lp _ x i _ _ (λ _, Φ x)%I
              with "Hinv Hxv AU [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ AU Hst".
    (* The linearization point: in the state the accessor exposes, [x] is
       its own representative — which is what [find] is returning — so
       this is where the client's update is committed. Its private
       postcondition is produced on the spot. *)
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iMod ("Hcommit" $! x with "[$Hcl]") as "HΦ"; first by rewrite HRx.
    iFrame "Hst". iApply "HΦ".
    iSplitR; [by iExists i | iApply same_class_refl]. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]: nothing left to do, the branch returns [x]. *)
    rewrite (@encode_encode' content).
    next_branch.
    imp_path. }

  (* [Link { parent = y } -> find y]: the update was handed back
     untouched, together with the loaded value's [content_info] — which
     for a [Link] says that [rc] is [x]'s own record, permanently. *)
  iDestruct "Hc" as "[(_ & (%lp & #Hlocs) & #Hlk) AU]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp]
            with "Hlocs [AU]"); first done.
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk Hlocs [AU]").
  iNext.
  iIntros (y j Hj) "#Hxy #Hy".

  (* Recurse on the parent. The call is on [y] and the update is about
     [x], so it is transported across [same_class γ x y]: the wrapper
     opens the outer update and, at mask [∅] where no invariant could be
     opened, [UF_same_class_eq] turns that class fact into [R x = R y].
     The inner commit's [⌜z = R y⌝] then discharges the outer's
     [⌜z = R x⌝], and the private postcondition — [in_uf γ z] and
     [same_class γ y z] — is re-based from [y] to [x] by composition.
     Nothing else about the call changes: this is a tail call, so the
     outer update is committed by the inner one and never comes back. *)
  imp_app τ[elem].
  iIntros "Hm".
  iApply ("Hm" with "Hinv [] [AU]").
  { by iExists j. }
  iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxy") as "[%Hxy' Hst]".
  iAaccIntro with "Hst".
  { (* Abort: nothing has happened, hand the state back. *)
    iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  (* Commit: [z] is [y]'s representative, hence [x]'s. *)
  iIntros (z) "[-> Hst] !>".
  iRight. iExists (R y).
  iSplitL "Hst"; first by iFrame "Hst"; iPureIntro; symmetry.
  iIntros "H !>". iIntros "[#Hin #Hyz]".
  iApply "H". iFrame "Hin".
  iApply (same_class_trans with "Hxy Hyz").
Qed.

(* The same code again, against the observer specification. The two proofs
   differ only where the update is involved: at the linearization point,
   which here is not one — the [Root] branch has nothing to commit, so
   [read_vertex_lp] is run with [P := True] and a trivial hook — and at
   the recursive call, where the transport degenerates into composing the
   returned class fact with the hop. *)

Lemma find_observe_proof γ η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_observe_spec γ)) η -∗
  EWP (eval η (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))))
    {{ c, □ iSpec τ[elem] c (find_observe_spec γ) }}.
Proof.
  iIntros "#IH".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_observe_spec.
  iIntros "#Hinv #Hx".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.
  imp_match content with "[]".
  { iApply (read_vertex_lp _ x i _ True%I
              (λ _, in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv [] [] []"); last first.
    { imp_path. }
    { iNext. iIntros (c D R V) "_ %HRx _ _ _ Hst".
      iFrame "Hst".
      iSplitR; [by iExists i | iApply same_class_refl]. }
    done. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.
  { rewrite (@encode_encode' content).
    next_branch.
    imp_path. }
  iDestruct "Hc" as "[(_ & (%lp & #Hlocs) & #Hlk) _]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp]
            with "Hlocs []"); first done.
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk Hlocs []").
  iNext.
  iIntros (y j Hj) "#Hxy #Hy".
  (* The recursive call reports [same_class γ y z]; compose it with the
     hop to get back to [x]. *)
  imp_app τ[elem].
  iIntros "Hm".
  iSpecialize ("Hm" with "Hinv []"); first by iExists j.
  iApply (imp_wand with "Hm").
  iIntros (z) "[$ #Hyz]".
  iApply (same_class_trans with "Hxy Hyz").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [compress]. *)

(* [compress x z] walks the path out of [x], rerouting each link it passes
   to point directly at [z], and returns [z].

   Alone among the functions here, [compress] gets no atomic triple — and
   that is the point of it. It moves no vertex between classes, changes no
   representative and no value, and reports nothing: there is no state
   transition to linearize, and a client's [UF] is untouched across the
   whole call. What it does need is a precondition, [same_class γ x z],
   because that is exactly the obligation each rerouting write incurs — a
   link's parent must stay inside its holder's class — and it is all the
   caller has anyway, since [findc] obtains [z] by running [find] on [x]'s
   parent.

   Two things carry the proof.

   First, the write is justified without re-reading anything. [linked γ x rc]
   pins [x]'s link record permanently, identifiers never change, and the
   bound the field must respect is [x]'s own identifier — so [k < jy < i]
   survives the race even though the parent field may have moved on since
   [y] was read.

   Second, the recursive call [compress y z] needs [same_class γ y z],
   while this call holds [same_class γ x y] (from the parent read) and
   [same_class γ x z] (its own precondition). That is
   [same_class_sibling]. It used to be the hardest lemma in the
   development — path confluence in a disjoint-set forest, plus the
   identifier ordering to rule out the wrong direction — and it used to be
   what the [y.id > z.id] guard existed to enable. With class membership
   recorded directly it is [Rp y = Rp x = Rp z], and the guard is back to
   doing only what the algorithm advertises: never reroute to a larger
   identifier. *)

Definition compress_spec (γ : uf_names) (x z : elem) (m : microvx) : iProp Σ :=
  ∀ i k,
    is_uf γ -∗
    vertex γ x i -∗
    vertex γ z k -∗
    same_class γ x z -∗
    EWP m {{ (w : elem), ⌜w = z⌝ }}.

Lemma compress_proof γ η :
  ▷ in_env "compress"
      (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ)) η -∗
  EWP (eval η (EAnonFun (AnonFun "x" (EAnonFun __compress_fun))))
    {{ c, □ iSpec τ[elem; elem] c (compress_spec γ) }}.
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

  (* [Link link -> ...]. [linked γ x rc] names [rc] as [x]'s record for
     good, which is what makes the racy re-reads below harmless. *)
  iDestruct "Hc" as "(_ & (%lp & #Hlocs) & #Hlk)".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.

  (* [let y = link.parent in ...]: an ordinary field read, so it goes
     through [imp_ERecordAccess_atomic] rather than the pattern rule
     [find] uses; [uf_link_parent_acc_elem] supplies its fupd. *)
  iApply (imp_ELet_var (B:=elem)
    (λ y : elem, ∃ jy, ⌜(jy < i)%Z⌝ ∗ same_class γ x y ∗ vertex γ y jy)%I).
  { iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ [lp] rc with "Hlocs [] []").
    { list_z.length; lia. }
    { imp_path. }
    iNext.
    iApply (uf_link_parent_acc_elem with "Hinv Hx Hlk Hlocs []").
    iNext.
    iIntros (y jy Hjy) "#Hsnap #Hy".
    iExists jy. iFrame "Hsnap Hy". done. }
  iIntros (y) "(%jy & %Hjy & #Hsxy & #Hy)".
  iMod (vertex_representable with "Hinv Hy") as %Hrepjy.

  (* [assert (x.id > y.id)]: discharged by the link field's own bound,
     [jy < i]. *)
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
    (* The guard, at the [Z] level: it is what the second assert and the
       write's bound obligation rest on. *)
    assert (Hkjy : (k < jy)%Z).
    { pose proof (Zgt_cases jy k) as Hgt. rewrite <- Hcmp in Hgt. lia. }

    (* [assert (x.id > z.id)]: chains the two, [k < jy < i]. *)
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

    (* [link.parent <- z]: the compression write. The link field's
       conjuncts are re-established from [vertex γ z k], the bound
       [k < jy < i], and the caller's [same_class γ x z]. *)
    iApply (imp_ESeq (λ _ : unit, True)%I).
    { iApply (imp_ERecordSet_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ _ [lp] rc (λ w : elem, ⌜w = z⌝)%I
                with "Hlocs [] [] []").
      { list_z.length; lia. }
      { imp_path. }
      { imp_path. }
      iNext.
      iIntros (a) "->".
      iApply (uf_link_parent_set with "Hinv Hx Hlk Hlocs Hz Hxz []").
      { lia. }
      done. }
    iIntros "_".

    (* [compress y z]: the recursive call's precondition. *)
    iDestruct (same_class_sibling with "Hsxy Hxz") as "#Hyz".
    imp_app τ[elem; elem].
    iIntros "Hm".
    unfold compress_spec.
    iApply ("Hm" $! jy k with "Hinv Hy Hz Hyz"). }

  (* [else z]: compression would not lower the identifier, so stop. *)
  { iIntros "%Hcmp". imp_path. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [findc]. *)

(* [findc] satisfies [find]'s specification. Not an analogue of it, not a
   variant with an extra conjunct about the path it rewrote — the same
   proposition, so that [find_atomic_spec] applies to it verbatim and
   gives [findc] the same atomic triple. That is the specification's
   entire content: the compression [findc] performs along the way is
   invisible.

   [findc] is [find] followed by [compress], and its linearization point
   is inside the [find]: at the instant [find] reports its answer,
   [findc]'s answer is already determined, and everything after it — the
   whole compression pass, a sequence of writes — is invisible to the
   abstract state. So [findc] hands its client's atomic update straight to
   [find].

   Both sides use the PLAIN [find_spec] — no generalisation over a third
   vertex anywhere. [findc]'s own update is about [R x], the call is on
   [x]'s parent [y], and the wrapper in the proof turns the one into the
   other. That transport is what [UF] carrying half the class authority
   buys: it happens inside the update's access, at mask [∅], where no
   invariant can be opened, and [UF_same_class_eq] still yields
   [⌜R x = R y⌝] there.

   The same wrapper solves the other half of the problem. [findc] needs
   [find]'s private postcondition back — [in_uf γ z] and
   [same_class γ x z] are exactly [compress]'s precondition — and an
   atomic triple does not hand it over: [atomic_ewp] folds [POST] into the
   update's commit, where the implementation produces it and consumes it
   on the spot to yield [Φ z]. But [POST] is PERSISTENT, so the wrapper
   keeps a copy on the way out, re-based from [y] to [x] by transitivity,
   which is free. *)

Lemma findc_proof γ η :
  in_env "find" (λ find, □ iSpec τ[elem] find (find_spec γ)) η -∗
  in_env "compress"
    (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ)) η -∗
  EWP (eval η (EAnonFun __findc))
    {{ c, □ iSpec τ[elem] c (find_spec γ) }}.
Proof.
  iIntros "#IFind #ICompress".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_spec.
  iIntros "#Hinv #Hx".
  iIntros (Φ) "AU".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* [match x.content with ...]: the same linearization point as [find]'s,
     for the same reason — this is the case where [x] is a root. The read
     must be the LP-carrying one: by the time the branch is taken, the
     read has happened and [⌜x = R x⌝] is no longer available. *)
  imp_match content with "[AU]".
  { iApply (read_vertex_lp _ x i _ _ (λ _, Φ x)%I
              with "Hinv Hxv AU [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ AU Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iMod ("Hcommit" $! x with "[$Hcl]") as "HΦ"; first by rewrite HRx.
    iFrame "Hst". iApply "HΦ".
    iSplitR; [by iExists i | iApply same_class_refl]. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]. *)
    rewrite (@encode_encode' content).
    next_branch.
    imp_path. }

  (* [Link { parent = y } -> let z = find y in compress x z]. *)
  iDestruct "Hc" as "[(_ & (%lp & #Hlocs) & #Hlk) AU]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp]
            with "Hlocs [AU]"); first done.
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk Hlocs [AU]").
  iNext.
  iIntros (y jy Hjy) "#Hxy #Hy".

  (* [let z = find y in ...]: the call is on [y], but the update [findc]
     holds is about [x]. TRANSPORTING it is the whole point of [UF]
     carrying half the class authority: the wrapper below opens the outer
     update, and right there — at mask [∅], where no invariant could be
     opened — [UF_same_class_eq] turns [same_class γ x y] into the
     equation [R x = R y], which is exactly what lets the inner commit's
     [⌜z = R y⌝] discharge the outer's [⌜z = R x⌝].

     On the way out the wrapper also keeps the private postcondition (it
     is persistent) and re-bases it from [y] to [x], which is free now
     that class facts compose definitionally. That is what [compress]
     needs, and it is why the call's postcondition carries it. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, Φ z ∗ in_uf γ z ∗ same_class γ x z)%I with "[AU]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" with "Hinv [] [AU]").
    { by iExists jy. }
    iAuIntro.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (D R V) "Hst".
    iDestruct (UF_same_class_eq with "Hst Hxy") as "[%Hxy' Hst]".
    iAaccIntro with "Hst".
    { (* Abort: nothing has happened, hand the state back. *)
      iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
    (* Commit: [z] is [y]'s representative, hence [x]'s. *)
    iIntros (z) "[-> Hst] !>".
    iRight. iExists (R y).
    iSplitL "Hst"; first by iFrame "Hst"; iPureIntro; symmetry.
    iIntros "H !>". iIntros "[#Hin #Hyz]".
    iDestruct (same_class_trans with "Hxy Hyz") as "#Hxz".
    iFrame "Hin Hxz". iApply "H". by iFrame "Hin Hxz". }
  iIntros (z) "(HΦ & #Hz & #Hxz)".

  (* [compress x z]: its precondition is [same_class γ x z], which is
     precisely what the call above re-based onto [x]. Compression returns
     [z] unchanged and reports nothing, so the result of the call is the
     result of the [find]. *)
  iDestruct "Hz" as (k) "#Hzv".
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold compress_spec.
  iSpecialize ("Hm" $! i k with "Hinv Hxv Hzv Hxz").
  iApply (imp_wand with "Hm").
  iIntros (w) "->".
  iExact "HΦ".
Qed.

(* And the same code against the observer specification. *)

Lemma findc_observe_proof γ η :
  in_env "find" (λ find, □ iSpec τ[elem] find (find_observe_spec γ)) η -∗
  in_env "compress"
    (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ)) η -∗
  EWP (eval η (EAnonFun __findc))
    {{ c, □ iSpec τ[elem] c (find_observe_spec γ) }}.
Proof.
  iIntros "#IFind #ICompress".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_observe_spec.
  iIntros "#Hinv #Hx".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.
  imp_match content with "[]".
  { iApply (read_vertex_lp _ x i _ True%I
              (λ _, in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv [] [] []"); last first.
    { imp_path. }
    { iNext. iIntros (c D R V) "_ %HRx _ _ _ Hst".
      iFrame "Hst".
      iSplitR; [by iExists i | iApply same_class_refl]. }
    done. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.
  { rewrite (@encode_encode' content).
    next_branch.
    imp_path. }
  iDestruct "Hc" as "[(_ & (%lp & #Hlocs) & #Hlk) _]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ 0%Z rc [lp]
            with "Hlocs []"); first done.
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk Hlocs []").
  iNext.
  iIntros (y jy Hjy) "#Hxy #Hy".
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iSpecialize ("Hm" with "Hinv []"); first by iExists jy.
    iApply (imp_wand with "Hm").
    iIntros (z) "[$ #Hyz]".
    iApply (same_class_trans with "Hxy Hyz"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (k) "#Hzv".
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold compress_spec.
  iSpecialize ("Hm" $! i k with "Hinv Hxv Hzv Hxz").
  iApply (imp_wand with "Hm").
  iIntros (w) "->".
  iFrame "Hxz". by iExists k.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [get]. *)

(* [get x] returns the value stored at [x]'s representative, retrying if
   the vertex it reached has been linked away in the meantime.

   The abstract claim is the sequential [get_spec]'s (UnionFind.v) with
   the state quantified atomically instead of owned throughout: the call
   returns [V (R x)], for the [R] and [V] of one instant during it.

   That instant is the read of the content cell that sees a [Root] — NOT
   the field access that follows and actually produces the value. Reading
   a field one step after the state has moved on would be indefensible for
   a mutable field; it is fine here because a [Root] record's payload is
   never written. The cell read fixes both which record the answer comes
   from and what that record holds ([content_val], against the state at
   that instant), and the payload's persistent points-to carries the
   second fact out of the open. Contrast [set], whose effect is not a read
   at all and which therefore has to linearize at its CAS.

   It is stated as a hook rather than as a triple, for the reason spelled
   out at [find_observe_spec]: [get] calls [findc] and then reads, so its
   own linearization point is the later read, and a caller holding a
   triple would have nothing to hand over at the traversal. *)

Definition get_hook (γ : uf_names) (x : elem) (Ψ : val → iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val),
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ (V (R x)).

(* Re-basing onto another member of the class, as [union_hook_rebase]
   does, and for the same reason: the retry runs on the vertex [findc]
   returned, and must still report the caller's value. Here it is one
   equation — the two vertices have the same representative, so the hook
   already reports the right thing. *)

Lemma get_hook_rebase γ x z Ψ :
  same_class γ x z -∗ get_hook γ x Ψ -∗ get_hook γ z Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  rewrite -Heq. iApply ("Hhook" with "Hst").
Qed.

Definition get_spec (γ : uf_names) (x : elem) (m : microvx) : iProp Σ :=
  ∀ (Ψ : val → iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    get_hook γ x Ψ -∗
    EWP m {{ Ψ }}.

(* The specification as a client sees it: the sequential [get_spec]'s
   postcondition verbatim. There is no private postcondition — a value is
   a value, and nothing about it expires. *)

Lemma get_atomic_spec γ x m :
  get_spec γ x m -∗
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ UF γ D R V | RET (V (R x)) }>>.
Proof.
  iIntros "Hspec #Hinv #Hx" (Φ) "AU".
  iApply ("Hspec" $! Φ with "Hinv Hx [AU]").
  (* The hook: the state the client's atomic update offers is the state at
     the linearization point, so this is where it is committed. *)
  iIntros (D R V) "Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iMod ("Hcommit" with "Hcl") as "HΦ".
  by iFrame "Hst HΦ".
Qed.

(* Proof outline:
   1. [let x = findc x]: run as a pure observer ([find_observe_spec]) —
      the traversal is not [get]'s linearization point, and the hook is
      untouched by it.
   2. Read the content cell through [read_vertex_lp], carrying the hook.
      On a [Root] the hook is run there and then, against the state that
      read exposes, and what comes back is the pair "[Ψ] of the value" and
      "that value is this record's payload".
   3. [Root root -> root.value] is then an ordinary persistent field read:
      it opens nothing, and produces exactly the value step 2 committed to.
   4. [Link _ -> get x] retries at the vertex reached, with the hook
      re-based onto it ([get_hook_rebase]). *)

Lemma get_proof γ η :
  ▷ in_env "get" (λ get, □ iSpec τ[elem] get (get_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_observe_spec γ)) η -∗
  EWP (eval η (EAnonFun (AnonFun "x"
        (ELet [Binding (PVar "x") (EApp (EPath ["findc"]) (EPath ["x"]))]
              __get_exp))))
    {{ c, □ iSpec τ[elem] c (get_spec γ) }}.
Proof.
  iIntros "#IGet #IFindc".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold get_spec.
  iIntros (Ψ) "#Hinv #Hx Hhook".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call — the traversal is not
     [get]'s linearization point, so it gets the trivial hook and [get]
     keeps its own. All it reports is where it landed. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" with "Hinv Hx"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".

  (* From here on everything is stated at [z], so the hook moves there
     once and for all. *)
  iDestruct (get_hook_rebase with "Hxz Hhook") as "Hhook".

  (* [match x.content with ...]: the scrutinee read carries the hook. On a
     [Root] it is run there and then, and what it leaves behind is [Ψ] of
     the value together with the persistent evidence that this record
     holds it — which is what the branch below goes on to read. *)
  imp_match content with "[Hhook]".
  { iApply (read_vertex_lp _ z j _ _
              (λ c : content, match c with
                              | CtRoot rc => ∃ v : val, root_val rc v ∗ Ψ v
                              | CtLink _ => False
                              end)%I
              with "Hinv Hzv Hhook [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "%Hroot %HRz _ #Hval Hhook Hst".
    destruct c as [rc|rc]; last discriminate.
    iMod ("Hhook" $! D R V with "Hst") as "[Hst HΨ]".
    (* [z] is its own representative in the state just committed, so the
       value that state assigns to it is the payload of this record. *)
    rewrite HRz. iFrame "Hst".
    iExists (V z). by iFrame "Hval HΨ". }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root root -> root.value]: an ordinary field read against the
       payload's persistent points-to. It opens nothing, and the value it
       produces is the one already committed to. *)
    rewrite (@encode_encode' content).
    next_branch.
    iDestruct "Hc" as (v) "[#Hrv HΨ]".
    iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
    iApply (imp_ERecordAccess_pers 0%Z rc [lv] _ v with "Hrclocs [] [] [HΨ]").
    { by vm_compute. }
    { imp_path. }
    { iExact "Hlv". }
    { iIntros "!> _". iExact "HΨ". } }

  (* [Link _ -> get x]: [z] was linked away between [findc] and the read,
     so nothing was linearized; retry from [z], with the hook handed back
     untouched — and already stated at [z]. *)
  iDestruct "Hc" as "[_ Hhook]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem].
  iIntros "Hm".
  iApply ("Hm" $! Ψ with "Hinv [] Hhook").
  by iExists j.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [set]. *)

(* [set x v] writes [v] as the value of [x]'s equivalence class.

   Abstractly that is [update_class]: the whole class takes the new value
   at once. It has to be the whole class rather than the representative
   alone, because the abstract state has no notion of "where the value is
   stored" — [V] is a function on all of [D], constrained by
   [V u = V (R u)] — and because a later [union] may make some other
   vertex the representative without anything being written.

   [set] does not write the payload field: it allocates a fresh
   [Root { value = v }] and CASes the whole content cell, retrying if it
   loses. This is what makes payloads immutable, which is what lets [get]
   read one outside the invariant. The linearization point is the
   successful CAS.

   The code is two functions: an internal, two-argument recursive helper
   that consumes the freshly allocated record, and a one-argument wrapper
   that allocates it. [fresh_root cx' v] (defined at [make]) is what the
   helper's caller supplies, and, on the retry path, what a failed CAS
   gives back. *)

Definition set_hook (γ : uf_names) (x : elem) (v : val)
    (Ψ : iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val),
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V.[x -/R/> v] ∗ Ψ.

(* Re-basing, for the retry, as in [get]. Here it is [update_class]'s own
   congruence that does the work: naming a class by one member or another
   is literally the same function. *)

Lemma set_hook_rebase γ x z v Ψ :
  same_class γ x z -∗ set_hook γ x v Ψ -∗ set_hook γ z v Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  rewrite -(update_class_congr_class R x z V v Heq).
  iApply ("Hhook" with "Hst").
Qed.

Definition set_content_spec (γ : uf_names) (x : elem) (cx' : content)
    (m : microvx) : iProp Σ :=
  ∀ (v : val) (Ψ : iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    fresh_root cx' v -∗
    set_hook γ x v Ψ -∗
    EWP m {{ (_ : unit), Ψ }}.

Definition set_spec (γ : uf_names) (x : elem) (v : val)
    (m : microvx) : iProp Σ :=
  ∀ (Ψ : iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    set_hook γ x v Ψ -∗
    EWP m {{ (_ : unit), Ψ }}.

(* The specification as a client sees it. *)

Lemma set_atomic_spec γ x v m :
  set_spec γ x v m -∗
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ UF γ D R V.[x -/R/> v] | RET tt }>>.
Proof.
  iIntros "Hspec #Hinv #Hx" (Φ) "AU".
  iApply (imp_wand _ _ _ _ (λ _ : unit, Φ tt)%I _ with "[Hspec AU]"); last first.
  { iIntros ([]) "H". iExact "H". }
  iApply ("Hspec" $! (Φ tt) with "Hinv Hx [AU]").
  (* The hook: here both halves of the abstract state move together. *)
  iIntros (D R V) "Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iMod (UF_update_2 _ _ _ _ D R V.[x -/R/> v]
          with "Hst Hcl") as "[Hst Hcl]";
    [done | by apply uf_val_congr_set |].
  iMod ("Hcommit" with "Hcl") as "HΦ".
  by iFrame "Hst HΦ".
Qed.

(* Proof outline (the internal helper):
   1. [let x = findc x]: an observer call, as in [get].
   2. [let cx = x.content]: an ordinary atomic read, NOT a linearization
      point — all it produces is the value the CAS will compare against,
      and [content_info]'s persistent [root_val] for it, which is what
      makes the CAS's ABA argument go through.
   3. [Root _ -> if cas x.content cx cx' ...]: the CAS, carried by
      [uf_cas_set_fupd]. On success the hook is run against the state at
      that instant; on failure the hook AND the fresh record come back and
      the call retries on the vertex [findc] found.
   4. [_ -> set x cx']: the cell raced ahead; retry likewise.

   As in [get], the hook is moved onto that vertex once, at step 1. *)

Lemma set_proof γ η :
  ▷ in_env "set"
      (λ set, □ iSpec τ[elem; content] set (set_content_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_observe_spec γ)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  EWP (eval η (EAnonFun (AnonFun "x" (EAnonFun __set_fun))))
    {{ c, □ iSpec τ[elem; content] c (set_content_spec γ) }}.
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x cx' v Ψ).
  iIntros "#Hinv #Hx Hcx' Hhook".
  (* The caller's record is a [Root]: that is what [fresh_root] says. *)
  destruct cx' as [rcn|rcn]; last by iDestruct "Hcx'" as "[]".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call, as in [get]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" with "Hinv Hx"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".
  iDestruct (set_hook_rebase with "Hxz Hhook") as "Hhook".

  (* [let cx = x.content in ...]: an ordinary read, and not a
     linearization point — all it produces is the value the CAS will
     compare against, together with the persistent [root_val] that makes
     the CAS's ABA argument go through. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γ z c)%I).
  { iApply (read_vertex with "Hinv Hzv"). imp_path. }
  iIntros (cx) "#Hcx".

  (* Re-match on the already-loaded [cx]: a plain path lookup. *)
  imp_match content with "[]".
  destruct cx as [rc|rc]; simpl.

  { (* [Root _ -> if cas x.content cx cx' then () else set x cx']. *)
    iDestruct "Hcx" as "(#HrcP & (%vexp & #Hrv))".
    rewrite (@encode_encode' content).
    next_branch.

    imp_if with "[Hcx' Hhook]".
    { set_postcondition (λ res : bool,
        if res then Ψ else set_hook γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I.
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hzv"). imp_path. }
      { set_postcondition (λ c : content, ⌜c = CtRoot rc⌝)%I.
        iApply (imp_EPath (A:=content) (CtRoot rc)); first reflexivity.
        done. }
      iIntros "-> Hptr Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_set_fupd _ z j _ rc rcn vexp v (set_hook γ z v Ψ) Ψ
                (λ res : bool,
                   if res then Ψ
                   else set_hook γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I
                with "Hinv Hzv Hptr Hrv Hcx' Hhook [] []").
      { (* Both hooks speak of [z]'s class, so this is a hand-over: the
           CAS's own report is already the client's. *)
        iNext. iIntros (D R V) "%Hax %Hval Hhook Hst".
        iMod ("Hhook" $! D R V with "Hst") as "[Hst HΨ]".
        by iFrame "Hst HΨ". }
      { iNext. iIntros ([|]) "H"; iExact "H". } }

    { (* CAS succeeded: the hook has already produced the postcondition. *)
      iIntros "HΨ". iApply imp_EUnit. iExact "HΨ". }
    { (* CAS failed: retry on the vertex [findc] found, with the hook and
         the fresh record handed back. *)
      iIntros "[Hhook Hcx']".
      imp_app τ[elem; content].
      iIntros "Hm".
      iApply ("Hm" $! v Ψ with "Hinv [] Hcx' Hhook").
      by iExists j. } }

  (* [_ -> set x cx']: the cell raced ahead of us; retry likewise. *)
  rewrite {2}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; content].
  iIntros "Hm".
  iApply ("Hm" $! v Ψ with "Hinv [] Hcx' Hhook").
  by iExists j.
Qed.

(* The public, one-argument [set x v]: allocates the fresh
   [Root { value = v }] and calls the helper above. It has nothing of its
   own to say about the abstract state, so it simply passes the hook on. *)

Lemma set_wrapper_proof γ η :
  in_env "set"
    (λ setv, □ iSpec τ[elem; content] setv (set_content_spec γ)) η -∗
  EWP (eval η (EAnonFun __set))
    {{ c, □ iSpec τ[elem; val] c (set_spec γ) }}.
Proof.
  iIntros "#ISet".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x v Ψ).
  iIntros "#Hinv #Hx Hhook".
  iApply imp_please; iNext.

  (* [let cx' = Root { value = v } in set x cx']. [A] is pinned explicitly
     ([root_fields]): both it and [link_fields] are single-field
     [RecordRepr] instances, so bare [imp_record] cannot disambiguate. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, fresh_root c v)%I).
  { imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (cx') "Hco".
  imp_app τ[elem; content].
  iIntros "Hm".
  iApply ("Hm" $! v Ψ with "Hinv Hx Hco Hhook").
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [union]. *)

(* [union x y] merges the two classes and returns the value that was
   stored at the root it absorbed — or [None] if there was nothing to do.

   The abstract transition mirrors the sequential [union_spec]
   (UnionFind.v), which redirects both classes to a common root and
   reports [⌜z = R x ∨ z = R y⌝]. Here the direction is likewise not the
   client's to choose: the implementation links whichever root has the
   LARGER identifier to the other, and identifiers are random. So the
   postcondition existentially quantifies which way round it went — [b]'s
   class absorbed into [c]'s — and says only that it is one of the two.
   The returned value is [V b], the absorbed class's, which is the one
   that stops being reachable through [V].

   Both halves of the transition are [update_class]: [b]'s class takes
   [c]'s representative, and [c]'s value. Note that it is stated at [b]
   and [c] themselves rather than at their representatives — a class may
   be named by any of its members, and only this naming is usable by a
   client, who cannot collapse the [R (R x)] that the other would leave. *)

Definition union_post (γ : uf_names) (D : gset elem) (R : elem → elem)
    (V : elem → val) (x y : elem) (o : option val) : iProp Σ :=
  match o with
  | None => ⌜R x = R y⌝ ∗ UF γ D R V
  | Some v =>
      ∃ b c : elem,
        ⌜(b = x ∧ c = y) ∨ (b = y ∧ c = x)⌝ ∗
        ⌜R x ≠ R y⌝ ∗ ⌜v = V b⌝ ∗
        UF γ D R.[b -/R/> R c] V.[b -/R/> V c]
  end.

(* As with [find], the composable form states the linearization point as a
   hook — here a pair of them, one per outcome, of which the
   implementation uses exactly one. Unlike [find] it cannot be replaced by
   the atomic triple: [union] spends its update at a CAS several steps
   after its traversals, and a caller holding a triple would have nothing
   to hand over at the traversal. *)

Definition union_hook (γ : uf_names) (x y : elem)
    (Ψ : option val → iProp Σ) : iProp Σ :=
  (* nothing to do: the two are already in one class *)
  (∀ D (R : elem → elem) (V : elem → val), ⌜R x = R y⌝ -∗
     UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ None)
  ∧
  (* the merge *)
  (∀ D (R : elem → elem) (V : elem → val) b c,
     ⌜(b = x ∧ c = y) ∨ (b = y ∧ c = x)⌝ -∗ ⌜R x ≠ R y⌝ -∗
     UF γ D R V ={⊤ ∖ ↑ufN}=∗
     UF γ D R.[b -/R/> R c] V.[b -/R/> V c] ∗
     same_class γ b c ∗ Ψ (Some (V b))).

Definition union_spec (γ : uf_names) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ (Ψ : option val → iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗ in_uf γ y -∗
    union_hook γ x y Ψ -∗
    EWP m {{ Ψ }}.

(* Re-basing a hook onto other members of the same two classes. This is
   what [union]'s retry needs: after a lost CAS the call restarts on the
   vertices its traversals reached, and the hook it is carrying speaks of
   the original arguments.

   It is a pure elimination — no fupd, no invariant open — because both
   facts it rests on come out of the [UF] the hook is handed:
   [UF_same_class_eq] turns the class facts into [R x = R a] and
   [R y = R b], and [UF_val_congr] turns those into [V x = V a] and
   [V y = V b]. Together they say the two transitions are literally the
   same functions ([update_class_congr_class]) and the same reported
   value. *)

Lemma union_hook_rebase γ x y a b Ψ :
  same_class γ x a -∗ same_class γ y b -∗
  union_hook γ x y Ψ -∗ union_hook γ a b Ψ.
Proof.
  iIntros "#Hxa #Hyb Hhook".
  iSplit.
  - iIntros (D R V) "%Hab Hst".
    iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hx Hst]".
    iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Hy Hst]".
    iDestruct "Hhook" as "[Hnone _]".
    iApply ("Hnone" with "[%] Hst"). congruence.
  - iIntros (D R V b' c') "%Hdir %Hne Hst".
    iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hx Hst]".
    iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Hy Hst]".
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iDestruct "Hhook" as "[_ Hsome]".
    (* The two directions are mirror images; in each, the hook is run at
       the original pair and the goal rewritten back onto it. *)
    assert (Hne' : R x ≠ R y) by congruence.
    destruct Hdir as [[-> ->] | [-> ->]].
    + rewrite -(update_class_congr_class R x a R (R b) Hx).
      rewrite -(update_class_congr_class R x a V (V b) Hx).
      rewrite -Hy -(Hcongr y b Hy) -(Hcongr x a Hx).
      iMod ("Hsome" $! D R V x y with "[%] [%] Hst") as "(Hst & #Hxy & HΨ)";
        [by left | done |].
      iModIntro. iFrame "Hst HΨ".
      iDestruct (same_class_sym with "Hxa") as "#Hax".
      iDestruct (same_class_trans with "Hax Hxy") as "#Hay".
      iApply (same_class_trans with "Hay Hyb").
    + rewrite -(update_class_congr_class R y b R (R a) Hy).
      rewrite -(update_class_congr_class R y b V (V a) Hy).
      rewrite -Hx -(Hcongr x a Hx) -(Hcongr y b Hy).
      iMod ("Hsome" $! D R V y x with "[%] [%] Hst") as "(Hst & #Hyx & HΨ)";
        [by right | done |].
      iModIntro. iFrame "Hst HΨ".
      iDestruct (same_class_sym with "Hyb") as "#Hby".
      iDestruct (same_class_trans with "Hby Hyx") as "#Hbx".
      iApply (same_class_trans with "Hbx Hxa").
Qed.

(* The specification as a client sees it. *)

Lemma union_atomic_spec γ x y m :
  union_spec γ x y m -∗
  is_uf γ -∗
  in_uf γ x -∗ in_uf γ y -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ o : option val, union_post γ D R V x y o | RET o }>>.
Proof.
  iIntros "Hspec #Hinv #Hx #Hy" (Φ) "AU".
  iApply ("Hspec" $! Φ with "Hinv Hx Hy").
  iSplit.
  - (* [None]: the state does not move, so the atomic update is committed
       with the state it was offered. *)
    iIntros (D R V) "%Heq Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iMod ("Hcommit" $! None with "[$Hcl]") as "HΦ"; first done.
    by iFrame "Hst HΦ".
  - (* [Some]: both halves move together — and this is the one instant at
       which they are both in hand, so it is where the new equivalence is
       recorded. *)
    iIntros (D R V b c) "%Hdir %Hne Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iMod (UF_update_2 _ _ _ _ D R.[b -/R/> R c] V.[b -/R/> V c]
            with "Hst Hcl") as "[Hst Hcl]".
    { intros u w. apply update_class_R_congr. }
    { by apply uf_val_congr_link. }
    iMod (UF_same_class_update _ _ _ _ b c with "Hst Hcl")
      as "(Hst & Hcl & #Hbc)".
    { rewrite /update_class /fcupdate; repeat case_decide; done. }
    iMod ("Hcommit" $! (Some (V b)) with "[Hcl]") as "HΦ".
    { iExists b, c. by iFrame "Hcl". }
    by iFrame "Hst Hbc HΦ".
Qed.

(* Proof outline:
   1. [let x = findc x and y = findc y]: both traversals are run as pure
      observers ([find_observe_spec]) — neither is a linearization point
      for [union], which spends its own hook later.
   2. [if x == y then None]: the two arguments have been chased to one
      vertex, so they are equivalent, permanently. There is no physical
      step left at which to say so, and none is needed: an invariant open
      with no step in it is an instant like any other
      ([uf_same_class_commit]).
   3. Otherwise the two identifiers are compared, and the branch links the
      root with the LARGER identifier to the other vertex. The two
      branches are mirror images; each reads its vertex's content, matches
      a [Root] (a [Link] means the race was lost — retry), reads the
      payload out of the record with an ordinary persistent field read,
      allocates [Link { parent = ... }] and CASes it in.
   4. The CAS is the linearization point, and [uf_cas_link_fupd] carries
      it: on success it runs the hook against the state at that instant;
      on failure it hands the hook and the fresh record straight back, and
      the call retries on the vertices [findc] found.

   The hook is re-based onto those vertices once, at step 1, by
   [union_hook_rebase]; everything after that is stated at [a] and [b]
   alone. *)

Lemma union_proof γ η :
  ▷ in_env "union"
      (λ union, □ iSpec τ[elem; elem] union (union_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_observe_spec γ)) η -∗
  in_env "cas"
    (λ cas, □ ∀ `(Encode A), iSpec τ[loc; A; A] cas compare_and_set_spec) η -∗
  EWP (eval η (EAnonFun (AnonFun "x" (EAnonFun __union_fun))))
    {{ c, □ iSpec τ[elem; elem] c (union_spec γ) }}.
Proof.
  iIntros "#IUnion #IFindc #Hcas".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold union_spec.
  iIntros (Ψ) "#Hinv #Hx #Hy Hhook".
  iApply imp_please; iNext.

  (* [let x = findc x and y = findc y in ...] *)
  imp_let $! (λ z : elem, in_uf γ z ∗ same_class γ x z)%I
          $! (λ z : elem, in_uf γ z ∗ same_class γ y z)%I.
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" with "Hinv Hx"). }
  { imp_app τ[elem].
    iIntros "Hm".
    iApply ("Hm" with "Hinv Hy"). }
  iIntros (a b) "[#Ha #Hxa] [#Hb #Hyb]".
  iDestruct "Ha" as (i') "#Hav".
  iDestruct "Hb" as (j') "#Hbv".

  (* Re-base the hook onto the vertices the traversals reached. From here
     on the original [x] and [y] play no part: the retries pass [Hhook]
     along unchanged. *)
  iDestruct (union_hook_rebase with "Hxa Hyb Hhook") as "Hhook".
  iDestruct (vertex_mut with "Hav") as "#HaP".
  iDestruct (vertex_mut with "Hbv") as "#HbP".

  (* [if x == y then None else ...]: physical equality on two non-inline
     records, which needs at least one operand to be a mutable block —
     supplied by [vertex_mut]. *)
  imp_if.
  { set_postcondition
    (λ res : bool, if res then ⌜a = b⌝ else ⌜a ≠ b⌝)%I.
    iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I
                                       (λ l : record, ⌜l = b⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec a b) as [->|Hneq]. } }

  { (* [a = b]: both traversals landed on one vertex, so the two arguments
       were already equivalent and nothing needs to happen. *)
    iIntros "->".
    iDestruct "Hhook" as "[Hnone _]".
    iMod (uf_same_class_commit with "Hinv [] [] Hnone") as "HΨ";
      [iApply same_class_refl | iApply same_class_refl |].
    iApply (imp_wand with "[]").
    { imp_constant. }
    iIntros (v) "->". simpl. iExact "HΨ". }

  iIntros "%Heq".
  (* [assert (x.id <> y.id)]: discharged from the identifier registry,
     through [vertex_ids_ne]. *)
  iMod (vertex_ids_ne with "Hinv Hav Hbv") as %(Hij & Hrepi & Hrepj);
    first exact Heq.

  imp_match unit with "[]".
  { iApply (imp_EAssert (R:=⌜i' ≠ j'⌝%I)).
    iSplit; first done.
    iApply (imp_EOpNe (A1:=Z) (A2:=Z)).
    { set_postcondition (λ n, ⌜n=i'⌝)%I.
      iApply (read_vertex_id with "Hav"). imp_path. }
    { set_postcondition (λ n, ⌜n=j'⌝)%I.
      iApply (read_vertex_id with "Hbv"). imp_path. }
    { iIntros "!>" (v1 v2) "-> ->".
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
    { iApply (read_vertex_id with "Hbv"). imp_path. } }

  { iIntros "%Hcmp2".
    assert (Hlt : (j' < i')%Z).
    { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γ a c)%I).
    { iApply (read_vertex with "Hinv Hav"). imp_path. }
    iIntros (cx) "#Hcx".

    imp_match content with "[]".
    destruct cx as [rc|rc]; simpl.

    { (* [Root {v} -> if cas x.content cx (Link {parent = y}) ...] *)
      iDestruct "Hcx" as "(#HrcP & (%v & #Hrv))".
      rewrite (@encode_encode' content).
      next_branch.

      (* Read the absorbed root's payload. Its field is immutable and the
         invariant has discarded its fraction, so this opens nothing. *)
      iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc [lv] _ v with "Hrclocs Hlv [Hhook]");
        first done.
      iNext. iIntros "_".

      imp_if with "[Hhook]".
      { set_postcondition
          (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)%I.
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hav"). imp_path. }
        { set_postcondition (λ c : content, ⌜c = CtRoot rc⌝)%I.
          iApply (imp_EPath (A:=content) (CtRoot rc)); first reflexivity.
          done. }
        { set_postcondition
            (λ c : content, ∃ rcn, ⌜c = CtLink rcn⌝ ∗
                                   rcn ⤇ {| link_parent := b |})%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists r'. iSplit; first done. iApply "Hown". }
        iIntros "-> Hptr (%rcn & -> & Hrcn) Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_link_fupd _ a b i' j' _ rc rcn v
                  (union_hook γ a b Ψ) (Ψ (Some v))
                  (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)
                  with "Hinv Hav Hptr [] Hbv Hrcn Hhook [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* Hook and CAS now speak of the same two vertices, so this is a
             hand-over with nothing to re-index. *)
          iNext. iIntros (D R V) "%Hax %Hne %Hval Hhook Hst".
          iDestruct "Hhook" as "[_ Hsome]".
          iMod ("Hsome" $! D R V a b with "[%] [%] Hst") as "($ & #Hab & HΨ)".
          { by left. }
          { done. }
          iFrame "Hab". rewrite Hval. by iModIntro. }
        { iNext. iIntros ([|]) "H"; [iExact "H" | by iDestruct "H" as "[$ _]"]. } }

      { iIntros "HΨ".
        (* CAS succeeded: the hook has already produced the whole
           postcondition, for the value the [Root] record held. *)
        imp_data.
        2: { iIntros (w) "H". iExact "H". }
        iExact "HΨ". }
      { iIntros "Hhook".
        (* CAS failed: retry on the vertices [findc] found — which is what
           the hook is already stated at. *)
        imp_app τ[elem; elem].
        iIntros "Hm3".
        iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
        { by iExists i'. }
        { by iExists j'. } } }

    { (* [_ -> union x y]: the cell raced ahead of us. *)
      rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
      { by iExists i'. }
      { by iExists j'. } } }

  { (* [x.id <= y.id]: the mirror image. *)
    iIntros "%Hcmp2".
    assert (Hlt : (i' < j')%Z).
    { pose proof (Zgt_cases i' j') as Hgt. rewrite <- Hcmp2 in Hgt. lia. }
    iApply (imp_ELet_var (B:=content) (λ c : content, content_info γ b c)%I).
    { iApply (read_vertex with "Hinv Hbv"). imp_path. }
    iIntros (cy) "#Hcy".

    imp_match content with "[]".
    destruct cy as [rc|rc]; simpl.

    { iDestruct "Hcy" as "(#HrcP & (%v & #Hrv))".
      rewrite (@encode_encode' content).
      next_branch.

      iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc [lv] _ v with "Hrclocs Hlv [Hhook]");
        first done.
      iNext. iIntros "_".

      imp_if with "[Hhook]".
      { set_postcondition
          (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)%I.
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hbv"). imp_path. }
        { set_postcondition (λ c : content, ⌜c = CtRoot rc⌝)%I.
          iApply (imp_EPath (A:=content) (CtRoot rc)); first reflexivity.
          done. }
        { set_postcondition
            (λ c : content, ∃ rcn, ⌜c = CtLink rcn⌝ ∗
                                   rcn ⤇ {| link_parent := a |})%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists r'. iSplit; first done. iApply "Hown". }
        iIntros "-> Hptr (%rcn & -> & Hrcn) Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_link_fupd _ b a j' i' _ rc rcn v
                  (union_hook γ a b Ψ) (Ψ (Some v))
                  (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)
                  with "Hinv Hbv Hptr [] Hav Hrcn Hhook [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* The mirror image: here it is [b]'s class that is absorbed. *)
          iNext. iIntros (D R V) "%Hby %Hne %Hval Hhook Hst".
          iDestruct "Hhook" as "[_ Hsome]".
          iMod ("Hsome" $! D R V b a with "[%] [%] Hst") as "($ & #Hba & HΨ)".
          { by right. }
          { by intros ?. }
          iFrame "Hba". rewrite Hval. by iModIntro. }
        { iNext. iIntros ([|]) "H"; [iExact "H" | by iDestruct "H" as "[$ _]"]. } }

      { iIntros "HΨ".
        imp_data.
        2: { iIntros (w) "H". iExact "H". }
        iExact "HΨ". }
      { iIntros "Hhook".
        imp_app τ[elem; elem].
        iIntros "Hm3".
        iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
        { by iExists i'. }
        { by iExists j'. } } }

    { rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
      { by iExists i'. }
      { by iExists j'. } } }
Qed.

(* ======================================================================== *)
(* TODO (abstract state): everything below is the previous, non-atomic
   development, parked while the specifications are reworked one operation
   at a time. What is left is [eq], which has to be re-specified
   atomically against the same [UF γ D R V] as the rest:

     eq — RET [bool_decide (R x = R y)].

   It linearizes at a single step the invariant file already isolates
   ([uf_find_content_acc], a read). Note where that step is NOT: not at
   the [findc] call it opens with. Like [get], [set], [update] and
   [union] it calls that as an observer ([find_observe_spec]), which
   yields the two facts it needs about the vertex it got back ([in_uf]
   and [same_class]).

   [eq] is two observer traversals and a physical equality test, whose
   linearization point is the second traversal's — and see
   [[cuf-eq-false-case]]: only the sound half is provable through this
   API, which is a design decision, argued below, rather than unfinished
   work.

   Read the body below for its EWP-level structure, not for its ghost
   steps: those are several refactors out of date (the abstract graph is
   gone, [reaches] is now [same_class], and the content registry has been
   replaced by persistent [Root] payloads plus [linked]). Concretely,
   every [content_own]/[cinfo]/[↪[γl]□ CRoot _] below has no counterpart
   any more — a value read is now justified by [root_val]'s persistent
   points-to, and values are reported through [V] instead of through
   registration receipts. *)
(* ======================================================================== *)

(*
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

Definition eq_spec (γ γl γn γe : gname) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ i j,
    is_uf γ γl γn γe -∗
    vertex γ x i -∗
    vertex γ y j -∗
    EWP m {{ (b : bool), if b then same_class γ x y else True }}.

(* The internal, recursive [eq]. Since the two mutually recursive
   functions were merged into one, both [findc] calls happen at the top
   of every iteration rather than only on the retry path. *)

Lemma eq_proof γ γl γn γe η :
  ▷ in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ γl γn γe)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (findc_spec γ γl γn γe)) η -∗
  EWP (eval η (EAnonFun (AnonFun "x" (EAnonFun __eq_fun))))
    {{ c, □ iSpec τ[elem; elem] c (eq_spec γ γl γn γe) }}.
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

Lemma eq_wrapper_proof γ γl γn γe η :
  in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ γl γn γe)) η -∗
  EWP (eval η (EAnonFun __eq)) {{ c, □ iSpec τ[elem; elem] c (eq_spec γ γl γn γe) }}.
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
*)

End ConcurrentUnionFind.
