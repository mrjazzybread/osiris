From iris.base_logic Require Export iprop.
From iris.base_logic Require Import own.
From iris.proofmode Require Import ltac_tactics.

From osiris.adequacy.satisfiable Require Import satisfiable_global satisfiable_standard.

(** *** The Satisfiable Predicate *)
(**
  In standard Iris, there are two possible definitions for the satisfiable predicate:

  - [sat_global], which allows for global resources to be allocated with [sat_global_alloc_res].
    This definition does not allow for hoisting out disjunctions (not even classically).

  - [sat_standard], which allows hoising out disjunctions (classically).
    This definition, however, does not allow for global resources (e.g., later credits, invariants, ...) to be allocated.

  Apart from resource allocation and disjunction, both definitions have the same properties
  (see [satisfiable_global.v] and [satisfiable_standard.v]).

  In this file, we define a new satisfiable predicate [sat] which combines these two definitions.
  With it, we obtain the best of both worlds (resource allocation and disjunction hoisting).
  The way it works is that we divide adequacy proofs into two phases, [Alloc] and [Running].
  In the [Alloc] phase, [sat] acts as [sat_global], allowing for global resource allocation.
  In the [Running] phase, [sat] acts as [sat_standard], allowing for disjunction hoisting.
  Concretely, an adequacy proof should look as follows:

  1. Phase: [Alloc]
    - Start with [sat Alloc True] (obtained from [sat_intro]).
    - Allocate all global resources (using [sat_alloc_res]).
    - Apply, at will, [sat_mono], [sat_upd], and [sat_later].
    - Finally, transition to the [Running] phase (using [sat_end_alloc]).

  2. Phase: [Running]
    - Execute the weakest precondition or whatever definition you want to prove adequacy of.
    - Apply, at will, [sat_mono], [sat_upd], and [sat_later].
    - Apply [sat_or] for disjunctions if you are comfortable with using classical logic.
    - Finally, extract pure results using [sat_elim].
*)

Inductive sat_mode := Alloc | Running.

Definition sat_def {Σ: gFunctors} (m: sat_mode) (P: iProp Σ) : Prop :=
  match m with
  | Alloc => sat_global P
  | Running => sat_standard P
  end.
Definition sat_aux : seal (@sat_def). by eexists. Qed.
Definition sat := sat_aux.(unseal).
Global Arguments sat {Σ} _ _%_I.
Definition sat_eq : @sat = @sat_def := sat_aux.(seal_eq).
Global Instance: Params (@sat) 2 := {}.



Section satisfiable_properties.
  Context {Σ: gFunctors}.

  (* NOTE: This lemma would also hold for the [Running] mode,
     but the lemma [sat_end_alloc] can always be used to transition
     from [Alloc] to [Running] mode. *)
  Lemma sat_intro: sat (Σ := Σ) Alloc True.
  Proof.
    rewrite sat_eq /sat_def. eapply sat_global_intro.
  Qed.

  (* NOTE: The allocation rule can only be used in the [Alloc] phase. *)
  Lemma sat_alloc_res {A: cmra} `{!inG Σ A} (a: A) P:
    ✓ a → sat Alloc P → ∃ γ, sat Alloc (own γ a ∗ P).
  Proof.
    rewrite sat_eq /sat_def. eapply sat_global_alloc_res.
  Qed.

  Lemma sat_end_alloc (P: iProp Σ) : sat Alloc P → sat Running P.
  Proof.
    rewrite sat_eq /sat_def. eapply sat_global_sat.
  Qed.

  Lemma sat_mono m (P Q: iProp Σ) : (P ⊢ Q) → sat m P → sat m Q.
  Proof.
    rewrite sat_eq /sat_def.
    destruct m; [eapply sat_global_mono|eapply sat_standard_mono].
  Qed.

  Lemma sat_upd m (P: iProp Σ) : sat m (|==> P) → sat m P.
  Proof.
    rewrite sat_eq /sat_def.
    destruct m; [eapply sat_global_upd|eapply sat_standard_upd].
  Qed.

  Lemma sat_later m (P: iProp Σ) : sat m (▷ P) → sat m P.
  Proof.
    rewrite sat_eq /sat_def.
    destruct m; [eapply sat_global_later|eapply sat_standard_later].
  Qed.

  (* NOTE: The disjunction rule can only be used in the [Running] phase. *)
  Lemma sat_or (P Q: iProp Σ) :
    (∀ P, P ∨ ¬ P) →
    sat Running (P ∨ Q) → sat Running P ∨ sat Running Q.
  Proof.
    rewrite sat_eq /sat_def. eapply sat_standard_or.
  Qed.

  (* NOTE: This lemma would also hold for the [Running] mode,
     but the lemma [sat_end_alloc] can always be used to transition
     from [Alloc] to [Running] mode. *)
  Lemma sat_elim m (φ: Prop): sat (Σ := Σ) m ⌜φ⌝ → φ.
  Proof.
    rewrite sat_eq /sat_def. destruct m; [eapply sat_global_elim|eapply sat_standard_elim].
  Qed.


  (* Derived Properties *)
  Global Instance sat_proper m : Proper ((≡) ==> (≡)) (sat (Σ := Σ) m).
  Proof.
    intros P Q HPQ. split; eapply sat_mono; rewrite HPQ //.
  Qed.

  Global Instance sat_proper_ent m : Proper ((⊢) ==> impl) (sat (Σ := Σ) m).
  Proof.
    intros P Q HPQ. rewrite /impl. by eapply sat_mono.
  Qed.

  Global Instance sat_proper_flip_ent m : Proper (flip (⊢) ==> flip impl) (sat (Σ := Σ) m).
  Proof.
    intros P Q HPQ. rewrite /flip /impl. by eapply sat_mono.
  Qed.

End satisfiable_properties.




(** *** Satisfiable which bakes in a frame and a list of resources. *)

Definition SAT_def {Σ: gFunctors} (m: sat_mode) (F: iProp Σ) (Rs: list (iProp Σ)) (P: iProp Σ) : Prop := sat m (F ∗ ([∗] Rs) ∗ P).
Definition SAT_aux : seal (@SAT_def). by eexists. Qed.
Definition SAT := SAT_aux.(unseal).
Global Arguments SAT {Σ} _ _%_I _%_I _%_I.
Definition SAT_eq : @SAT = @SAT_def := SAT_aux.(seal_eq).
Global Instance: Params (@SAT) 2 := {}.

(* type class for searching for resources in the resource list *)
Class find_resource {Σ: gFunctors} (Rs: list (iProp Σ)) (P: iProp Σ) (Rs': list (iProp Σ)) : Prop :=
  find_resource_iff: ([∗] Rs) ⊣⊢ P ∗ ([∗] Rs').
Global Arguments find_resource {_} _%_I _%_I _%_I.
Global Hint Mode find_resource + + ! - : typeclass_instances.


Section satisfiable_frame_properties.
  Context {Σ: gFunctors}.

  Lemma SAT_intro : SAT (Σ:=Σ) Alloc True [] True.
  Proof.
    rewrite SAT_eq /SAT_def.
    eapply sat_mono, sat_intro.
    simpl; by iIntros "_".
  Qed.

  Lemma SAT_mono m F Rs (P Q: iProp Σ):
    (P ⊢ Q) → SAT m F Rs P → SAT m F Rs Q.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hent Hsat. eapply sat_mono, Hsat.
    iIntros "($ & $ & P)". by iApply Hent.
  Qed.

  Lemma SAT_elim m F Rs (φ: Prop):
    SAT (Σ := Σ) m F Rs ⌜φ⌝ → φ.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hsat. eapply sat_elim, sat_mono, Hsat.
    iIntros "(_ & _ & $)".
  Qed.

  Lemma SAT_end_alloc F Rs (P: iProp Σ) : SAT Alloc F Rs P → SAT Running F Rs P.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hsat. eapply sat_end_alloc, sat_mono, Hsat.
    iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_upd m F Rs (P: iProp Σ):
    SAT m F Rs (|==> P) → SAT m F Rs P.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hsat. eapply sat_upd, sat_mono, Hsat.
    iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_later m F Rs (P: iProp Σ):
    SAT m F Rs (▷ P) → SAT m F Rs P.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hsat. eapply sat_later, sat_mono, Hsat.
    iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_or F Rs (P Q: iProp Σ):
    (∀ P, P ∨ ¬ P) →
    SAT Running F Rs (P ∨ Q) → SAT Running F Rs P ∨ SAT Running F Rs Q.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros xm Hsat. eapply sat_or; first apply xm.
    eapply sat_mono, Hsat.
    iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_alloc_res {A: cmra} `{!inG Σ A} (a: A) F Rs P:
    ✓ a → SAT Alloc F Rs P → ∃ γ, SAT Alloc F Rs (own γ a ∗ P).
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hv Hsat. destruct (sat_alloc_res _ _ Hv Hsat) as [γ Hsat'].
    exists γ. eapply sat_mono, Hsat'.
    iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_resource_exchange m F F' Rs Rs' (P: iProp Σ):
    F ∗ [∗] Rs ⊣⊢ F' ∗ [∗] Rs' →
    SAT m F Rs P → SAT m F' Rs' P.
  Proof.
    rewrite SAT_eq /SAT_def.
    intros Hiff Hsat. eapply sat_mono, Hsat.
    rewrite bi.sep_assoc Hiff -bi.sep_assoc //.
  Qed.

  Lemma SAT_frame_resource m (R: iProp Σ) F Rs Rs' (P: iProp Σ):
    SAT m F Rs P →
    find_resource Rs R Rs' →
    SAT m (R ∗ F) Rs' P.
  Proof.
    intros Hsat Hfind. eapply SAT_resource_exchange, Hsat.
    rewrite (@find_resource_iff _ Rs R) - bi.sep_assoc.
    iSplit; iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_unframe_resource m (R: iProp Σ) F Rs (P: iProp Σ):
    SAT m (R ∗ F) Rs P →
    SAT m F (R :: Rs) P.
  Proof.
    intros Hsat. eapply SAT_resource_exchange, Hsat; simpl.
    rewrite -bi.sep_assoc. iSplit; iIntros "($ & $ & $)".
  Qed.


  (* Context Search *)
  Global Instance find_resource_head (R: iProp Σ) Rs :
    find_resource (R :: Rs) R Rs | 1.
  Proof.
    rewrite /find_resource //=.
  Qed.

  Global Instance find_resource_tail (R R': iProp Σ) Rs Rs' :
    find_resource Rs R Rs' →
    find_resource (R' :: Rs) R (R' :: Rs') | 2.
  Proof.
    rewrite /find_resource //=.
    intros ->. iSplit; iIntros "($ & $ & $)".
  Qed.

  Lemma SAT_res_cons m F R Rs (P: iProp Σ):
    SAT m F (R :: Rs) P ↔ SAT m F Rs (R ∗ P).
  Proof.
    rewrite SAT_eq /SAT_def /=. rewrite -!bi.sep_assoc.
    split; eapply sat_mono; iIntros "($ & $ & $ & $)".
  Qed.

  Lemma SAT_frame_cons m F R Rs (P: iProp Σ):
    SAT m (R ∗ F) Rs P ↔ SAT m F Rs (R ∗ P).
  Proof.
    rewrite SAT_eq /SAT_def /=. rewrite -!bi.sep_assoc.
    split; eapply sat_mono; iIntros "($ & $ & $ & $)".
  Qed.


  (* Derived Properties *)
  Lemma SAT_elim_iterated m F Rs G n (P: iProp Σ):
    (∀ P, SAT m F Rs (G P) → SAT m F Rs P) →
    SAT m F Rs (Nat.iter n G P) → SAT m F Rs P.
  Proof.
    intros Hiterated. induction n as [|n IHn]; eauto.
  Qed.

  Global Instance SAT_proper m : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (SAT (Σ := Σ) m).
  Proof.
    intros F F' HF Rs Rs' HRs P P' HP. rewrite SAT_eq /SAT_def.
    rewrite HF HP. f_equiv. f_equiv. f_equiv.
    induction HRs as [|R R' Rs Rs' Heq _ IH]; simpl; first done.
    rewrite Heq IH //.
  Qed.

  Global Instance SAT_proper_ent F Rs m : Proper ((⊢) ==> impl) (SAT (Σ := Σ) m F Rs).
  Proof.
    intros P Q HPQ. rewrite /impl. by eapply SAT_mono.
  Qed.

  Global Instance SAT_proper_flip_ent m F Rs : Proper (flip (⊢) ==> flip impl) (SAT (Σ := Σ) m F Rs).
  Proof.
    intros P Q HPQ. rewrite /flip /impl. by eapply SAT_mono.
  Qed.

  Lemma SAT_except_0 m F Rs (P: iProp Σ):
    SAT m F Rs (◇ P) → SAT m F Rs P.
  Proof.
    intros Hsat. eapply SAT_later. rewrite -bi.except_0_into_later //.
  Qed.



End satisfiable_frame_properties.
