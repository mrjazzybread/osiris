From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp.

(* This file should move to the [proofmode] directory. *)

(* -------------------------------------------------------------------------- *)

(* The following section provides helper lemmas to reason on mutually-recursive
   functions ([let rec ... and ...] and [let ... = ...] constructs). *)
Section MutuallyRecursive.

  Context `{!osirisGS_gen hlc Σ}.

  (* ------------------------------------------------------------------------ *)

  (* The idea of this section is to allow to prove goals of the form
     [wp s E (concatenating ...) φ] and [wp s E (ret_dconcat ...) φ] by
     proving that it is enough to prove:
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ spec1 v1 ],
      ... ,
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ specn vn ], and
     [ (spec1 v1 -∗ ... -∗ specn vn -∗ P) ],
     where [P] represents the initial goal to prove.

     Note: this lemma follows directly from a few tautologies. *)

  (* ------------------------------------------------------------------------ *)

  (* Definitions to build the lemmas on mutually-recursive functions. *)

  (* [sepn] is similar to the iterated separating conjunction on lists.
     Using this ad-hoc definition makes the following proofs easier.
     Note: it would be possible to avoid the [emp] term in the conjunctions, but
           this would alter the structure of the definition, which has been
           chosen to mimic that of [wandn] below.
           As [sepn] should never be exposed to users, this is not an issue. *)
  Local Definition sepn (pl: list (iProp Σ)) : iProp Σ :=
    foldr (fun e res => e ∗ res)%I emp%I pl.

  (* [wandn] is an iterated magic wand:
     [wandn [a; b; c] P ] reduces to [a -∗ b -∗ c -∗ P] *)
  Definition wandn (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    foldr (fun e res => e -∗ res)%I P pl.

  Definition sepn_wand (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    sepn pl -∗ P.

  (* ------------------------------------------------------------------------ *)

  (* Simple lemmas on the above definitions to prepare the main proof. *)

  (* [wandn_sepn_wand_1] and [wandn_sepn_wand_2] state that it is equivalent to
     have nested wands or a conjunction followed by a wand. *)

  Lemma wandn_sepn_wand_1 (pl: list (iProp Σ)) (P: iProp Σ) :
    wandn pl P -∗ sepn_wand pl P.
  Proof.
    iInduction (pl) as [ | p pl ] "IH";
      unfold wandn; unfold sepn_wand; simpl; auto.
    iIntros "H_impl [Hp H_conj]".
    iApply ("IH" with "[H_impl Hp] H_conj").
    iApply ("H_impl" with "Hp").
  Qed.

  Lemma wandn_sepn_wand_2 (pl: list (iProp Σ)) (P: iProp Σ) :
    sepn_wand pl P -∗ wandn pl P.
  Proof.
    iInduction (pl) as [ | p pl ] "IH";
      unfold wandn; unfold sepn_wand; simpl.

    { iIntros "H". iApply ("H" with "[//]"). }

    iIntros "H_sepn Hp".
    iPoseProof (wand_curry with "H_sepn Hp") as "H_sepn".
    iApply ("IH" with "H_sepn").
  Qed.

  (* The [▷] modality can enter inside a separating conjunction. *)
  Lemma sepn_later_1 (pl: list (iProp Σ)) :
    ▷ sepn pl -∗ sepn (map (fun e => ▷ e)%I pl).
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  (* The [▷] modality can be factorized in front of a separating conjunction. *)
  Lemma sepn_later_2 (pl: list (iProp Σ)) :
    sepn (map (fun e => ▷ e)%I pl) -∗ ▷ sepn pl.
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  (* [sepn_pers] states that the conjunction of persistent propositions is
     persistent. *)
  Lemma sepn_pers (pl: list (iProp Σ)) :
    Forall Persistent pl →
    Persistent (sepn pl).
  Proof.
    induction pl as [ | p pl IH].
    { simpl. intros. apply emp_persistent. }
    { intros [Hp Hpl]%Forall_cons.
      simpl. apply sep_persistent; first exact Hp.
      exact (IH Hpl). }
  Qed.

  (* [sepn_löb] paraphrases the Löb-induction principle on conjunctions. *)
  Lemma sepn_löb pl :
    (□ (sepn (map (fun e => ▷ e)%I pl) -∗ sepn pl)) -∗
    sepn pl.
  Proof.
    iIntros "#H1".
    iLöb as "Hl".
    iApply "H1".
    iApply (sepn_later_1 with "Hl").
  Qed.

  (* [wand_sepn_l] states that for any persistent proposition [P], to prove a
     conjunction under the assumption [P], it suffices to show each element of
     the conjunction under the assumption [P]. *)
  Lemma wand_sepn_l (pl: list (iProp Σ)) (P: iProp Σ) :
    Persistent P →
    sepn (map (fun p => P -∗ p) pl)%I -∗
    (P -∗ sepn pl).
  Proof.
    intros Hpers.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    iIntros "[Hp Hpl] #HP".
    iPoseProof ("IH" with "Hpl HP") as "$".
    iApply ("Hp" with "HP").
  Qed.

  (* [sepn_persistent_l] states that to prove that a conjunction is persistent,
     it suffices to show that each proposition of the conjunction is. *)
  Lemma sepn_persistent_l (pl: list (iProp Σ)) :
    sepn (map (λ e, □ e)%I pl) -∗ (□ sepn pl).
  Proof.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    assert (Persistent (sepn (map (λ e, □ e)%I pl))).
    { apply sepn_pers. induction pl as [ | ? ? IHpl ]; simpl;
        [ by apply Forall_nil | apply Forall_cons; split].
      - apply intuitionistically_persistent.
      - apply IHpl. }
    iIntros "[#Hp #Hpl]".
    iSplitL; first by auto.
    iApply ("IH" with "Hpl").
  Qed.

  (* [sepn_weaken2] allows to weaken the elements of a conjunction. *)
  Lemma sepn_weaken2 (f g: iProp Σ → iProp Σ) (pl: list (iProp Σ)) :
    (forall e, f e -∗ g e) → sepn (map f pl) -∗ sepn (map g pl).
  Proof.
    iIntros (Hf).
    induction pl as [ | p pl IH ]; simpl; auto.
    iIntros "[Hp Hpl]".
    iSplitL "Hp".
    { iApply (Hf with "Hp"). }
    { iApply (IH with "Hpl"). }
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* Main result.
     [assumming_list] (* TODO: find a better suited name for this lemma. *)
     states that for any persistent propositions [p1], ..., [pn] and any
     proposition [P] (which does not have to be persistent),
     [
     □ (▷ p1 -∗ ... -∗ ▷ pn -∗ p1) -∗
       ... -∗
     □ (▷ p1 -∗ ... -∗ ▷ pn -∗ pn) -∗
     (p1 -∗ ... -∗ pn -∗ P) -∗
     P
     ].
   *)


  Lemma assumming_list_nonrec (pl: list (iProp Σ)) (P: iProp Σ) :
    ⊢ wandn pl ((wandn pl P) -∗ P).
  Proof.
    iApply wandn_sepn_wand_2.
    iIntros "??".
    iApply (wandn_sepn_wand_1 with "[$][$]").
  Qed.

  Lemma assumming_list (pl: list (iProp Σ)) (P: iProp Σ) :
    Forall Persistent pl → ⊢
    (wandn
       (map (λ p, □ p)
       (map (λ p, wandn (map (λ e : iPropI Σ, ▷ e) pl) p) pl)))%I
    ((wandn pl P) -∗
    P).
  Proof.
    intros Hpers.
    iApply wandn_sepn_wand_2.
    iIntros "Hspecs1 HP"; unfold sepn_wand.
    iPoseProof (sepn_persistent_l with "Hspecs1") as "#Hspecs3".
    iPoseProof (wandn_sepn_wand_1 with "HP") as "HP".
    unfold sepn_wand.

    assert (Persistent (sepn (map (λ e, ▷ e)%I pl))).
    { apply sepn_pers.
      induction pl as [ | p pl IH]; first by apply Forall_nil.
      apply Forall_cons in Hpers as [Hp Hpl].
      apply Forall_cons; split;
        [ exact (later_persistent _ Hp)
        | exact (IH Hpl) ]. }
    iPoseProof (sepn_weaken2 with "Hspecs3") as "#Hspecs".
    { iIntros (e) "H".
      iApply (wandn_sepn_wand_1 with "H"). }
    iPoseProof ((wand_sepn_l pl (sepn (map (λ e : iPropI Σ, ▷ e)%I pl))
                              H) with "Hspecs") as "Hspecs2".
    iPoseProof (sepn_löb with "Hspecs2") as "Hspecs4".
    iApply ("HP" with "Hspecs4").
  Qed.
End MutuallyRecursive.
