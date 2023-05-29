From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import wp wp_tactics.

(* This file should move to the [proofmode] directory. *)



(* The follwoing section defines the typeclasses to use to define a
   specification. *)
Section FunctionSpecifications.
  Context `{!osirisGS_gen hlc Σ}.

  (* [pure_unary_spec] is used to tell osiris that [f] represents a closure
     whose behaviour is that of [ff], a unary Gallina function. *)
  Class pure_unary_spec
        {A B: Type} `{!Encode A} `{!Encode B}
        (f: val) (ff: A → B) :=
    spec:
      ∀ (b: A) s E (φ: val → iProp Σ),
        ▷ (φ #(ff b)) -∗
        wp s E (call f #b) φ.

  (* [pure_binary_spec] is used to tell osiris that [f] represents a closure
     whose behaviour is that of [ff], a binary Gallina function. *)
  Class pure_binary_spec
        {A B C: Type} `{!Encode A} `{!Encode B} `{!Encode C}
        (f: val) (ff: A → B → C) (a: A) (b: B) :=
    spec2:
      ∀ s E (φ: val → iProp Σ),
        ▷ (φ #(ff a b)) -∗
        wp s E (call f #a) (λ (v: val), wp s E (call v #b) φ).
  Global Hint Mode pure_binary_spec - - - - - - - - ! !
    : typeclass_instances.


  (* [pure_partial_binary_spec] is used to tell osiris that [f] represents a
     closure whose behaviour is that of [ff], a binary Gallina function.
     Using this typeclass will allow for automation when encounting partial
     applications of [f]. *)
  Class pure_binary_partial_spec
        {A B C: Type} `{!Encode A} `{!Encode B} `{!Encode C}
        (f: val) (ff: A → B → C) :=
    spec2_1:
      ∀ (a: A) s E (φ: val → iProp Σ),
         (∀ (vpartial: val),
                       (∀ (b: B) s' E',
                           wp s' E' (call vpartial #b)
                              (λ res, ⌜res = #(ff a b)⌝)) -∗
                       φ vpartial) -∗ (* TODO: get a later here. *)
        wp s E (call f #a) φ.

End FunctionSpecifications.

(* -------------------------------------------------------------------------- *)

(* The following section provides helper lemmas to reason on mutually-recursive
   functions ([let rec ... and ...] and [let ... = ...] constructs). *)
Section MutuallyRecursive.

  Context `{!osirisGS_gen hlc Σ}.

  (* ------------------------------------------------------------------------ *)

  (* The idea of this section is to allow to prove goals of the form
     [wp s E (concatenating ...) φ] and [wp s E (dconcatenating ...) φ] by
     proving that it is enough to prove:
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ spec1 v1 ],
      ... ,
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ specn vn ], and
     [ (spec1 v1 -∗ ... -∗ specn vn -∗ P) ],
     where [P] represents the initial goal to prove.

     Note: it does not seem possible to prove the lines above in separate
           branches of the proof (ie. outside of the Iris proofmode) as one may
           need resources to prove the specifications.
           There does not seem to be an easy way to share the resources and keep
           the built-in Löb induction. *)

  (* ------------------------------------------------------------------------ *)

  (* Definitions to build the lemmas on mutually-recursive functions. *)

  Definition conjn (pl: list (iProp Σ)) : iProp Σ :=
    foldr (fun e res => e ∗ res)%I emp%I pl.

  Definition wandn (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    foldr (fun e res => e -∗ res)%I P pl.

  Definition sepn_wand (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    conjn pl -∗ P.

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

  (* ------------------------------------------------------------------------ *)

  Lemma conjn_later_1 (pl: list (iProp Σ)) :
    ▷ conjn pl -∗ conjn (map (fun e => ▷ e)%I pl).
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  Lemma conjn_later_2 (pl: list (iProp Σ)) :
    conjn (map (fun e => ▷ e)%I pl) -∗ ▷ conjn pl.
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  Lemma conjn_pers (pl: list (iProp Σ)) :
    Forall Persistent pl →
    Persistent (conjn pl).
  Proof.
    induction pl as [ | p pl IH].
    { simpl. intros. apply emp_persistent. }

    { intros [Hp Hpl]%Forall_cons.
      simpl. apply sep_persistent; first exact Hp.
      exact (IH Hpl). }
  Qed.

  Lemma conjn_löb pl :
    (□ (conjn (map (fun e => ▷ e)%I pl) -∗ conjn pl)) -∗
    conjn pl.
  Proof.
    iIntros "#H1".
    iLöb as "Hl".
    iApply "H1".
    iApply (conjn_later_1 with "Hl").
  Qed.

  Lemma wand_conjn_l (pl: list (iProp Σ)) (P: iProp Σ) :
    Persistent P →
    conjn (map (fun p => P -∗ p) pl)%I -∗
    (P -∗ conjn pl).
  Proof.
    intros Hpers.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    iIntros "[Hp Hpl] #HP".
    iPoseProof ("IH" with "Hpl HP") as "$".
    iApply ("Hp" with "HP").
  Qed.

  Lemma persistent_intro (P: iProp Σ):
    (Persistent P -> ⊢ P -∗ □ P)%I.
  Proof. auto. Qed.

  Lemma conjn_persistent_l (pl: list (iProp Σ)) :
    conjn (map (λ e, □ e)%I pl) -∗ (□ conjn pl).
  Proof.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    assert (Persistent (conjn (map (λ e, □ e)%I pl))).
    { apply conjn_pers. induction pl as [ | ? ? IHpl ]; simpl;
        [ by apply Forall_nil | apply Forall_cons; split].
      - apply intuitionistically_persistent.
      - apply IHpl. }
    iIntros "[#Hp #Hpl]".
    iSplitL; first by auto.
    iApply ("IH" with "Hpl").
  Qed.

  Lemma conjn_weaken2 (f g: iProp Σ → iProp Σ) (pl: list (iProp Σ)) :
    (forall e, f e -∗ g e) → conjn (map f pl) -∗ conjn (map g pl).
  Proof.
    iIntros (Hf).
    induction pl as [ | p pl IH ]; simpl; auto.
    iIntros "[Hp Hpl]".
    iSplitL "Hp".
    { iApply (Hf with "Hp"). }
    { iApply (IH with "Hpl"). }
  Qed.

  Lemma prove_specify (pl: list (iProp Σ)) (P: iProp Σ) :
    Forall Persistent pl → ⊢
    (*□ (wandn (map (fun e => ▷ e)%I pl) (conjn pl)) -∗*)
    (wandn
       (map (λ p, □ p)
       (map (λ p, wandn (map (λ e : iPropI Σ, ▷ e) pl) p) pl)))%I
    ((wandn pl P) -∗
    P).
  Proof.
    intros Hpers.
    iApply wandn_sepn_wand_2.
    iIntros "Hspecs1 HP"; unfold sepn_wand.
    iPoseProof (conjn_persistent_l with "Hspecs1") as "#Hspecs3".
    iPoseProof (wandn_sepn_wand_1 with "HP") as "HP".
    unfold sepn_wand.

    assert (Persistent (conjn (map (λ e, ▷ e)%I pl))).
    { apply conjn_pers.
      induction pl as [ | p pl IH]; first by apply Forall_nil.
      apply Forall_cons in Hpers as [Hp Hpl].
      apply Forall_cons; split;
        [ exact (later_persistent _ Hp)
        | exact (IH Hpl) ]. }
    iPoseProof (conjn_weaken2 with "Hspecs3") as "#Hspecs".
    { iIntros (e) "H".
      iApply (wandn_sepn_wand_1 with "H"). }
    iPoseProof ((wand_conjn_l pl (conjn (map (λ e : iPropI Σ, ▷ e)%I pl))
                              H) with "Hspecs") as "Hspecs2".
    iPoseProof (conjn_löb with "Hspecs2") as "Hspecs4".
    iApply ("HP" with "Hspecs4").
  Qed.
End MutuallyRecursive.
