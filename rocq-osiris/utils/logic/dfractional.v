From iris.algebra Require Import dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.

(** * Splitting a resource along [dfrac] composition.

    Iris's [Fractional] describes resources that split along [Qp]
    addition: [Φ (p + q) ⊣⊢ Φ p ∗ Φ q]. That is enough for a resource
    that is always held at a genuine fraction, but it cannot describe the
    *discarded* fraction [DfracDiscarded], the one that makes a resource
    persistent, because [DfracDiscarded] is not a [Qp]. A predicate
    indexed by [Qp] therefore has to be dropped for a lower-level, hand-
    rolled one as soon as any of its ownership becomes persistent.

    [DFractional] is the same law one level up, along [dfrac] composition
    [⋅]. A single instance covers all of

      [DfracOwn p ⋅ DfracOwn q = DfracOwn (p + q)]        (real fractions)
      [DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded]  (duplication)
      [DfracOwn q ⋅ DfracDiscarded = DfracBoth q]         (the mixed form)

    and it implies the corresponding [Fractional] law
    ([dfractional_fractional]), so Iris's own [iSplitL] / [iCombine] /
    [AsFractional] machinery keeps working unchanged on the owned
    fractions. *)

Class DFractional {PROP : bi} (Φ : dfrac → PROP) :=
  dfractional dq1 dq2 : Φ (dq1 ⋅ dq2) ⊣⊢ Φ dq1 ∗ Φ dq2.
Global Arguments DFractional {_} _%_I : simpl never.
Global Arguments dfractional {_} _%_I {_} _ _.
Global Hint Mode DFractional - ! : typeclass_instances.

(** [AsDFractional P Φ dq] states that [P] is [Φ dq] for a [DFractional]
    [Φ], mirroring Iris's [AsFractional]. *)

Class AsDFractional {PROP : bi} (P : PROP) (Φ : dfrac → PROP) (dq : dfrac) := {
  as_dfractional : P ⊣⊢ Φ dq;
  as_dfractional_dfractional : DFractional Φ;
}.
Global Arguments AsDFractional {_} _%_I _%_I _.
Global Arguments as_dfractional {_} _%_I _%_I _ {_}.
Global Hint Mode AsDFractional - ! - - : typeclass_instances.
Global Existing Instance as_dfractional_dfractional.

Section dfractional.
  Context {PROP : bi}.
  Implicit Types Φ : dfrac → PROP.

  (* On the owned fractions, [DFractional] is exactly [Fractional].

     This is stated as a lemma rather than declared as an instance: a
     [Fractional] goal has the shape [Fractional (λ q, Ψ q)] with [Ψ]
     concrete, and recovering [Φ] from it is a higher-order unification
     problem that instance search cannot be relied on to solve. Concrete
     [Fractional] instances should be declared by applying this with [Φ]
     supplied explicitly. *)
  Lemma dfractional_fractional Φ `{!DFractional Φ} :
    Fractional (λ q, Φ (DfracOwn q)).
  Proof. intros p q. by rewrite -dfrac_op_own dfractional. Qed.

  Lemma dfractional_discarded_dup Φ `{!DFractional Φ} :
    Φ DfracDiscarded ⊣⊢ Φ DfracDiscarded ∗ Φ DfracDiscarded.
  Proof. by rewrite -dfractional dfrac_op_discarded. Qed.

  (* [DfracBoth] splits into its owned and its discarded halves. *)
  Lemma dfractional_both Φ `{!DFractional Φ} q :
    Φ (DfracBoth q) ⊣⊢ Φ (DfracOwn q) ∗ Φ DfracDiscarded.
  Proof. by rewrite -dfractional. Qed.

  (* Halving, the most common concrete split. *)
  Lemma dfractional_half Φ `{!DFractional Φ} q :
    Φ (DfracOwn q) ⊣⊢ Φ (DfracOwn (q/2)) ∗ Φ (DfracOwn (q/2)).
  Proof. by rewrite -dfractional dfrac_op_own Qp.div_2. Qed.
End dfractional.

(** ** Division at the [dfrac] level.

    Iris's proofmode splits an abstract fractional resource by halving:
    [Φ q] becomes [Φ (q/2) ∗ Φ (q/2)]. To do the same for a [dfrac]-
    indexed resource we need a division that also makes sense for a
    *discarded* share, where "half" is not a fraction at all: a discarded
    share splits by duplication. [dfrac_half] is that operation, defined
    by cases so that it computes. *)

Definition dfrac_half (dq : dfrac) : dfrac :=
  match dq with
  | DfracOwn q => DfracOwn (q/2)
  | DfracDiscarded => DfracDiscarded
  | DfracBoth q => DfracBoth (q/2)
  end.

(* [dfrac]'s [⋅] does not reduce under [simpl] (it is a CMRA operation
   behind an instance), hence the explicit unfolding. *)
Lemma dfrac_half_op dq : dfrac_half dq ⋅ dfrac_half dq = dq.
Proof. destruct dq; rewrite /op /cmra_op /= /dfrac_op_instance ?Qp.div_2 //. Qed.

Section dfractional_split.
  Context {PROP : bi}.
  Implicit Types Φ : dfrac → PROP.

  (* [Φ] is supplied explicitly to [dfractional] throughout this section:
     the [Hint Mode] above (deliberately) refuses to run instance search
     with [Φ] unknown, which is what a backwards [rewrite -dfractional]
     would ask it to do. *)

  Lemma dfractional_halve Φ `{!DFractional Φ} dq :
    Φ dq ⊣⊢ Φ (dfrac_half dq) ∗ Φ (dfrac_half dq).
  Proof. rewrite -{1}(dfrac_half_op dq). apply (dfractional Φ). Qed.

  Lemma dfractional_as_halve P Φ dq :
    AsDFractional P Φ dq → P ⊣⊢ Φ (dfrac_half dq) ∗ Φ (dfrac_half dq).
  Proof. intros [HP HΦ]. rewrite HP. apply (dfractional_halve Φ). Qed.

  (* Proofmode plumbing, mirroring [iris.bi.lib.fractional]'s own
     [into_sep_fractional] / [from_sep_fractional]. These are what make
     [iDestruct "H" as "[H1 H2]"] and [iCombine] work on a resource held
     at an abstract [dfrac]. Going through [AsDFractional] (rather than
     matching on [Φ] directly) keeps [Φ] a first-order unknown that
     instance search can actually solve. *)

  Global Instance into_sep_dfractional P Φ dq :
    AsDFractional P Φ dq → IntoSep P (Φ (dfrac_half dq)) (Φ (dfrac_half dq)).
  Proof. intros. rewrite /IntoSep (dfractional_as_halve P Φ dq) //. Qed.

  Global Instance from_sep_dfractional P1 P2 Φ dq1 dq2 :
    AsDFractional P1 Φ dq1 → AsDFractional P2 Φ dq2 →
    FromSep (Φ (dq1 ⋅ dq2)) P1 P2.
  Proof.
    intros [H1 HΦ] [H2 _]. rewrite /FromSep H1 H2.
    rewrite (dfractional Φ dq1 dq2) //.
  Qed.
End dfractional_split.
