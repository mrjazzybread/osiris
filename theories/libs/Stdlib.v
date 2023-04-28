From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

Require Import base lang sugar free eval step wp wp_tactics encode notations.

Section StdLib.
  Context `{!osirisGS_gen hlc Σ}.

  Definition Stdlib__add : val :=
    VClo EnvNil $
      AnonFun "x" $
      EFun "y" $
      EIntAdd (EVar "x") (EVar "y").

  Definition Stdlib :=
    VStruct $
      EnvCons "+" Stdlib__add EnvNil.

  Lemma Stdlib__add__spec s E:
    ∀ v1 v2 i1 i2,
    v1 = VInt (int.repr i1) →
    v2 = VInt (int.repr i2) →
    ⊢ WP call Stdlib__add v1 @s; E
         {{ λ v, WP call v v2 @s; E {{ λ v, ⌜v = VInt (int.repr (i1 + i2))⌝ }} }}.
  Proof.
    intros. subst. wp.
    wp_call.
    by rewrite int.add_repr_repr.
  Qed.

  Opaque Stdlib__add.
End StdLib.

