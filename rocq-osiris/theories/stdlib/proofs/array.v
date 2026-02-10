From osiris.lang Require Import type_nel encode.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import proofmode.

From osiris.stdlib Require Import og_array.

Section proof.

  Context `{!osirisGS Σ}.

  Definition invert_spec : Z → val → microvx → iProp Σ :=
    λ n f m,
      (∀ `(_ : Encode A) Φ,
         iSpec τ[Z] f Φ -∗
         imp m {{ λ a, isArray a n ∗ ∃ (xs : list A), isSlice (DfracOwn 1) a n xs }})%I.

  Definition init := (EAnonFun __fun8).

  Lemma ewp_invert η :
    ⊢ imp (eval η init) {{ λ c, □ iSpec τ[Z; val] c invert_spec }}.
  Proof.
  Admitted.

End proof.
