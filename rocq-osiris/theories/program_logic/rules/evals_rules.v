From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.utils Require Import list_z.
Require Import osiris_utils.
Require Import ewp tactics fun_spec escrows.
Require Import
  basic_rules impure_rules stop_rules
  handler_rules auxiliary_rules.

Section evals_rules.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Local Instance notval_listval : NotVal (list val) := {}.

  Lemma imp_evals_nil η (Φ : list val → iProp Σ) :
    Φ [] -∗
    impure E (evals η []) Ψ ζ Φ.
  Proof.
    iIntros "HΦ".
    simpl_evals.
    by iApply (imp_ret with "HΦ").
  Qed.

  Global Instance observe_types_cons `{Encode A} {τ : types} : Observe (A * τ) (list val) :=
  { observe := λ '(x, xs), observe x :: observe xs }.

  Lemma imp_evals_cons `{Encode A} {τ : types} η e es (Φ : A → iProp Σ) (Φs : τ → iProp Σ) :
    impure E (eval η e) Ψ ζ Φ -∗
    impure E (evals η es) Ψ ζ Φs -∗
    impure (A:=type_nel.Tcons A τ) E (evals η (e :: es)) Ψ ζ (λ '(x, xs), Φ x ∗ Φs xs).
  Proof.
    iIntros "He Hes".
    simpl_evals.
    iApply (imp_bind_par with "He Hes").
    iIntros (x xs) "HΦ HΦs".
    iApply (imp_ret _ (x, xs)).
    - reflexivity.
    - iFrame.
  Qed.

  Local Instance observe_singleton `{Encode A} : Observe A (list val) :=
  { observe := λ (x : A), [ encode.encode x ] }.

  Lemma imp_evals_singleton `{Encode A} η e (Φ : A → iProp Σ) :
    impure E (eval η e) Ψ ζ Φ -∗
    impure E (evals η [e]) Ψ ζ Φ.
  Proof.
    iIntros "He". simpl_evals.
    iApply (imp_bind_par (A2:=list val) (H1:=observe_id) with "He").
    { set_postcondition (λ (l : list val), ⌜l = []⌝)%I.
      iApply (imp_ret _ []); auto. }
    iIntros (x xs) "HΦ ->".
    iApply (imp_ret _ x). encode.
    iApply "HΦ".
  Qed.

  Lemma imp_EData `{DC : Data c τ A} {Φ : A → iProp Σ} η es (Φs : τ → iProp Σ) :
    impure E (evals η es) Ψ ζ Φs -∗
    (∀# xs, Φs xs -∗ Φ (DC.(ctor_apply) xs)) -∗
    imp eval η (EData c es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H Hk". simpl_eval.
    iApply (imp_bind with "H").
    iIntros (xs) "HΦs".
    rewrite bi_tforall_equiv.
    iDestruct ("Hk" with "HΦs") as "HΦ".
    iApply (imp_ret _ (DC.(ctor_apply) xs)); last iApply "HΦ".
    simpl. apply DC.(ctor_encode).
  Qed.

  Lemma imp_EXData `{DC : XData l τ A} {Φ : A → iProp Σ} η π es (Φs : τ → iProp Σ) :
    lookup_path η π = Some #l →
    impure E (evals η es) Ψ ζ Φs -∗
    (∀# xs, Φs xs -∗ Φ (DC.(xctor_apply) xs)) -∗
    imp eval η (EXData π es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hlookup) "He Hk". simpl_eval.
    rewrite Hlookup. unfold as_loc; simpl. rewrite !bind_ret.
    iApply (imp_bind with "He").
    rewrite bi_tforall_equiv.
    iIntros (xs) "HΦs".
    iDestruct ("Hk" with "HΦs") as "HΦ".
    iApply (imp_ret _ (DC.(xctor_apply) xs)); last iApply "HΦ".
    simpl. apply DC.(xctor_encode).
  Qed.

End evals_rules.
