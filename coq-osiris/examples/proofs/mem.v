From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_mem.



From Coq Require Import List.

Class Eq {A} :=
  {
    eqb : A -> A -> bool;
  }.

Fixpoint memb `{Eq A} (x : A) l :=
  match l with
  | [] => false
  | y :: l =>
      if eqb x y then true else memb y l
  end.

Section proof.

Context `{!osirisGS Σ}.

Definition mem_spec mem :=
  (∀ (A : Type) (H : Encode A) (H0 : Eq) (x : A) (l : list A),
      EWP (ncall mem [ #x; #l]) <|⊥|> {{ RET #b, ⌜b = memb x l⌝ }})%I.

Lemma mem_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{RET m, module_spec [("mem", mem_spec)] m}}.
Proof.
  iIntros.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_struct_let_single mem_spec).
    Simp. Ret. simpl.

    unfold mem_spec.
    iIntros (A ? ? x l).

    simpl.
    Bind. iApply ewp_call_nonrec. iNext.
    Simp. Ret. simpl.
    iApply ewp_call_nonrec. iNext.

    iApply ewp_ELetOpen.
    iApply ewp_module.
    iApply ewp_sitems_extend.

    iIntros ([η δ]) "[%found [-> Hfound]]"; clear η δ.

    iApply ewp_sitems_nil; simpl.

    fold eval. iExists _. iSplit; [ equality | ].

    iApply ewp_EMatch.
    iApply ewp_deep_handler.
    { unfold deco.
      (* Specification needed for Iter! *)
      admit.  }

    rewrite deep_handler_spec_unfold; iSplit.
    { iIntros ([ | ]) "Hf".
      iNext. unfold __branches3.
      admit.
      admit. }

    { iIntros (??) "Hprot".
      iPoseProof (upcl_bottom with "Hprot") as "F".
      done. } }

  iIntros ([η δ]) "[%mem [ Hmem [ -> -> ] ] ]".
  iApply ewp_sitems_nil; simpl.
  unfold module_spec.
  iExists _; iSplit; [ equality | ].
  simpl.
  iSplit; [ | trivial ].
  eauto.
Admitted.

End proof.
