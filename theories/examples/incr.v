(* Original file:
let new_counter () =
  let c = ref 0 in let upd i = c := i in let get () = !c in (get, upd) *)

(* Converting a single CMT file for [Incr]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
Require Import base lang sugar encode.
(* TODO: get the From _ to work From libs *) Require Import Stdlib.


(* Generated code: *)
Definition new_counter :=
  EFun "_" $
  ELet (BiCons (Binding (PVar "c") (EApp (EMkPath ["Stdlib";"ref"]) (EInt 0))) BiNil) $
  ELet (BiCons
    (Binding (PVar "upd")
       (EFun "i" (EApp (EApp (EMkPath ["Stdlib";":="]) (EVar "c")) (EVar "i"))))
    BiNil) $
  ELet (BiCons
    (Binding (PVar "get")
       (EFun "_" (EApp (EMkPath ["Stdlib";"!"]) (EVar "c"))))
    BiNil) $
  ETuple (ECons (EVar "get") (ECons (EVar "upd") ENil)).



From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.
Require Import free eval step wp wp_tactics notations.

Context `{!osirisGS_gen hlc Σ}.


Definition new_counter_spec_get s E vget: iProp Σ :=
  {{{ ⌜ True⌝ }}}
    call vget VUnit @s; E
  {{{ v, RET v; ∃ i, ⌜v = VInt (int.repr i)⌝ }}}.

Definition new_counter_spec_upd s E vupd: iProp Σ :=
  ∀ i,
    {{{ ⌜ True ⌝ }}}
      call vupd (VInt (int.repr i)) @s; E
    {{{ v, RET v; ⌜v = VUnit⌝ }}}.

Definition new_counter_spec_def s E v: Prop :=
  ⊢ WP call v VUnit @ s; E
       {{ λ v,
           ∃ vget vupd,
           ⌜v = VTuple $
                  VCons vget $
                  VCons vupd $
                  VNil⌝ ∗
           new_counter_spec_get s E vget ∗
           new_counter_spec_upd s E vupd }}.

Lemma new_counter__spec (s: stuckness) E:
  let η : env :=
    EnvCons "Stdlib" Stdlib $
    EnvCons "!" (VClo EnvNil (AnonFun "x" (ELoad (EVar "x")))) $
    EnvNil
  in
  ⊢ WP eval η new_counter @ s; E
        {{ λ v, ⌜new_counter_spec_def s E v⌝ }}.
Proof.
  intros.
  wp. iPureIntro. unfold new_counter_spec_def.
  wp_call.
  wp_use Stdlib__ref__spec.
  iIntros.
  wp.
  iExists _, _; repeat iSplit.
  1: iPureIntro; f_equal.
  { iIntros(i) "!> Hpre Hφ".
    wp_call.
    iApply (Stdlib__load__spec with .
  { admit. }
Admitted.

(* Check the result. *)
Print new_counter.
