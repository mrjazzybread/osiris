(* Original file:
let new_counter () =
  let c = ref 0 in let upd i = c := i in let get () = !c in (get, upd)
let _ =
  let res = new_counter () in
  let get = fst res in
  let upd = snd res in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res
let _test =
  let (get, upd) = new_counter () in
  let c = get () in match upd 13 with | () -> let res = (get ()) - c in res *)

(* Converting a single CMT file for [Incr]. *)

(* Auto generated headers. They import the required Coq modules:
   - either translations of the dependencies of the present file
   - or static dependencies defining the language
   - or part of the verification of the [StdLib] (or maybe other verified libraries). *)
Require Import base lang sugar encode notations.
(* TODO: get the From _ to work From libs *) Require Import Stdlib.


(* Generated code: *)
Definition new_counter :=
  EFun "()" $
    ELet
      (BiCons
         (Binding (PVar "c")
                  (EApp (EMkPath ["Stdlib";"ref"]) (EInt 0)))
         BiNil) $
    ELet
      (BiCons
         (Binding (PVar "upd")
                  (EFun "i"
                        (EApp
                           (EApp (EMkPath ["Stdlib";":="]) (EVar "c"))
                           (EVar "i"))))
         BiNil) $
    ELet
      (BiCons
         (Binding (PVar "get")
                  (EFun "()" (EApp (EMkPath ["Stdlib";"!"]) (EVar "c"))))
         BiNil) $
    ETuple (ECons (EVar "get") (ECons (EVar "upd") ENil)).

Definition pleasedontclash (*This is not a name. *) :=
  ELet
    (BiCons
       (Binding (PVar "res")
                (EApp (EVar "new_counter") (EData "()" (ETuple ENil))))
       BiNil) $
  ELet
    (BiCons
       (Binding (PVar "get")
                (EApp (EMkPath ["Stdlib";"fst"]) (EVar "res")))
       BiNil) $
  ELet
    (BiCons
       (Binding (PVar "upd")
                (EApp (EMkPath ["Stdlib";"snd"]) (EVar "res")))
       BiNil) $
  ELet
    (BiCons
       (Binding (PVar "c")
                (EApp (EVar "get") (EData "()" (ETuple ENil))))
       BiNil) $
  EMatch
  (EApp (EVar "upd") (EInt 13))
  (BrCons (Branch
             (PData "()" (PTuple PNil))
             (ELet
                (BiCons
                   (Binding (PVar "res")
                            (EApp (EApp
                                     (EMkPath ["Stdlib";"-"])
                                     (EApp (EVar "get")
                                           (EData "()" (ETuple ENil))))
                                  (EVar "c")))
                   BiNil)
                (EVar "res")))
          BrNil).

Definition _test :=
  (* *** START OF A MODIFICATION TO THE TRANSLATION *** *)
  (* The current translator assumes that the user will provide the correct
     environment to work with previously-defined symbols. Nonetheless, as
     translations are in fact expressions and not values (at least for now), it
     would be tedious to do so. An alternative is to use the trick described in
     [traduction/lib/Pp.ml]: translate a single file as a huge let:
     let a, b, c, ... =
         let a_at_top-level := ... in
         let _ = ... in
         let b_at_top-level := ... in
         let c_at_top-level := ... in
         (a_at_top-level, ...).
     Notes:
       - this would also solve the issue of taking into account the
         [let _ = ...] and [let () = ...] that appear at top-level.
       - use structures instead of an enclosing let.

     For now, I add this let by hand, but the above trick will be directly
     applied by the translator in the futur. *)
  ELet
    (BiCons
       (Binding (PVar "new_counter")
                new_counter)
       BiNil) $
  (* ***  END OF A MODIFICATION TO THE TRANSLATION  *** *)
  ELet
    (BiCons
       (Binding (PTuple (PCons (PVar "upd")
                         (PCons (PVar "get") PNil)))
                (EApp (EVar "new_counter") (EData "()" (ETuple ENil))))
       BiNil) $
  ELet
    (BiCons
       (Binding
          (PVar "c")
          (EApp (EVar "get") (EData "()" (ETuple ENil))))
       BiNil) $
    EMatch
    (EApp (EVar "upd") (EInt 13))
    (BrCons (Branch
               (PData "()" (PTuple PNil))
               (ELet
                  (BiCons
                     (Binding (PVar "res")
                              (EApp (EApp
                                       (EMkPath ["Stdlib";"-"])
                                       (EApp (EVar "get")
                                             (EData "()" (ETuple ENil))))
                                    (EVar "c")))
                     BiNil)
                  (EVar "res")))
            BrNil).






From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

Require Import base lang sugar locations free eval step wp wp_tactics encode notations.

Context `{!osirisGS_gen hlc Σ}.

Definition is_counter ℓ i : iProp Σ :=
  ∃ v, ⌜ v = VInt (int.repr i) ⌝ ∗ ℓ ↦ v.

Definition get_spec ℓ get : iProp Σ :=
  ∀ i s E,
  {{{ is_counter ℓ i }}}
    call get VUnit @ s; E
  {{{ v, RET v; ∃ i, ⌜ v = VInt (int.repr i) ⌝ }}}.

Definition upd_spec ℓ upd : iProp Σ :=
  ∀ s E i i',
    {{{ is_counter ℓ i }}}
      call upd (VInt (int.repr i')) @ s; E
    {{{ RET VUnit; is_counter ℓ i' }}}.

Lemma new_counter__spec s E :
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval η new_counter @ s; E
       {{ λ v, {{{ ⌜ True ⌝ }}}
                 call v VUnit
               {{{ vget vupd,
                     RET (VTuple (VCons vget (VCons vupd VNil)));
                   ∃ ℓ,
                   is_counter ℓ 0 ∗
                   get_spec ℓ vget ∗
                   upd_spec ℓ vupd }}} }}.
Proof.
  intros. wp.
  iIntros (ϕ) "!> _ Hϕ".
  wp_call.
  iApply wp_covariant; first by iApply Stdlib__ref__spec.
  iIntros (?) "(%ℓ&Hℓ&->)".
  wp. iApply "Hϕ". clear ϕ.
  iExists ℓ.
  iSplitL; last iSplit.

  { (* Proof of the [is_counter] predicate. *)
    unfold is_counter. iExists _. by iFrame. }

  { (* Proving the specification of [get]. *)
    unfold get_spec. iIntros.
    iIntros(ϕ)"!>(%&->&Hℓ) Hϕ".
    wp_call. wp.

    (* TODO: understand why the postcondition has to be specified. *)
    iApply ((Stdlib__load__spec_tac _ _ _ _ _ ϕ)
             with "[//]Hℓ").
    iApply "Hϕ".
    iExists _. done. }

  { (* Proof of the specification of [upd]. *)
    unfold upd_spec. iIntros.
    iIntros (ϕ) "!>(%&->&Hℓ) Hϕ".
    wp_call.
    iApply (Stdlib__store__spec_tac with "Hℓ[Hϕ]").
    iNext.
    iIntros "Hℓ".
    iApply "Hϕ".
    iExists _. by iFrame. }
Qed.


Opaque new_counter.
(* The following example shows the necessity of a better way to interact with
   the definitions of [Stdlib], as well as better ways to use former
    specifications. *)
Lemma _test__spec s E:
  let η :=
    EnvCons "Stdlib" Stdlib $
    EnvNil in
  {{{ ⌜ True ⌝ }}}
    eval η _test @ s; E
                        {{{ v, RET v; ⌜ True ⌝ }}}.
Proof.
  iIntros (η ϕ)"_ Hϕ".
  wp.
Abort.
