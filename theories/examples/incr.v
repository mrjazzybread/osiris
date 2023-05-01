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
    iIntros(ϕ)"!>Hℓ Hϕ".
    wp_call. wp.
    iApply (wp_covariant with "[Hℓ]"); last first.
    { iIntros (v)"Hv".
      iApply "Hϕ".
      iAssumption. }
    { unfold is_counter.
      iDestruct "Hℓ" as "(%&->&Hℓ)".
      iApply (Stdlib__load__spec with "[$Hℓ]"); first done.
      iNext.
      iIntros(?) "[-> Hℓ]".
      by iExists _. } }

  { (* Proof of the specification of [upd]. *)
    unfold upd_spec. iIntros.
    iIntros (ϕ) "!>(%&->&Hℓ) Hϕ".
    wp_call.
    iApply ((Stdlib__store__spec _ _ (VInt (int.repr i)) (VInt (int.repr i')))
             with "[Hℓ]").
    { by iFrame. }
    iNext.
    iIntros (?)"Hstore".
    iApply (wp_covariant with "Hstore").
    iIntros (?) "[-> Hℓ]".
    iApply "Hϕ".
    iExists _. by iFrame. }
Qed.
