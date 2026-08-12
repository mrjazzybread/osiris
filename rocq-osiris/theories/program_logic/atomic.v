From stdpp Require Import namespaces.
Require Import ewp rules.basic_rules rules.impure_rules.
From osiris.lang Require Import encode.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode classes.
(** This file declares notation for logically atomic Hoare triples, and some
generic lemmas about them. To enable the definition of a shared theory applying
to triples with any number of binders, the triples themselves are defined via telescopes, but as a user
you need not be concerned with that. You can just use the following notation:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | z, RET return_value; private_postcondition }>>

Here, [x] (which can be any number of binders, including 0) is bound in all of
the atomic pre- and postcondition and the private (non-atomic) postcondition and
the return value, [y] (which can be any number of binders, including 0) is bound
in both postconditions and the return value, and [z] (which can be any number of
binders, including 0) is bound in the return value and the private
postcondition.

Note that atomic triples are *not* implicitly persistent, unlike Texan triples.
If you need a private (non-atomic) precondition, you can use a magic wand:

  private_precondition -∗
  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition
    | z, RET return_value; private_postcondition }>>

If you don't need a private postcondition, you can leave it away, e.g.:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | RET return_value }>>

Note that due to combinatorial explosion and because Rocq does not have a
facility to declare such notation in a compositional way, not *all* variants of
this notation exist: if you have binders before the [RET] (which is very
uncommon), you must have a private postcondition (it can be [True]), and you
must have [∀∀] and [∃∃] binders (they can be [_: ()]).

For an example for how to prove and use logically atomic specifications, see
[iris_heap_lang/lib/increment.v].

*)

(* This warning is misleading for Hoare triple style notation where the first
terminal can also occur in the middle of a notation. *)
Local Set Warnings "-closed-notation-not-level-0".

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else.

For the non-atomic post-condition, we use an [option PROP], combined with a
[-∗?]. This is to avoid introducing spurious [True -∗] into proofs that do not
need a non-atomic post-condition (which is most of them). *)
Definition atomic_ewp `{!osirisGS Σ} `{Observe A V} {X} {TA TB TP : tele}
  (m: micro V X) (* computation *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f: TA → TB → TP → A) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : A → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            imp m {{ Φ }}.

(** We avoid '<<{'/'}>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!osirisGS Σ} {TA TB TP : tele}.
  Notation iProp := (iProp Σ).
  Context `{Observe A V}.
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → A).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_ewp_seq {X} e E α β POST f :
    atomic_ewp (X:=X) e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ imp e {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (imp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros (z) "Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_ewp_seq_step {X} (e : micro V X) E α β POST f :
    TCEq (is_ewp_case e) WPStep →
    atomic_ewp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ imp e {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (imp_step_fupd ⊤ ⊤ _ _ (∀.. y : TB, _)
      with "[$HΦ //]"); first done.
    iApply (atomic_ewp_seq with "H Hα").
    iIntros "%y Hβ %z Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_ewp_atomic {X} (e : micro V X) E α β POST f
      `{!thread_step.Atomic e}
      `{!TCEq (to_eff e) None}
      `{!TCEq (to_join e) None} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ imp e @ ∅ {{ Φ }}) -∗
    atomic_ewp e E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros "%y Hβ %z Hpost".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_ewp_atomic {X} (e : micro V X) E
      (α : [tele] → iProp) (β : [tele] → TB → iProp)
      (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → A)
      {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ imp e {{ Φ }}) -∗
    atomic_ewp e E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_imp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply imp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  (** An atomic update may be weakened in its continuation. Iris seals
      [atomic_update] and keeps its introduction rule local, so this goes
      through [iAuIntro] rather than through the fixpoint directly: reintroduce
      the update with the old one as the coinductive invariant, unfold that one
      into an accessor ([aupd_aacc]), and weaken the accessor
      ([atomic_acc_wand]).

      The wand must be persistent: an atomic update may be accessed any number
      of times before it commits, and each access needs it again.

      This is what lets an intermediate caller hand its client's update to a
      callee whose private postcondition it wants to keep — see [findc] in
      examples/proofs/UnionFind. *)
  Lemma atomic_update_mono Eo Ei α β (Φ1 Φ2 : TA → TB → iProp) :
    □ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_update Eo Ei α β Φ1 -∗
    atomic_update Eo Ei α β Φ2.
  Proof.
    iIntros "#HΦ HAU". iAuIntro.
    iApply (atomic_acc_wand with "[] [HAU]"); last by iApply aupd_aacc.
    iSplit; [by iIntros "$" | iApply "HΦ"].
  Qed.

  Lemma atomic_ewp_mask_weaken {X} (e : micro V X) E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_ewp e E1 α β POST f -∗ atomic_ewp e E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_ewp_inv {X} (e : micro V X) E α β POST f N I :
    ↑N ⊆ E →
    atomic_ewp e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_ewp e E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
