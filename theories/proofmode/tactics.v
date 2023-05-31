From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.

(* -------------------------------------------------------------------------- *)

(* [Ltac] helpers to deal with value abstraction. *)

Tactic Notation "oAbstract" constr(s1) ident(i1):=
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2) :=
  oAbstract s1 i1;
  oAbstract s2 i2.

(* [oCall] behaves in the same way that wp_call does, except that it abstracts
   the required closures.
   It is defined as a notation so that it is easy to ask for more idents (Ltac
   cannot take a list of idents as argument for a tactic). *)
Tactic Notation "oCall" constr(s1) ident(i1):=
  with_strategy transparent [call] unfold call; simpl (bind _ _);
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end;
  wp.
Tactic Notation "oCall" constr(s1) ident(i1) constr(s2) ident(i2) :=
  with_strategy transparent [call] unfold call; wp;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s2] =>
      generalize (VCloRec η bds s2); intro i2
  end.

(* [oSpecify] is used to provide the user the possibility to provide
   specifications for variables which are about to be added to the environment
   through [dconcatenating].
   The tactic notation only works for two arguments, as it is what is required
   here. If it works, it should be moved to [proofmode/specifications.v].
   Note: [dconcatenating] only takes two arguments now (the continuation is
         always ret). *)
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) constr(H1) ident(i1)
       constr(n2) constr(spec2) constr(H2) ident(i2) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (dconcatenating ?δ _) _) =>
      let v1 := eval cbn in (δ !!! n1) in
        let v2 := eval cbn in (δ !!! n2) in
          let hyps := eval cbn in (foldr String.append "" [H1; H2]) in
            iApply
              (assumming_list [
                    spec1 v1;
                    spec2 v2
              ]);
                                  [ by eauto using intuitionistically_persistent
                                  | (* A Specification is persistent. *) iModIntro;
                                    (* Upon proving the addition, one can have access to Löb-like IH. *)
                                    iIntros hyps
                                  | iModIntro; iIntros hyps
                                  | iIntros H1;
                                    iIntros H2;
                                    oAbstract n1 vadd
                                              n2 vmult;
                                    wp_continue]
  end.
