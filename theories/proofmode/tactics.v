From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.weakestpre Require Import weakestpre.

(* -------------------------------------------------------------------------- *)

(* [Ltac] helpers to deal with value abstraction. *)

Tactic Notation "oAbstract" constr(s1) ident(i1):=
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  | |- context [EnvCons s1 (VClo ?η ?e) _] =>
      generalize (VClo η e); intro i1
  end.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2) :=
  oAbstract s1 i1;
  oAbstract s2 i2.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2)
       constr(s3) ident(i3) :=
  oAbstract s1 i1;
  oAbstract s2 i2
            s3 i3.
Tactic Notation "oAbstract"
       constr(s1) ident(i1)
       constr(s2) ident(i2)
       constr(s3) ident(i3)
       constr(s4) ident(i4):=
  oAbstract s1 i1
            s2 i2;
  oAbstract s3 i3
            s4 i4.

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
   through [ret_dconcat].
   The tactic notation only works for two arguments, as it is what is required
   here. If it works, it should be moved to [proofmode/specifications.v].
   Note: [ret_dconcat] only takes two arguments now (the continuation is
         always ret). *)
Local Ltac oSpecify_intros lnames :=
  let hyps := eval cbn in (foldr String.append "" lnames) in
  iIntros hyps.

Local Ltac oSpecify_assume lspecs lnames lhyps δ :=
  let specs :=
    eval cbn in (
               foldr
                 (λ '(spec, name) (res: list (iProp _)),
                   let value := δ !!! name in
                   spec value :: res)
                 [] (combine lspecs lnames)
             )
    in
    iApply (assumming_list specs);
      first (by eauto using intuitionistically_persistent);
      (try iModIntro);
      oSpecify_intros lhyps.

Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1] [n1] [H1] δ;
      last ( oAbstract n1 i1 ;
             wp_continue)
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2] [n1; n2] [H1; H2] δ;
      last ( oAbstract n1 i1
                       n2 i2;
             wp_continue)
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3] [n1; n2; n3] [H1; H2; H3] δ;
      last ( oAbstract n1 i1
                       n2 i2
                       n3 i3;
             wp_continue)
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3)
       constr(n4) constr(spec4) ident(i4) constr(H4) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3; spec4]
                      [n1; n2; n3; n4]
                      [H1; H2; H3; H4]
                      δ;
      last ( oAbstract n1 i1
                       n2 i2
                       n3 i3
                       n4 i4;
             wp_continue)
  end.
