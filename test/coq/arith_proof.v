From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris.weakestpre Require Import weakestpre.
From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import arith.

(* -------------------------------------------------------------------------- *)

(* The current file is a sandbox to develop tactics on the specification of
   mutually recursive functions. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS_gen hlc Σ}.

(* -------------------------------------------------------------------------- *)

(* Definition of the specifications. They have to be persistent for the tactics
   to work properly. *)

Definition add_spec vadd : iProp Σ :=
  □ (∀ (x : Z),
    ⌜0 <= x⌝%Z →
    WP call vadd #x
    {{ λ v,
        ∀ (y: Z),
          ⌜0 <= y⌝%Z →
        WP call v #y {{ λ res, ⌜res = #(x + y)%Z⌝ }} }}).

Definition mult_spec vmult : iProp Σ :=
  □ (∀ (x: Z),
    ⌜0 <= x⌝%Z →
    WP call vmult #x
       {{ λ v, ∀ (y: Z),
             ⌜0 <= y⌝%Z →
             WP call v #y {{ λ res, ⌜res = #(x * y)%Z⌝ }} }}).

Definition trivial_spec: val → iProp Σ := λ v, ⌜ True ⌝%I.
Definition is_equal e : val → iProp Σ := λ v, ⌜v = #e⌝%I.

(* -------------------------------------------------------------------------- *)

(* As there is no proper notation for specifications of closures yet, I added
   the following for the goal to remain readable. *)

Local Notation "'Spec'  'of'  'the'  'addition.'" :=
  (add_spec _)
  (only printing).

Local Notation "'Spec'  'of'  'the'  'multiplication.'" :=
  (mult_spec _)
  (only printing).

(* -------------------------------------------------------------------------- *)

(* Whether or not integers are representable does not matter for now. *)
Axiom int_representable:
  forall (i: Z), (int.min_signed ≤ i ≤ int.max_signed)%Z.

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
        (prove_specify [
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


(* The specification of [Add] will be proven several times. Each attempt should
   improve the proof --- especially the way to handle mutually recursive
   functions. *)

(* -------------------------------------------------------------------------- *)

(* Sixth version: It should no longer be necessary to provide en environment [η]
                  which contains the standard library as a module. *)

(* -------------------------------------------------------------------------- *)

(* Fifth version: Once the specifications proven, the [wp] tactic should know
                  how to handle them (ie. use their spec as soon as possible,
                  and handle their partial applications automatically!). *)

(* -------------------------------------------------------------------------- *)

(* Fourth version: The process of declaring specifications should be
                   interactive. *)

(* -------------------------------------------------------------------------- *)

(* Third version: a lemma exists to better reason on mutually recursive
                  functions. *)

Lemma Add_spec3 :
    let Λ :=
    [
      ("add", add_spec);
      ("mult", mult_spec);
      ("i3", is_equal #3)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Arith {{ module_spec Λ }}.
Proof.
  intros.
  wp.

  oSpecify "add" add_spec "#Hadd" vadd
           "mult" mult_spec "#Hmult" vmult.

  (* Specification of the addition. *)
  { (* The rest of the proof is unchanged. *) admit. }

  (* Specification of the multiplication. *)
  { (* The rest of the proof is unchanged. *) admit. }

  (* The rest of the proof is unchanged. *)
Admitted.

(* -------------------------------------------------------------------------- *)

(* Second version: the values of [add] and [mult] are opacified manually at "the
                   right time". *)

Lemma Add_spec2 :
    let Λ :=
    [
      ("add", add_spec);
      ("mult", mult_spec);
      ("i3", is_equal #3)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Arith {{ module_spec Λ }}.
Proof.
  intros.
  wp.

  (* [add] and [mult] are recursively defined.
     Intuitively, one wants:
     1. to provide the required specs for the environment;
     2. to prove each spec one by one using Löb Induction.

     Although it is not the case here, it might also be necessary to provide
     external hypotheses to prove the specs.

     The following does *not* work as expected. As the [RecBinding]s take
     functions as argument and we only generalize values in the current process,
     the specs hidden behind the [▷] are unusable (and useless).
     Therefore, one should abstract the bodies of the function, and prove a spec
     for them. *)

  lazymatch goal with
  | |- environments.envs_entails
         ?Δ (wp ?s ?E
                (dconcatenating
                   (EnvCons "add" ?vadd $
                            EnvCons "mult" ?vmult $
                            EnvNil)
                   ?δη)
                ?φ) =>
      iAssert (add_spec vadd ∗ mult_spec vmult ∗ emp)%I as "(#Hadd & #Hmult & _)"
  end;
  [ (* In order to prove the assertion, we use Löb induction. *)
    iLöb as "IH";
    iDestruct "IH" as "(#Hadd&#Hmult&_)";
    iSplitL "" ; (* Proving the addition does not require prior resources. *)
    [
    | iSplitL "";
      [
      | done ]
    ]
  | (* After the specifications have been proven, abstract the addition and
       multiplication and .continue. *)
    oAbstract "add" vadd; oAbstract "mult" vmult; wp_continue ].

  { (* ---------------------------------------------------------------------- *)
    (* Proof of [add]. *)
    { iModIntro. iIntros(i1 H1).

      (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
      oCall "add" vadd "mult" vmult. wp. wp_continue.

      (* The proof can now continue as expected. *)
      iIntros(i2 H2). wp. wp_continue.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      iIntros (veq_part) "Hspec_eq".
      wp.
      iApply (wp_covariant with "Hspec_eq"). (* TODO: fix [wp_use]. *)
      iIntros (? ->).
      destruct (i2 =? 0)%Z eqn:E; wp.
      { (* [i2 = 0%Z] *)
        apply Z.eqb_eq in E as ->.
        wp_use "Hmult"; first done.
        iIntros (Hmult_part) "Hmult_part".
        iApply (wp_covariant with "[Hmult_part]").
        { iApply "Hmult_part"; done. }
        iIntros(?->).
        iPureIntro. do 2 f_equal. lia. }
      { (* [i2 != 0%Z], goal: [1 + (add x (y - 1)) == x + y] *)
        wp_par.
        { (* [λ y, 1 + y] *) iIntros (vpartial) "H". iExact "H". }
        { (* [add x (y - 1)]. *)
          wp_par.
          { wp_use "Hadd"; iPureIntro; exact H1. }
          - wp_call.
            instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I).
            by rewrite int.sub_repr_repr.
          - iIntros (vpadd ?) "Hadd_partial ->".
            wp_use "Hadd_partial".
            iPureIntro. lia. }
        { iIntros (vadd1 ?) "Hadd1 ->".
          wp.
          iSpecialize ("Hadd1" $! (i1 + (i2 - 1))%Z NotStuck top). wp.
          iApply (wp_covariant with "Hadd1").
          iIntros (?->).
          iPureIntro. do 2 f_equal. lia. } } } }

    (* ------------------------------------------------------------------ *)
    (* Proof of [mult]. *)
    { iModIntro. iIntros (i1 H1).

      (* It is during the function call to add that the environment is extended
         to include the definition of [mult].*)
      oCall "add" vadd "mult" vmult. wp_continue.

      (* The proof can now continue as expected. *)
      iIntros(i2 H2). wp. wp_continue.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      iIntros (veq_part) "Heq_part".
      wp. iApply (wp_covariant with "Heq_part").
      iIntros (?->).
      destruct (i2 =? 0)%Z eqn:E.
      { (* [i2 = 0%Z]. *) wp.
        apply Z.eqb_eq in E as ->. iPureIntro. do 2 f_equal. lia. }
      { (* [i2 != 0%Z]. *) wp.
        wp_use Stdlib__eq__spec; try done; try apply int_representable.
        clear veq_part.
        iIntros (veq_part) "Heq_part".
        wp. iApply (wp_covariant with "Heq_part").
        iIntros (?->).
        destruct (i2 =? 1)%Z eqn:E1.
        { (* [i2 = 1%Z]. *) wp.
          apply Z.eqb_eq in E1 as ->. iPureIntro. do 2 f_equal. lia. }
        { (* [i2 <> 1%Z]. *) wp.
          (* Proof that [add x (mult x (y - 1)) == x * y]. *)
          wp_par.
          { (* [λ y, add x y]. *)
            iSpecialize ("Hadd" $! i1 H1).
            wp_use "Hadd". }
          { (* [mult x (y - 1)] *)
            wp_par.
            { (* [λ y, mult x y]. *)
              wp_use "Hmult"; iPureIntro; exact H1. }
            { (* [y - 1]. *) wp_call.
              instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I).
              by rewrite int.sub_repr_repr. }
            { iIntros (vmult_part ?) "Hmult_part ->".
              wp. wp_use "Hmult_part".
              iPureIntro. lia. } }
          { (* Finish the application of [add]. *)
            iIntros (vadd_part ?) "Hadd_part ->".
            wp.
            unshelve iSpecialize ("Hadd_part" $! (i1 * (i2 - 1))%Z _).
            { apply Ztac.mul_le; lia. }
            iApply (wp_covariant with "Hadd_part").
            iIntros (?->).
            iPureIntro. do 2 f_equal.
            lia. } } } }

  wp_par;
    [ wp_use "Hadd"; done
    | wp_use "Hadd";
      [ done | iIntros (vadd_part) "Hadd_part"; wp; by iApply "Hadd_part" ]
    | ].
  iIntros (vadd_part ?) "Hadd_part ->". wp.
  iSpecialize("Hadd_part" $! _ _).
  iApply (wp_covariant with "Hadd_part").
  Unshelve. 2: lia.
  iIntros (?->). wp.
  wp_specify "i3" (is_equal #3); first done.
  iIntros (i3) "#Hi3". wp_continue.

  repeat wp_par.
  { wp_use "Hmult"; first done.
    iIntros (vmult_part) "Hmult_part".
    iSpecialize ("Hmult_part" $! _ _). wp.
    iApply (wp_covariant with "Hmult_part").
    iIntros (?->).
    wp_use "Hadd"; first done. }
  { wp_use "Hadd"; first done. }
  { wp_use "Hmult"; first done. }
  { wp_use "Hadd"; first done.
    iIntros (vadd_part') "Hadd_part'".
    iSpecialize ("Hadd_part'" $! _ _).
    iApply (wp_covariant with "Hadd_part'").
    iIntros(?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). wp. wp_continue.

    wp_module_spec. }

  Unshelve.
  all: done.
Time Qed.

(* -------------------------------------------------------------------------- *)

(* Initial version: the values of [add] and [mult] are abstracted away after
                    having proven their specifications. Unfortunately, [add]
                    (resp. [mult]) is not opaque when proving [mult]
                    (resp. [add]). *)
Lemma Add_spec :
    let Λ :=
    [
      ("add", add_spec);
      ("mult", mult_spec);
      ("i3", is_equal #3)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Arith {{ module_spec Λ }}.
Proof.
  intros.
  wp.

  (* [add] and [mult] are recursively defined.
     Intuitively, one wants:
     1. to provide the required specs for the environment;
     2. to prove each spec one by one using Löb Induction.

     Although it is not the case here, it might also be necessary to provide
     external hypotheses to prove the specs.

     The following does *not* work as expected. As the [RecBinding]s take
     functions as argument and we only generalize values in the current process,
     the specs hidden behind the [▷] are unusable (and useless).
     Therefore, one should abstract the bodies of the function, and prove a spec
     for them. *)

  lazymatch goal with
  | |- environments.envs_entails
         ?Δ (wp ?s ?E
                (dconcatenating
                   (EnvCons "add" ?vadd $
                            EnvCons "mult" ?vmult $
                            EnvNil)
                   ?δη)
                ?φ) =>
      iAssert (add_spec vadd ∗ mult_spec vmult ∗ emp)%I as "H"
  end.
  (* [_ ∗ emp] allows to better understand how the process would work with more
     functions. *)
  { iLöb as "IH".
    iSplitL "".
    (* ---------------------------------------------------------------------- *)
    (* Proof of [add]. *)
    { iRevert "IH" (* ;
        lazymatch goal with
        | |- context [VCloRec η ?rbds "mult"] =>
            generalize (VCloRec η rbds "mult")
        end *) .
      iIntros (* vmult *) "(#Hadd&#Hmult&_) !>".
      iIntros(i1 H1). wp_call. wp_continue. iIntros(i2 H2). wp. wp_continue.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      iIntros (veq_part) "Hspec_eq".
      wp.
      iApply (wp_covariant with "Hspec_eq"). (* TODO: fix [wp_use]. *)
      iIntros (? ->).
      destruct (i2 =? 0)%Z eqn:E; wp.
      { (* [i2 = 0%Z] *)
        apply Z.eqb_eq in E as ->.
        wp_use "Hmult"; first done.
        iIntros (Hmult_part) "Hmult_part".
        iApply (wp_covariant with "[Hmult_part]").
        { iApply "Hmult_part"; done. }
        iIntros(?->).
        iPureIntro. do 2 f_equal. lia. }
      { (* [i2 != 0%Z], goal: [1 + (add x (y - 1)) == x + y] *)
        wp_par.
        { (* [λ y, 1 + y] *) iIntros (vpartial) "H". iExact "H". }
        { (* [add x (y - 1)]. *)
          wp_par.
          { wp_use "Hadd"; iPureIntro; exact H1. }
          - wp_call.
            instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I).
            by rewrite int.sub_repr_repr.
          - iIntros (vpadd ?) "Hadd_partial ->".
            wp_use "Hadd_partial".
            iPureIntro. lia. }
        { iIntros (vadd1 ?) "Hadd1 ->".
          wp.
          iSpecialize ("Hadd1" $! (i1 + (i2 - 1))%Z NotStuck top). wp.
          iApply (wp_covariant with "Hadd1").
          iIntros (?->).
          iPureIntro. do 2 f_equal. lia. } } }

    iSplitL "".
    (* ------------------------------------------------------------------ *)
    (* Proof of [mult]. *)
    { iRevert "IH"(* ;
        lazymatch goal with
        | |- context [VCloRec η ?rbds "add"] =>
             generalize (VCloRec η rbds "add")
        end *) .
      iIntros (* vadd *) "(#Hadd&#Hmult&_) !>".
      iIntros (i1 H1). wp_call. wp_continue.
      iIntros(i2 H2). wp. wp_continue.
      wp_use Stdlib__eq__spec; try done; try apply int_representable.
      iIntros (veq_part) "Heq_part".
      wp. iApply (wp_covariant with "Heq_part").
      iIntros (?->).
      destruct (i2 =? 0)%Z eqn:E.
      { (* [i2 = 0%Z]. *) wp.
        apply Z.eqb_eq in E as ->. iPureIntro. do 2 f_equal. lia. }
      { (* [i2 != 0%Z]. *) wp.
        wp_use Stdlib__eq__spec; try done; try apply int_representable.
        clear veq_part.
        iIntros (veq_part) "Heq_part".
        wp. iApply (wp_covariant with "Heq_part").
        iIntros (?->).
        destruct (i2 =? 1)%Z eqn:E1.
        { (* [i2 = 1%Z]. *) wp.
          apply Z.eqb_eq in E1 as ->. iPureIntro. do 2 f_equal. lia. }
        { (* [i2 <> 1%Z]. *) wp.
          (* Proof that [add x (mult x (y - 1)) == x * y]. *)
          wp_par.
          { (* [λ y, add x y]. *)
            iSpecialize ("Hadd" $! i1 H1).
            wp_use "Hadd". }
          { (* [mult x (y - 1)] *)
            wp_par.
            { (* [λ y, mult x y]. *)
              wp_use "Hmult"; iPureIntro; exact H1. }
            { (* [y - 1]. *) wp_call.
              instantiate (1 := λ v, ⌜ v = # (i2 - 1)%Z ⌝%I).
              by rewrite int.sub_repr_repr. }
            { iIntros (vmult_part ?) "Hmult_part ->".
              wp. wp_use "Hmult_part".
              iPureIntro. lia. } }
          { (* Finish the application of [add]. *)
            iIntros (vadd_part ?) "Hadd_part ->".
            wp.
            unshelve iSpecialize ("Hadd_part" $! (i1 * (i2 - 1))%Z _).
            { apply Ztac.mul_le; lia. }
            iApply (wp_covariant with "Hadd_part").
            iIntros (?->).
            iPureIntro. do 2 f_equal.
            lia. } } } }
    done. }
  oAbstract "add" vadd
            "mult" vmult.
  iDestruct "H" as "(#Hadd & #Hmult & _)".
  wp_continue.

  wp_par;
    [ wp_use "Hadd"; done
    | wp_use "Hadd";
      [ done | iIntros (vadd_part) "Hadd_part"; wp; by iApply "Hadd_part" ]
    | ].
  iIntros (vadd_part ?) "Hadd_part ->". wp.
  iSpecialize("Hadd_part" $! _ _).
  iApply (wp_covariant with "Hadd_part").
  Unshelve. 2: lia.
  iIntros (?->). wp.
  wp_specify "i3" (is_equal #3); first done.
  iIntros (i3) "#Hi3". wp_continue.

  repeat wp_par.
  { wp_use "Hmult"; first done.
    iIntros (vmult_part) "Hmult_part".
    iSpecialize ("Hmult_part" $! _ _). wp.
    iApply (wp_covariant with "Hmult_part").
    iIntros (?->).
    wp_use "Hadd"; first done. }
  { wp_use "Hadd"; first done. }
  { wp_use "Hmult"; first done. }
  { wp_use "Hadd"; first done.
    iIntros (vadd_part') "Hadd_part'".
    iSpecialize ("Hadd_part'" $! _ _).
    iApply (wp_covariant with "Hadd_part'").
    iIntros(?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). wp. wp_continue.

    wp_module_spec. }

  Unshelve.
  all: done.
Time Qed.
