From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris.weakestpre Require Import weakestpre.
From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import arith.

Context `{!osirisGS_gen hlc Σ}.

Definition add_spec vadd : iProp Σ :=
  ∀ (x : Z),
    ⌜0 <= x⌝%Z →
    WP call vadd #x
    {{ λ v,
        ∀ (y: Z),
          ⌜0 <= y⌝%Z →
        WP call v #y {{ λ res, ⌜res = #(x + y)%Z⌝ }} }}.

Definition mult_spec vmult : iProp Σ :=
  ∀ (x: Z),
    ⌜0 <= x⌝%Z →
    WP call vmult #x
       {{ λ v, ∀ (y: Z),
             ⌜0 <= y⌝%Z →
             WP call v (encode y) {{ λ res, ⌜res = #(x * y)%Z⌝ }} }}.

Local Notation "'Spec'  'of'  'the'  'addition.'" :=
  (add_spec _)
  (only printing).

Local Notation "'Spec'  'of'  'the'  'multiplication.'" :=
  (mult_spec _)
  (only printing).

Definition trivial_spec: val → iProp Σ := λ v, ⌜ True ⌝%I.
Definition is_equal e : val → iProp Σ := λ v, ⌜v = #e⌝%I.

(* Integer representations do not matter for now. *)
Axiom int_representable:
  forall (i: Z), (int.min_signed ≤ i ≤ int.max_signed)%Z.


(* The specification of [Add] will be proven several times. *)

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
     1. to provide teh required specs for the environment;
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
                   ?δη ?k)
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
      iIntros (* vmult *) "(#Hadd&#Hmult&_)".
      iIntros(i1 H1). wp_call. iIntros(i2 H2). wp.
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
        (* TODO: simplify after simplification get fixed. *)
        wp_par.
        { (* [λ y, 1 + y] *) iIntros (vpartial) "H". iExact "H". }
        { (* [add x (y - 1)]. *)
          wp_par.
          { wp_use "Hadd"; iPureIntro; exact H1. }
          - by wp_set_postcondition.
          - iNext. iIntros (vpadd ?) "Hadd_partial ->".
            wp_use "Hadd_partial".
            wp. iPureIntro. lia. }
        { iNext. iIntros (vadd1 ?) "Hadd1 ->".
          wp.
          iSpecialize ("Hadd1" $! (i1 + (i2 - 1))%Z NotStuck top).
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
      iIntros (* vadd *) "(#Hadd&#Hmult&_)".
      iIntros (i1 H1). wp_call.
      iIntros(i2 H2). wp.
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
            { (* [y - 1]. *)
              by wp_set_postcondition. }
            { iNext. iIntros (vmult_part ?) "Hmult_part ->".
              wp. wp_use "Hmult_part".
              iPureIntro. lia. } }
          { (* Finish the application of [add]. *)
            iNext. iIntros (vadd_part ?) "Hadd_part ->".
            wp.
            unshelve iSpecialize ("Hadd_part" $! (i1 * (i2 - 1))%Z _).
            { apply Ztac.mul_le; lia. }
            iApply (wp_covariant with "Hadd_part").
            iIntros (?->).
            iPureIntro. do 2 f_equal.
            lia. } } } }
    done. }
  lazymatch goal with
  | |- context [VCloRec η ?rbds "add"] =>
      generalize (VCloRec η rbds "add")
  end; intros vadd.
  lazymatch goal with
  | |- context [VCloRec η ?rbds "mult"] =>
      generalize (VCloRec η rbds "mult")
  end; intros vmult.
  iDestruct "H" as "(#Hadd & #Hmult & _)".
  wp_continue.

  wp_par;
    [ wp_use "Hadd"; done
    | wp_use "Hadd";
      [ done | iIntros (vadd_part) "Hadd_part"; wp; by iApply "Hadd_part" ]
    | ].
  iNext. iIntros (vadd_part ?) "Hadd_part ->". wp.
  iSpecialize("Hadd_part" $! _ _).
  iApply (wp_covariant with "Hadd_part").
  Unshelve. 2: lia.
  iIntros (?->). wp.
  wp_specify "i3" (is_equal #3); first done.
  iIntros (i3) "#Hi3". wp_continue.

  repeat wp_par.
  { wp_use "Hmult"; first done.
    iIntros (vmult_part) "Hmult_part".
    iSpecialize ("Hmult_part" $! _ _).
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
  { iNext. iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iNext. iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). by wp_set_postcondition. }
  { iNext. iIntros (v1 ?) "H1 ->". wp.
    iSpecialize ("H1" $! _ _).
    iApply (wp_covariant with "H1").
    iIntros (?->). wp. wp_continue.

    wp_module_spec. }

  Unshelve.
  all: done.

  Restart.

  (* TODO: This time, we would like to generalize the variables ["add"] and
           ["mult"]. *)

Admitted.
