From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import simple_examples.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Section TypesExamples.
  Inductive my_nat :=
  | O'
  | S' (n: my_nat).

  Definition encode_my_nat_aux : my_nat -> val :=
    fix go m :=
      match m with
      | O' => VConstant "O"
      | S' n =>
          VData "S" (VTuple (VCons (go n) VNil))
      end.

  Global Instance encode_my_nat : Encode my_nat :=
    {| encode := encode_my_nat_aux |}.
End TypesExamples.

(* -------------------------------------------------------------------------- *)

Ltac wp_prove_spec :=
  iExists _;
  by (iSplit;
      [ done | repeat (iSplit; first (iExists _; iSplit; done))] ).

(* -------------------------------------------------------------------------- *)

Section SpecsExample.
  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Specifications for the module [Recursion]. *)

  Definition infinite_spec : val -> iProp Σ :=
    λ f,
      (□
         ∀ (n: my_nat),
           WP call f #n
              {{ λ res,
                  match n with
                  | O' => ⌜ res = #0 ⌝
                  | _ => ⌜ False ⌝
                  end }})%I.

  Fixpoint my_nat_to_nat (n: my_nat) :=
    match n with
    | O' => O
    | S' n => S (my_nat_to_nat n)
    end.
  Fixpoint nat_to_my_nat (n: nat) :=
    match n with
    | O => O'
    | S n => S' (nat_to_my_nat n)
    end.

  Definition nat_to_int_spec (f : val) : iProp Σ :=
    □ ∀ (n : my_nat),
    WP call f #n {{ λ res, ⌜ res = #(my_nat_to_nat n) ⌝ }}.

  Definition int_to_nat_spec (f : val) : iProp Σ :=
    □ ∀ (i : nat),
    ⌜Nat.le O i ∧ representable i⌝ →
    WP call f #i {{ λ res, ⌜ res = #(nat_to_my_nat i) ⌝ }}.

  Definition Recursion_specs :=
    [
      ("infinite", infinite_spec) ;
      ("nat_to_int", nat_to_int_spec) ;
      ("int_to_nat", int_to_nat_spec)
    ].
  Definition Recursion_spec :=
    λ v, (□ (module_spec Recursion_specs) v)%I.

  (* ------------------------------------------------------------------------ *)
  (* Specifications for the module [Counter]. *)

  Definition is_counter (n : nat) (v : val) : iProp Σ :=
    ∃ (ℓ : loc), ⌜v = #ℓ⌝ ∗ ℓ ↦ #n.

  Definition init_spec (vinit : val) : iProp Σ :=
    □ WP call vinit #() {{ λ res, is_counter O res }}.

  Definition get_spec (vget : val) : iProp Σ :=
    □ ∀ (v : val) (n : nat),
    is_counter n v -∗ WP call vget v {{ λ res, ⌜res = #n⌝ ∗ is_counter n v }}.

  Definition incr_spec (vincr : val) : iProp Σ :=
    □ ∀ (v : val) (n : nat),
    is_counter n v -∗
    WP call vincr v {{ λ res, ⌜res = VUnit⌝ ∗ is_counter (S n) v }}.
  Definition set_spec (vset : val) : iProp Σ :=
    □ ∀ (v : val),
    WP call vset v {{
          λ res,
            ∀ (n m : nat),
            is_counter n v -∗
            WP call res #m {{ λ res, ⌜res = VUnit⌝ ∗ is_counter m v }} }}.

  Definition Counter_specs : spec val :=
    SpecModule
      Auto
      [
        ("init", SpecImpure NoAuto init_spec) ;
        ("get", SpecImpure NoAuto get_spec) ;
        ("incr", SpecImpure NoAuto incr_spec) ;
        ("set", SpecImpure NoAuto set_spec)
      ]
      emp%I.

  Definition Counter_spec : val → iProp Σ :=
    λ v, (□ satisfies_spec Counter_specs v)%I.

  (* ------------------------------------------------------------------------ *)

  Definition Examples_spec :=
    [
      ("Recursion", Recursion_spec) ;
      ("Counter", Counter_spec)
    ].
End SpecsExample.

Lemma solve_encode_O : #O' = VConstant "O".
Proof. reflexivity. Qed.
Lemma solve_encode_S v (n: my_nat) :
  #n = v →
  #(S' n) = VData "S" $ VTuple1 v.
Proof.
  intros<-.
  reflexivity.
Qed.

Lemma solve_encode_decode n :
  #n = encode_my_nat_aux n.
Proof. reflexivity. Qed.


Local Hint Resolve
      solve_encode_O
      solve_encode_S : encode.

(* -------------------------------------------------------------------------- *)
(* Staging area: Ltac and Notations. *)

(* Useful Ltac tactics. *)
Ltac prove_counter := iSplit;
                      [ by equality
                      | iExists _; iSplit ; [ equality | iFrame ] ].
Ltac call := @oCall unfold; wp_bind; wp_continue.

(* -------------------------------------------------------------------------- *)

Section ProofExamples.
  Context `{!osirisGS Σ}.

  (* This proof uses variables in the context instead of an explicit environment
     [η] to the goal below. This is thought to be easier to use in the proof of
     foreign modules. *)
  Variables (η : env)
            (Hη_eq: lookup_name η "=" = Ret Stdlib__eq)
            (Hη_add: lookup_name η "+" = Ret Stdlib__add)
            (Hη_sub: lookup_name η "-" = Ret Stdlib__sub)
            (Hη_le: lookup_name η "<=" = Ret Stdlib__le)
            (Hη_ref: lookup_name η "ref" = Ret Stdlib__ref)
            (Hη_load: lookup_name η "!" = Ret Stdlib__load)
            (Hη_store: lookup_name η ":=" = Ret Stdlib__store)
            (representable_0 : representable 0).

  Goal
    ⊢ WP eval_mexpr η _Examples {{ module_spec Examples_spec }}.
  Proof using Hη_sub Hη_store Hη_ref Hη_load Hη_le Hη_eq Hη_add
    osirisGS0 representable_0 Σ η.

    (* ---------------------------------------------------------------------- *)
    (* The OCaml program begins with the [Recursion] module.  The elements of
       the module will be evaluated one by one into values. Then, the module
       will be built as an environment binding variables to the
       aforementioned values.  *)

    (* Use [wp], [wp_continue] and [wp_bind] until ["infinite"] is added to the
       environment. *)
    wp until "infinite"!.
    (* Now, let us prove that "infinite" satisfies its specification. *)
    oSpecify "infinite" infinite_spec vinfinite "#Hinfinite".
    { (* As the function is recursive, there is a Löb-induction-related
         hypothesis already available in the context. *)
      iIntros "!>" ([|n]);
        oCall "infinite" vinfinite; do 2 (wp_bind; wp_continue);
        first equality.
      change (VData _ _) with #(S' n). (* TODO: get rid of this line. *)
      wp_use "Hinfinite". }

    (* [infinite] is followed by [nat_to_int] in OCaml. *)
    (* One can add '!' after [oSpecify] to fast-forward to the targeted
       bindings (it uses [wp until _ !] under the hood). *)
    oSpecify "nat_to_int" nat_to_int_spec vnat_to_int "#Hnat_to_int" !.
    { iIntros "!>"([|n]);
        oCall "nat_to_int" f; do 2 (wp_bind; wp_continue);
        first done.
      wp_bind. wp_use "Hnat_to_int".
      iIntros(?->). wp; equality. }

    (* Finally, [nat_to_int] is followed by [int_to_nat] in OCaml. *)
    oSpecify "int_to_nat" int_to_nat_spec vint_to_nat "#Hint_to_nat" !.
    { iIntros (i) "!> [%Hle %Hrepresentable]".
      oCall "int_to_nat" vint_to_nat;
        do 2 (wp_bind; wp_continue);
        destruct (decide (i = O)) as [-> | n].
      { change (Z.of_nat O) with 0%Z.
        rewrite eq_repr_repr; [ by wp | done | done ]. }
      { rewrite eq_repr_repr; [ | done | done ].
        replace (i =? 0) with false by lia.
        wp; wp_bind.
        destruct i as [|j] eqn:Ei;
          wp_use "[Hint_to_nat]"; first by destruct n.
        2: {
          unshelve iPoseProof ("Hint_to_nat" $! j _) as "#h".
          { (* j is positive and representable. *)
            unfold representable in *. split; lia. }
          replace (VInt (repr (S j - 1))) with #j; last first.
          { unfold encode, Encode_nat. do 2 f_equal. lia. }
          iClear "Hinfinite Hnat_to_int Hint_to_nat".
          iApply "h". }
        { exfalso; by apply n. }
        { iIntros (?->).
          wp. iPureIntro; reflexivity. }

        (* The goal resolved with [exfalso] contained an unresolved
           post-condition. We provide a dummy one below. *)
        Unshelve.
        1: exact (λ _, emp%I). } }

    (* Every binding of the module [Recursion] has been proven.  Therefore,
       [wp_module_spec] is enough to prove the spec of [Recursion]. *)
    oSpecify "Recursion" Recursion_spec vRecursion "#HRec" !.
    { iModIntro; wp_module_spec. }
    (* Now that the module has been proven, these specs can be forgotten. *)
    iClear "Hnat_to_int Hint_to_nat Hinfinite".
    clear vinfinite vint_to_nat vnat_to_int.

    (* ---------------------------------------------------------------------- *)
    (* Specification of the module [Counter]. *)

    oSpecify "init" init_spec vinit "#Hinit" !.
    { iIntros "!>".
      @oCall unfold; wp_bind; wp_continue.
      wp_alloc ℓ "[Hℓ _]".
      iExists ℓ.
      iSplit; first equality.
      by cbn. }

    oSpecify "get" get_spec vget "#Hget" !.
    { iIntros "!>"(? nc) "(%ℓ&->&Hℓ)".
      call. wp_load "Hℓ". prove_counter. }

    oSpecify "incr" incr_spec vincr "#Hincr" !.
    { iIntros "!>" (? n) "(%ℓ&->&Hℓ)".
      call. wp_load "Hℓ". wp_store "Hℓ".
      replace (VInt (repr (n + 1))) with (#(S n)); last first.
      { simpl. do 2 f_equal; lia. }
      prove_counter. }

    oSpecify "set" set_spec vset "#Hset" !.
    { iIntros "!>" (vc). call.
      iIntros (n m) "(%ℓ&->&Hℓ)". call.
      wp_store "Hℓ". prove_counter. }

    oSpecify "Counter" Counter_spec vCounter "#HCounter"!.
    { iModIntro; wp_prove_spec. }
    iClear "Hinit Hincr Hget Hset"; clear vinit vget vset vincr.

    (* ---------------------------------------------------------------------- *)
    (* ---------------------------------------------------------------------- *)
    (* Tests using the above-defined modules. *)

    (* Justification for [val_as_struct_total] and [lookup_name_total]: what
       should we do it they did not.

       The specifications cannot stay as is for seeral reasons: [simp] assumes
       that every goal of the form [lookup_path _ = Ret _] can be solved, while
       the elements of the modules are not available to the outside world. Thus,
       one needs to logically open the modules tobe able to use them. This means
       destructing the modules specifications.
       The reason why the specifications should be destroyed is mainly to unpack
       existential values corresponding to the above paths. Note that
       [simp] could not perform these destructions on-the-fly as it does not
       have access to the Iris context in which the specs live.

       However, the specifications should be reformed afterwards... as the
       specification of the file (seen as a module) requries those.

       In this example, the specifcation of [Recursive] is
       persistent. Therefore, it is possible to duplicate it and destruct one of
       the copies. The specification of [Counter] is not entirely persistent,
       but part of it is. Therefore, it is possible to split the persistent part
       from the rest and copy it. The non-persistent part should not disappear
       (each time it is used by a function of [Counter], it will be given back
       to the user). At the end of the module (ie. file), the sepcification of
       [Counter] can be proven again.


       (* Destruction of ["HRec"]. *)
       iPoseProof "HRec" as "HRec'".
       unfold Recursion_specs at 1;
       unfold module_spec,module_spec_list at 1; simpl.
       iDestruct "HRec" as "(%ηRec&->&
                            (%vinfinite&%Hlookup_infinite&#Hinifinite)&
                            (%vnat_to_int&%Hlookup_nat_to_int&#Hnat_to_int)&
                            (%vint_to_nat&%Hlookup_int_to_nat&#Hint_to_nat)&_)".
     *)

    (* The following line avoids to unfold [encode] with [cbn]. It should be
       able to move up at the beginning of the file. It is not currently the
       case at it breaks the tactic [equality].  *)
    Local Arguments encode _ : simpl never.
    Local Ltac counter_init := oSpec' "init" from "HCounter"; iIntros (vc) "Hc";
                               wp; wp_continue.
    Local Ltac counter_incr := oSpec' "incr" from "HCounter" with "[$]";
                               iIntros(?)"[->Hc]".
    Local Ltac counter_get := oSpec' "get" from "HCounter" with "[$]";
                              iIntros (?)"[->Hc]"; wp; wp_continue.

    (* Instead of opening existentials corresponding to [Recursion], we use
       [is_module], which is a trick introduced in
       [theories/proofmode/tactics.v] *)
    oModule vRecursion.

    (* ---------------------------------------------------------------------- *)

    (* The constant [twelve] is defined. *)
    wp skip "twelve".

    (* ---------------------------------------------------------------------- *)

    (* The constant [twelve] is defined.  In this let-binding, a counter is
       instantiated.  Then, a loop is run to increase the counter twelve times.
       Note : two calls to [Counter.get] are also performed. *)
    change VUnit with #tt. (* TODO: get rid of me. *)

    (* Initialize the counter and eliminate the first call to [Counter.get]. *)
    counter_init. counter_get.

    (* Small loop.  In order to prove the loop with the rest of the program as
       continuation, one can define an invariant in the form of a predicate over
       the loop index, and prove the preservation of said predicate by the body
       of the loop. *)

    oLoopPos 1%nat 12%nat (λ i, ∃ n, ⌜i = S n⌝ ∗ is_counter n vc)%I with "[Hc]" "[]".

    (* Proof that the invariant holds before the execution of the loop. *)
    { iExists O. iSplit; [ equality | iExact "Hc" ]. }

    (* Proof that the invariant is indeed preserved by the loop. *)
    { iIntros "!>" (i Hi1 Hi2) "(%ni&->&Hc)".
      wp. counter_incr.
      iExists _; iSplit; [ equality | iExact "Hc" ]. }

    (* retrive the invariant after the loop and continue the proof. *)
    iIntros "(%n&%Heq&Hc)".
    assert (n = 12%nat) as -> by lia; clear Heq.
    wp. wp_bind.

    (* Final call to [Counter.get]. *)
    counter_get.

    (* ---------------------------------------------------------------------- *)

    (* The constant [twelve_nat] is defined. *)
    wp skip "twelve_nat". wp_bind.

    (* ---------------------------------------------------------------------- *)
    (* Now, some conversion functions of [Recursion] are called. *)

    (* Before the environment gets extended with [twelve_nat'], its body needs
       to be evaluated. It is a function call.
       The function is present in the module [Recursion].
       One can use the tactic notation [oSpec] to fetch the Iris specification
       from ["HRec"] of the function and apply it. *)
    change (VInt (repr 12)) with #12%nat. (* TODO: erase me. *)
    oSpec "int_to_nat" from "HRec" with "[]".
    (* Proof of the precondition of [Rrecursion.int_to_nat]. *)
    {  iPureIntro. split; [ lia | representable ]. }
    iIntros (?->).
    wp_bind. wp_continue. wp_bind.

    lazymatch goal with
    | |- context [call _ ?v] => (* TODO: erase me. *)
        repeat (change v with #(S' $ S' $ S' $ S' $
                                   S' $ S' $ S' $ S' $
                                   S' $ S' $ S' $ S' $ O'))
    end.
    (* Ditto. *)
    oSpec "nat_to_int" from "HRec".
    iIntros (?->).
    wp_bind. wp_continue. wp_bind.

    lazymatch goal with
    | |- context [call _ ?v] => (* TODO: erase me. *)
        change v with #(S' $ S' $ S' $ S' $
                           S' $ S' $ S' $ S' $
                           S' $ S' $ S' $ S' $ O')
    end.
    (* Ditto. *)
    oSpec "nat_to_int" from "HRec".
    iIntros (?->).
    wp_bind. wp_continue.

    (* The evaluation of the module-expressions is over. One now needs to prove
       that the obtained value satisfies its specification. As the only required
       proofs are about [Counter] and [Recursion], and as they have been
       verified above, [wp_module_spec] can finish the proof. *)
    wp_module_spec.
  Qed.

End ProofExamples.
