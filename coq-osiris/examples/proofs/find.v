From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_find.

Require Import Coq.Wellfounded.Inverse_Image.

Section iris_proof.

Context `{!osirisGS Σ}.
Context `{Encode A}.

Definition listiter_invariant_spec `{Encode A} (f : val) (lsuf : list A) (m : microvx) : Prop :=
  ∀ (lpre l : list A) (I : list A → Prop) φ,
    lpre ++ lsuf = l ->
    @Spec τ[A] f (λ (X : A) (mf : microvx),
        ∀ (Xs : list A),
          (Xs ++ [X]) `prefix_of` l ->
          I Xs ->
          pure mf
            (λ v : (), I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
      I lpre ->
      pure m
        (λ (v : ()), I l)
        (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

Definition listiter_spec `{Encode A} (f : val) (l : list A) (m : microvx) : Prop :=
  ∀ (I : list A → Prop) φ,
    Spec τ[A] f (λ (X : A) (mf : microvx),
        ∀ (Xs : list A),
          (Xs ++ [X]) `prefix_of` l ->
          I Xs ->
          pure mf
            (λ v : (), I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
      I [] ->
      pure m
        (λ (v : ()), I l)
        (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

Definition scan_spec `{Encode A} ℓ (l : list A) φ (X : A) (m : microvx) : Prop :=
  ∀ (Xs : list A),
    (Xs ++ [X]) `prefix_of` l ->
    Forall (λ x, ¬ (φ x)) Xs ->
    pure m
      (λ (v :()), Forall (λ x, ¬ (φ x)) (Xs ++ [X]))
      (λ e, (∃ (x : A), e = VXData ℓ [ #x ] ∧ x ∈ l ∧ φ x) ∧ Forall (λ x, ¬ (φ x)) Xs).

Definition find_spec `{Encode A} (l : list A) (pred : val) (m : microvx) : iProp Σ :=
  ∀ (φ : A -> Prop),
    (* Assuming that [pred] is a pure function such that
       [pred x] reflects the pure proposition [φ x]*)
    ⌜Spec τ[A] pred (λ x mx, pure mx (λ (P : Prop), P <-> φ x) ⊥)⌝ -∗
    (* Calling [find l pred] returns an option [o] such that
       - if [o = Some x] then [φ x]
       - if [o = None] then there is no [x] such that [φ x]. *)
    EWP m {{ ensures #o, ⌜match o with
                          | Some x => x ∈ l ∧ φ x
                          | None => Forall (λ x, ¬ (φ x)) l
                          end⌝ }}.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness *)

(* FIXME use the measure function to only have a WF condition on lists *)
#[local] Program Instance list_tuple_wf {A B} : WellFounded (B * list A) :=
  {| wf_relation := (fun x y => (length x.2 < length y.2)%nat )|}.
Next Obligation. intros; apply wf_inverse_image, lt_wf. Qed.

(* -------------------------------------------------------------------------- *)

Lemma iter_module_pure :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{ ensures m, module_spec [("find_first", λ find, iSpec τ[list A; val] find find_spec)] m }}.
Proof.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  instantiate (1 := (λ (ηδ : envs),
            ⌜∃ iter, ηδ = (("iter", iter) :: stdlib_env, [("iter",iter)]) ∧
                       @Spec τ[val; list A] iter listiter_spec⌝)%I).
  { iApply ewp_pure_wp.
    eapply (@struct_letrec τ[val; list A]) with (P := listiter_invariant_spec).
    { repeat eexists. }
    { apply list_tuple_wf. }
    { simpl.
      intros iter f l IH.
      intros lpre lsuf I φ Heql Hf HI.
      fold eval.

      eapply pure_eval_match. { pure_path. }
      pure_match.

      { pure_const. rewrite app_nil_r. apply HI. }

      rename xs' into l.
      eapply pure_seq.
      eapply (pure_EApp τ[A]). { pure_path. } { pure_path. apply eq_refl. }
      intros ? <- callsite_f Hcall_f. unfold tapp in Hcall_f.
      eapply pure_mono. { apply Hcall_f; eauto.
                          apply prefix_app. apply prefix_cons. apply prefix_nil. }
      - intros ? HI'.
        eapply (pure_EApp τ[val; list A]). { pure_path. } { pure_path. } { pure_path. apply eq_refl. }
        simpl; unfold tapp.
        intros ?? <-<- m Hm. unfold listiter_spec in Hm.
        eapply Hm; [ lia | | apply Hf | apply HI'].
        change (x :: l) with ([x] ++ l); by rewrite app_assoc.
      - intros e (Hφ & HIpre).
        split; [ | exists lpre; split ]; eauto.
        replace lpre with (lpre ++ []) at 1 by apply app_nil_r.
        apply prefix_app; apply prefix_nil. }
    intros iter Hiter.

    exists iter; split; [ apply eq_refl | ].
    eapply Spec_mono; [ apply Hiter | simpl ].
    intros f l m Hinvspec.
    unfold listiter_spec, tapp.
    intros I φ Hf HI.
    specialize (Hinvspec [] l).
    apply Hinvspec; auto. }

  iIntros (?) "(%iter & -> & %Hiter)".
  (* We now face the toplevel definition of [find_elem]. *)
  iApply (ewp_sitems_let_singleton_var
            (* We give [find_elem] the specification [find_spec]. *)
            (λ (find : val), iSpec τ[list A; val] find find_spec)).

  { (* START OF THE PROOF FROM THE PAPER *)
    (* Subgoal: Prove that [find_elem] satisfies its specification. *)
    (* Step into the function's body *)
    iApply (ewp_eval_anon τ[list A; val]).
    (* FIXME: we can't simplify here to keep a "RET #o" notation folded.
       This means we have to proceed "blind" here. *)
    (* Introduce the function's arguments. *)
    iIntros (xs pred φ Hpred).
    (* Declare and open a local module. *)
    iApply ewp_ELetOpen.
    (* Evaluate the module expression. *)
    iApply ewp_module; iApply ewp_sitems_extend;
      iIntros (?) "(%l & -> & Hl)".
    (* Finish evaluating the local module and enrich the scoping environment. *)
    iApply ewp_sitems_nil;
      iExists _; iSplitR; [ iPureIntro; reflexivity | ].

    (* We are done with the effectful part of the program, so we can drop down
       to Horus, the pure program logic. *)
    iApply ewp_pure.
    eapply pure_eval_match'_exn.
    { (* Subgoal: evaluate the scrutinee [List.iter _ _]. *)
      eapply (pure_EApp τ[val; list A]); last (simpl; unfold tapp; fold eval).
      { (* Find iter in the environment. *) pure_path. }
      2:{ (* find [l] in the environment. *) pure_path; apply eq_refl. }
      { (* Evaluate the lambda expression we pass to [iter]:
           it is a function with
           - a single argument of type [a]
           - a specification [scan_spec]. *)
          eapply (pure_eval_anon τ[A]) with (P := scan_spec l xs φ); simpl.
          unfold scan_spec; fold eval.
          (* Prove that the lambda expression satisfies its spec. *)
          intros x Xs Hpref Hforall.
          eapply pure_eval_ifthen.
          { (* Subgoal: evaluate the conditional [pred x]. *)
            eapply (pure_EApp τ[A]);
              [ pure_path | pure_path; apply eq_refl | simpl; unfold tapp ].
            (* We now connect the specs of [pred] and the lambda.
               They have the same success postcondition, so we only need
               to exploit the fact that [pred] cannot fail. *)
            intros ? -> m Hm; eapply pure_exn_mono.
            eapply Hm. contradiction. }
          - (* Case: [pred x] returned true and we learn [φ x]. *)
            intros Hx.
            apply pure_eval_raise.
            (* Evaluate the constructor [Found x]. *)
            (* TODO: better rule, even if a little ad-hoc. *)
            simpl_eval.
            apply pure_wp_Par_vals_right.
            eapply pure_wp_ret. eapply pure_wp_widen. eapply pure_wp_ret.
            simpl. pure_ret.
            (* Prove the failure postcondition of the lambda.
               That is to say, that [φ] holds for some [x ∈ xs]. *)
            split; try auto.
            exists x; split; first reflexivity.
            split; last assumption.
            eapply elem_of_prefix; last eassumption.
            apply elem_of_app; right.
            apply elem_of_list_here.
          - (* Case: [pred x] returned false and we learn [¬ φ x]. *)
            intros Hnφ.
            (* Prove the success postcondition of the lambda.
             That is to say, that [φ] does not hold over the prefix of
             [xs] we have visited so far. *)
            apply Forall_app_2; [ apply Hforall | ].
            apply Forall_singleton. apply Hnφ. }
        (* Use the spec of [iter] *)
        intros ? scan Hscan -> m Hm.
        unfold listiter_spec in Hm.
        (* Specifiy the invariant that [iter] will maintain. *)
        specialize (Hm (λ Xs, Forall (λ x, ¬ φ x) Xs)).
        apply Hm. apply Hscan. apply Forall_nil. done. }

    (* We have now finished evaluating the scrutinee of the
       [match .. with ..] expression, we move on to the branches. *)
    - (* Case 1: We returned a value, we don't get caught in the branch *)
      intros () Hforall. pure_match.
      eapply pure_eval_const.
      instantiate (1 := @None A); apply solve_encode_None; reflexivity.
      apply Hforall.

    - (* Case 2: We raised an exception, we get caught by the branch. *)
      simpl. intros ? [(x & -> & Hx) _].
      pure_match.
      apply pure_eval_data. eapply pure_evals_cons. pure_path. apply pure_evals_nil.
      exists (Some x). split; [ encode | ].
      assumption. }

  (* We conclude: update the environment to add [find_elem] to it. *)
  iIntros ([??]) "(%find & -> & Hfind)"; iApply ewp_sitems_nil; simpl.
  (* Show that the toplevel module satisfies its spec: it contains a value named
     ["find_elem"] which is specified by [iSpec find find_spec]. *)
  iExists _; iSplitR; [ iPureIntro; reflexivity | ].
  simpl; rewrite bi.sep_emp.
  iExists find. equality.
Qed.

End iris_proof.
