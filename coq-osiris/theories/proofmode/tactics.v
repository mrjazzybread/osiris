From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris Require Import base_logic.lib.gen_heap.

From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import simp specifications.

(* ---------------------------------------------------------------------- *)
(* Tactics to work on WPs. They mimic those on [is_safe]. *)

Lemma tac_change_goal {Σ: gFunctors} Δ (P Q : iProp Σ) :
  (P ⊢ Q) →
  environments.envs_entails Δ P →
  environments.envs_entails Δ Q.
Proof.
  intros H Henv.
  eapply coq_tactics.tac_eval; last done.
  intros Q''; subst Q''. assumption.
Qed.

(* [lem] must be of the form (P -∗ Q). Thanks to the tactic notation it can be
   lemma whose forall quantifiers have been instantiated with [_]. *)
Ltac tac_change_goal lem :=
  simple notypeclasses refine (tac_change_goal _ _ _ lem _).
Tactic Notation "tac_change_goal" uconstr(lem) := (tac_change_goal lem).

(* -------------------------------------------------------------------------- *)

(* Tactics to move forward in the proof. *)

(* NOTE:
 * - The performance of the calls to [cbn] made by the functions below
 *   crucially depends on adequate unfolding settings being set for terms
 *   that can appear in the goal, using the [Arguments] command.
 *   (Such as [eval] and definition it uses transitively or combinators
 *   of the monad.)
 *
 * TODO:
-* - we still reduce too much:
 *   + we reduce under continuations;
 *   + because we reduce the whole Coq context, we reduce all the Iris
       hypotheses!
 * TODO: just apply [wp_simp] and reduce in the subgoal [simp m ?m'].

 * TODO: letting [simp] reduce [Stop CEval _ _] is not satisfactory,
         as it deprives us from the opportunity of applying the lemma
         [wp_eval] and eliminating a [later] modality. So, the lemma
         [wp_eval] should be applied first, when applicable.

 * TODO: blindly applying [wp_bind] is dangerous, as it will duplicate
         the continuation (therefore the entire rest of the proof!)
         if the left-hand side of the sequence involves a conditional
         construct. A more cautious approach is to use
         [wp_bind_binary] and silently apply this lemma
         only if we are able to silently solve its first premise. *)

Ltac wp_simp :=
  iApply wp_simp; first by simp_really.

Ltac wp_step :=
  (* The lazymatch stills misses a few cases and should be completed. *)
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ret _) _) =>
      tac_change_goal (wp_ret _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (try _ _ _) _) =>
      tac_change_goal (wp_try _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) (ret _) _ _) _) =>
      tac_change_goal (wp_par_ret_ret _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par _ (ret _) _ _) _) =>
      tac_change_goal (wp_par_ret_right _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (Par (ret _) _ _ _) _) =>
      tac_change_goal (wp_par_ret_left _ _ _ _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (stop CEval _) _) =>
      first [ tac_change_goal (wp_eval_ret _ _ _ _ _ _)
            | tac_change_goal (wp_eval _ _ _ _ _ _ _) ]
  | |- environments.envs_entails _ (wp _ _ (choose ok ?m2) _) =>
      tac_change_goal (wp_choose_ok _ _ _ _)
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      fail "[bind] is no longer simplified by [wp_step]."
  | _ =>
      fail "The goal must be a wp to apply [wp_step]."
  end.

Ltac wp_cbn_term m :=
  lazymatch m with
  | Par ?m1 ?m2 ?k ?z =>
      let m'1 := wp_cbn_term m1 in
      let m'2 := wp_cbn_term m2 in
      uconstr:(Par m'1 m'2 k z)
  | Stop ?c ?x ?k ?z =>
      let x' := eval cbn in x in uconstr:(Stop c x' k z)
  | _ => let m' := eval cbn -[encode] in m in uconstr:(m')
  end.

Ltac wp_cbn :=
  lazymatch goal with
  | |- environments.envs_entails _ $ wp _ _ ?m _ =>
      let m' := wp_cbn_term m in
      first [
          progress change m with m'
        | fail "[wp_cbn] No progress to be made." ]
  | _ => fail "[wp_cbn] WP goal expected."
  end.

Local Ltac wp_progress :=
  first [
      lazymatch goal with
      | |- environments.envs_entails _ $ wp _ _ (eval _ _) _ =>
          rewrite eval_eval'; try progress wp_cbn
      end
    | wp_cbn (* TODO: better control the reduction strategy. *)
    | progress wp_simp
    | cbn beta
    ].

Ltac wp_concat :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ ?m _) =>
      lazymatch m with
      | bind (ret_concat ?η ?δ) ?k =>
          with_strategy transparent [ret_concat]
                        (change (bind (ret_concat η δ) k) with (k (η ++ δ)))
      | ret_concat ?η ?δ =>
          with_strategy transparent [ret_concat]
                        (change (ret_concat η δ) with (ret (η ++ δ)))

      | bind (ret_dconcat ?δ' ?ηδ) ?k =>
          with_strategy transparent [ret_dconcat]
                        (change (bind (ret_dconcat δ' ηδ) k) with (k (dconcat δ' ηδ)))
      | ret_dconcat ?δ' ?ηδ =>
          with_strategy transparent [ret_dconcat]
                        (change (ret_dconcat δ' ηδ) with (ret (dconcat δ' ηδ)))
      | _ => fail "There is no concatenation here."
      end
  | _ => fail "There is no concatenation here."
  end.

Local Ltac wp_setup :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails ?Δ $ wp _ _ _ _ =>
      let Δ :=
        eval cbn in (environments.env_to_list
                       (environments.env_intuitionistic Δ)) in
      let rec lookforme l :=
        lazymatch constr:(l) with
        | [] => idtac
        | (satisfies_spec ?Λ0 ?v) :: ?t =>
            let Λ := eval hnf in Λ0 in
            lazymatch constr:(Λ) with
            | SpecModule Auto ?l ?P =>
                lazymatch goal with
                | _ : pure_spec Λ0 v |- _ => idtac
                | _ =>
                    iPoseProof ((satisfies_pure_spec Λ v) with "[$]")
                    as "%";
                    change Λ with Λ0 in *
                end
            | _ => idtac
            end ; lookforme t
        | _ :: ?t => lookforme t
        end in
      lookforme Δ
  end
.

Ltac wp :=
  wp_setup;
  repeat
    (first [
          (* 1. Try to eliminate a later or take a step. *)
          lazymatch goal with
          | |- environments.envs_entails _ (bi_later _) => iNext
          | _ => wp_step
          end
        | (* 2. Try to simplify the proof goal using [wp_progress].*)
          progress wp_progress
        | (* Otherwise, do nothing ([repeat] will stop). *)
          idtac
    ]).
  (* ;normalize.
    (* TODO [wp] should NOT normalize the entire goal *) *)

(* [wp_bind] can be applied when the goal is of the form [WP bind m m' {{ _ }}].
   It bahaves differently depending on the term [m]:
   - if [m] can be simplified into [ret v], then [bind] can reduce: do it;
   - otherwise, apply the lemma [wp_bind]. *)
Ltac wp_bind :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (bind _ _) _) =>
      first [
          (* [wp_simp] will reduce the bind if it can. *)
          progress wp_simp; try once wp_bind
        | tac_change_goal (wp_bind _ _ _ _ _) ]
  | _ => fail "[wp_bind] should only be applied to goals of the form [WP bind _ _ {{ _ }}]."
  end; wp.

(* -------------------------------------------------------------------------- *)

(* We want symbolic execution to stop at breakpoints, that is, when the
   environment is extended with new bindings. This gives the user a chance
   to prove specifications about these bindings using [wp_specify]. *)

(* The tactic [wp_continue] moves past a breakpoint and invokes [wp]
   to continue simplifying the goal. *)

(* The tactic [simp] applies [rewrite ?bind_bind], which ensures that
   the breakpoint of interest cannot be buried under several [bind]s. *)

Ltac wp_continue :=
  wp_concat;
  wp.

(* -------------------------------------------------------------------------- *)

(* TODO: get [wp until check _] to use [idtac_or_do]. *)
Local Tactic Notation "idtac_or_do" constr(name) constr(δ) ltac(t) :=
  let is_in := eval cbn in (lookup_name δ name) in
  lazymatch is_in with
  | Ret _ => idtac
  | _ => t
  end.

Local Tactic Notation "@wp" "until" "check" constr(name) :=
  lazymatch goal with
  | |- environments.envs_entails _ $ wp _ _ (ret_dconcat ?δ ?η) _ =>
      let is_in := eval cbn in (lookup_name δ name) in
        lazymatch is_in with
        | Ret _ => idtac
        | _ => fail "[wp until] cannot find the requested bindings"
        end
  | |- environments.envs_entails _ $ wp _ _ (ret_concat ?δ ?η) _ =>
      let is_in := eval cbn in (lookup_name δ name) in
        lazymatch is_in with
        | Ret _ => idtac
        | _ => fail "[wp until] cannot find the requested bindings"
        end
  | _ => fail "[wp until] cannot find the requested bindings."
  end.

Tactic Notation "@wp" "until" constr(name) :=
  repeat (
      first
        [
          lazymatch goal with
          | |- environments.envs_entails _ $ wp _ _ (ret_dconcat ?δ ?η) _ =>
              idtac_or_do
                name δ
                (unfold_breakpoint (ret_dconcat δ η); fail)
          | |- environments.envs_entails _ $ wp _ _ (ret_concat ?δ ?η) _ =>
              idtac_or_do
                name δ
                (unfold_breakpoint (ret_concat δ η); fail)
          end
        | wp
    ]).

Tactic Notation "wp" "until" constr(name) :=
  @wp until name;
  first [ @wp until check name
        | idtac "The requested binding was not found."
    ].

Tactic Notation "wp" "until" constr(name) "!" :=
  repeat (@wp until name; try wp_bind);
  @wp until check name.

(* -------------------------------------------------------------------------- *)

Ltac wp_par :=
  iApply wp_par; [wp | wp | ].

Ltac wp_par_with H :=
  iApply (wp_par with H); [wp | wp | ].

Ltac wp_use H :=
  first [
    iApply H
  | iApply wp_covariant; [ iApply H |]
  | iApply (wp_covariant with H)
  ];
  cbn.

Ltac wp_enter :=
  iApply wp_simp; [
    simp_enter; [ normalize; eapply SimpReflexive ]
  | (* residual goal *)
  ].

Ltac wp_enter_and_abstract :=
  lazymatch goal with |- environments.envs_entails _ (wp _ _ (call ?v _) _) =>
    (* First, expand [call] away. *)
    iApply wp_simp; [
      simp_enter; eapply SimpReflexive
    | normalize
    ];
    (* Second, abstract away the closure (of which there are typically
       several occurrences in the hypotheses and goal), replacing it
       with an abstract value. This ensures that we cannot step into
       recursive calls. *)
    generalize dependent v
  end.

(* TODO: not great *)
Ltac wp_set_postcondition :=
    by
    lazymatch goal with
    | |- environments.envs_entails ?Δ (?φ ?v) =>
        is_evar φ;
        let hyps :=
          eval cbn in (
                     environments.env_to_list $
                     environments.env_spatial Δ
                   ) in
          let H := eval cbn in (
                              match hyps with
                              | [] => λ res, ⌜ res = v ⌝%I
                              | _ => (λ res, ⌜ res = v ⌝ ∗ [∗ list] p ∈ hyps, p)%I
                              end)%I in
            instantiate (1 := H)
    end.

(* -------------------------------------------------------------------------- *)

(* Store-related tactics. *)

Ltac wp_alloc l H:=
  iApply wp_alloc; iNext; iIntros (l) H; wp.
Ltac wp_load H :=
  iApply (wp_load with H); iNext; iIntros H; wp.
Ltac wp_store H :=
  iApply (wp_store with H); iNext; iIntros H; wp.

(* -------------------------------------------------------------------------- *)
(* Tactics used to prove the specification of a module expression. *)


Ltac wp_module_spec :=
  lazymatch goal with
  | |- environments.envs_entails _  (?φ (VStruct ?η)) =>
      iExists _; iSplit ; first  (iPureIntro; reflexivity);
      repeat first
             [ (iApply big_sepL_cons; iSplitL;
                first (iExists _; iSplit; [ done | iAssumption || done ])
               )
             | iApply big_sepL_nil; iPureIntro; exact I
             | idtac
                 "I cannot prove the required spec; please go back and prove the required specifications."
             ]
  end.

(* -------------------------------------------------------------------------- *)

(* Help reason on loops of the form [for i = x to y], whth [0 <= x <= y]. *)
Tactic Notation "oLoopPos" constr(v1) constr(v2) constr(Hinv) "with" constr(Hini) constr(Hend) :=
  let H := eval cbn in (Hini +:+ Hend) in
    lazymatch goal with
    | |- environments.envs_entails
           _ $
           wp _ _ (Stop CLoop (?η, ?x, repr ?i1, repr ?i2, ?e) ?k ?z) ?φ =>
        iApply
          ((wp_loop_inv_pos NotStuck ⊤ η x v1 v2 e k z φ Hinv)
            with H);
        try lia; try representable
    | _ => fail "[oLoop] can only be applied to terms of the form [WP (Stop CLoop _ _ _) {{ _ }}]"
    end.

(* -------------------------------------------------------------------------- *)

(* [Ltac] helpers to deal with value abstraction. *)

Tactic Notation "oAbstract" constr(s1) ident(i1):=
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  | |- context [(s1, (VClo ?η ?e)) :: _] =>
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

(* -------------------------------------------------------------------------- *)

(* [oCall] behaves in the same way that wp_call does, except that it abstracts
   the required closures.
   It is defined as a notation so that it is easy to ask for more idents (Ltac
   cannot take a list of idents as argument for a tactic). *)
Tactic Notation "@oCall" "unfold" :=
  with_strategy
    transparent [call]
    ( lazymatch goal with
      | |- environments.envs_entails ?Δ $ wp ?s ?E (call ?f ?a) ?φ =>
          let m := eval unfold call in (call f a) in
            change (environments.envs_entails Δ $ wp s E (call f a) φ)
              with (environments.envs_entails Δ $ wp s E m φ)
      | _ => fail "[oCall] The goal is not a call"
      end); try wp.

Tactic Notation "oCall" constr(s1) ident(i1) :=
  (* TODO if possible, use [wp_enter] instead of [unfold call] *)
  @oCall unfold; try wp;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end; try wp.
Tactic Notation "oCall" constr(s1) ident(i1) constr(s2) ident(i2) :=
  @oCall unfold; try wp;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s1] =>
      generalize (VCloRec η bds s1); intro i1
  end;
  lazymatch goal with
  | |- context [VCloRec ?η ?bds s2] =>
      generalize (VCloRec η bds s2); intro i2
  end; try wp.

(* -------------------------------------------------------------------------- *)

(* Below are defined local tactics which are used to define [oSpecify]. *)

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

(* [oSpecify_assume_nonrec specs names hyps δ] assumes specifications of
   elements of a let-binding. *)
Local Ltac oSpecify_assume_nonrec lspecs lnames lhyps δ :=
  let specs :=
    eval cbn in (
               foldr
                 (λ '(spec, name) (res: list (iProp _)),
                   let value :=
                     match lookup_name δ name with
                     | Ret v => v
                     | _ => VUnit
                     end in
                   spec value :: res)
                 [] (combine lspecs lnames)
             )
    in
    iApply (assumming_list_nonrec specs);
    last oSpecify_intros lhyps.

(* [oSpecify_assume specs names hyps δ] assumes specifications of elements of a
   letrec-binding. The difference with a let-binding is that
   Löb-induction-related hypotheses are provided: when proving the spec of
   mutually recursive functions [f] and [g], the specifications are available
   under a later modality. This only works for persistent specifications.
   Cf. [assumming_list] in [theories/weakestpre/specifications.v] for more
   details. *)
Local Ltac oSpecify_assume lspecs lnames lhyps δ :=
  let specs :=
    eval cbn in (
               foldr
                 (λ '(spec, name) (res: list (iProp _)),
                   let value :=
                     match lookup_name δ name with
                     | Ret v => v
                     | _ => VUnit
                     end in
                   spec value :: res)
                 [] (combine lspecs lnames)
             )
    in
    iApply (assumming_list specs);
      first (by eauto using intuitionistically_persistent);
      (try iModIntro);
      oSpecify_intros lhyps.

Tactic Notation "oSpecify_abstract" constr(δ) constr(n1) ident(i1) :=
  let value :=
    eval cbn in (match lookup_name δ n1 with
                           | Ret v => v
                           | _ => VUnit
                           end) in
    generalize value; intros i1.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2) :=
  oSpecify_abstract δ n1 i1;
  oSpecify_abstract δ n2 i2.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2)
       constr(n3) ident(i3) :=
  oSpecify_abstract δ n1 i1 n2 i2;
  oSpecify_abstract δ n3 i3.

Tactic Notation "oSpecify_abstract" constr(δ)
       constr(n1) ident(i1)
       constr(n2) ident(i2)
       constr(n3) ident(i3)
       constr(n4) ident(i4) :=
  oSpecify_abstract δ n1 i1 n2 i2;
  oSpecify_abstract δ n3 i3 n4 i4.

(* -------------------------------------------------------------------------- *)

(* Definition of [oSpecify], used to specify and abstract away values when the
   evaluation stops on en environment concatenation. *)

Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume_nonrec [spec1] [n1] [H1] δ;
      last ( oSpecify_abstract δ n1 i1 ;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1] [n1] [H1] δ;
      last ( oSpecify_abstract δ n1 i1 ;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2]
                             [n1; n2]
                             [H1; H2]
                             δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 ;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume_nonrec [spec1; spec2]
                      [n1; n2]
                      [H1; H2]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 ;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume_nonrec [spec1; spec2; spec3] [n1; n2; n3] [H1; H2; H3] δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3] [n1; n2; n3] [H1; H2; H3] δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.
Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1)
       constr(n2) constr(spec2) ident(i2) constr(H2)
       constr(n3) constr(spec3) ident(i3) constr(H3)
       constr(n4) constr(spec4) ident(i4) constr(H4) :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (ret_concat ?δ _) _) =>
      oSpecify_assume_nonrec [spec1; spec2; spec3; spec4]
                             [n1; n2; n3; n4]
                             [H1; H2; H3; H4]
                             δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3 n4 i4;
             wp_continue)
  | |- environments.envs_entails
         _ (wp _ _ (ret_dconcat ?δ _) _) =>
      oSpecify_assume [spec1; spec2; spec3; spec4]
                      [n1; n2; n3; n4]
                      [H1; H2; H3; H4]
                      δ;
      last ( oSpecify_abstract δ n1 i1 n2 i2 n3 i3 n4 i4;
             wp_continue)
  | _ => fail "[oSpecify] only works on environment extension."
  end.

(* -------------------------------------------------------------------------- *)

  (* [list_specifications] returns a list of specifications for a given symbol
     of a given module specification. *)
  Definition list_specifications `{Σ: gFunctors}
           (Λ : @spec_env Σ) (name : name)
    : list (val → iProp Σ) :=
    List.map snd $
             List.filter (fun '(n, _) => n =? name)%string Λ.

Tactic Notation "oSpecOf" constr(name) "from" constr(hyp) "as" constr(hyp_dest) :=
  lazymatch goal with
  | |- environments.envs_entails
         ?Δ $ wp _ _
         (call ((lookup_name_total (val_as_struct_total ?v) ?n)) _) _ =>
      (* - [v] stores the value of the module,
         - [n] stores the name of the symbol (depth 1).
         The first step is to find the Iris hypothesis discussing the module
         [v]. *)
      let env := eval cbn in
      (environments.env_lookup
         (INamed hyp) $ environments.env_intuitionistic Δ) in
      let φs :=
        lazymatch constr:(env) with
        | None => fail "Unknown hypothesis"
        | Some (module_spec ?Λ v) =>
            eval cbn in (list_specifications Λ name)
        | _ => fail "The target hypothesis is not a module specification"
        end in
      lazymatch constr:(φs) with
      | [] => fail "There is no specification for" name
      | [ ?φ ] =>
          iPoseProof ((module_spec_spec _ _ name) with hyp) as hyp_dest
      | _ => fail "There are too many specifications to choose from"
      end
  | _ => fail "[oSpecOf] could not fild the required specification."
  end.

Ltac oSpecError name spec :=
  fail "[oSpec] failed to apply the specification of" name
       "; Please consider using [oSpecOf " name "from" spec
       "as ...] to retrieve the spec yourself".

Tactic Notation "oSpec" constr(name) "from" constr(spec) "with" constr(Hyp) :=
  let H := iFresh in
  oSpecOf name from spec as H;
  first [
      iSpecialize (H with Hyp);
      last (iApply (wp_covariant with H) ; try iClear H)
    | oSpecError name spec
    ]; try wp.

(* Preconditions are often pure and might not need any hypothesis. *)
Tactic Notation "oSpec" constr(name) "from" constr(spec) :=
  first [
      oSpec name from spec with "[//]"
    | let H := iFresh in
      oSpecOf name from spec as H;
      first [
          iApply (wp_covariant with H);
          last try iClear H
        | oSpecError name spec
        ]
    | oSpec name from spec with "[]"
    ].

(* Ditto for [satisfies_spec]... *)

Tactic Notation "oSpecOf'" constr(name) "from" constr(hyp) "as" constr(H) :=
  iPoseProof ((bloupyfetcher _ _ _ _ name) with hyp) as H
.
Tactic Notation "oSpec'" constr(name) "from" constr(spec) "with" constr(Hyp) :=
  let H := iFresh in
  oSpecOf' name from spec as H;
  first [
      iSpecialize (H with Hyp);
      last (iApply (wp_covariant with H) ; try iClear H)
    | oSpecError name spec
    ]; try wp.

Tactic Notation "oSpec'" constr(name) "from" constr(spec) :=
  first [
      oSpec' name from spec with "[//]"
    | let H := iFresh in
      oSpecOf' name from spec as H;
      first [
          iApply (wp_covariant with H);
          last try iClear H
        | oSpecError name spec
        ]
    | oSpec' name from spec with "[]"
    ].

(* -------------------------------------------------------------------------- *)

(* In order for lookups and evaluation of module-values to be evaluated, one
   needs to declare the value the representation of a module. *)
Tactic Notation "oModule" ident(v) :=
  iPoseProof ((module_spec_is_module v) with "[$]") as "%";
  simpl (spec_env_erase _) in *.
Tactic Notation "oModule" ident(v1) ident(v2) :=
  oModule v1; oModule v2.
Tactic Notation "oModule" ident(v1) ident(v2) ident(v3) :=
  oModule v1; oModule v2 v3.
Tactic Notation "oModule" ident(v1) ident(v2) ident(v3) ident(v4) :=
  oModule v1 v2; oModule v3 v4.

(* -------------------------------------------------------------------------- *)

(* Wrapers around the above [Tactic Notation]s to autoname idents.
   For some (unknown) reason, it is not possible to overload [oSpecify] with
   four new notations, even if the arities differ from the previous notations.
 *)
(*
From iris.proofmode Require Import string_ident.

Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1) :=
  string_to_ident_cps n1 ltac:(fun i1 =>
  let i1 := fresh i1 in
  oSpecify n1 spec1 i1 H1).
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2) :=
  string_to_ident_cps
    n1
    ltac:(fun i1 =>
            let i1 := fresh i1 in
            string_to_ident_cps
              n2
              ltac:(fun i2 =>
                      let i2 := fresh i2 in
                      oSpecify n1 spec1 i1 H1
                               n2 spec2 i2 H2)).
Tactic Notation "o_specify"
       constr(n1) constr(spec1) constr(H1)
       constr(n2) constr(spec2) constr(H2)
       constr(n3) constr(spec3) constr(H3) :=
  string_to_ident_cps
    n1
    ltac:(fun i1 =>
            let i1 := fresh i1 in
            string_to_ident_cps
              n2
              ltac:(fun i2 =>
                      let i2 := fresh i2 in
                      string_to_ident_cps
                        n3
                        ltac:(fun i3 =>
                                let i3:= fresh i3 in
                                oSpecify n1 spec1 i1 H1
                                         n2 spec2 i2 H2
                                         n3 spec3 i3 H3))).
 *)

(* -------------------------------------------------------------------------- *)

(* When using the above tactics in real-life examples, some patterns have
   emerged. The following tactic notations are shortcuts one may find useful in
   proofs. *)

Tactic Notation "oSpecify"
       constr(n1) constr(spec1) ident(i1) constr(H1) "!" :=
  wp until n1 ! ;
  oSpecify n1 spec1 i1 H1.

Tactic Notation "wp" "skip" constr(n1) := wp until n1 ! ; wp_continue.
Tactic Notation "wp" "skip" constr(n1) constr(n2) := wp skip n1 ; wp skip n2.
Tactic Notation "wp" "skip" constr(n1) constr(n2) constr(n3) :=
  wp skip n1 ; wp skip n2 n3.
Tactic Notation "wp" "skip" constr(n1) constr(n2) constr(n3) constr(n4) :=
  wp skip n1 n2 ; wp skip n3 n4.
