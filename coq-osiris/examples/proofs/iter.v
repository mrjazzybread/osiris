From iris.proofmode Require Import base proofmode classes ltac_tactics.
From iris.bi Require Import weakestpre.
From iris Require Import base_logic.lib.gen_heap.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_iter.

Context `{!osirisGS Σ}.

Context (A : Type) `{Encode A}.

Definition isListIter (iter : val) : iProp Σ :=
  ∀ (ψ : iEff Σ) E (I : list A → iProp Σ) φ (f : val) (l : list A),
    □ (∀ (Xs : list A) (X : A),
          ⌜ (Xs ++ [X]) `prefix_of` l ⌝ -∗
            I Xs -∗
            EWP (call f #X) @ E <| ψ |> {{ | RET v => ⌜ v = VUnit ⌝ ∗ I (Xs ++ [X]);
                                           | EXN e => φ e ∗ I Xs }})
      -∗
      I [] -∗
      EWP (ncall iter [f; #l] ) @E <| ψ |>
      {{ | RET v => ⌜ v = VUnit ⌝ ∗ I l;
         | EXN e => φ e ∗ ∃ Xs, I Xs ∗ ⌜ Xs `prefix_of` l ⌝ }}.

Lemma ewp_module η sitems (Q : val -> iProp Σ) :
  EWP (eval_sitems (η, []) sitems) {{ RET ηδ, let '(_, δ) := ηδ in Q (VStruct δ) }} -∗
  EWP (eval_mexpr η (MStruct sitems)) {{ RET v, Q v }}.
Proof.
  iIntros "Hsitems".
  simpl_eval_mexpr. Bind.
  iApply (ewp_mono with "Hsitems").
  iIntros ([ ηδ | e ]); [ simpl | done ].
  destruct ηδ; iIntros "HQ".
  by Ret.
Qed.

Lemma ewp_sitems_cons ηδ sitem sitems E ψ Q (φ : env * env -> iProp Σ) :
    EWP eval_sitem ηδ sitem @ E <| ψ |> {{ RET ηδ, φ ηδ }} -∗
    (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| ψ |> {{ Q }}) -∗
    EWP eval_sitems ηδ (sitem :: sitems) @ E <| ψ |> {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov". simpl_eval_sitems.
    Bind.
    iApply (ewp_mono with "Hsitem").
    iIntros ([ηδ'|]); [ simpl | done ].
    iApply "Hcov".
  Qed.

Lemma ewp_sitems_nil ηδ E ψ Q :
  Q (O2Ret ηδ) -∗
    EWP eval_sitems ηδ [] @ E <| ψ |> {{ Q }}.
Proof.
  simpl_eval_sitems.
  by iApply ewp_value.
Qed.

Lemma ewp_sitem_letrec_singleton (spec : val -> iProp Σ) η δ x af E ψ :
    spec (VCloRec η [RecBinding x af] x) -∗
    EWP eval_sitem (η, δ) (ILetRec [RecBinding x af]) @ E <| ψ |>
    {{ RET ηδ, let '(η0, δ0) := ηδ in
               ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
    }}.
Proof.
  iIntros "Hspec".
  simpl_eval_sitem. Ret. simpl.
  iExists _. iFrame. equality.
Qed.

Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

Ltac prove_handler_spec := rewrite deep_handler_spec_unfold; iSplit.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 iris_goal () :=
  lazy_match! goal with
  | [ |- environments.envs_entails _ ?g ] => g
  | [ |- _ ] => Control.throw (Tactic_failure None)
  end.

Ltac2 rec strip_laters (g : constr) :=
  lazy_match! g with
  | bi_later ?c => strip_laters c
  | _ => g
  end.

Ltac2 prepare_pattern_post () :=
  lazy_match! goal with
  | [ |- pattern _ _ _ ?φ _ ] =>
      let η := open_constr:(_:env) in
      unify $φ (fun δ => δ = $η)
  end.

From iris Require Import  spec_patterns.

Lemma bi_sep_intro (P Q : iProp Σ) :
  P -∗
  Q -∗
  P ∗ Q.
Proof.
  iStartProof.
  iIntros "H1 H2". iFrame.
Qed.

From iris Require Import string_ident.

Ltac to_ident_list env acc :=
  match env with
  | environments.Enil => constr:(acc)
  | environments.Esnoc ?env ?h _ =>
      to_ident_list env (h::acc)
  end.

Ltac all_intuitionistic_hyps :=
  match goal with
  | |- environments.envs_entails ?env _ =>
      match env with
      | environments.Envs ?env_intuitionistic _ _ =>
          to_ident_list env_intuitionistic (@nil ident)
      end
  end.

Ltac all_spatial_hyps :=
  match goal with
  | |- environments.envs_entails ?env _ =>
      match env with
      | environments.Envs _ ?env_spatial _ =>
          to_ident_list env_spatial (@nil ident)
      end
  end.

Fixpoint not_mem (a : ident) (l : list ident) :=
  match l with
  | [] => true
  | h :: t =>
      if ident_beq h a then false else not_mem a t
  end.

Definition hyp_different initial excluding :=
  List.filter (fun hyp => not_mem hyp excluding) initial.

Ltac conj_hyps hyps :=
  match hyps with
  | [] => idtac
  | [?hyp] => idtac
  | ?h1 :: ?h2 :: ?hyps =>
      let h := iFresh in
      iPoseProof (bi_sep_intro) as h;
      iSpecialize (h with h1);
      iSpecialize (h with h2);
      iRename h into h1;
      conj_hyps (h1 :: hyps)
  end.

Ltac unconj_hyps_aux hyp_name hyps :=
  match hyps with
  | [] => idtac
  | [_] => idtac
  | ?h1 :: ?t =>
      _iDestruct0 hyp_name
        (intro_patterns.IList [[intro_patterns.IIdent hyp_name;
                                intro_patterns.IIdent h1]]);
      unconj_hyps_aux hyp_name t

  end.

Ltac unconj_hyps hyps :=
  match hyps with | [] => idtac | ?hyp_name :: _ =>
  let hyps := (eval vm_compute in (List.rev hyps)) in
  unconj_hyps_aux hyp_name hyps
  end.

Ltac revert_intuitionistic hyps :=
  match hyps with
  | [] => idtac
  | ?h :: ?t =>
      iRevert h; iIntros h; revert_intuitionistic t
  end.

Ltac unrevert_intuitionistic hyps :=
  match hyps with
  | [] => idtac
  | ?h :: ?t =>
      iRevert h;
      _iIntros0 (intro_patterns.IIntuitionistic (intro_patterns.IIdent h));
      unrevert_intuitionistic t
  end.

Ltac reintroduce_env intuitionistic_hyps spatial_hyps :=
  match intuitionistic_hyps with
  | ?h1 :: _ =>
      iIntros h1;
      match spatial_hyps with
      | ?h2 :: _ => unconj_hyps [h1; h2]
      | _ => idtac
      end
  | _ =>
      match spatial_hyps with
      | ?h2 :: _ =>
          iIntros h2
      | _ => idtac
      end
  end;
  unconj_hyps intuitionistic_hyps;
  unrevert_intuitionistic intuitionistic_hyps;
  unconj_hyps spatial_hyps.

Ltac apply_deep_handle_cons_unary :=
  let intuitionistic_hyps := all_intuitionistic_hyps in
  let spatial_hyps := all_spatial_hyps in
  conj_hyps spatial_hyps;
  revert_intuitionistic intuitionistic_hyps;
  conj_hyps intuitionistic_hyps;
  match intuitionistic_hyps with
  | ?h1 :: _ =>
      match spatial_hyps with
      | ?h2 :: _ => conj_hyps [h1; h2]
      | _ => idtac
      end
  | _ => idtac
  end;
  match intuitionistic_hyps with
  | ?h1 :: _ =>
      iApply (deep_handle_cons_unary with h1)
  | _ => match spatial_hyps with
        | ?h2 :: _ => iApply (deep_handle_cons_unary with h2)
        | _ => iApply deep_handle_cons_no_resources
        end
  end;
  [ iPureIntro;
    specify_cpattern;
    pattern_match;
    iStartProof
  | try iModIntro ];
  reintroduce_env intuitionistic_hyps spatial_hyps.

(* Ltac hyps_from_selpat selpat := *)
(*   let pats := spec_pat.parse selpat in *)
(*   let pat := match pats with [?x] => x end in *)
(*   match pat with *)
(*   | SGoal (SpecGoal _ false _ ?hyps _) => hyps *)
(*   | SGoal (SpecGoal _ true _ ?hyps _) => *)
(*       let starting_hyps := all_hyps in *)
(*       let hyps := (eval vm_compute in (hyp_different starting_hyps hyps)) in *)
(*       hyps *)
(*   end. *)

(* Lemma trivial_goal : @bi_emp_valid (iProp Σ) ⌜ True ⌝. *)
(* Proof. done. Qed. *)

(* Ltac2 red_match (intropat : constr) := *)
(*   let g := strip_laters (iris_goal ()) in *)
(*   lazy_match! g with *)
(*   | ewp_def _ (deep_eval_match _ ?bs ?o) _ _ => *)
(*       lazy_match! Std.eval_hnf bs with *)
(*       | _ :: _ => *)
(*           ltac1:(selpat |- *)
(*                    let hyps := hyps_from_selpat selpat in *)
(*                    conj_hyps hyps; *)
(*                    match hyps with *)
(*                    | [] => iApply (deep_handle_cons_unary); [ iApply trivial_goal | | ] *)
(*                    | ?h :: _ => iApply (deep_handle_cons_unary with h) *)
(*                    end *)
(*                 ) (Ltac1.of_constr intropat); *)
(*           Control.focus 1 1 *)
(*             (fun _ => *)
(*                ltac1:(iPureIntro); *)
(*                let m := specify_cpattern () in *)
(*                Control.focus 1 m (fun _ => pattern_match0 ())); *)
(*             Control.focus 2 2 (fun _ => *)
(*                                  let no_match := Fresh.in_goal @no_match in *)
(*                                  ltac1:(no_match |- iIntros (no_match)) (Ltac1.of_ident no_match)) *)
(*       | _ => () *)
(*       end *)
(*   | _ => Message.print (Message.of_constr g) *)
(*   end. *)

Lemma iter_module :
  ⊢ EWP (eval_mexpr stdlib_env __main)
    {{ RET m, module_spec [("iter", isListIter)] m}}.
Proof.
  iIntros. unfold __main.
  iApply ewp_module.
  iApply ewp_sitems_cons.
  { iApply (ewp_sitem_letrec_singleton isListIter).
    unfold isListIter.
    iIntros (Ψ E I φ f l).
    iIntros "#Hf HI".

    (* At this point, we have [EWP ncall clo [f; #l] ...]
       Unfortunately, n-ary calls do not play well with proofs by
       induction, so we reduce the [ncall] until we have a call to
       a single closure.  *)
    Bind. iApply ewp_call_rec; [ reflexivity | iNext ].
    simpl_eval. Ret. simpl. (* TODO: expr lemma for [EAnonFun]. *)

    (* We generalize the goal to strengthen the induction. We want the
       invariant [I] to hold over the visited prefix of [l], and we
       want the argument of the call to be the remaining suffix. *)
    assert ([] ++ l = l) as Heql by reflexivity; revert Heql.
    (* We generalize the initial prefix (the empty list)
       in [[] ++ l = l] and in [I []]. *)
    generalize (@nil A) at 1 4; intro lpre.
    (* We generalize the initial suffix (the whole list)
       in [lpre ++ l = l] and in [EWP call clo #l]. *)
    generalize l at 1 4; intro lsuf.
    intros Heql.

    (* Induction generalizing over the prefix and suffix, but not [l]. *)
    iLöb as "IH" forall (lsuf lpre Heql) "Hf HI".

    (* Cases on if the suffix is empty or not. *)
    iApply ewp_call_nonrec; iNext.
    iApply ewp_EMatch.
    iApply (ewp_deep_handler _ _ (ieq ?[y])). { Simp; Ret; equality. }

    prove_handler_spec; last first.
    (* No effects are used, so the effectful case is discarded,
         we definitely want to automate this. *)
    { iIntros (??) "HF".
      by iPoseProof (upcl_bottom with "HF") as "F". }

    iIntros (o) "->".
    apply_deep_handle_cons_unary.

    { Simp; Ret; simpl.
      (* Subgoal: show the postcondition when we return unit. *)
      iSplit; [ equality | ].
      (* If the suffix is empty, then the prefix is the whole list. *)
      rewrite app_nil_r.
      iApply "HI". }

    iIntros (no_match1).
    apply_deep_handle_cons_unary.

    { iApply (ewp_ESeq_exn with "[HI]").
      { Simp. iApply "Hf".
        - iPureIntro. instantiate (1 := lpre).
          apply prefix_app. apply prefix_cons. apply prefix_nil.
        - iApply "HI". }
      simpl.
      iIntros (e) "[Hφ HI]". iFrame.
      iExists lpre. iFrame.
      iPureIntro.
      replace lpre with (lpre ++ []) at 1 by (rewrite app_nil_r; reflexivity).
      apply prefix_app, prefix_nil.

      { iIntros (vu); simpl.
        iIntros "[-> HI]". fold eval.

        iApply ewp_EApp.
        { iApply ewp_EApp; try (iApply ewp_EPath; Ret; equality).
          iApply ewp_call_rec; [ reflexivity | ].
          Simp. Ret. equality. }
        { iApply ewp_EPath; Ret; equality. }

        iApply (ewp_mono with "[HI]").
        { iApply "IH".
          { iPureIntro.
            instantiate (1 := lpre ++ [x]).
            rewrite (cons_middle x lpre xs').
            by rewrite app_assoc. }

          { iIntros "!>" (Xs X) "Hpref HI".
            iApply (ewp_mono with "[-]").
            iApply ("Hf" with "Hpref HI").
            iIntros (?) "?". iAssumption. }

          { iApply "HI". } }

        iIntros (?) "?". iAssumption. } }

    iIntros (no_match2).
    iApply deep_handle_nil_ret.
    ltac2:(destruct_hyps [@no_match1; @no_match2]). }

    iIntros ([δ η]).
    iIntros "(%iter & Hiter & -> & ->)".

    iApply ewp_sitems_nil. simpl.
    unfold module_spec; intros.
    iExists _; iSplit; [ equality | simpl ].
    iSplit; [ | done ].
    iExists _; iSplit; [ equality | iAssumption ].
Qed.
