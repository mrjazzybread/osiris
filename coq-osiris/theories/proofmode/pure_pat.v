From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp.

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

Implicit Type φ : env → Prop.
Implicit Type ψ : Prop.

(* The judgement [pat η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition pat η p v φ ψ :=
  total (extend η p v) φ (λ (_ : unit), ψ).

Definition pats η ps vs φ ψ :=
  total (extends η ps vs) φ (λ (_ : unit), ψ).

(* A consequence rule. *)

Lemma pat_consequence η p v φ φ' ψ ψ' :
  pat η p v φ ψ →
  (∀ η, φ η → φ' η) →
  (ψ → ψ') →
  pat η p v φ' ψ'.
Proof.
  unfold pat. eauto using total_consequence.
Qed.

Lemma pat_consequence_psi η p v φ ψ ψ' :
  pat η p v φ ψ →
  (ψ → ψ') →
  pat η p v φ ψ'.
Proof.
  unfold pat. eauto using total_consequence.
Qed.

Lemma pats_consequence_psi η ps vs φ ψ ψ' :
  pats η ps vs φ ψ →
  (ψ → ψ') →
  pats η ps vs φ ψ'.
Proof.
  unfold pats. eauto using total_consequence.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [pats]. *)

Lemma pats_PNil η φ :
  φ η →
  pats η [] [] φ False.
Proof.
  unfold pats. simpl. eauto using total_ret.
Qed.

Lemma pats_PCons_unary η p ps v vs φ ψ :
  pat η p v (λ η, pats η ps vs φ ψ) ψ →
  pats η (p :: ps) (v :: vs) φ ψ.
    (* a simple statement (unused) *)
Proof.
  unfold pats, pat. intro Hp. simpl.
  eapply total_bind; [ eapply Hp | simpl ]. intros η' Hps.
  rewrite bind_ret_right. eauto.
Qed.

Lemma pats_PCons η p ps v vs φ' φ ψ1 ψ2 :
  pat η p v φ' ψ1 →
  (∀ η, φ' η → pats η ps vs φ ψ2) →
  pats η (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
    (* a more elaborate statement, where [ψ1] and [ψ2] are unconstrained,
       and where a disjunction is explicitly constructed -- see below. *)
Proof.
  unfold pats, pat. intros. simpl.
  eapply total_bind; [ eauto using total_consequence | simpl ].
  intros η' ?.
  rewrite bind_ret_right.
  eauto using total_consequence.
Qed.

Lemma pats_PCons_single η p v φ ψ :
  pat η p v φ ψ ->
  pats η [p] [v] φ ψ.
Proof.
  intros Hpat.
  eapply pats_consequence_psi.
  eapply pats_PCons.
  { eapply total_consequence.
    { apply Hpat. }
    { intros η' ?. eapply pats_PNil; eauto. }
    { simpl; intros _ Hψ; apply Hψ. } }
  { simpl; intros. eassumption. }
  { intros [|]; [ tauto | contradiction ]. }
Qed.

Ltac pats :=
  repeat first [
      eapply pats_PNil; [ eauto ]
    | eapply pats_PCons; [ eauto | simpl; intros ]
    ].

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the judgement [pat]. *)

(* From an operational point of view, the repeated application of these
   lemmas to a pattern [p] and a value [v] have the effect of translating
   the pattern matching operation [p = v] into a positive formula and a
   negative formula. The positive formula, the postcondition [φ],
   accumulates a sequence of universal quantifiers and equations that
   describe what is learnt when pattern matching succeeds. The negative
   formula, the failure postcondition [ψ], describes what is learnt when
   pattern matching fails. *)

(* When a pattern cannot fail or can fail due to several distinct causes,
   a naive statement of its reasoning rule would have one occurrence of
   [ψ] in its conclusion and no occurrence or multiple occurrences of [ψ]
   in its premises. From an operational point of view, this is
   undesirable, because [ψ] is then unconstrained or duplicated. We avoid
   this phenomenon by using [False] or a disjunction in the conclusion of
   the reasoning rule. Thus, from an operational point of view, applying
   the reasoning rule instantiates the failure postcondition with a
   logical connective. *)

Lemma pat_PAny η v φ :
  φ η →
  pat η PAny v φ False.
Proof.
  unfold pat. simpl. eauto using total_ret.
Qed.

Lemma pat_PVar η x v φ :
  φ ((x, v) :: η) →
  pat η (PVar x) v φ False.
Proof.
  unfold pat. simpl. eauto using total_ret.
Qed.

Lemma pat_PVar2 η x v :
  pat η (PVar x) v (λ η', η' = (x, v) :: η) False.
Proof.
  by apply pat_PVar.
Qed.

Ltac pat_PVar :=
  match goal with
  | |- pat _ (PVar _) _ _ _ =>
      (apply pat_PVar2 || eapply pat_PVar)
  end.

Lemma pat_PAlias η p x v φ ψ :
  pat η p v (λ η, φ ((x, v) :: η)) ψ →
  pat η (PAlias p x) v φ ψ.
Proof.
  unfold pat. simpl. intros Hp.
  eapply total_bind; [ eapply Hp | simpl ]. intros η' ?.
  eauto using total_ret.
Qed.

Lemma pat_POr η p1 p2 v φ ψ1 ψ2 :
  pat η p1 v φ ψ1 →
  pat η p2 v φ ψ2 →
  pat η (POr p1 p2) v φ (ψ1 ∧ ψ2).
    (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
       disjunction pattern to fail, both sides must fail. *)
Proof.
  unfold pat; intros Hp1 Hp2. simpl.
  eauto using total_orelse, total_consequence.
Qed.

Lemma pat_PUnit η v φ :
  φ η →
  v = #() →
  pat η PUnit v φ False.
Proof.
  unfold pat. intros. subst. simpl. eauto using total_ret.
Qed.

Lemma pat_PTuple η ps vs φ ψ :
  pats η ps vs φ ψ →
  pat η (PTuple ps) (VTuple vs) φ ψ.
Proof.
  unfold pats, pat. simpl. eauto.
Qed.

Lemma pat_PPair `{Encode A, Encode B} η p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
  v1 = #x1 ->
  v2 = #x2 ->
  pat η p1 #x1 (λ η', pat η' p2 #x2 φ (ψ2)) (ψ1) ->
  pat η (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
Proof.
  intros; subst.
  apply pat_PTuple.
  eapply pats_PCons; eauto.
  intros; apply pats_PCons_single; assumption.
Qed.

Ltac pat_PPair := eapply pat_PPair; [ solve [encode]
                                    | solve [encode]
                                    |].

Lemma pat_PData η c p c' v φ ψ :
  (c = c' → pat η p v φ ψ) →
  pat η (PData c p) (VData c' v) φ (ψ ∨ c ≠ c').
    (* This form is useful when the truth of the equality [c = c']
       is not statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; eauto using total_throw, total_consequence.
Qed.

Lemma pat_PData_eq η c p v φ ψ :
  pat η p v φ ψ →
  pat η (PData c p) (VData c v) φ ψ.
    (* This form is useful when [c = c'] is statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; solve [ eauto using total_throw | tauto ].
Qed.

Lemma pat_PData_neq η c p c' v φ :
  c ≠ c' →
  pat η (PData c p) (VData c' v) φ True.
    (* This form is useful when [c ≠ c'] is statically known. *)
Proof.
  unfold pat; intros. simpl.
  destruct_string_eqb; solve [ eauto using total_throw | tauto ].
Qed.

Lemma pat_false η v (P : Prop) φ :
  v = #P →
  (¬P → φ η) →
  pat η (PConstant "false") v φ P.
Proof.
  intros; subst.
  eapply pat_consequence_psi.
  { (* The definition of [#] at type [Prop] involves [VBool], which
       itself involves [BoolConstructor]. *)
    change "false" with (BoolConstructor false).
    eapply pat_PData.
    intro Heq. symmetry in Heq.
    apply BoolConstructor_injective, truth_false_elim in Heq.
    pats. }
  { intros [| Hneq ]; [ tauto |]. apply not_eq_sym in Hneq.
    apply BoolConstructor_congruent_contrapositive in Hneq.
    apply bool_neq in Hneq.
    apply truth_true_elim in Hneq.
    tauto. }
Qed.

Lemma pat_true η v (P : Prop) φ :
  v = #P →
  (P → φ η) →
  pat η (PConstant "true") v φ (¬P).
Proof.
  intros; subst.
  eapply pat_consequence_psi.
  { change "true" with (BoolConstructor true).
    eapply pat_PData.
    intro Heq. symmetry in Heq.
    apply BoolConstructor_injective, truth_true_elim in Heq.
    pats. }
  { intros [| Hneq ]; [ tauto |]. apply not_eq_sym in Hneq.
    apply BoolConstructor_congruent_contrapositive in Hneq.
    apply bool_neq in Hneq.
    apply truth_false_elim in Hneq.
    tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning for data *)

(* The following reasoning rules exemplify a general approach for matching
   against algebraic data types. *)

Lemma pat_pNil `{Encode A} η v (xs : list A) φ :
  v = #xs →
  (xs = [] -> φ η) →
  (* Enter the branch with knowledge that [xs] is empty *)
  pat η pNil v φ (xs ≠ []).
  (* If the match is unsuccessful, move to the next branch
     with the knowledge that [xs] is not empty *)
Proof.
  intros; subst.
  destruct xs as [| x xs ]; eapply pat_consequence_psi.
  { eapply pat_PData_eq; eauto.
    eapply pat_PTuple.
    pats. }
  { tauto. }
  { eapply pat_PData_neq; eauto. }
  { done. }
Qed.

Lemma pat_pCons `{Encode A} v xs η p1 p2 φ (φ1 : A -> env -> Prop)
  (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
  :
  v = #xs ->
  (∀ (x : A) (xs' : list A),
      xs = x :: xs' →
      pat η p1 #x (φ1 x) (ψ1 x)) ->
      (* If [#x] matches [p1], we gain the knowledge [φ1 x η0].
         Otherwise, we gain the knowledge [ψ1 x] *)
  (∀ (x : A) (xs' : list A),
      xs = x :: xs' →
      (forall η', φ1 x η' -> pat η' p2 #xs' φ (ψ2 xs'))) ->
      (* If [#xs'] does not match [p2], then we gain the knowledge [ψ2 xs'] *)
  pat η (pCons p1 p2) v φ (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
  (* There are three ways the match can be unsuccessful:
     - the list is empty
     - the list is non-empty, but its head did not match [p1]
     - the list is non-empty, but its tail did not match [p2] *)
Proof.
  intros ? Hpat Hpats; subst.
  destruct xs as [| x xs]; eapply pat_consequence_psi.
  { eapply pat_PData_neq; eauto. }
  { by left. }
  { eapply pat_PData_eq; eauto.
    rewrite ?encode_list_is_encode. (* optional, but helpful *)
    eapply pat_PTuple.
    eapply pats_PCons; eauto. intros ?; simpl; intros.
    pats. }
  { intros [ | [ | F ]]; right; eauto; contradiction. }
Qed.

Ltac pat_pNil :=
  eapply pat_pNil; first solve [ encode ].

Ltac pat_pCons :=
  eapply pat_pCons; first solve [ encode ].

(* The previous lemmas give us a general scheme for reasoning about
   pattern matching on ADTs.

   Given an ADT [G], we need one lemma for each of its constructor.

   Given a constructor [C] of [G] with [m] arguments with types [A1 ... A__m],
   its reasoning rule should have the following form:

   Lemma pat_pC v x η (p1 p2 ... p__m : pat) (φ : env -> Prop)
   (φ1 : A1 -> env -> Prop) ... (φ__(m-1) : A__(m-1) -> env -> Prop)
   (ψ1 : A1 -> Prop) ... (ψ__m : A__m -> Prop)
   :
   v = #x ->
   (∀ (x1 : A1) ... (x__m : A__m),
      x = C x1 ... x__m ->
      pat η p1 #x1 (φ1 x1) (ψ1 x1)) ->
   ⋮
   (∀ (x1 : A1) ... (x__m : A__m),
      x = C x1 ... x__m ->
      pat η p__(m-1) #x__(m-1) (φ__(m-1) x__(m-1)) (ψ__(m-1) x__(m-1))) ->
   (∀ (x1 : A1) ... (x__m : A__m),
      x = C x1 ... x__m ->
      pat η p__m #x__m φ (ψ__m x__m)) ->
   pat (pC p1 ... p__m) v φ (match x with
                             | C _ ... _ => ⊥
                             | _ => ⊤
                             end ∨ (∃ x1 ... x__m, x = C x1 ... x__m ∧
                                     (ψ1 x1 ∨ ... ∨ ψ__m x__m)))
   .
*)

(* TODO: Move/remove the following section *)

(* -------------------------------------------------------------------------- *)

Section HelperLemmas.

Lemma pure_total {B E} `{Encode A} (m : micro B E) k ko (φ : A -> Prop) :
  total m (fun a => pure (k a) φ) (λ e, pure (ko e) φ) <->
  pure (try m k ko) φ.
Proof.
  unfold pure; unfold total.
  split; [intros Ht | intros (a & Hsimp & Hψ)].
  { destruct Ht as [Hterm | Hcont].
    { destruct Hterm as (b & Hsimp & a & Ha & Hψ).
      exists a. split; last assumption.
      eapply prove_simp_try; eauto. }
    { destruct Hcont as (e & Hnext & a & Hcont & Hψ).
      exists a. split; last assumption.
      eapply prove_simp_try_throw; eauto. } }
  { apply invert_simp_try_ret in Hsimp as [(? & ? & ?) | (? & ? & ?)].
    - left; eauto.
    - right; eauto. }
Qed.
End HelperLemmas.

(* -------------------------------------------------------------------------- *)

(* Todo: comment *)

Definition pure_match `{Encode A} (η : env) (v : val) bs (φ : A -> Prop) :=
  pure (eval_match η v bs) φ.
Arguments pure_match {A} {H} _ _ _ _.

Lemma pure_eval_match' `{Encode A, Encode B} η e bs (φ : A -> Prop) :
  pure (eval η e) (λ v : B, pure_match η #v bs φ) ->
  pure (eval η (EMatch e bs)) φ.
Proof.
  intros. unfold pure_match in *.
  destruct_pure v. destruct_pure x.
  eapply pure_simp.
  { rewrite eval_eval'; simpl.
    eapply prove_simp_bind; eauto. }
  eapply pure_ret; eauto.
Qed.

Lemma pure_eval_match `{Encode A, Encode B} η e bs (a : A) (φ : B -> Prop) :
  pure (eval η e) (λ x, x = a) ->
  pure_match η #a bs φ ->
  pure (eval η (EMatch e bs)) φ.
Proof.
  intros.
  eapply pure_eval_match'.
  eapply pure_consequence; [ eassumption | ].
  by intros ? ->.
Qed.

Lemma pure_match_cons_unary `{Encode A} η v p e bs (φ : A -> Prop) :
  pat η p v (λ η', pure (eval η' e) φ) (pure_match η v bs φ) ->
  pure_match η v ((Branch p e) :: bs) φ.
Proof.
  unfold pure_match; unfold pat.
  intros Hpat. simpl.
  by apply pure_total.
Qed.

Lemma pure_match_cons `{Encode A} η v p e bs (φ : A -> Prop) ψ :
  pat η p v (λ η', pure (eval η' e) φ) ψ ->
  (ψ -> (pure_match η v bs φ)) ->
  pure_match η v ((Branch p e) :: bs) φ.
Proof.
  intros.
  apply pure_match_cons_unary.
  eauto using pat_consequence.
Qed.

Lemma pure_match_single `{Encode A} η v p e (φ : A -> Prop) ψ :
  pat η p v (λ η' : env, pure (eval η' e) φ) ψ →
  (ψ -> False) ->
  pure_match η v [Branch p e] φ.
Proof.
  intros.
  eapply pure_match_cons; eauto.
  tauto.
Qed.

Ltac extend_env :=
  match goal with
  | |- forall (η : env), η = _ -> _ =>
      intros ? ->
  | _ => idtac
  end.

Ltac pattern_match :=
   repeat (pat_PVar
    || (pat_pNil;
       let Heql := fresh "Heql" in
       intros Heql)
    || (pat_pCons;
       (let h := fresh "h" in
        let t := fresh "t" in
        let Heql := fresh "Heql" in
        intros h t Heql);
       [ pattern_match | simpl; extend_env; pattern_match ])
    || (apply pat_POr; pattern_match)
    || pat_PPair
    || apply pat_PAny
     ); subst.


Ltac strip_disjunction :=
  match goal with
  | H : _ \/ _ |- _ =>
      destruct H as [ H | H ]; try contradiction
  end.
Ltac remove_tauto :=
  lazymatch goal with
  | H : ?x = ?x |- _ => clear H
  | _ => idtac
  end.
Ltac subst_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ => subst x
  | _ => idtac
  end.
Ltac inject_eq :=
  lazymatch goal with
  | H : ?x = _ |- _ =>
      (injection H; repeat (intros ->) || clear dependent x)
  | _ => idtac
  end.
Ltac elim_exists :=
  lazymatch goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  end.

Ltac destruct_hyp :=
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

(* Goal: show that never matching is impossible *)
Ltac resolve_no_match :=
  repeat ((repeat strip_disjunction);
          (repeat elim_exists);
          (repeat destruct_hyp);
          try contradiction;
          (repeat remove_tauto);
          (repeat subst_eq);
          inject_eq).

Ltac pure_match :=
  lazymatch goal with
  | |- pure_match _ _ [?b] _ =>
      eapply pure_match_single;
      [ pattern_match
      | let no_match := fresh "no_match" in
        intros no_match; resolve_no_match ]
  | |- pure_match _ _ (?b :: ?bs) _ =>
      eapply pure_match_cons;
      [ pattern_match
      | (let no_match := fresh "no_match" in
         intros no_match; pure_match) ]
  end.
