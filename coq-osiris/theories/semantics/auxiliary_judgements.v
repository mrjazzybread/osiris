From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar.
From osiris.semantics Require Import code eval simplification pure_wp pure.

(* This file defines judgements for Hoare-style reasoning on
   the auxiliary functions in [semantics/eval.v]. *)

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

(* The judgement [pattern η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition cpattern η p o (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (cextend η p o) φ (λ (_ : unit), ψ).

Definition pattern η p v (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extend η p v) φ (λ (_ : unit), ψ).

Definition patterns η ps vs (φ : env -> Prop) (ψ : Prop) :=
  pure_wp (extends η ps vs) φ (λ (_ : unit), ψ).


(* A consequence rule. *)

Lemma pat_consequence η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
  pattern η p v φ ψ →
  (∀ η, φ η → φ' η) →
  (ψ → ψ') →
  pattern η p v φ' ψ'.
Proof.
  unfold pattern. eauto using pure_wp_mono.
Qed.

Lemma pat_consequence_phi η p v (φ φ' : env -> Prop) (ψ : Prop) :
  pattern η p v φ ψ →
  (∀ η, φ η → φ' η) →
  pattern η p v φ' ψ.
Proof.
  unfold pattern. eauto using pure_wp_mono.
Qed.

Lemma pat_consequence_psi η p v φ (ψ ψ' : Prop) :
  pattern η p v φ ψ →
  (ψ → ψ') →
  pattern η p v φ ψ'.
Proof.
  unfold pattern. eauto using pure_wp_mono.
Qed.

Lemma pats_consequence_psi η ps vs φ (ψ ψ' : Prop) :
  patterns η ps vs φ ψ →
  (ψ → ψ') →
  patterns η ps vs φ ψ'.
Proof.
  unfold patterns. eauto using pure_wp_mono.
Qed.

Lemma cpat_CVal η p v φ ψ :
  pattern η p v φ ψ ->
  cpattern η (CVal p) (O2Ret v) φ ψ.
Proof.
  tauto.
Qed.

Lemma cpat_CExc η p v φ ψ :
  pattern η p v φ ψ ->
  cpattern η (CExc p) (O2Throw v) φ ψ.
Proof.
  tauto.
Qed.

Lemma cpat_COr η cp1 cp2 o φ ψ1 ψ2 :
  cpattern η cp1 o φ ψ1 ->
  cpattern η cp2 o φ ψ2 ->
  cpattern η (COr cp1 cp2) o φ (ψ1 /\ ψ2).
Proof.
  unfold cpattern. intros.
  eapply pure_wp_orelse; [ eassumption | ].
  eauto using pure_wp_mono.
Qed.

Lemma cpat_CEff η peff pk v k φ ψ1 ψ2 :
  pattern η peff v (λ δ, pattern δ pk (VCont k) φ ψ2) ψ1 ->
  cpattern η (CEff peff pk) (O3Perform v k) φ (ψ1 \/ ψ2).
Proof.
  unfold cpattern, pattern; intros. simpl.
  eapply pure_wp_bind_conseq; [ eapply pure_wp_mono; eauto | ].
  simpl; intros δ ?.
  eauto using pure_wp_mono.
Qed.

Fixpoint valid_cpattern_match {A E} cp (o : outcome3 A E) :=
  match cp, o with
  | CVal _, O3Ret _
  | CExc _, O3Throw _
  | CEff _ _, O3Perform _ _ =>
      true
  | COr cp1 cp2, _ =>
      valid_cpattern_match cp1 o || valid_cpattern_match cp2 o
  | _, _ =>
      false
  end.

Lemma invert_valid_match cp o :
  valid_cpattern_match cp o = false ->
  ∀ η, cextend η cp o = throw ().
Proof.
  intros Hvalid η.
  induction cp; destruct o; simpl in *; try congruence;
    (* Only the [COr cp1 cp2] case remains. *)
    unfold orelse;
    apply orb_false_elim in Hvalid as [H1 H2];
    apply IHcp1 in H1; apply IHcp2 in H2;
    by rewrite H1, H2, !try_throw.
Qed.

Lemma cpat_mismatch η cp o φ (ψ : Prop) :
  valid_cpattern_match cp o = false ->
  ψ ->
  cpattern η cp o φ ψ.
Proof.
  intros.
  unfold cpattern.
  rewrite invert_valid_match by assumption.
  by apply pure_wp_throw.
Qed.

(* -------------------------------------------------------------------------- *)

(* A judgement for the evaluation of structure items. *)

Definition struct_item ηδ item (φ : envs -> Prop) :=
  pure_wp (eval_sitem ηδ item) φ (λ _, False).

Definition struct_items ηδ sitems (φ : envs -> Prop) :=
  pure_wp (eval_sitems ηδ sitems) φ (λ _, False).


(* A judgement for the evaluation of module expressions. *)

Definition eval_module η me (φ : env -> Prop) :=
  pure_wp (eval_mexpr η me) (λ v, match v with
                                 | VStruct η' => φ η'
                                 | _ => False
                                 end) (λ _, False).


(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) :=
  pure_wp (eval_bindings η bs) φ (λ _, False).


(* A judgement for module coercion. *)

Definition coerces c η (φ : env -> Prop) :=
  pure_wp (coerce c (VStruct η)) (λ v, match v with
                                       | VStruct η' => φ η'
                                       | _ => False
                                       end) (λ _, False).


(* -------------------------------------------------------------------------- *)

Lemma struct_consequence ηδ item (φ φ' : envs -> Prop) :
  struct_item ηδ item φ ->
  (∀ ηδ, φ ηδ -> φ' ηδ) ->
  struct_item ηδ item φ'.
Proof.
  unfold struct_item. eauto using pure_wp_mono.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [structs]. *)

Lemma structs_nil ηδ (φ : envs -> Prop) :
  φ ηδ ->
  struct_items ηδ [] φ.
Proof.
  unfold struct_items.
  simpl_eval_sitems.
  by apply pure_wp_ret.
Qed.

Lemma structs_cons_unary ηδ item items (φ : envs -> Prop) :
  struct_item ηδ item (λ ηδ', struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros.
  simpl_eval_sitems.
  apply pure_wp_bind.
  eapply pure_wp_mono; eauto.
Qed.

Lemma structs_cons ηδ item items φ ψ :
  struct_item ηδ item ψ ->
  (∀ ηδ', ψ ηδ' -> struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros.
  simpl_eval_sitems.
  eapply pure_wp_bind_conseq; eauto.
Qed.

(* Syntax-directed reasoning rules for the judgement [struct]. *)

Lemma struct_let η δ bs (φ : envs -> Prop) ψ :
  bindings η bs ψ ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet bs) φ.
Proof.
  unfold struct_item; simpl_eval_sitem; intros.
  eapply pure_wp_bind_conseq; eauto using pure_wp_ret.
Qed.

Lemma struct_letrec η δ rbs (φ : envs -> Prop) ψ :
  ψ (eval_rec_bindings η rbs) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILetRec rbs) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem; auto using pure_wp_ret.
Qed.

Lemma struct_let_single η δ e name (spec : val -> Prop) :
  pure (eval η e) spec ->
  struct_item (η, δ) (ILet [Binding (PVar name) e])
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
                   η0 = [(name, clo)] ++ η /\
                   δ0 = [(name, clo)] ++ δ) .
Proof.
  intros; unfold struct_item; simpl_eval_sitem; simpl_eval_bindings.
  eapply pure_wp_simp. { simpl. apply SimpParRetRight. }
  eapply pure_wp_try2_conseq; eauto. 2: intros _ [].
  simpl; intros ? (? & -> & Hextend).
  unfold irrefutably_extend; simpl_extend.
  eapply pure_wp_ret; eauto.
Qed.

Lemma struct_let_pat η δ p e (spec : val -> Prop) (φ : envs -> Prop) ψ :
  pure (eval η e) (λ v, pattern [] p v ψ False) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet [Binding p e]) φ.
Proof.
  intros; unfold struct_item; simpl_eval_sitem; simpl_eval_bindings.
  eapply pure_wp_simp. { simpl. apply SimpParRetRight. }
  eapply pure_wp_try2_conseq; eauto. 2: intros _ [].
  simpl; intros v (? & -> & Hextend).
  eapply pure_wp_bind_conseq.
  { unfold pattern in Hextend. unfold irrefutably_extend; cbn.
    apply pure_wp_widen.
    eapply pure_wp_try_conseq; eauto. 2: intros _ [].
    eauto using pure_wp_ret. }
  auto using pure_wp_ret.
Qed.

Lemma struct_letrec_single η δ name af (spec : val -> Prop) :
  spec (VCloRec η [RecBinding name af] name) ->
  struct_item (η, δ)
    (ILetRec [RecBinding name af])
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
               η0 = [(name, clo)] ++ η /\
               δ0 = [(name, clo)] ++ δ) .
Proof.
  intros; unfold struct_item.
  simpl_eval_sitem.
  apply pure_wp_ret; eauto.
Qed.

Lemma struct_module η δ m me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ ((m, VStruct η') :: η, (m, VStruct η') :: δ)) ->
  struct_item (η, δ) (IModule m me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_wp_bind_conseq; eauto.
  intros []; try contradiction; eauto using pure_wp_ret.
Qed.

Lemma struct_open η δ me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ (η' ++ η, δ)) ->
  struct_item (η, δ) (IOpen me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_wp_bind_conseq.
  { unfold as_struct.
    eapply pure_wp_bind_conseq; eauto.
    intros [] Hx; try contradiction. apply pure_wp_widen;
    eauto using pure_wp_ret. }
  eauto using pure_wp_ret.
Qed.

Lemma struct_include η δ me (φ : envs -> Prop) module_spec :
  eval_module η me module_spec ->
  (∀ η', module_spec η' ->
         φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (IInclude me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_wp_bind_conseq.
  { unfold as_struct.
    eapply pure_wp_bind_conseq; eauto.
    intros [] Hx; try contradiction; apply pure_wp_widen;
      eauto using pure_wp_ret. }
  eauto using pure_wp_ret.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [module]. *)

Lemma pure_module η me φ :
  eval_module η me φ ->
  pure (eval_mexpr η me) (λ v, match v with
                               | VStruct η => φ η
                               | _ => False
                               end).
Proof.
  intros.
  eapply pure_wp_mono; eauto.
Qed.

Lemma module_struct η sitems φ :
  struct_items (η, []) sitems (λ '(η, δ), φ δ) ->
  eval_module η (MStruct sitems) φ.
Proof.
  intros; unfold eval_module.
  simpl_eval_mexpr.
  eapply pure_wp_bind_conseq; [ eassumption | ].
  intros [??]; auto using pure_wp_ret.
Qed.

Lemma module_struct_let η bs sitems φ ψ :
  bindings η bs ψ ->
  (∀ η', ψ η' ->
         struct_items (η' ++ η, η') sitems (λ '(_, δ), φ  δ)) ->
  eval_module η (MStruct ((ILet bs) :: sitems)) φ.
Proof.
  intros Hbs Hψsitems.
  eapply module_struct.
  { eapply structs_cons_unary.
    eapply struct_let; [ eassumption | ].
    intros; rewrite app_nil_r; by apply Hψsitems. }
Qed.

Lemma module_path η π φ :
  pure_wp (lookup_path η π) (λ v, match v with
                                 | VStruct η => φ η
                                 | _ => False
                                 end) (λ _, False) ->
  eval_module η (MPath π) φ.
Proof.
  unfold eval_module; simpl_eval_mexpr; intros.
  apply pure_wp_widen.
  eapply pure_wp_mono; eauto.
Qed.

Lemma module_coercion η me c φ :
  eval_module η me φ ->
  (∀ η', φ η' -> coerces c η' φ) ->
  eval_module η (MCoercion me c) φ.
Proof.
  intros; unfold eval_module.
  simpl_eval_mexpr.
  eapply pure_wp_bind_conseq; [ eassumption | ].
  intros [] Hx; try contradiction; apply pure_wp_widen;
    unfold coerces in *; auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [bindings]. *)

Lemma bindings_cons `{Encode A} η p e bs φ φ' (ψ : A -> Prop) :
  pure (eval η e) ψ ->
  bindings η bs φ' ->
  (∀ (x : A) (η' : env), ψ x -> φ' η' -> pattern η' p #x φ False) ->
  bindings η ((Binding p e) :: bs) φ.
Proof.
  unfold bindings. simpl. intros Hpure Hbs Hcov.
  simpl_eval_bindings.
  apply pure_wp_Par_vals_left.
  apply (pure_wp_mono_ret _ Hpure). intros v (a & -> & Ha).
  apply (pure_wp_mono_ret _ Hbs). intros η' Hη'.
  eapply pure_wp_widen, pure_wp_try_conseq. by apply Hcov.
  intros. by apply pure_wp_ret. intros _ [].
Qed.

Lemma bindings_nil `{Encode A} η (φ : env -> Prop) :
  φ [] ->
  bindings η [] φ.
Proof.
  unfold bindings. simpl_eval_bindings. apply pure_wp_ret.
Qed.

Lemma bindings_var `{Encode A} η v e bs φ' (ψ : A -> Prop) :
  pure (eval η e) ψ ->
  bindings η bs φ' ->
  bindings η
    (Binding (PVar v) e :: bs)
    (λ η,
      ∃ a η', ψ a /\ φ' η' /\ η = (v, #a) :: η').
Proof.
  intros.
  eapply bindings_cons; eauto.
  intros; unfold pattern. simpl_extend.
  apply pure_wp_ret; eauto.
Qed.

Lemma bindings_pair `{Encode A, Encode B} η p1 p2 e bs φ φ'
  (ψ1 : A -> Prop) (ψ2 : B -> Prop) :
  pure (eval η e) (λ '(a, b), ψ1 a /\ ψ2 b) ->
  bindings η bs φ' ->
  (∀ a b η', ψ1 a -> ψ2 b -> φ' η' -> pattern η' (PPair p1 p2) #(a, b) φ False) ->
  bindings η (Binding (PPair p1 p2) e :: bs) φ.
Proof.
  intros Hpure Hbs Hpat.
  eapply bindings_cons; eauto.
  intros [a b] η' [Hψ1 Hψ2] Hη'.
  auto.
Qed.
