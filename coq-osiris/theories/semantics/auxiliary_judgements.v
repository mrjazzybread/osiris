From osiris Require Import base.
From osiris.lang Require Import syntax encode sugar.
From osiris.semantics Require Import code eval simplification pure.

(* This file defines judgements for Hoare-style reasoning on
   the auxiliary functions in [semantics/eval.v]. *)

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

(* The judgement [pattern η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition cpattern η p o (φ : env -> Prop) (ψ : Prop) :=
  total (cextend η p o) φ (λ (_ : unit), ψ).

Definition pattern η p v (φ : env -> Prop) (ψ : Prop) :=
  total (extend η p v) φ (λ (_ : unit), ψ).

Definition patterns η ps vs (φ : env -> Prop) (ψ : Prop) :=
  total (extends η ps vs) φ (λ (_ : unit), ψ).


(* A consequence rule. *)

Lemma pat_consequence η p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
  pattern η p v φ ψ →
  (∀ η, φ η → φ' η) →
  (ψ → ψ') →
  pattern η p v φ' ψ'.
Proof.
  unfold pattern. eauto using total_consequence.
Qed.

Lemma pat_consequence_psi η p v φ (ψ ψ' : Prop) :
  pattern η p v φ ψ →
  (ψ → ψ') →
  pattern η p v φ ψ'.
Proof.
  unfold pattern. eauto using total_consequence.
Qed.

Lemma pats_consequence_psi η ps vs φ (ψ ψ' : Prop) :
  patterns η ps vs φ ψ →
  (ψ → ψ') →
  patterns η ps vs φ ψ'.
Proof.
  unfold patterns. eauto using total_consequence.
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
  eapply total_orelse; [ eassumption | ].
  eauto using total_consequence.
Qed.

(* -------------------------------------------------------------------------- *)

(* A judgement for the evaluation of structure items. *)

Definition struct_item ηδ item (φ : envs -> Prop) :=
  totalv (eval_sitem ηδ item) φ.

Definition struct_items ηδ sitems (φ : envs -> Prop) :=
  totalv (eval_sitems ηδ sitems) φ.


(* A judgement for the evaluation of module expressions. *)

Definition eval_module η me (φ : env -> Prop) :=
  totalv (eval_mexpr η me) (λ v, match v with
                                 | VStruct η' => φ η'
                                 | _ => False
                                 end).


(* A judgement for the evaluation of let bindings. *)

Definition bindings η bs (φ : env -> Prop) :=
  totalv (eval_bindings η bs) φ.


(* A judgement for module coercion. *)

Definition coerces c η (φ : env -> Prop) :=
  totalv (coerce c (VStruct η)) (λ v, match v with
                                       | VStruct η' => φ η'
                                       | _ => False
                                       end).


(* -------------------------------------------------------------------------- *)

Lemma struct_consequence ηδ item (φ φ' : envs -> Prop) :
  struct_item ηδ item φ ->
  (∀ ηδ, φ ηδ -> φ' ηδ) ->
  struct_item ηδ item φ'.
Proof.
  unfold struct_item. eauto using totalv_consequence.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [structs]. *)

Lemma structs_nil ηδ (φ : envs -> Prop) :
  φ ηδ ->
  struct_items ηδ [] φ.
Proof.
  unfold struct_items. intros. simpl.
  by apply totalv_ret.
Qed.

Lemma structs_cons_unary ηδ item items (φ : envs -> Prop) :
  struct_item ηδ item (λ ηδ', struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros. simpl.
  apply totalv_bind_unary.
  eapply totalv_consequence; eauto.
Qed.

Lemma structs_cons ηδ item items φ ψ :
  struct_item ηδ item ψ ->
  (∀ ηδ', ψ ηδ' -> struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros. simpl.
  eapply totalv_bind; eauto.
Qed.

(* Syntax-directed reasoning rules for the judgement [struct]. *)

Lemma struct_let η δ bs (φ : envs -> Prop) ψ :
  bindings η bs ψ ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet bs) φ.
Proof.
  unfold struct_item; simpl; intros.
  eapply totalv_bind; eauto.
  intros.
  apply totalv_ret; auto.
Qed.

Lemma struct_letrec η δ rbs (φ : envs -> Prop) ψ :
  ψ (eval_rec_bindings η rbs) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILetRec rbs) φ.
Proof.
  unfold struct_item; simpl; intros.
  auto using totalv_ret.
Qed.

Lemma struct_let_single η δ e name (spec : val -> Prop) :
  pure (eval η e) spec ->
  struct_item (η, δ) (ILet [Binding (PVar name) e])
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
                   η0 = [(name, clo)] ++ η /\
                   δ0 = [(name, clo)] ++ δ) .
Proof.
  intros; unfold struct_item; simpl.
  eapply totalv_simp. { apply SimpParRetRight. }
  eapply totalv_try2. { eapply pure_totalv; eassumption. }
  simpl; intros ? (? & -> & Hextend).
  eapply totalv_ret. eauto.
Qed.

Lemma struct_let_pat η δ p e (spec : val -> Prop) (φ : envs -> Prop) ψ :
  pure (eval η e) (λ v, pattern [] p v ψ False) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet [Binding p e]) φ.
Proof.
  intros; unfold struct_item; simpl.
  eapply totalv_simp. { apply SimpParRetRight. }
  eapply totalv_try2. { eapply pure_totalv; eassumption. }
  simpl; intros v (? & -> & Hextend).
  eapply totalv_bind.
  { unfold pattern in Hextend. unfold irrefutably_extend; cbn.
    rewrite totalv_widen.
    eapply totalv_try; [ eassumption | ].
    eauto using totalv_ret. }
  auto using totalv_ret.
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
  intros.
  unfold struct_item.
  apply totalv_ret.
  eauto.
Qed.

Lemma struct_module η δ m me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ ((m, VStruct η') :: η, (m, VStruct η') :: δ)) ->
  struct_item (η, δ) (IModule m me) φ.
Proof.
  unfold struct_item; simpl; intros.
  eapply totalv_bind; eauto.
  intros []; try contradiction; eauto using totalv_ret.
Qed.

Lemma struct_open η δ me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ (η' ++ η, δ)) ->
  struct_item (η, δ) (IOpen me) φ.
Proof.
  unfold struct_item; simpl; intros.
  eapply totalv_bind.
  { unfold as_struct.
    eapply totalv_bind; eauto.
    intros []; try contradiction; rewrite totalv_widen;
    eauto using totalv_ret. }
  eauto using totalv_ret.
Qed.

Lemma struct_include η δ me (φ : envs -> Prop) module_spec :
  eval_module η me module_spec ->
  (∀ η', module_spec η' ->
         φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (IInclude me) φ.
Proof.
  unfold struct_item; simpl; intros.
  eapply totalv_bind.
  { unfold as_struct.
    eapply totalv_bind; eauto.
    intros []; try contradiction; rewrite totalv_widen;
      eauto using totalv_ret. }
  eauto using totalv_ret.
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
  apply pure_totalv.
  eapply totalv_consequence; eauto.
Qed.

Lemma module_struct η sitems φ :
  struct_items (η, []) sitems (λ '(η, δ), φ δ) ->
  eval_module η (MStruct sitems) φ.
Proof.
  intros  Hcov.
  unfold module; simpl.
  eapply totalv_bind; [ eassumption | ].
  intros [??]; auto using totalv_ret.
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
  totalv (lookup_path η π) (λ v, match v with
                                 | VStruct η => φ η
                                 | _ => False
                                 end) ->
  eval_module η (MPath π) φ.
Proof.
  unfold eval_module; simpl; intros.
  rewrite totalv_widen.
  eapply totalv_consequence; [ eassumption | ].
  auto.
Qed.

Lemma module_coercion η me c φ :
  eval_module η me φ ->
  (∀ η', φ η' -> coerces c η' φ) ->
  eval_module η (MCoercion me c) φ.
Proof.
  unfold module. intros. simpl.
  eapply totalv_bind; [ eassumption | ].
  intros []; try contradiction; rewrite totalv_widen;
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
  destruct_pure a.
  eapply totalv_simp.
  { eapply SimpPar; eauto with simp. }
  eapply totalv_simp; [ apply SimpParRetLeft | ].
  eapply totalv_try2; [ eassumption | ].
  intros η' Hη'. cbn. rewrite totalv_widen.
  eapply totalv_try.
  { by apply Hcov. }
  intros. by apply total_ret.
Qed.

Lemma bindings_nil `{Encode A} η (φ : env -> Prop) :
  φ [] ->
  bindings η [] φ.
Proof.
  unfold bindings. apply totalv_ret.
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
  intros; unfold pattern; simpl.
  apply total_ret; eauto.
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
