From osiris Require Import base.
From osiris.lang Require Import syntax.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import simp.

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for evaluation struct items. *)

Implicit Type φ : envs -> Prop.

Definition struct ηδ item φ :=
  totalv (eval_sitem ηδ item) φ.

Definition structs ηδ sitems φ :=
  totalv (eval_sitems ηδ sitems) φ.

Lemma struct_consequence ηδ item (φ φ' : envs -> Prop) :
  struct ηδ item φ ->
  (∀ ηδ, φ ηδ -> φ' ηδ) ->
  struct ηδ item φ'.
Proof.
  unfold struct. eauto using totalv_consequence.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [structs]. *)

Lemma structs_nil ηδ φ :
  φ ηδ ->
  structs ηδ [] φ.
Proof.
  unfold structs. intros. simpl.
  by apply totalv_ret.
Qed.

Lemma structs_cons_unary ηδ item items φ :
  struct ηδ item (λ ηδ', structs ηδ' items φ) ->
  structs ηδ (item :: items) φ.
Proof.
  unfold structs, struct. intros. simpl.
  apply totalv_bind_unary.
  eapply totalv_consequence; eauto.
Qed.

Lemma structs_cons ηδ item items φ ψ :
  struct ηδ item ψ ->
  (∀ ηδ', ψ ηδ' -> structs ηδ' items φ) ->
  structs ηδ (item :: items) φ.
Proof.
  unfold structs, struct. intros. simpl.
  eapply totalv_bind; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the judgement [struct]. *)

Lemma struct_let η δ bs φ ψ :
  totalv (eval_bindings η bs) ψ ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct (η, δ) (ILet bs) φ.
Proof.
  unfold struct; simpl; intros.
  eapply totalv_bind; eauto.
  intros.
  apply totalv_ret; auto.
Qed.

Lemma struct_letrec η δ rbs φ ψ :
  ψ (eval_rec_bindings η rbs) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct (η, δ) (ILetRec rbs) φ.
Proof.
  unfold struct; simpl; intros.
  auto using totalv_ret.
Qed.

Lemma struct_module η δ m me φ module_spec :
  totalv (eval_mexpr η me) module_spec ->
  (∀ v, module_spec v ->
        φ ((m, v) :: η, (m, v) :: δ)) ->
  struct (η, δ) (IModule m me) φ.
Proof.
  unfold struct; simpl; intros.
  eapply totalv_bind; eauto.
  eauto using totalv_ret.
Qed.

Lemma struct_open η δ me φ module_spec env_spec :
  totalv (eval_mexpr η me) module_spec ->
  (∀ m, module_spec m ->
        totalv (val_as_struct m) env_spec) ->
  (∀ η', env_spec η' ->
        φ (η' ++ η, δ)) ->
  struct (η, δ) (IOpen me) φ.
Proof.
  unfold struct; simpl; intros.
  eapply totalv_bind; last first.
  { eauto using totalv_ret. }
  unfold as_struct.
  eapply totalv_bind; eauto.
Qed.

Lemma struct_include η δ me φ module_spec env_spec :
  totalv (eval_mexpr η me) module_spec ->
  (∀ m, module_spec m ->
        totalv (val_as_struct m) env_spec) ->
  (∀ η', env_spec η' ->
         φ (η' ++ η, η' ++ δ)) ->
  struct (η, δ) (IInclude me) φ.
Proof.
  unfold struct; simpl; intros.
  eapply totalv_bind; last first.
  { eauto using totalv_ret. }
  unfold as_struct.
  eapply totalv_bind; eauto.
Qed.
