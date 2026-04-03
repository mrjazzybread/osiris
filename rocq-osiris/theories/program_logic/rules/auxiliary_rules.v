From iris.proofmode Require Import proofmode.

From osiris Require Import lang.
From osiris.program_logic Require Import ewp.
From osiris.program_logic.rules Require Import impure_rules stop_rules.

From osiris.program_logic.pure Require Import pattern_rules.

(** This file contains [imp] rules for module and binding evaluation. *)

Section imp_eval.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Lemma imp_module sitems {Q : env -> iProp Σ} η :
    imp (eval_sitems (η, []) sitems) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ '((_, δ) : envs), Q δ }} -∗
    imp (eval_mexpr η (MStruct sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr.
    iApply (imp_bind with "Hsitems").
    iIntros ([η' δ']) "HQ".
    iApply (imp_ret with "HQ"). encode.
  Qed.

  Lemma imp_sitems_cons {Q : envs → iProp Σ} (φ : envs → iProp Σ) sitem sitems (ηδ : envs) :
    imp (eval_sitem ηδ sitem) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    (∀ ηδ, φ ηδ -∗ imp eval_sitems ηδ sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp (eval_sitems ηδ (sitem :: sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply (imp_bind with "Hsitem").
    iIntros ([η' δ']) "Hφ".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_nil Q ηδ :
    Q ηδ -∗
    imp eval_sitems ηδ [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    simpl_eval_sitems.
    iIntros "HQ". destruct ηδ.
    by iApply (imp_ret with "HQ").
  Qed.

  Lemma imp_sitem_letrec_singleton (spec : val → iProp Σ) x af (η δ : env) :
    spec (VCloRec η [RecBinding x af] x) -∗
    imp (eval_sitem (η, δ) (ILetRec [RecBinding x af])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η0, δ0),
            ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem.
    iApply imp_ret. instantiate (1:=(_,_)). reflexivity.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Lemma imp_sitems_letrec sitems (spec : val → iProp Σ) x af (η δ : env) Q :
    spec (VCloRec η [RecBinding x af] x) -∗
    (∀ v, spec v -∗ imp (eval_sitems ((x, v) :: η, (x, v) :: δ) sitems) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}) -∗
    imp (eval_sitems (η, δ) ((ILetRec [RecBinding x af]) :: sitems)) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hspec Hcov".
    iApply (imp_sitems_cons with "[Hspec]").
    { iApply (imp_sitem_letrec_singleton with "Hspec"). }
    iIntros ([??]) "(% & Hspec & [-> ->])".
    iApply ("Hcov" with "Hspec").
  Qed.

  Lemma imp_struct_let bs (Q : envs → iProp Σ) (Q' : env → iProp Σ) η δ :
    imp (eval_bindings η bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q' }} -∗
    (∀ η', Q' η' -∗ Q (η' ++ η, η' ++ δ)) -∗
    imp (eval_sitem (η, δ) (ILet bs)) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem.
    iApply (imp_bind with "Hbindings").
    iIntros (η') "HQ'".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hmono" with "HQ'").
  Qed.

  Lemma imp_bindings_cons `{Encode A} (Φ : A → iProp Σ) η e bs Q P p :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ (a : A), Φ a -∗ ⌜pattern η [] p #a (P a) False⌝) -∗
    imp eval_bindings η bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }} -∗
    imp eval_bindings η (Binding p e :: bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
      {{ λ η, ∃ a η' δ', ⌜η = η' ++ δ'⌝ ∗ Φ a ∗ ⌜P a η'⌝ ∗ Q δ' }}.
  Proof.
    iIntros "He Hpat Hbs".
    simpl_eval_bindings.
    iApply (imp_bind_par with "[He Hpat] Hbs").
    { iApply (imp_bind with "He").
      iIntros (?) "HΦ". iApply imp_widen.
      iDestruct ("Hpat" with "HΦ") as "%Hpat".
      unfold pattern in Hpat. simpl.
      destruct (eval_pat η [] p #x).
      - instantiate (1 := (λ η, ∃ x, Φ x ∗ ⌜P x η⌝)%I).
        iFrame. iFrame "%". auto.
      - contradiction. }
    iIntros (η' δ) "(%a & HΦ & HP) Hη".
    iApply imp_ret. reflexivity.
    iFrame. auto.
  Qed.

  Lemma imp_bindings_nil η :
    ⊢ imp eval_bindings η [] @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ η, ⌜η = []⌝ }}.
  Proof.
    simpl_eval_bindings.
    iApply imp_ret. reflexivity. auto.
  Qed.

  Lemma imp_bind_var `{Encode A} (Φ : A → iProp Σ) η e name :
    imp eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    imp eval_bindings η [Binding (PVar name) e] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
          {{ λ (η' : env), ∃ a : A, Φ a ∧ ⌜η' = [(name, #a)]⌝ }}.
  Proof.
    iIntros "HSpec".
    iApply (imp_wand with "[HSpec]").
    { iApply (imp_bindings_cons with "HSpec").
      - iIntros (a) "HΦ".
        iPureIntro; apply pat_PVar.
        instantiate (1:=(λ a η, η = [(name, #a)])).
        reflexivity.
      - iApply imp_bindings_nil. }
    iIntros (η') "(%a & % & % & -> & HΦ & -> & ->)".
    iFrame. auto.
  Qed.

  Lemma imp_struct_let_single `{Encode A} (spec : A → iProp Σ) name e (η δ : env) :
    imp (eval η e) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    imp (eval_sitem (η, δ) (ILet [Binding (PVar name) e])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η', δ'),
            ∃ a : A, spec a ∧ ⌜η' = (name, #a) :: η ∧ δ' = (name, #a) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    iApply (imp_struct_let with "[Hspec]").
    { iApply (imp_bind_var with "Hspec"). }
    iIntros (?) "(%a & Hspec & ->)".
    iFrame. iPureIntro; split; reflexivity.
  Qed.

  Lemma imp_sitem_extend es (Q : envs -> iProp Σ) (η δ : env) :
    imp eval_type_extensions es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ (δ' : env), Q (δ' ++ η, δ' ++ δ) }} -∗
    imp eval_sitem (η,δ) (IExtend es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem.
    iApply (imp_bind _ _ (λ δ', ret (δ' ++ η, δ' ++ δ)) with "Hes").
    iIntros (η') "HQ".
    iApply (imp_ret with "HQ"); reflexivity.
  Qed.

  Lemma imp_sitems_extend sitems x Q η δ :
    (∀ l, l ↦ #() -∗
          imp eval_sitems ((x, VLoc l) :: η, (x, VLoc l) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η,δ) ((IExtend [x]) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (imp_sitems_cons).
    { iApply (imp_sitem_extend).
      iApply imp_bind. iApply imp_alloc.
      iIntros (l) "Hl"; simpl; iApply imp_ret. reflexivity.
      Unshelve.
      2: (apply (λ ηδ,
                   (∃ l, ⌜ηδ = ((x, VLoc l) :: η, (x, VLoc l):: δ)⌝ ∗ l ↦ VUnit)%I)).
      simpl.
      iExists l; iFrame. iPureIntro; reflexivity. }
    iIntros ([??]) "(% & -> & Hl)".
    iApply ("Hcov" with "Hl").
  Qed.

  Lemma imp_sitem_open me Q φ (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q (δ' ++ η, δ) ) -∗
    imp eval_sitem (η, δ) (IOpen me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "[Hme]").
    { iApply (imp_as_struct with "Hme"). }
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitem_module m me Q (φ : env → iProp Σ) (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q ((m, #δ') :: η, (m, #δ') :: δ) ) -∗
    imp eval_sitem (η, δ) (IModule m me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "Hme").
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_module {m me sitems Q} (φ : env → iProp Σ) (η δ : env) :
    imp eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ imp eval_sitems ((m, #δ') :: η, (m, #δ') :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η, δ) ((IModule m me) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov".
    iApply (imp_sitems_cons with "[Hme]").
    { iApply (imp_sitem_module with "Hme").
      iIntros (δ') "Hφ".
      instantiate (1 := (λ ηδ, ∃ δ', φ δ' ∗ ⌜ηδ = (_,_)⌝)%I).
      iFrame. auto. }
    iIntros (?) "(% & Hφ & ->)".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_type_extension_cons e es Q :
    ▷ (∀ l, l ↦ #() -∗
            imp eval_type_extensions es @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ δ, Q ((e, VLoc l) :: δ) }}) -∗
    imp eval_type_extensions (e :: es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes". simpl.
    iApply (imp_bind with "[Hes]").
    { iApply imp_alloc'. iIntros "!>" (l) "Hl".
      iSpecialize ("Hes" with "Hl").
      iExact "Hes". }
    iIntros (l) "Hes".
    iApply (imp_bind with "Hes").
    iIntros (η) "HQ".
    iApply (imp_ret with "HQ"). reflexivity.
  Qed.

  Lemma imp_type_extension_nil :
    ⊢ imp eval_type_extensions [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ λ η, ⌜η = []⌝ }}.
  Proof. simpl. by iApply imp_ret. Qed.

  Lemma imp_let `{Encode A} (spec : A → iProp Σ) x e Q η δ :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    (∀ a, spec a -∗ Q ((x, #a) :: η, (x, #a) :: δ)) -∗
    imp eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He HQ".
    iApply (imp_wand _ (eval_sitem (η, δ) (ILet [Binding (PVar x) e])) with "[He]").
    iApply (imp_struct_let_single with "He").
    iIntros ([η' δ']) "(%a & Ha & -> & ->)".
    iApply ("HQ" with "Ha").
  Qed.

  Lemma imp_sitems_let `{Encode A} (spec : A → iProp Σ) sitems x e Q η δ :
    imp eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
      (∀ a, spec a -∗
            imp eval_sitems ((x, #a) :: η, (x, #a) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
      imp eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    iApply (imp_let with "He").
    instantiate (1 := (λ ηδ, ∃ a, spec a ∗ ⌜ηδ = (x ~> #a; η, x ~> #a; δ)⌝)%I).
    iIntros (a) "Ha". iFrame. auto.
    iIntros (ηδ) "(%a & Ha & ->)".
    iApply ("Hcov" with "Ha").
  Qed.

  Lemma imp_sitems_external Φ sitems x e Q η δ :
    imp eval [] e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ v, Φ v -∗ imp eval_sitems ((x, v) :: η, (x, v) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    imp eval_sitems (η, δ) ((IExternal x e)::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    { simpl_eval_sitem.
      instantiate (1 := (λ ηδ, ∃ x0, ⌜ηδ = (x ~> x0; η, x ~> x0; δ)⌝ ∗ Φ x0)%I).
      iApply (imp_bind with "He").
      iIntros (?) "HΦ".
      iApply imp_ret; first (instantiate (1:=(_,_)); encode).
      by iFrame. }
    iIntros (?) "(% & -> & HΦ)".
    iApply ("Hcov" with "HΦ").
  Qed.

End imp_eval.
