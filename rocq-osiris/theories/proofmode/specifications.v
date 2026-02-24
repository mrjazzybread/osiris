From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.

(* --------------------------------------------------------------------------*)
(* The following part defines module specifications. *)

From iris.base_logic Require Import iprop.

Lemma lookup_name_nil name :
  lookup_name [] name = None.
Proof. reflexivity. Qed.

Lemma lookup_name_app_l name xs ys a :
  lookup_name xs name = Some a →
  lookup_name (xs ++ ys) name = Some a.
Proof.
  induction xs as [|[x v] xs IH].
  - rewrite lookup_name_nil. discriminate 1.
  - simpl.
    destruct (name =? x)%string.
    + inversion 1; by subst.
    + apply IH.
Qed.

Lemma lookup_name_app_r name xs ys :
  lookup_name xs name = None →
  lookup_name (xs ++ ys) name = lookup_name ys name.
Proof.
  induction xs as [|[x v] xs IH].
  - auto.
  - simpl.
    destruct (name =? x)%string.
    + discriminate 1.
    + apply IH.
Qed.

Section Modules.
  Context `{!osirisGS Σ}.

  (* Specification over a whole path. *)

  Definition path_spec `{Encode A} (p : path) (spec : A → iProp Σ) (η : env) : iProp Σ :=
    ∃ x, ⌜lookup_path η p = Some #x⌝ ∗ spec x.

  Definition var_spec `{Encode A} (name : var) (spec : A → iProp Σ) (η : env) : iProp Σ :=
    ∃ x, ⌜lookup_name η name = Some #x⌝ ∗ spec x.

  Lemma var_spec_app `{Encode A} x (Φ : A → iProp Σ) δ η :
    var_spec x Φ δ -∗
    var_spec x Φ (δ ++ η).
  Proof.
    iIntros "(% & % & $)".
    iPureIntro.
    by apply lookup_name_app_l.
  Qed.

  Lemma var_spec_mono `{Encode A} {Φ : A → iProp Σ} (Φ' : A → iProp Σ) x η :
    var_spec x Φ' η -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    var_spec x Φ η.
  Proof.
    iIntros "(%a & % & HΦ') Hmono".
    iExists a. iSplit; [ iPureIntro; assumption | ].
    iApply ("Hmono" with "HΦ'").
  Qed.

  Record enc_spec :=
    Spec
      {
        res_type : Type;
        res_type_enc : Encode res_type;
        name : var;
        spec : res_type → iProp Σ;
      }.
  (* Make it so [enc_spec] displays as [Spec name Φ]. *)
  Global Arguments Spec {_ _}.
  Global Add Printing Constructor enc_spec.

  Instance dom_env : Dom (env) (gset var) := λ η, list_to_set (η.*1).

  Definition context (specs : list enc_spec) d : env → iProp Σ :=
    λ η, (⌜dom η = d⌝ ∗
           [∗ list] s ∈ specs,
            @var_spec s.(res_type) s.(res_type_enc) s.(name) (λ res, □ s.(spec) res) η)%I.

  Global Instance context_pers specs d η : Persistent (context specs d η).
  Proof. apply _. Qed.

  Check
  context [
      Spec "+" (λ add, iSpec τ[Z; Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})%I);
      Spec "-" (λ sub, iSpec τ[Z; Z] sub (λ i j m, imp m {{ λ n, ⌜(n = i - j)%Z⌝ }})%I)
    ] {["+";"-";"*"]}.

  Lemma extract_context `{Encode A} {η} xs ys d name (spec : A → iProp Σ) :
    context (xs ++ [Spec name spec] ++ ys) d η -∗ var_spec name spec η.
  Proof.
    unfold context.
    iIntros "(%Hdom & Hspecs)".
    iPoseProof (big_sepL_app with "Hspecs") as "(_ & Hspecs)".
    iPoseProof (big_sepL_app with "Hspecs") as "(Hspec & _)".
    iDestruct "Hspec" as "[#Hspec _]".
    iApply (var_spec_mono with "Hspec").
    iIntros (res) "#Hspec'". iApply "Hspec'".
  Qed.

  (* We immediately reduce [path_spec] to [var_spec] if the path is a singleton. *)

  Lemma path_spec_singleton `{Encode A} name (Φ : A → iProp Σ) η :
    var_spec name Φ η -∗ path_spec [name] Φ η.
  Proof.
    unfold var_spec.
    iIntros "(%x & Hlookup & HΦ)".
    iExists x. simpl. iFrame.
  Qed.

  (* If the path is a cons, we find the specification for the module
     at the head of the path. *)

  Lemma path_spec_cons {A : Type} `{Encode A} {Φ : A → iProp Σ} {η x p} mspec :
    var_spec x mspec η -∗
    (∀ (δ : env), mspec δ -∗ path_spec p Φ δ) -∗
    path_spec (x :: p) Φ η.
  Proof.
    iIntros "(%δ & %Hlookup & Hpost) Hcov".
    iDestruct ("Hcov" with "Hpost") as "(% & %Hlookup' & HΦ)".
    iFrame. iPureIntro.
    simpl. destruct p.
    - simpl in Hlookup'. discriminate Hlookup'.
    - rewrite Hlookup. apply Hlookup'.
  Qed.


  (* If the environment is a cons, where the head does not match the
     name we are looking for, we keep looking in the tail of the
     environment. *)

  Lemma var_spec_cons {A : Type} `{Encode A} {Φ : A → iProp Σ} {η v} x y :
    (x =? y)%string = false →
    var_spec x Φ η -∗
    var_spec x Φ ((y, v) :: η).
  Proof.
    iIntros (Hneq) "(%a & %Hlookup & $)".
    iPureIntro.
    simpl lookup_name; rewrite Hneq; apply Hlookup.
  Qed.

  (* If the environment is a cons, where the head does not match the
     name we are looking for, we keep looking in the tail of the
     environment. *)

  Lemma var_spec_here {A : Type} `{Encode A} {Φ : A → iProp Σ} {η v} x y :
    (x =? y)%string = true →
    Φ v -∗
    var_spec x Φ ((y, #v) :: η).
  Proof.
    iIntros (Heq) "$".
    iPureIntro.
    simpl lookup_name; rewrite Heq. reflexivity.
  Qed.

  (* If the environment is an app, where the name we are looking for
     is not in the first fragment, we keep looking in the second
     fragment. *)

  Lemma var_spec_app_r `{Encode A} {Φ : A → iProp Σ} {η x} δ d mspec :
    x ∉ d →
    context mspec d δ -∗
    var_spec x Φ η -∗
    var_spec x Φ (δ ++ η).
  Proof.
    iIntros (Hnin) "(%Hdom & _) Hη".
    iInduction δ as [| [y v] δ ] "IH" forall (d Hnin Hdom).
    - iApply "Hη".
    - simpl. iApply var_spec_cons.
      + unfold dom, dom_env in Hdom. simpl in Hdom.
        rewrite <- Hdom in Hnin.
        apply not_elem_of_union in Hnin as [Hnin _].
        apply not_elem_of_singleton in Hnin.
        apply String.eqb_neq. apply Hnin.
      + iApply ("IH" $! (dom δ) with "[] [//] Hη").
        iPureIntro.
        unfold dom, dom_env in Hdom. simpl in Hdom.
        rewrite <- Hdom in Hnin.
        apply not_elem_of_union in Hnin as [_ Hnin].
        apply Hnin.
  Qed.

  (* If the environment is an app, where the name we are looking for
     is not in the first fragment, we keep looking in the second
     fragment. *)

  Lemma var_spec_app_l `{Encode A} {Φ : A → iProp Σ} {η x} δ d xs ys :
    context (xs ++ [Spec x Φ] ++ ys) d δ -∗
    var_spec x Φ (δ ++ η).
  Proof.
    iIntros "Hcontext".
    iPoseProof (extract_context with "Hcontext") as "Hspec".
    iApply var_spec_app. iApply "Hspec".
  Qed.

  (* We can pick out the right specification from a context. *)

  Lemma var_spec_context `{Encode A} {Φ : A → iProp Σ} {x} δ d specs :
    Spec x Φ ∈ specs →
    context specs d δ -∗
    var_spec x Φ δ.
  Proof.
    iIntros (Hin) "Hcontext".
    apply list_elem_of_split in Hin as (l1 & l2 & ->).
    iPoseProof (extract_context with "Hcontext") as "$".
  Qed.

  Lemma var_spec_context_mono `{Encode A} {Φ : A → iProp Σ} Φ' {x} δ d specs :
    Spec x Φ' ∈ specs →
    context specs d δ -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    var_spec x Φ δ.
  Proof.
    iIntros (Hin) "Hcontext Hmono".
    apply list_elem_of_split in Hin as (l1 & l2 & ->).
    iPoseProof (extract_context with "Hcontext") as "Hspec".
    iApply (var_spec_mono with "Hspec Hmono").
  Qed.

  Lemma imp_EPath_spec {E : coPset} {Ψ : iEff Σ} {A : Type} {EncA : Encode A}
    {Φ : A → iProp Σ} {ζ : exn → iProp Σ} (η : env) (p : path) :
    path_spec p Φ η -∗
    imp eval η (EPath p) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} : iProp Σ.
  Proof.
    iIntros "(% & %Hlookup & Hspec)".
    simpl_eval.
    iApply imp_widen.
    rewrite Hlookup.
    iExists x; auto.
  Qed.

  Lemma imp_EPath_var {E Ψ ζ} {A : Type} `{Encode A} {η p} (a : A) :
    lookup_path η p = Some #a →
    ⊢ imp (eval η (EPath p)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ λ a', ⌜a' = a⌝ }}.
  Proof.
    iIntros (Hlookup).
    iApply imp_EPath; eauto.
  Qed.

End Modules.

Section TacticTests.

  Context `{!osirisGS Σ}.

  Local Open Scope Z.

  (* We define a short program, [e]:
     let x = 2 in
     let y = z in
     Module1.add (Module2.Module3.sub y x) x *)

  Definition e :=
    ELet [Binding (PVar "x") (EInt 2)] (
        ELet [Binding (PVar "y") (EPath ["z"])] (
            EApp
              (EApp (EPath ["Module1"; "add"])
                 (EApp
                    (EApp (EPath ["Module2";"Module3";"sub"]) (EPath ["y"]))
                    (EPath ["x"])))
              (EPath ["x"])
          )
      ).

  (* We then verify this program under the assumption that:
     - [z] is in the environment and is positive
     - Module1 is in the environment and contains [add]
     - Module2 is in the environment and contains [Module3],
       which contains [sub] *)

  Definition add_spec add : iProp Σ := □ iSpec τ[Z;Z] add (λ (i j : Z) m, imp m {{ λ k, ⌜(k = i + j)%Z⌝ }})%I.
  Definition sub_spec sub : iProp Σ := □ iSpec τ[Z;Z] sub (λ (i j : Z) m, imp m {{ λ k, ⌜(k = i - j)%Z⌝ }})%I.

  Definition module3_spec := context [Spec "sub" sub_spec] {["sub"]}.
  Definition module2_spec := context [Spec "Module3" module3_spec] {["Module3"; "some"; "other"; "stuff"]}.

  Lemma example_proof δ η :
    var_spec "z" (λ (i : Z), ⌜i > 0⌝) η -∗
    context [Spec "Module1" (context [Spec "some_other_val" (λ (_ : val), True);
                                      Spec "add" add_spec] {["add"]})] {["Module1"]} δ -∗
    context [Spec "Module2" module2_spec] {["Module2"]} η -∗
    imp (eval (δ ++ η) e) {{ λ (i : Z), ⌜i > 0⌝ }}.
  Proof.
    iIntros "#zspec #δspec #ηspec".
    iApply (imp_ELet_var (B:=Z)). { iApply imp_EInt. }
    iIntros (? ->).
    iApply (imp_ELet_var (B:=Z)).
    { iApply imp_EPath_spec.
      iApply path_spec_singleton.
      iApply var_spec_cons; first auto.
      iApply (var_spec_app_r with "δspec"). { set_solver. }
      iAssumption. }
    iIntros (y) "%yspec".
    iApply (imp_EApp τ[Z;Z]).
    { iApply imp_EPath_spec.
      iApply path_spec_cons.
      { iApply var_spec_cons; first auto.
        iApply var_spec_cons; first auto.
        iApply var_spec_app.
        iApply (var_spec_context_mono with "δspec"); [ repeat constructor | auto ]. }
      iIntros (?) "#module1spec".
      iApply path_spec_singleton.
      iApply (var_spec_context_mono with "module1spec"); first repeat constructor.
      auto. }
    { iApply (imp_EApp τ[Z;Z]).
      { iApply imp_EPath_spec.
        iApply path_spec_cons.
        { iApply var_spec_cons; first auto.
          iApply var_spec_cons; first auto.
          iApply (var_spec_app_r with "δspec"). { set_solver. }
          iApply (var_spec_context with "ηspec"). repeat constructor. }
        iIntros (?) "#module2spec".
        iApply path_spec_cons. { iApply (var_spec_context with "module2spec"). repeat constructor. }
        iIntros (?) "#module3spec".
        iApply path_spec_singleton.
        iApply (var_spec_context_mono with "module3spec"); [ repeat constructor | auto ]. }
      { iApply imp_EPath_spec.
        iApply path_spec_singleton.
        iApply var_spec_here; first auto.
        instantiate (1:=(λ y',⌜y'=y⌝)%I). auto. }
      { iApply imp_EPath_spec.
        iApply path_spec_singleton.
        iApply var_spec_cons; first auto.
        iApply var_spec_here; first auto.
        instantiate (1:=(λ y',⌜y'=2⌝)%I). auto. }
      iIntros (??) "-> -> %m Hm !>".
      iApply "Hm". }
    { iApply imp_EPath_spec.
      iApply path_spec_singleton.
      iApply var_spec_cons; first auto.
      iApply var_spec_here; first auto.
      instantiate (1:=(λ y',⌜y'=2⌝)%I). auto. }
    iIntros (??) "-> -> %m Hm !>".
    iApply (imp_mono_ret with "Hm").
    iIntros (x ->). iPureIntro.
    lia.
  Qed.

End TacticTests.
