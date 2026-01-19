From osiris.lang Require Import type_nel.
From iris.bi Require Import interface.

From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import ewp basic_rules pure.fun_spec.

From iris.proofmode Require Import proofmode.

From Equations Require Import Equations.

(** Quantifiers *)

From iris.bi Require Import interface.
Include universes.

(* Have to redefine [tfold] for universe reasons. *)

Definition tfold {X Y} {τ : types}
  (step : ∀ {A : Type}, (A → Y) → Y)
  (base : X → Y)
  : (τ -#> X) → Y :=
(*  We use a [fix] because, for better term-printing in proofs. *)
  (fix rec {τ} : (τ -#> X) → Y :=
     match τ with
     | Tbase T =>
         λ f, step (λ x, base (f x))
     | type_nel.Tcons T τ' =>
         λ f, step (λ x, @rec τ' (f x))
     end) τ.
Global Arguments tfold {_ _ !_} _ _ /.

Definition bi_tforall {PROP : bi} {τ : types} (Ψ : τ → PROP) : PROP :=
  tfold (λ (T : Type@{_}) (b : T → PROP), ∀ x : T, b x)%I Datatypes.id (tbind Ψ).
Global Arguments tforall {!_} _ /.
Definition bi_texists {PROP : bi} {τ : types} (Ψ : τ → PROP) : PROP :=
  tfold (@bi_exist PROP) Datatypes.id (@tbind PROP τ Ψ).
Global Arguments texists {!_} _ /.

Notation "'∀#' x .. y , P" := (bi_tforall (λ x, .. (bi_tforall (λ y, P)) .. ))
                                (at level 200, x binder, y binder, right associativity,
                                  format "∀#  x  ..  y ,  P") : bi_scope.
Notation "'∃#' x .. y , P" := (bi_texists (λ x, .. (bi_texists (λ y, P)) .. ))
                                (at level 200, x binder, y binder, right associativity,
                                  format "∃#  x  ..  y ,  P") : bi_scope.

Lemma bi_tforall_equiv {Σ} {τ : types} (P : τ → iProp Σ) :
  (∀# xs, P xs)%I ≡ (∀ xs, P xs)%I.
Proof.
  unfold bi_tforall.
  induction τ as [|X H τ IH].
  - simpl; done.
  - apply bi.iff_equiv. apply _. apply _.
    iStartProof.
    simpl. iSplit.
    + iIntros "H".
      iIntros ([x xs]).
      iSpecialize ("H" $! x).
      iApply (IH with "H").
    + iIntros "H %x".
      iApply IH. iIntros (xs).
      iApply "H".
Qed.

Equations bi_pure_spec (PROP: bi) (τ : types) (f : τ -#> microvx -> Prop) : (τ -#> microvx -> PROP) :=
| PROP, Tbase T, f :=
    λ x m, bi_pure (f x m)
| PROP, type_nel.Tcons T τ', f :=
    λ x, bi_pure_spec PROP τ' (f x).

Arguments bi_pure_spec {_ _} _.

Section ewp_spec.

  Context `{!osirisGS Σ}.

  (* -------------------------------------------------------------------------- *)

  (* To reason about curried n-ary function, and give them natural specifications
   (i.e. specifications over the function when fully applied)
   We introduce the predicate [Spec arg_τ c P]. *)

  (* [Spec arg_τ c P] should be read as "[c] is a function value, with
   arguments described by [arg_τ], and with specification [P]." *)

  (* [Spec] matches on the list of argument types [arg_τ], producing a series of
   nested calls, where the base case asserts [P] over the full call. *)

  Equations iSpec (τ : types) (c : val) (P : τ -#> microvx -> iProp Σ) : iProp Σ :=
  | Tbase X, c, P :=
      ∀ (x : X), P x (call c #x)
  | type_nel.Tcons X τ', c, P :=
      ∀ (x : X), EWP (call c #x) <|⊥|> {{ ensures c, iSpec τ' c (P x) }}.

  Local Lemma ewp_eval_anon_unary `{Encode X} ι
    (P : τ[X] -#> microvx -> iProp Σ) η (x : var) e E Ψ
    :
    (∀ (v : X), P v (please_eval ((x, #v) :: η) e)) -∗
    EWP[ι] (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ ensures c, iSpec τ[X] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply ewp_ret.
    iApply "HP".
  Qed.

  Local Lemma ewp_eval_anon_binary `{Encode X, Encode Y} ι
    (P : τ[X;Y] -#> microvx -> iProp Σ) η (x y : var) e E Ψ
    :
    (∀ (vx : X) (vy : Y), P vx vy (please_eval ((y, #vy) :: (x, #vx) :: η) e)) -∗
    EWP[ι] (eval η (EAnonFun (AnonFun x (EAnonFun (AnonFun y e))))) @ E <| Ψ |> {{ ensures c, iSpec τ[X;Y] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply ewp_ret. simpl; simp iSpec.
    iIntros (vx) "%ι'". simpl.
    iApply ewp_please. iNext.
    iApply (ewp_eval_anon_unary ι').
    iIntros (vy).
    iApply "HP".
  Qed.

  (* [iSpec] is monotonic over specification predicates. *)

  Lemma iSpec_mono (τ : types) (P P' : τ -#> microvx -> iProp Σ) c :
    iSpec τ c P -∗
    (∀# args, ∀ m, (P args) m -∗ (P' args) m) -∗
    iSpec τ c P'.
  Proof.
    revert c.
    induction τ as [ | X HX arg_τ IH ]; iIntros (c) "HP Hmono".
    { simp iSpec. iIntros (x).
      iApply "Hmono". iApply "HP". }
    simp iSpec; iIntros (x) "%ι".
    iApply (ewp_mono with "HP").
    iIntros ([c'| ]); [ | iIntros ([])].
    iIntros "HSpec'". simpl.
    iApply (IH with "HSpec'").
    iApply "Hmono".
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* We define [predicate_over_function_body τ P η e], which fetches the
     function body from a series of nested [EAnonFun] in [e], at a depth
     equal to the number of arguments specified by [τ], and asserts [P]
     over the evaluation of that function body. *)

  (* In particular, [predicate_over_function_body] can be used to prove
     a goal of the form [Spec τ c P]. *)

  Equations predicate_over_function_body
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    (η : env)
    (e : expr)
    : iProp Σ :=
  | Tbase X, P, η, EAnonFun (AnonFun arg e) :=
      ∀ (x : X), P x (please_eval ((arg, #x) :: η) e)
  | type_nel.Tcons X arg_τ', P, η, (EAnonFun (AnonFun arg e)) :=
      ∀ (x : X), predicate_over_function_body arg_τ' (P x) ((arg, #x) :: η) e
  (* If the expression isn't an [EAnonFun] we produce an unprovable proposition. *)
  | _, _, _, _ := False.

  (* We always want to unfold [predicate_over_function_body] until only a
   statement of the form [∀ x, P x (eval η e)] remains. *)
  Arguments predicate_over_function_body !τ /.
  Transparent predicate_over_function_body.
  Strategy transparent [ predicate_over_function_body ].

  Lemma invert_predicate_over_body τ P η e :
    predicate_over_function_body τ P η e -∗
    ⌜∃ arg e', e = EAnonFun (AnonFun arg e')⌝.
  Proof.
    iIntros "HP".
    funelim (predicate_over_function_body τ P η e); try done;
      iPureIntro; eexists _, _; reflexivity.
  Qed.

  Local Lemma prove_iSpec (τ : types) η x e (P : τ -#> microvx -> iProp Σ) :
    predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    iSpec τ (VClo η (AnonFun x e)) P.
  Proof.
    iLöb as "IH" forall (e x η τ P).
    iIntros "HP".
    destruct τ as [ X | X HX τ ].
    { iApply "HP". }
    simp iSpec; iIntros (vx) "%ι".
    simp predicate_over_function_body.
    iSpecialize ("HP" $! vx).
    iPoseProof (invert_predicate_over_body with "HP") as "(%y & %e' & ->)".
    simpl. iApply ewp_please. iNext. simpl_eval.
    iApply ewp_ret.
    simpl.
    iApply ("IH" with "HP").
  Qed.

  Local Lemma prove_iSpec_pers (τ : types) η x e (P : τ -#> microvx -> iProp Σ) :
    □ predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    □ iSpec τ (VClo η (AnonFun x e)) P.
  Proof.
    iLöb as "IH" forall (e x η τ P).
    iIntros "#HP".
    destruct τ as [ X | X HX τ ].
    { iApply "HP". }
    simp iSpec; iIntros (vx) "%ι".
    simp predicate_over_function_body.
    iSpecialize ("HP" $! vx).
    iPoseProof (invert_predicate_over_body with "HP") as "(%y & %e' & ->)".
    simpl. iModIntro. iApply ewp_please. iNext. simpl_eval.
    iApply ewp_ret.
    simpl.
    iApply ("IH" with "HP").
  Qed.

  (* The reasoning rule for an n-ary non-recursive function. *)

  Lemma ewp_EAnon
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    ι
    η
    (x : var)
    e E Ψ :
    predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    EWP[ι] (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ ensures c, iSpec τ c P }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply ewp_ret; simpl.
    by iApply prove_iSpec.
  Qed.

  Lemma ewp_EAnon_pers
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    ι
    η
    (x : var)
    e E Ψ :
    □ predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    EWP[ι] (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ ensures c, □ iSpec τ c P }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply ewp_ret; simpl.
    by iApply prove_iSpec_pers.
  Qed.

  Fixpoint lookup_rec_bindings_opt (rbs : list rec_binding) (g : var) {struct rbs} :
    option anonfun :=
    match rbs with
    | [] => None
    | RecBinding g' a :: rbs0 =>
        if (g =? g')%string then Some a else lookup_rec_bindings_opt rbs0 g
    end.

  Definition lookup_rec_bindings' (rbs : list rec_binding) (g : var) :
    micro anonfun exn :=
    match lookup_rec_bindings_opt rbs g with
    | None => missing_variable g
    | Some a => ret a
    end.

  Lemma lookup_rec_bindings_equiv :
    ∀ rbs g, lookup_rec_bindings' rbs g = lookup_rec_bindings rbs g.
  Proof.
    intros rbs g. induction rbs.
    reflexivity.
    unfold lookup_rec_bindings'. simpl.
    rewrite <- IHrbs.
    destruct a; simpl.
    case (g =? f)%string. reflexivity.
    reflexivity.
  Qed.

  Lemma pure_iSpec τ c P :
    ⌜@Spec τ c P⌝ -∗
    iSpec τ c (bi_pure_spec P)%I.
  Proof.
    iLöb as "IH" forall (τ c P).
    iIntros "%HSpec".
    destruct τ as [ X | X HX τ ].
    { simp iSpec. simp Spec in HSpec. simp bi_pure_spec.
      iIntros (x).
      iPureIntro.
      apply HSpec. }
    simp iSpec. iIntros (x) "%ι". simp Spec in HSpec.
    specialize (HSpec x).
    destruct c; simpl in HSpec; try by apply invert_pure_wp_crash in HSpec.
    - destruct a; simpl in *.
      iApply ewp_please. iNext.
      iApply ewp_mono.
      iApply ewp_pure_wp. apply invert_pure_wp_eval in HSpec. apply HSpec.
      iIntros ([|]); [ | iIntros ([]) ].
      simpl. iApply "IH".
    - simpl. rewrite <- lookup_rec_bindings_equiv in HSpec |- *.
      unfold lookup_rec_bindings' in HSpec |- *.
      case_eq (lookup_rec_bindings_opt rbs f).
      + intros a Heqlookup. rewrite Heqlookup in HSpec.
        simpl in *. destruct a; simpl in *.
        iApply ewp_please; iNext.
        apply invert_pure_wp_eval in HSpec.
        iApply ewp_mono.
        iApply ewp_pure_wp. apply HSpec.
        iIntros ([|]); [ | iIntros ([]) ].
        simpl. iApply "IH".
      + intros Heqlookup. rewrite Heqlookup in HSpec.
        simpl in HSpec.
        by apply invert_pure_wp_crash in HSpec.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* [ewp_EApp_partial] is a lemma for partial application. *)

  Lemma ewp_EApp_partial `{Encode X} (τ: types) ι η e e1 Ψ
    (P : type_nel.Tcons X τ -#> microvx -> iProp Σ) :
    EWP[ι] eval η e <|Ψ|> {{ ensures c, iSpec (type_nel.Tcons X τ) c P }} -∗
    EWP[ι] eval η e1 <|Ψ|> {{ ensures v1, ∃ (x : X), ⌜v1 = #x⌝ }} -∗
    EWP[ι] eval η (EApp e e1) <|Ψ|> {{ ensures c, ∃ (x : X), iSpec τ c (P x) }}.
  Proof.
    iIntros "He He1". simpl_eval.
    iApply (ewp_Par with "He He1").
    - iIntros (?) "[]".
    - iIntros (?) "[]".
    - iIntros (c v1) "HSpec [%x ->]". simpl. simp iSpec.
      iSpecialize ("HSpec" $! x). simpl.
      iApply ewp_prot_mono; [iApply iEff_le_bottom |].
      iApply (ewp_mono with "HSpec").
      iIntros "!>" ([c'|]); [| iIntros "[]"].
      iIntros "HSpec'". iExists x. iApply "HSpec'".
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* We provide infrastructure for reasoning about n-ary function application,
     similar to the pure case. *)

End ewp_spec.

(* The following definitions are outside the section to avoid capturing Σ *)

Section ewp_EApp_prop_aux_def.

  Context `{!osirisGS Σ}.
  Context (ι : thread) (η : env) (Ψ : iEff Σ).
  Context (expr_base : expr) (goal_prop : expr -> iProp Σ).

  (* [accumulate_argument_premises_and_build_consequence_hyp] builds up
     premises for each argument and a consequence hypothesis. *)

  Equations accumulate_argument_premises_and_build_consequence_hyp
    (τ : types) (es : list expr) (conseq_acc : τ -#> iProp Σ -> iProp Σ) :
    iProp Σ :=
  | Tbase X, es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP[ι] eval η e <|Ψ|> {{ ensures #x, φ x }} -∗
        (* [Hconseq] is the consequence premise built over all parameters *)
        let Hconseq := ∀ (x : X), conseq_acc x (φ x) in
        (* [nested_eapp] is the nested application *)
        let nested_eapp := app_exprs expr_base (e :: es) in
        Hconseq -∗ goal_prop (nested_eapp)
  | type_nel.Tcons X τ', es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP[ι] eval η e <|Ψ|> {{ ensures #x, φ x }} -∗
        let conseq_acc :=
          (λ# (tt : τ') (Q : iProp Σ),
              ∀ (x : X),
                φ x -∗
                (tapp (conseq_acc x) tt) Q)
        in
        accumulate_argument_premises_and_build_consequence_hyp
          τ' (e :: es) conseq_acc.

  Arguments accumulate_argument_premises_and_build_consequence_hyp !τ /.
  Transparent accumulate_argument_premises_and_build_consequence_hyp.
  Strategy transparent [ accumulate_argument_premises_and_build_consequence_hyp ].

  (* Monotonicity of the accumulator *)

  Lemma ewp_EApp_mono (τ : types) es (Hmon' Hmon : τ -#> iProp Σ -> iProp Σ) :
    accumulate_argument_premises_and_build_consequence_hyp τ es Hmon' -∗
    □ (∀ args (P : iProp Σ), Hmon args P -∗ Hmon' args P) -∗
    accumulate_argument_premises_and_build_consequence_hyp τ es Hmon.
  Proof.
    revert es.
    induction τ as [ X HX | X HX τ IH ]; iIntros (es) "HEApp' #Hmono"; simpl.
    - iIntros (ex φx) "Hex Hx". cbn zeta.
      iSpecialize ("HEApp'" $! ex φx with "Hex"). cbn zeta.
      iApply "HEApp'".
      iIntros (v). iApply ("Hmono" with "Hx").
    - iIntros (ex φx) "Hex".
      iApply (IH with "[HEApp' Hex]").
      + iApply ("HEApp'" with "Hex").
      + iModIntro. iIntros (args P). rewrite !tapp_bind.
        iIntros "Hx" (x) "Hφx".
        iApply ("Hmono" $! (x, args) P).
        iApply ("Hx" with "Hφx").
  Qed.

End ewp_EApp_prop_aux_def.

Section ewp_EApp_def.
  Context `{!osirisGS Σ}.

  Definition ewp_EApp_prop `{Encode A} (τ : types) : iProp Σ :=
    ∀ (ι : thread) (η : env) (e : expr) (Ψ' : A -> iProp Σ) (Ψ : iEff Σ)
      (P : τ -#> microvx -> iProp Σ),
    EWP[ι] eval η e <|Ψ|> {{ ensures c, iSpec τ c P }} -∗
    accumulate_argument_premises_and_build_consequence_hyp
      ι η Ψ e
      (λ e, EWP[ι] eval η e <|Ψ|> {{ ensures #v, Ψ' v }})
      τ
      []
      (λ# (tt : τ) (Q : iProp Σ),
           Q -∗ ∀ m, (tapp P tt) m -∗ ▷ EWP[ι] m <|Ψ|> {{ ensures #v, Ψ' v }}).

  Arguments ewp_EApp_prop {_ _} !τ /.
  Transparent ewp_EApp_prop.
  Strategy transparent [ ewp_EApp_prop ].

  (* Helper lemma for the induction step *)

  Lemma ewp_EApp_prop_induction_step
    (τ : types) ι (η : env) (Ψ : iEff Σ) e (g : expr -> iProp Σ) :
    ∀ (Hconseq : τ -#> iProp Σ -> iProp Σ) (es : list expr) (ei : expr),
      app_exprs (EApp e ei) es = app_exprs e (es ++ [ei]) →
      accumulate_argument_premises_and_build_consequence_hyp
        ι η Ψ (EApp e ei) g τ es Hconseq -∗
      accumulate_argument_premises_and_build_consequence_hyp
        ι η Ψ e g τ (es ++ [ei]) Hconseq.
  Proof.
    induction τ as [ X HX | X HX τ IH ]; iIntros (Hconseq es ei HeqEApp) "Happlied".
    - (* Base case *)
      simpl in *. rewrite <- HeqEApp. iApply "Happlied".
    - (* Inductive case *)
      iIntros (ex φx) "Hex". cbn zeta.
      iApply (IH (λ# (tt : τ) (B : iProp Σ),
                   ∀ x : X,
                     φx x -∗
                     tapp Hconseq (x, tt) B)%I
                 (ex :: es) ei).
      + simpl. f_equal. apply HeqEApp.
      + iApply ("Happlied" with "Hex").
  Qed.

  (* Main lemma for n-ary function application *)

  Lemma ewp_EApp `{Encode A} (τ : types) :
    ⊢ @ewp_EApp_prop A _ τ.
  Proof.
    induction τ as [ X HX | X HX τ IH].
    - (* Base case *)
      unfold ewp_EApp_prop.
      iIntros (ι η e Ψ' Ψ P) "HSpec"; iIntros (ex φx) "Hex"; cbn zeta.
      iIntros "Hmono".
      simpl_eval.
      iApply (ewp_Par with "HSpec Hex").
      + iIntros (?) "[]".
      + iIntros (?) "[]".
      + iIntros (c v) "HSpec' Hφx". simpl. simp iSpec.
        iDestruct "Hφx" as (x) "[-> Hφx]".
        iApply ("Hmono" with "Hφx HSpec'").

    - (* Inductive case: multi-argument function *)
      unfold ewp_EApp_prop.
      iIntros (ι η e Ψ' Ψ P) "HSpec"; iIntros (ex φx) "Hex".
      change [ex] with ([] ++ [ex]).
      iApply (ewp_EApp_prop_induction_step τ ι η Ψ e
              (λ e, EWP[ι] eval η e <|Ψ|> {{ ensures #x, Ψ' x }})%I); first reflexivity.

    (* Define the intermediate specification P' *)
    set (P' := (λ# (tt : τ) m,
                 ∃ x : X,
                   φx x ∗
                   tapp P (x, tt) m)%I : τ -#> microvx -> iProp Σ).

    (* Use IH *)
    iPoseProof IH as "HIH".
    unfold ewp_EApp_prop.
    iSpecialize ("HIH" $! ι η (EApp e ex) _ _ P' with "[HSpec Hex]").
    { simpl_eval.
      iApply (prove_ewp_Par with "HSpec Hex").
      iIntros (??) "HSpec (%x & -> & Hφx) /=".
      simp iSpec.
      iPoseProof (ewp_prot_mono with "[] HSpec") as "HSpec"; last first.
      iApply (ewp_mono with "HSpec").
      iIntros ([|]); [ | iIntros ([]) ].
      iIntros "HSpec /=".
      iApply (iSpec_mono with "HSpec").
      rewrite bi_tforall_equiv.
      iIntros (xs m) "HP".
      subst P'. cbn. rewrite tapp_bind.
      iFrame. iApply iEff_le_bottom. }

    (* Apply monotonicity *)
    iApply (ewp_EApp_mono with "HIH").

    iIntros "!>" (args Q). rewrite !tapp_bind.
    iIntros "H HQ %m (%x & Hφx & HP)".
    iSpecialize ("H" $! x with "Hφx").
    rewrite tapp_bind.
    iApply ("H" with "HQ HP").
  Qed.

End ewp_EApp_def.

Section ewp_EApp_prop_aux_def.

  Context `{!osirisGS Σ}.
  Context (ι : thread) (η : env) (Ψ : iEff Σ).
  Context (expr_base : expr) (goal_prop : expr -> iProp Σ).

  (* [accumulate_argument_premises_and_build_consequence_hyp] builds up
     premises for each argument and a consequence hypothesis. *)

  Equations iaccumulate_argument_premises_and_build_consequence_hyp
    (τ : types) (es : list expr) (conseq_acc : τ -#> iProp Σ -> iProp Σ) :
    iProp Σ :=
  | Tbase X, es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP[ι] eval η e <|Ψ|> {{ ensures #x, φ x }} -∗
        (* [Hconseq] is the consequence premise built over all parameters *)
        let Hconseq := ∀ (x : X), conseq_acc x (φ x) in
        (* [nested_eapp] is the nested application *)
        let nested_eapp := app_exprs expr_base (e :: es) in
        Hconseq -∗ goal_prop (nested_eapp)
  | type_nel.Tcons X τ', es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP[ι] eval η e <|Ψ|> {{ ensures #x, φ x }} -∗
        let conseq_acc :=
          (λ# (tt : τ') (Q : iProp Σ),
              ∀ (x : X),
                φ x -∗
                (tapp (conseq_acc x) tt) Q)
        in
        iaccumulate_argument_premises_and_build_consequence_hyp
          τ' (e :: es) conseq_acc.

  Arguments iaccumulate_argument_premises_and_build_consequence_hyp !τ /.
  Transparent iaccumulate_argument_premises_and_build_consequence_hyp.
  Strategy transparent [ iaccumulate_argument_premises_and_build_consequence_hyp ].

End ewp_EApp_prop_aux_def.
