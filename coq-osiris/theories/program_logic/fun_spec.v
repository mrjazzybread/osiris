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
  tfold (λ (T : Type@{Quant}) (b : T → PROP), ∀ x : T, b x)%I Datatypes.id (tbind Ψ).
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
      ∀ (x : X), P x (fun_spec.im_call c #x)
  | type_nel.Tcons X τ', c, P :=
      ∀ (x : X), EWP (call c #x) {{ ensures c, iSpec τ' c (P x) }}.

  Local Lemma ewp_eval_anon_unary `{Encode X}
    (P : τ[X] -#> microvx -> iProp Σ) η (x : var) e E Ψ
    :
    (∀ (v : X), P v (eval ((x, #v) :: η) e)) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ ensures c, iSpec τ[X] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply ewp_value.
    iApply "HP".
  Qed.

  Local Lemma ewp_eval_anon_binary `{Encode X, Encode Y}
    (P : τ[X;Y] -#> microvx -> iProp Σ) η (x y : var) e E Ψ
    :
    (∀ (vx : X) (vy : Y), P vx vy (eval ((y, #vy) :: (x, #vx) :: η) e)) -∗
    EWP (eval η (EAnonFun (AnonFun x (EAnonFun (AnonFun y e))))) @ E <| Ψ |> {{ ensures c, iSpec τ[X;Y] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply ewp_value. simpl; simp iSpec.
    iIntros (vx). simpl.
    iApply ewp_please. iNext.
    iApply ewp_eval_anon_unary.
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
    simp iSpec; iIntros (x).
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
      ∀ (x : X), P x (eval ((arg, #x) :: η) e)
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
    simp iSpec; iIntros (vx).
    simp predicate_over_function_body.
    iSpecialize ("HP" $! vx).
    iPoseProof (invert_predicate_over_body with "HP") as "(%y & %e' & ->)".
    simpl. iApply ewp_please. iNext. simpl_eval.
    iApply ewp_value.
    simpl.
    iApply ("IH" with "HP").
  Qed.

  (* The reasoning rule for an n-ary non-recursive function. *)

  Lemma ewp_eval_anon
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    η
    (x : var)
    e E Ψ :
    predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ ensures c, iSpec τ c P }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply ewp_value; simpl.
    by iApply prove_iSpec.
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
    simp iSpec. iIntros (x). simp Spec in HSpec.
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


End ewp_spec.
