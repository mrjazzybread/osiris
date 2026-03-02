From iris.proofmode Require Import proofmode.

From osiris.lang Require Import encode type_nel.
From osiris.program_logic Require Import program_logic.

From osiris.tactics Require Import utils iris_bindings.
From osiris.proofmode Require Import equality.

(* --------------------------------------------------------------------------*)
(* The following part defines module specifications. *)

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

  (* Specification over a variable name. *)

  Definition in_env `{Encode A} (name : var) (spec : A → iProp Σ) (η : env) : iProp Σ :=
    ∃ x, ⌜lookup_name η name = Some #x⌝ ∗ spec x.

  Definition pure_in_env `{Encode A} (name : var) (spec : A → Prop) (η : env) : Prop :=
    ∃ x, lookup_name η name = Some #x ∧ spec x.

  Lemma var_spec_app `{Encode A} x (Φ : A → iProp Σ) δ η :
    in_env x Φ δ -∗
    in_env x Φ (δ ++ η).
  Proof.
    iIntros "(% & % & $)".
    iPureIntro.
    by apply lookup_name_app_l.
  Qed.

  Lemma var_spec_mono `{Encode A} {Φ : A → iProp Σ} (Φ' : A → iProp Σ) x η :
    in_env x Φ' η -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    in_env x Φ η.
  Proof.
    iIntros "(%a & % & HΦ') Hmono".
    iExists a. iSplit; [ iPureIntro; assumption | ].
    iApply ("Hmono" with "HΦ'").
  Qed.

  Record enc_spec {PROP : Type} :=
    has_spec
      {
        res_type : Type;
        res_type_enc : Encode res_type;
        name : var;
        spec : res_type → PROP;
      }.
  (* Make it so [enc_spec] displays as [Spec name Φ]. *)
  Global Arguments enc_spec {_}.
  Global Arguments res_type {_}.
  Global Arguments res_type_enc {_}.
  Global Arguments name {_}.
  Global Arguments spec {_}.
  Global Arguments has_spec {_ _ _}.
  Global Add Printing Constructor enc_spec.

  Instance dom_env : Dom (env) (gset var) := λ η, list_to_set (η.*1).

  Definition context (specs : list (@enc_spec (iProp Σ))) d : env → iProp Σ :=
    λ η, (⌜dom η = d⌝ ∗
           [∗ list] s ∈ specs,
            @in_env s.(res_type) s.(res_type_enc) s.(name) (λ res, □ s.(spec) res) η)%I.

  Definition pure_context (specs : list (@enc_spec Prop)) d : env → Prop :=
    λ η, dom η = d ∧
         Forall (λ s,
                   @pure_in_env s.(res_type) s.(res_type_enc) s.(name) s.(spec) η) specs.

  Global Instance context_pers specs d η : Persistent (context specs d η).
  Proof. apply _. Qed.

  (*
    Check
    context [
       has_spec "+" (λ add, iSpec τ[Z; Z] add (λ i j m, imp m {{ λ n, ⌜(n = i + j)%Z⌝ }})%I);
       has_spec "-" (λ sub, iSpec τ[Z; Z] sub (λ i j m, imp m {{ λ n, ⌜(n = i - j)%Z⌝ }})%I)
     ] {["+";"-";"*"]}.
   *)

  Lemma extract_context `{Encode A} {η} xs ys d name (spec : A → iProp Σ) :
    context (xs ++ [has_spec name spec] ++ ys) d η -∗ in_env name spec η.
  Proof.
    unfold context.
    iIntros "(%Hdom & Hspecs)".
    iPoseProof (big_sepL_app with "Hspecs") as "(_ & Hspecs)".
    iPoseProof (big_sepL_app with "Hspecs") as "(Hspec & _)".
    iDestruct "Hspec" as "[#Hspec _]".
    iApply (var_spec_mono with "Hspec").
    iIntros (res) "#Hspec'". iApply "Hspec'".
  Qed.

  (* We immediately reduce [path_spec] to [in_env] if the path is a singleton. *)

  Lemma path_spec_singleton `{Encode A} name (Φ : A → iProp Σ) η :
    in_env name Φ η -∗ path_spec [name] Φ η.
  Proof.
    unfold in_env.
    iIntros "(%x & Hlookup & HΦ)".
    iExists x. simpl. iFrame.
  Qed.

  (* If the path is a cons, we find the specification for the module
     at the head of the path. *)

  Lemma path_spec_cons {A : Type} `{Encode A} {Φ : A → iProp Σ} {η x p} mspec :
    in_env x mspec η -∗
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
    in_env x Φ η -∗
    in_env x Φ ((y, v) :: η).
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
    in_env x Φ ((y, #v) :: η).
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
    in_env x Φ η -∗
    in_env x Φ (δ ++ η).
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
    context (xs ++ [has_spec x Φ] ++ ys) d δ -∗
    in_env x Φ (δ ++ η).
  Proof.
    iIntros "Hcontext".
    iPoseProof (extract_context with "Hcontext") as "Hspec".
    iApply var_spec_app. iApply "Hspec".
  Qed.

  (* We can pick out the right specification from a context. *)

  Lemma var_spec_context `{Encode A} {Φ : A → iProp Σ} {x} δ d specs :
    has_spec x Φ ∈ specs →
    context specs d δ -∗
    in_env x Φ δ.
  Proof.
    iIntros (Hin) "Hcontext".
    apply list_elem_of_split in Hin as (l1 & l2 & ->).
    iPoseProof (extract_context with "Hcontext") as "$".
  Qed.

  Lemma var_spec_context_mono `{Encode A} {Φ : A → iProp Σ} Φ' {x} δ d specs :
    has_spec x Φ' ∈ specs →
    context specs d δ -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    in_env x Φ δ.
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

(* --------------------------------------------------------------------------*)
(* Implementing the [imp_path] tactic. *)

From Ltac2 Require Import Ltac2 Printf Bool.

Ltac2 get_env_spec (η : constr) :=
  let (pers_hyps, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find [context] specification for environment %t" η)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | env_lookups.context ?_specs ?_domain ?δ =>
            if Constr.equal η δ then
              name
            else
              go env
        | ?_spec ?δ =>
            if Constr.equal η δ then
              name
            else
              go env
        | _ => go env
        end
    end
  in
  Control.plus
    (fun _ => go pers_hyps)
    (fun _ => go spat_hyps).

Ltac2 get_var_spec (x : constr) (η : constr) :=
  let (pers_hyps, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find [in_env] specification for name %t" x)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | in_env ?y ?_spec ?δ =>
            if Constr.equal x y && Constr.equal η δ then
              name
            else
              go env
        | _ => go env
        end
    end
  in
  Control.plus
    (fun _ => go pers_hyps)
    (fun _ => go spat_hyps).


Ltac2 var_spec_cons () :=
  iApply var_spec_cons; Control.focus 1 1 (fun _ => reflexivity).

Ltac2 var_spec_here () :=
  iApply var_spec_here; Control.focus 1 1 (fun _ => reflexivity).

Ltac2 var_spec_app_r (hyp : constr) :=
  iApply (var_spec_app_r with $hyp);
  Control.focus 1 1 (fun _ => complete (fun _ => ltac1:(set_solver))).

Ltac2 var_spec_app () :=
  iApply var_spec_app.

Ltac2 var_spec_context hyp :=
  Control.plus
    (fun _ =>
       iApply (var_spec_context with $hyp);
       complete (fun _ => repeat constructor))
    (fun _ =>
       iApply (var_spec_context_mono with $hyp) >
         [  complete (fun _ => repeat constructor) | auto ]).

Ltac2 rec solve_var_spec () :=
  lazy_match! get_iris_goal () with
  | in_env ?name ?_spec ?env =>
      match! env with
      | (?name', ?_val) :: _ =>
          if Constr.equal name name' then
            var_spec_here ()
          else
            (var_spec_cons ();
             Control.enter solve_var_spec)
      | ?δ ++ ?_η =>
          Control.plus
            (fun _ =>
               let spec_name := get_env_spec δ in
               var_spec_app_r spec_name;
               last solve_var_spec)
            (fun _ =>
               var_spec_app ();
               solve_var_spec ())
      | ?η =>
          Control.plus
            (fun _ =>
               let spec_name := get_var_spec name η in
               iApply (var_spec_mono with $spec_name);
               let ha := iFresh "ha" in
               iIntros ("% " ++ $ha)%string; try (iApply $ha))
            (fun _ =>
               Control.plus
                 (fun _ =>
                    let spec_name := get_env_spec η in
                    var_spec_context spec_name)
                 (fun _ =>
                    Control.zero (Tactic_failure
                                    (Some (fprintf "Could not solve goal [var_spec %t _ %t]" name env)))))
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Expected goal to be [path_spec]")))
  end.

Ltac2 Type detected_path :=
  [ | Psingleton
    | Pcons ].

Ltac2 rec path_spec_to_var_spec () :=
  lazy_match! get_iris_goal () with
  | path_spec ?path ?_spec ?_env =>
      match! path with
      | [ _ ] =>
          iApply path_spec_singleton;
          Psingleton
      | _ =>
          iApply path_spec_cons;
          Pcons
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Expected goal to be [path_spec]")))
  end.

Ltac2 rec solve_path_spec () :=
  match path_spec_to_var_spec () with
  | Psingleton => solve_var_spec ()
  | Pcons =>
      Control.focus 1 1 (fun _ => complete solve_var_spec);
      let hyp_name := iFresh "Hpath" in
      iIntros ("% #" ++ $hyp_name)%string;
      solve_path_spec ()
  end.

Ltac2 solve_eq_goal () :=
  lazy_match! get_iris_goal () with
  | (⌜_ = _⌝)%I => ltac1:(equality)
  | ?spec ?x =>
      match Constr.Unsafe.kind spec with
      | Constr.Unsafe.Evar _ _ =>
          let prop := '(λ x,⌜x=$x⌝)%I in
          try_complete (fun _ => Std.unify spec prop; auto)
      | _ => ()
      end
  end.

Ltac2 imp_path_tac () :=
  iApply imp_EPath_spec;
  solve_path_spec ().

Ltac2 Notation "imp_path" :=
  (* Resolve the path. *)
  imp_path_tac ();
  (* If there is a goal remaining. *)
  Control.enter
    (fun _ =>
       if empty_spatial_env () then
         (* If there are no resources, first try to solve the goal as an equality. *)
         solve_eq_goal ();
         (* If that failed, try to frame the persistent resources. *)
         Control.enter (fun _ => iFrame "#")
       else
         try_complete (fun _ => iFrame)).
Tactic Notation "imp_path" := ltac2:(imp_path).

Ltac2 Notation "imp_path_eq" :=
  imp_path_tac (); solve_eq_goal ().
Tactic Notation "imp_path_eq" := ltac2:(imp_path_eq).

(* --------------------------------------------------------------------------*)
(* Testing the [imp_path] tactic. *)

From iris.proofmode Require Import ltac_tactics.

Set Default Proof Mode "Classic".

Section TacticTests.

  Context `{!osirisGS Σ}.

  Local Open Scope Z.

  (* We define a short program, [e]:
     ```
     let x = 2 in
     let y = z in
     Module1.add (Module2.Module3.sub y x) a
     ```
   *)

  Definition e :=
    ELet [Binding (PVar "x") (EInt 2)] (
        ELet [Binding (PVar "y") (EPath ["z"])] (
            EApp
              (EApp (EPath ["Module1"; "add"])
                 (EApp
                    (EApp (EPath ["Module2";"Module3";"sub"]) (EPath ["y"]))
                    (EPath ["x"])))
              (EPath ["a"])
          )
      ).

  (* We then verify this program under the assumption that:
     - [z] is in the environment and is positive
     - Module1 is in the environment and contains [add]
     - Module2 is in the environment and contains [Module3],
       which contains [sub] *)

  Definition add_spec add : iProp Σ := □ iSpec τ[Z;Z] add (λ (i j : Z) m, imp m {{ λ k, ⌜(k = i + j)%Z⌝ }})%I.
  Definition sub_spec sub : iProp Σ := □ iSpec τ[Z;Z] sub (λ (i j : Z) m, imp m {{ λ k, ⌜(k = i - j)%Z⌝ }})%I.
  Definition a_spec a : iProp Σ := ∀ (A : Type), □ ⌜a > 2⌝.

  Definition module3_spec η := context [has_spec "sub" sub_spec] {["sub"]} η.
  Definition module2_spec η := context [has_spec "Module3" module3_spec] {["Module3"; "some"; "other"; "stuff"]} η.

  Lemma example_proof δ η :
    in_env "z" (λ (i : Z), ⌜i > 0⌝) η -∗
    in_env "a" a_spec η -∗
    context [has_spec
               "Module1"
               (context [has_spec "some_other_val" (λ (_ : val), True);
                         has_spec "add" add_spec] {["some_other_val";"add"]})
      ] {["Module1"]} δ -∗
    context [has_spec "Module2" module2_spec] {["Module2";"z"]} η -∗
    imp (eval (δ ++ η) e) {{ λ (i : Z), ⌜i > 0⌝ }}.
  Proof.
    iIntros "#zspec #aspec #δspec #ηspec".
    (* TODO: imp_let tactic which instantiates
       the return type of the left member with an evar. *)
    evar(B:Type).
    evar(HB:Encode B).
    iApply (imp_ELet_var (B:=B)). { iApply imp_EInt. }
    subst B HB.
    iIntros (? ->).
    iApply (imp_ELet_var (B:=Z)).
    { imp_path. }
    iIntros (z) "%yspec".
    iApply (imp_EApp τ[Z;Z]).
    { imp_path. }
    { iApply (imp_EApp τ[Z;Z]).
      { imp_path. }
      { imp_path. }
      { imp_path. }
      iIntros (??) "-> -> %m Hm !>".
      iApply "Hm". }
    { imp_path. }
    iIntros (??) "-> #%Ha %m Hm !>".
    iApply (imp_mono_ret with "Hm").
    iIntros (y ->). iPureIntro.
    specialize (Ha unit).
    lia.
  Qed.

End TacticTests.
