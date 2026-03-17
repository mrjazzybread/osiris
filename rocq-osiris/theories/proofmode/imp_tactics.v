From osiris.tactics Require Import tactics.
From osiris.lang Require Import encode type_nel.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import env_lookups.
From stdpp Require Import strings.
From Ltac2 Require Import Ltac2 Printf.

Ltac2 get_expr () :=
  let g := get_iris_goal () in
  lazy_match! g with
  | impure _ (eval _ ?e) ?_Ψ ?_ζ ?_Φ => e
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected goal of the form [imp (eval η e) _]")))
  end.

Ltac2 imp_int_tac () :=
  let e := get_expr () in
  lazy_match! eval hnf in $e with
  | EInt _ => iApply imp_EInt
  | EMaxInt => iApply imp_EMaxInt
  | EMinInt => iApply imp_EMinInt
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected %t to be an int literal" e)))
  end.

Ltac2 Notation "imp_int" := imp_int_tac ().
Tactic Notation "imp_int" := ltac2:(imp_int).

Ltac2 imp_load_tac (l : constr option) :=
  let specialized_load :=
    match l with
    | Some l => open_constr:(imp_ELoad _ _ $l)
    | None => 'imp_ELoad
    end
  in
  iApply ($specialized_load with "[$]").

Ltac2 Type arith_type :=
  [ Literal | Op | Comparison ].

Ltac2 fetch_appropriate_arith_lemma (e : constr) : (constr * arith_type) option :=
  lazy_match! e with
  | EInt _ => Some ('imp_EInt, Literal)
  | EMaxInt => Some ('imp_EMaxInt, Literal)
  | EMinInt => Some ('imp_EMinInt, Literal)
  | EIntAdd _ _ => Some ('imp_EIntAdd, Op)
  | EIntSub _ _ => Some ('imp_EIntSub, Op)
  | EIntMul _ _ => Some ('imp_EIntMul, Op)
  | EIntDiv _ _ => Some ('imp_EIntDiv, Op)
  | EIntMod _ _ => Some ('imp_EIntMod, Op)
  | EOpEq _ _ => Some ('imp_EOpEq_Z, Comparison)
  | EOpNe _ _ => Some ('imp_EOpNe_Z, Comparison)
  | EOpLt _ _ => Some ('imp_EOpLt_Z, Comparison)
  | EOpLe _ _ => Some ('imp_EOpLe_Z, Comparison)
  | EOpGt _ _ => Some ('imp_EOpGt_Z, Comparison)
  | EOpGe _ _ => Some ('imp_EOpGe_Z, Comparison)
  | _ => None
  end.

Ltac2 representable () := ltac1:(int.representable).

Ltac2 rec imp_step () :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  match fetch_appropriate_arith_lemma e with
  | Some (lemma, arith_kind) =>
      try (iApply $lemma;
           match arith_kind with
           | Literal => ()
           | Op => Control.extend [] (fun _ => complete imp_step) [ fun _ => auto ]
           | Comparison =>
               lastn [ (fun _ => complete imp_step); (fun _ => complete imp_step) ];
               firstn [ representable; representable ]
           end)
  | None =>
      lazy_match! e with
      | EPath _ => imp_path
      | ELoad _ => imp_load_tac None; try (imp_step ())
      | ERef _ => Control.plus
                    (fun _ => iApply imp_ERef;
                              complete imp_step)
                    (fun _ => iApply imp_ERef2; try (imp_step ()))
      | EStore _ _ => Control.plus
                        (fun _ => iApply (imp_EStore with "[$]");
                                  Control.dispatch [imp_step; fun _ => complete imp_step])
                        (fun _ => iApply (imp_EStore' with "[$]"); try (imp_step ()))
      | EData _ [] => iApply imp_EConstant; first (fun _ => ltac1:(encode))
      | _ =>
          Control.zero
            (Tactic_failure
               (Some (fprintf "[imp_step] doesn't know how to handle expression %t" e)))
      end
  end.

Ltac2 Notation "imp_step" := imp_step ().
Tactic Notation "imp_step" := ltac2:(imp_step).

Ltac2 Notation "imp_load" l(constr) := imp_load_tac (Some l); try (imp_step).
Ltac2 Notation "imp_load" := imp_load_tac None; try (imp_step).
Tactic Notation "imp_load" constr(l) :=
  let tac := ltac2:(l |- imp_load_tac (Ltac1.to_constr l); try (imp_step)) in
  tac l.
Tactic Notation "imp_load" := ltac2:(imp_load).

Ltac2 imp_ref_tac (x : constr option) :=
   let specialized_ref :=
    match x with
    | Some x => open_constr:(imp_ERef $x)
    | None => 'imp_ERef
    end
  in
  Control.plus
    (fun _ => iApply $specialized_ref;
              complete imp_step)
    (fun _ => iApply imp_ERef2; try (imp_step)).

Ltac2 Notation "imp_ref" x(constr) := imp_ref_tac (Some x).
Ltac2 Notation "imp_ref" := imp_ref_tac None.
Tactic Notation "imp_ref" constr(x) :=
  let tac := ltac2:(x |- imp_ref_tac (Ltac1.to_constr x)) in
  tac x.
Tactic Notation "imp_ref" := ltac2:(imp_ref).

Ltac2 imp_store_tac (l : constr) (x : constr option) :=
  let specialized_store :=
    match x with
    | Some x => open_constr:(imp_EStore $l $x)
    | None => open_constr:(imp_EStore' _ $l)
    end
  in
  iApply ($specialized_store with "[$]"); try (imp_step).

Ltac2 imp_store2_tac (l : constr) :=
  let specialized_store2 := open_constr:(imp_EStore2 $l) in
  iApply $specialized_store2; try (imp_step).

Ltac2 Notation "imp_store" l(constr) x(constr) := imp_store_tac l (Some x).
Ltac2 Notation "imp_store" l(constr) := imp_store_tac l None.
Tactic Notation "imp_store" constr(l) constr(x) :=
  let tac := ltac2:(l x |- imp_store_tac (Option.get (Ltac1.to_constr l)) (Ltac1.to_constr x)) in
  tac l x.
Tactic Notation "imp_store" constr(l) :=
  let tac := ltac2:(l |- imp_store_tac (Option.get (Ltac1.to_constr l)) None) in
  tac l.
Ltac2 Notation "imp_store2" l(constr) := imp_store2_tac l.
Tactic Notation "imp_store2" constr(l) :=
  let tac := ltac2:(l |- imp_store2_tac (Option.get (Ltac1.to_constr l))) in
  tac l.

Ltac2 imp_arith_tac (selpat : constr option) :=
  let e := get_expr () in
  let e := eval hnf in $e in
  let s :=
    match selpat with
    | Some s => s
    | None => '""
    end
  in
  match fetch_appropriate_arith_lemma e with
  | Some (lemma, arith_kind) =>
      iApply ($lemma with $s);
      match arith_kind with
      | Literal => ()
      | Op => try (imp_step)
      | Comparison =>
          lastn [ (fun _ => imp_step); (fun _ => imp_step) ];
          firstn [ representable; representable ]
      end
  | None =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected %t to be an arithmetic expression" e)))
  end.

Ltac2 Notation "imp_arith" "with" s(constr) := imp_arith_tac (Some s).
Ltac2 Notation "imp_arith" := imp_arith_tac None.
Tactic Notation "imp_arith" "with" constr(s) :=
  let tac := ltac2:(s |- imp_arith_tac (Ltac1.to_constr s)) in
  tac s.
Tactic Notation "imp_arith" := ltac2:(imp_arith).

Ltac2 rec length_type_nel (τ : constr) :=
  match! eval hnf in $τ with
  | type_nel.Tbase _ => 1
  | type_nel.Tcons _ ?τ => Int.add 1 (length_type_nel τ)
  | _ =>
      Control.throw
        (Tactic_failure (Some (fprintf "Failed to count number of types in %t" τ)))
  end.

Ltac2 imp_app_tac (types : constr) (sel : constr option) :=
  let specialized_eapp := open_constr:(imp_EApp $types) in
  let num_arg_goals := length_type_nel types in
  match sel with
  | Some sel => iApply ($specialized_eapp with $sel)
  | None => iApply $specialized_eapp
  end;
  let arg_tacs :=
    List.init num_arg_goals (fun _ => (fun _ => try (imp_step)))
  in
  let conseq_tac () :=
    (unfold tapp, tbind)
  in
  Control.dispatch (imp_path_tac :: (List.append arg_tacs [conseq_tac])).

Ltac2 Notation "imp_app" types(constr) := imp_app_tac types None.
Ltac2 Notation "imp_app" types(constr) "with" sel(constr) :=
  imp_app_tac types (Some sel).
Tactic Notation "imp_app" constr(types) :=
  let tac := ltac2:(types |- imp_app_tac (Option.get (Ltac1.to_constr types)) None) in
  tac types.
Tactic Notation "imp_app" constr(types) "with" constr(sel) :=
  let tac := ltac2:(types sel |-
                      imp_app_tac
                        (Option.get (Ltac1.to_constr types))
                        (Ltac1.to_constr sel)) in
  tac types sel.

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
              (EApp (EPath ["add"])
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
  Definition a_spec a : iProp Σ := □ ⌜a > 2⌝.

  Definition module3_spec η := context [var_spec "sub" sub_spec] {["sub"]} η.
  Definition module2_spec η := context [var_spec "Module3" module3_spec] {["Module3"; "some"; "other"; "stuff"]} η.

  Lemma example_proof δ η add :
    in_env "z" (λ (i : Z), ⌜i > 0⌝) η -∗
    □ iSpec τ[Z;Z] add (λ (i j : Z) m, imp m {{ λ k, ⌜(k = i + j)%Z⌝ }}) -∗
    in_env "a" a_spec η -∗
    context [var_spec
               "Module1"
               (context [var_spec "some_other_val" (λ (_ : val), True);
                         var_spec "add" add_spec] {["some_other_val";"add"]})
      ] {["Module1"]} δ -∗
    context [var_spec "Module2" module2_spec] {["Module2";"z"]} η -∗
    imp (eval (("add",add)::δ ++ η) e) {{ λ (i : Z), ⌜i > 0⌝ }}.
  Proof.
    iIntros "#zspec #add_spec #aspec #δspec #ηspec".
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
    imp_app τ[Z;Z].
    { imp_app τ[Z;Z].
      iIntros (??) "-> -> %m Hm !>".
      iApply "Hm". }
    iIntros (??) "-> #%Ha %m Hm !>".
    iApply (imp_mono_ret with "Hm").
    iIntros (y ->). iPureIntro.
    lia.
  Qed.

End TacticTests.
