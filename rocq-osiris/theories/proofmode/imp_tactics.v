From osiris.tactics Require Import tactics.
From osiris.lang Require Import encode type_nel.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import env_lookups.
From stdpp Require Import strings.
From Ltac2 Require Import Ltac2 Printf.

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

(* [mk_evar id ty] introduces a local let-binding [id : ty := ?x] into the
   proof context, where [?x] is a fresh metavariable.  The head symbol [id]
   is syntactically rigid, so [Hint Mode Encode +] is satisfied when Coq later
   searches for [Encode id], while the actual type is still deferred. *)
Ltac2 mk_evar (id : ident) (ty : constr) :=
  let v := open_constr:((_ : $ty)) in
  Std.pose (Some id) v.

Ltac2 get_pointsto (l : constr) : constr * constr :=
  let (_, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find hypothesis [%t ↦ _]" l)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | (?l' ↦ (#?a))%I =>
            if Constr.equal l l' then
              (name, Constr.type a)
            else
              go env
        | (▷ ?l' ↦ (#?a))%I =>
            if Constr.equal l l' then
              (name, Constr.type a)
            else
              go env
        | _ => go env
        end
    end
  in
  go spat_hyps.

Ltac2 rec imp_step () :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  match fetch_appropriate_arith_lemma e with
  | Some (lemma, arith_kind) =>
      try (iApply $lemma;
           match arith_kind with
           | Literal => ()
           | Op => Control.extend [] (fun _ => complete imp_step) [ fun _ => simple_intros (); auto ]
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
                        (fun _ =>
                           mk_evar @imp_store_A 'Type;
                           let store_a := Control.hyp @imp_store_A in
                           mk_evar @imp_store_HA open_constr:(Encode $store_a);
                           let specialized_store := open_constr:(imp_EStore' (A:=$store_a)) in
                           iApply ($specialized_store with "[$]");
                           try (imp_step ()))
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
  match x with
  | Some x =>
      let spec_ref := open_constr:(imp_ERef $x) in
      iApply $spec_ref; try (imp_step)
  | None =>
      Control.plus
        (fun _ => iApply imp_ERef;
                  complete imp_step)
        (fun _ => iApply imp_ERef2; try (imp_step))
  end.

Ltac2 Notation "imp_ref" x(constr) := imp_ref_tac (Some x).
Ltac2 Notation "imp_ref" := imp_ref_tac None.
Tactic Notation "imp_ref" constr(x) :=
  let tac := ltac2:(x |- imp_ref_tac (Ltac1.to_constr x)) in
  tac x.
Tactic Notation "imp_ref" := ltac2:(imp_ref).

Ltac2 imp_store_tac (l : constr) (x : constr option) :=
  let (hl, a) := get_pointsto l in
  match x with
  | Some x =>
      let specialized_store := open_constr:(imp_EStore $l $x) in
      iApply ($specialized_store with $hl) >
       [try (imp_step) | try (imp_step) ]
  | None =>
      let specialized_store := open_constr:(imp_EStore' (A:=$a) _ $l) in
      iApply ($specialized_store with $hl) >
        [try (imp_step) | try (imp_step) |
          iIntros "!>"; cbn beta;
          lazy_match! get_iris_goal () with
          | bi_forall (λ a, bi_wand (bi_pure (a = _)) _) =>
              let name := match! hl with | base.ident.INamed ?s => s | _ => '"" end in
              let pat := '("% -> " ++ $name)%string in
              iIntros $pat; auto
          end
        ]
  end.

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
      | Op => Control.extend [] (fun _ => try (imp_step)) [ fun _ => simple_intros (); auto ]
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
    (unfold tapp, tbind; simple_intros ())
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

Ltac2 imp_for_tac (invariant : constr) (i : constr) (j : constr) (selpat : constr option) :=
  let specialized_for := '(imp_EFor $invariant $i $j) in
  match selpat with
  | None => iApply $specialized_for
  | Some s => iApply ($specialized_for with $s)
  end >
    [ representable () | representable () | try (imp_step) | try (imp_step) | | iIntros "!>" ].

Tactic Notation "imp_for" constr(i) "to" constr(j) "$!" constr(invariant) "with" constr(sel) :=
  let tac := ltac2:(inv i j sel |-
                      imp_for_tac
                        (Option.get (Ltac1.to_constr inv))
                        (Option.get (Ltac1.to_constr i))
                        (Option.get (Ltac1.to_constr j))
                        (Ltac1.to_constr sel)) in
  tac invariant i j sel.
Tactic Notation "imp_for" constr(i) "to" constr(j) "$!" constr(invariant) :=
  let tac := ltac2:(inv i j |-
                      imp_for_tac
                        (Option.get (Ltac1.to_constr inv))
                        (Option.get (Ltac1.to_constr i))
                        (Option.get (Ltac1.to_constr j))
                        None) in
  tac invariant i j.

Ltac2 imp_if_tac (selpat : constr option) :=
  let specialized_if :=
    let e := get_expr () in
    lazy_match! eval hnf in $e with
    | EIfThen _ _ => 'imp_EIfThen2
    | EIfThenElse _ _ _ => 'imp_EIfThenElse2
    end
  in
  match selpat with
  | None => iApply $specialized_if
  | Some s => iApply ($specialized_if with $s)
  end >
    [ try (imp_step) | iSplit; try (iIntros "%") ].

Tactic Notation "imp_if" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_if_tac (Ltac1.to_constr sel)) in
  tac sel.
Tactic Notation "imp_if" := ltac2:(imp_if_tac None).

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
      iIntros "Hm".
      iApply "Hm". }
    iIntros "-> #%Ha Hm".
    iApply (imp_wand with "Hm").
    iIntros (y ->). iPureIntro.
    lia.
  Qed.

End TacticTests.
