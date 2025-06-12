From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.proofmode Require Import pure_tactics.
From stdpp Require Import relations base gmap.

(* We want to test our semantics, so as to ensure that it seems to be
   consistent with our expectations and with the informal definition
   of the semantics of OCaml.  *)

(* A difficulty is that the semantics is non-deterministic: in particular,
   function applications and tuples are evaluated in parallel. This gives
   rise to an exponential number of reduction paths. We do not wish to
   explore all paths, so we just verify that there exists one path that
   leads to the expected result. For now, this is good enough. Furthermore,
   the proof system already explores all paths, by construction, and can be
   used to prove facts of the form "for every result v, the assertion φ v
   holds". Here, we prove facts of the form "it is possible to reach the
   result v", which are of a different form, hence also valuable. *)

(* -------------------------------------------------------------------------- *)

(* [reduces e v] means that the expression [e] can reduce to the value [v]. *)

Local Notation reduces e v :=
  (∃ n σ, steps n (∅, eval [] e) (σ, ret v)).

(* [crashes e] means that the expression [e] can crash. *)

Local Notation crashes e :=
  (∃ n σ s, steps n (∅, eval [] e) (σ, crash s)).

(* -------------------------------------------------------------------------- *)

(* The tactic [step] solves a goal of the form [step e ?e']. *)

(* The construct [EAssert e] is evaluated as a choice between skipping the
   dynamic test and performing the dynamic test (eval.v). Here, we want the
   dynamic tests to be performed, so we choose the right-hand side. This is
   done by using [StepFlip false]. It is brittle, but should do for now. *)

Lemma is_fresh :
  ∀ (σ : store), σ !! (fresh (dom σ)) = None.
Proof.
  intros.
  apply fin_map_dom.not_elem_of_dom_1.
  apply fin_sets.is_fresh.
Qed.

Local Ltac step :=
  first [
      eapply StepEval
    | eapply StepLoop
    | eapply (StepFlip false)
    | eapply StepParRetRet
    | eapply StepParLeft; [ step ]
    | eapply StepParRight; [ step ]
    | eapply StepParPerformLeft
    | eapply StepParPerformRight
    | eapply StepHandleRet; simpl_wrap_eval_branches
    | eapply StepHandleThrow; simpl_wrap_eval_branches
    | match goal with
      | |- step (?σ, Stop CAlloc _ _) _ =>
          eapply StepAlloc with (l := fresh (dom σ));
          apply is_fresh
      end
    | eapply StepLoadSuccess;
      eauto using lookup_insert
      (* TODO this seems too restrictive:
              it will work only if we are reading the reference
              that was last allocated or updated *)
    | eapply StepStoreSuccess;
      eauto using lookup_insert (* TODO same as above *)
    | match goal with
      | |- step (?σ, Handle _ _) _ =>
          eapply StepHandlePerform with (l := fresh (dom σ));
          apply is_fresh
      end
    | match goal with
      | |- step (?σ, Stop CWrap (true, _, _, _) _) _ =>
          eapply StepWrap;
          [ apply is_fresh | by cbn ]
      | |- step (?σ, Stop CWrap (false, _, _, _) _) _ =>
          eapply StepShallowWrap;
          [ apply is_fresh | by cbn ]
      end
    | eapply StepHandleLeft; [ step ]
    | eapply StepResume; (try simpl_wrap_eval_branches); by cbn
    ].

(* The tactic [steps] solves a goal of the form [steps ?n e v]. *)

Local Ltac compute_lookup :=
  cbv [ lookup
          gmap_lookup
          gmap.gmap_dep_lookup
          gmap_car
          gmap.gmap_dep_ne_lookup
          encode
          loc_countable
          inj_countable'
          inj_countable
          Z_countable
          address ].

Local Ltac steps :=
  unfold_all; cbn;
  repeat
    (first [ eapply (nsteps_O)
               | eapply nsteps_l; [ step | compute_lookup; vm_compute fresh ]
               | rewrite add_repr_repr
               | rewrite eq_repr_repr by representable
       ]; unfold_all; cbn).

Local Ltac s := eapply nsteps_l; [ step | cbn; compute_lookup; vm_compute fresh ].

(* The tactic [reduces] solves a goal of the form [reduces e v]. *)

Local Ltac reduces :=
  intros; subst; repeat eexists; steps.

(* -------------------------------------------------------------------------- *)

(* Tests. *)

Lemma test_assert_false :
  let e := EAssert EFalse in
  crashes e.
Proof. reduces. Qed.

Lemma test_assert_true :
  let e := EAssert ETrue in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_seq_assert_true_unit :
  let e := ESeq (EAssert ETrue) EUnit in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_pair :
  let e := EPair ETrue EFalse in
  let v := VPair VTrue VFalse in
  reduces e v.
Proof. reduces. Qed.

(* The following tests verify that record fields are always alphabetically
   sorted in a record value, regardless of the order in which fields appear
   in the record construction expression. *)

Lemma test_record_construction_with_sorting_1 :
  let e := ERecord [Fexpr "foo" (EInt 0); Fexpr "bar" ETrue] in
  let fvs := [("bar", VTrue); ("foo", (VInt (repr 0)))] in
  let v := VRecord fvs in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_with_sorting_2 :
  let e := ERecord [Fexpr "bar" ETrue; Fexpr "foo" (EInt 0)] in
  let fvs := [("bar", VTrue); ("foo", (VInt (repr 0)))] in
  let v := VRecord fvs in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_and_access_1 :
  let e := ERecord [Fexpr "foo" (EInt 0); Fexpr "bar" ETrue] in
  let e := ERecordAccess e "bar" in
  let v := VTrue in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_and_access_2 :
  let e := ERecord [Fexpr "foo" (EInt 0); Fexpr "bar" ETrue] in
  let e := ERecordAccess e "foo" in
  let v := VInt (repr 0) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_and_deconstruction :
  let e := ERecord [Fexpr "foo" (EInt 10); Fexpr "bar" (EInt 32)] in
  let p := PRecord [("foo", (PVar "x")); ("bar", (PVar "y"))] in
  let e := ELet1 p e (EIntAdd (EVar "x") (EVar "y")) in
  let v := VInt (repr 42) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_record_construction_update_and_deconstruction :
  let e := ERecord [Fexpr "foo" (EInt 10); Fexpr "bar" (EInt 32)] in
  let e := ERecordUpdate e [Fexpr "bar" (EInt 14)] in
  let p := PRecord [("foo", (PVar "x")); ("bar", (PVar "y"))] in
  let e := ELet1 p e (EIntAdd (EVar "x") (EVar "y")) in
  let v := VInt (repr 24) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_match_integer :
  let e := EInt 12 in
  let e := EMatch e [
    Branch (CVal (PInt 0)) (EInt 0);
    Branch (CVal (PVar "x")) (EIntAdd (EVar "x") (EInt 1))
  ] in
  let v := VInt (repr 13) in
  reduces e v.
Proof. reduces. simpl. reduces. Qed.

Lemma test_match_integer_and_alias_pattern :
  let e := EInt 0 in
  let e := EMatch e [
    Branch (CVal (PAlias (PInt 0) "x")) (EVar "x");
    Branch (CVal (PVar "x")) (EIntAdd (EVar "x") (EInt 1))
  ] in
  let v := VInt (repr 0) in
  reduces e v.
Proof. reduces. reduces. Qed.

Lemma test_match_integer_and_disjunction_pattern :
  let e := EInt 1 in
  let e := EMatch e [
    Branch (CVal (PAlias (POr (PInt 0) (PInt 1)) "x")) (EIntAdd (EInt 1) (EVar "x"));
    Branch (CVal (PVar "x")) (EIntAdd (EVar "x") (EInt 33))
] in
  let v := VInt (repr 2) in
  reduces e v.
Proof. reduces. reduces. Qed.

Lemma test_call :
  let e :=
    ELet1Var "pair" (
      EFun1Var "x" (EFun1Var "y" (
        EPair (EVar "x") (EVar "y")
    ))) $
    EApp (EApp (EVar "pair") ETrue) EFalse
  in
  let v := VPair VTrue VFalse in
  reduces e v.
Proof. reduces. Qed.

Lemma test_EFunction :
  let e :=
    ELet1Var "f" (EFunction $ [
      Branch (CVal (PInt 0)) (EInt 32);
      Branch (CVal (PVar "x")) (EIntAdd (EVar "x") (EInt 33))
    ]) $
    EApp (EVar "f") (EInt 1)
  in
  let v := VInt (repr 34) in
  reduces e v.
Proof. reduces. simpl. reduces. Qed.

Fixpoint EFunMultiPat (ps : list cpat) (e : expr) :=
  match ps with
  | [] =>
      e
  | p :: ps =>
      EAnonFun (AnonFunction [Branch p (EFunMultiPat ps e)])
  end.

Lemma test_EFun :
  let e :=
    ELet1Var "f" (
      EFunMultiPat [
        CVal (PPair (PVar "x1") (PVar "x2"));
        CVal (PPair (PVar "y1") (PVar "y2"))
      ] $
      EIntAdd (EVar "x1") (EVar "y2")
    ) $
    (EVar "f")
      (EPair (EInt 10) (EInt 20))
      (EPair (EInt 30) (EInt 40))
  in
  let v := VInt (repr 50) in
  reduces e v.
Proof. reduces. reduces. Qed.

Lemma test_divergent_while_loop :
  let e := EWhile ETrue EUnit in
  ∃ e', steps 10 (∅, eval [] e) e'.
Proof. reduces. Qed.

Lemma test_trivial_while_loop :
  let e := EWhile EFalse EUnit in
  let v := VUnit in
  reduces e v.
Proof. reduces. Qed.

Lemma test_for_loop :
  (* for i = 0 to 1 do () done *)
  let e := EFor "i" (EInt 0) (EInt 1) EUnit in
  let v := VUnit in
  reduces e v.
Proof.
  (* This example is quite artificial, as we must manually force the
     execution of the loop. It is a good sanity check anyway. *)
  reduces.

  (* Iteration 0. *)
  (* Unroll this iteration. *)
  unfold loop.
  (* Simplify the comparison. *)
  rewrite lt_repr_repr by representable. cbn.
  (* Simplify the incrementation. *)
  unfold int.one. rewrite add_repr_repr. unfold Z.add. simpl.
  (* Step. *)
  steps.

  (* Iteration 1. *)
  unfold loop.
  rewrite lt_repr_repr by representable. cbn.
  unfold int.one. rewrite add_repr_repr. unfold Z.add. simpl.
  steps.

  (* Iteration 2. *)
  unfold loop.
  rewrite lt_repr_repr by representable. cbn.
  steps.

Qed.

(*
  let module A = struct
    module B = struct
      let x = 0
      let y = x + 1
    end
    let z = B.y
  end
  in A.z
 *)

Lemma test_struct_access :
  let e :=
    ELetModule "A" (
        MStruct [
          IModule "B" $ MStruct [
              ILet (Binding1 (PVar "x") (EInt 0));
              ILet (Binding1 (PVar "y") (EIntAdd (EVar "x") (EInt 1)))
            ];
          ILet (Binding1 (PVar "z") (EPath ["B"; "y"]))
        ]
      ) $
      (EPath ["A"; "z"])
  in
  let v := VInt (repr 1) in
  reduces e v.
Proof. reduces. Qed.

(*
  let module A = struct
    module B = struct
      let x = 0
      let y = x + 1
    end
    open B
    let z = y
  end
  in A.z
 *)

Lemma test_open :
  let e :=
    ELetModule "A" (
        MStruct [
            IModule "B" $ MStruct [
                ILet (Binding1 (PVar "x") (EInt 0));
                ILet (Binding1 (PVar "y") (EIntAdd (EVar "x") (EInt 1)))
              ];
            IOpen (MPath ["B"]);
            ILet (Binding1 (PVar "z") (EPath ["y"]))
          ]
      ) $
      EPath (["A"; "z"])
  in
  let v := VInt (repr 1) in
  reduces e v.
Proof. reduces. Qed.

(*
  let module A = struct
    module B = struct
      let x = 0
      let y = x + 1
    end
    include B
    let z = y
  end
  in A.x + A.z
 *)

Lemma test_include :
  let e :=
    ELetModule "A" (
        MStruct [
            IModule "B" $ MStruct [
                ILet (Binding1 (PVar "x") (EInt 0));
                ILet (Binding1 (PVar "y") (EIntAdd (EVar "x") (EInt 1)))
              ];
            IInclude (MPath ["B"]);
            ILet (Binding1 (PVar "z") (EPath ["y"]))
          ]
      ) $
      EIntAdd (EPath ["A"; "x"]) (EPath ["A"; "z"])
  in
  let v := VInt (repr 1) in
  reduces e v.
Proof. reduces. Qed.

(*
  let module A = struct
    module B = struct
      let x = 0
      let y = x + 1
    end
  end
  let open A in
  let open B in
  y
 *)

Lemma test_let_open :
  let e :=
    ELetModule "A" (
        MStruct [
            IModule "B" $ MStruct [
                ILet (Binding1 (PVar "x") (EInt 0));
                ILet (Binding1 (PVar "y") (EIntAdd (EVar "x") (EInt 1)))
              ]
          ]
      ) $
      ELetOpen (MPath ["A"]) $
      ELetOpen (MPath ["B"]) $
      EVar "y"
  in
  let v := VInt (repr 1) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_ref :
  let e :=
    ELet (Binding1 (PVar "x") (ERef (EInt 0)))
      (ELoad (EPath ["x"]))
  in
  reduces e (VInt (repr 0)).
Proof. reduces. Qed.

Lemma test_double_ref :
  let e :=
    ELet (Binding1 (PVar "x") (ERef (EInt 0)))
      (ESeq
         (EStore (EPath ["x"]) (EInt 1))
         (ELoad (EPath ["x"])))
  in
  reduces e (VInt (repr 1)).
Proof. reduces. Qed.

Notation "'cont'" := (K _).

Lemma test_handle_nocont :
  let e :=
    EPerform (EXData ["Choose"] [])
  in
  let m :=
    EMatch e
      [ (* | effect _, _ -> 42 *)
        Branch (CEff PAny PAny) (EInt 42)]
  in
  ∃ n σ, steps n (∅, eval [("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof. reduces. Qed.

Lemma test_handle :
  let e :=
    EPerform (EXData ["Choose"] [])
  in
  let m :=
    EMatch e
      [ (* | effect _, k -> continue k 42 *)
        Branch
         (CEff PAny (PVar "k"))
         (EContinue (EVar "k") (EInt 42));
        (* | x -> x *)
        Branch
          (CVal (PVar "x"))
          (EVar "x")]
  in
  ∃ n σ, steps n (∅, eval [("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof.
  reduces. fold (@try2 val).
  simpl_wrap_eval_branches. simpl_eval_branches. reduces.
Qed.

Lemma test_handle_compute_head :
  let e :=
      (21 + EPerform (EXData ["Choose"] []))%E
  in
  let m :=
    EMatch e
      [ (* | effect _, k -> continue k 21 *)
        Branch
          (CEff PAny (PVar "k"))
          (EContinue (EVar "k") (EInt 21));
        (* | x -> x *)
        Branch
          (CVal (PVar "x"))
          (EVar "x")]
  in
  ∃ n σ, steps n (∅, eval [("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof. reduces. simpl_wrap_eval_branches. simpl_eval_branches. reduces. Qed.

Lemma test_handle_compute_branch :
  let e :=
    (20 + EPerform (EXData ["Choose"] []))%E
  in
  let m :=
    EMatch e
      [ (* | effect _, k -> let y = continue k 21 in y + 1 *)
        Branch
          (CEff PAny (PVar "k"))
          (ELet1 (PVar "y")
             (EContinue (EVar "k") (EInt 21))
             (EVar "y" + 1)%E);
        (* | x -> x *)
        Branch
          (CVal (PVar "x"))
          (EVar "x")]
  in
  ∃ n σ, steps n (∅, eval [("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof. reduces. simpl_wrap_eval_branches. simpl_eval_branches. reduces. Qed.

Lemma test_handle_reinstall_ret :
  let e1 :=
    EPerform (EXData ["Choose"] [])
  in
  let e2 :=
    EMatch e1
      [ (* | x -> 21 + x *)
        Branch
          (CVal (PVar "x"))
          (21 + EVar "x")%E]
  in
  let m :=
    EMatch e2
      [ (* | effect _, k -> continue k 21 *)
        Branch
          (CEff PAny (PVar "k"))
          (EContinue (EVar "k") (EInt 21));
        (* | x -> x *)
        Branch
          (CVal (PVar "x"))
          (EVar "x")]
  in
  ∃ n σ, steps n (∅, eval [("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof. reduces. simpl_wrap_eval_branches. simpl_eval_branches. reduces. Qed.

Lemma test_handle_exception :
  let e :=
    EPerform (EXData ["Choose"] [])
  in
  let m :=
    EMatch e
      [ (* | effect _, k -> discontinue k Not_found *)
        Branch
         (CEff PAny (PVar "k"))
         (EDiscontinue (EVar "k") (EXData ["Not_found"] []));
        (* | exception Not_found -> 42 *)
        Branch
          (CExc (PXData ["Not_found"] []))
          (EInt 42)]
  in
  ∃ n σ, steps n (∅, eval [("Not_found", (VLoc (Loc 1)));
                           ("Choose", (VLoc (Loc 0)))] m) (σ, ret (VInt (repr 42))).
Proof. reduces. simpl_wrap_eval_branches. simpl_eval_branches. reduces. Qed.

Lemma test_shallow_handle :
  let η := [("Choose", (VLoc (Loc 0)))] in
  let e :=
    EPerform (EXData ["Choose"] [])
  in
  let bs :=
    [ (* | effect _, k -> continue k 42 *)
      Branch
        (CEff PAny (PVar "k"))
        (EContinue (EVar "k") (EInt 42))]
  in
  let m :=
    EShallowMatch e bs
  in
  ∃ n σ, steps n (∅, eval η m) (σ, ret (VInt (repr 42))).
Proof. do 2 eexists. reduces; unfold handle; reduces. Qed.

Lemma test_nested_handlers :
  let η := [("Get22", (VLoc (Loc 22))); ("Get20", (VLoc (Loc 20)))] in
  let e :=
    ELet1 (PVar "y")
      (EPerform (EXData ["Get20"] []))
      (EVar "y" + EPerform (EXData ["Get22"] []))%E
  in
  let m1 :=
    EMatch e
      [ (* | effect Get22, k -> continue k 22 *)
        Branch
          (CEff (PXData ["Get22"] []) (PVar "k"))
          (EContinue (EVar "k") (EInt 22));
        (* | x -> x *)
        Branch (CVal (PVar "x")) (EVar "x") ]
  in
  let m2 :=
    EMatch m1
      [ (* | effect Get20, k -> continue k 20 *)
        Branch
          (CEff (PXData ["Get20"] []) (PVar "k"))
          (EContinue
             (EVar "k")
             (EInt 20));
        (* | x -> x *)
        Branch (CVal (PVar "x")) (EVar "x") ]
  in
  ∃ n σ, steps n (∅, eval η m2) (σ, ret (VInt (repr 42))).
Proof.
  intros. subst e m1 m2. reduces.
  simpl_wrap_eval_branches; simpl_eval_branches.
  reduces. fold (@try2 val).
  simpl_wrap_eval_branches. reduces. reduces.
Qed.

Lemma test_repeat_handle :
  let η :=  [("Get21", (VLoc (Loc 21)))] in
  let e :=
    (EPerform (EXData ["Get21"] []) + EPerform (EXData ["Get21"] []))%E
  in
  let m :=
    EMatch e
      [ (* | effect Get21, k -> continue k 21 *)
        Branch
          (CEff (PXData ["Get21"] []) (PVar "k"))
          (EContinue (EVar "k") (EInt 21));
        (* | x -> x *)
        Branch
          (CVal (PVar "x"))
          (EVar "x")]
  in
  ∃ n σ, steps n (∅, eval η m) (σ, ret (VInt (repr 42))).
Proof.
  reduces.
  fold (@try2 val). simpl_wrap_eval_branches. simpl_eval_branches. reduces.
  fold (@try2 val). simpl_wrap_eval_branches. simpl_eval_branches. reduces.
Qed.

Lemma test_shallow_ret_reinstall :
  let η := [("Get32", (VLoc (Loc 32))); ("Get10", (VLoc (Loc 10)))] in
  let e := (ELet1 (PVar "x")
              (EPerform (EXData ["Get32"] []))
              (EVar "x" + EPerform (EXData ["Get10"] [])))%E
  in
  let bs :=
    [ (* | effect Get10, k -> continue k 10 *)
      Branch
        (CEff (PXData ["Get10"] []) (PVar "k"))
        (EContinue (EVar "k") (EInt 10))]
  in
  let m1 :=
    Handle (eval η e)
      (shallow_eval_branches η bs bs)
  in
  let m2 :=
    Handle m1
      (λ o,
        eval_branches η o
          [ (* | effect Get32, k -> continue k 32 *)
            Branch
              (CEff (PXData ["Get32"] []) (PVar "k"))
              (EContinue (EVar "k") (EInt 32));
            (* | x -> x *)
            Branch (CVal (PVar "x")) (EVar "x")])
  in
  ∃ n σ, steps n (∅, m2) (σ, ret (VInt (repr 42))).
Proof. intros. subst e m1 m2. reduces. Qed.

(* Further test ideas:
   - nested effect and exception handlers *)
