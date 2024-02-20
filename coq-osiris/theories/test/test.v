From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From stdpp Require Import relations.

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
  (∃ n, steps n (∅, eval [] e) (∅, ret v)).

(* [crashes e] means that the expression [e] can crash. *)

Local Notation crashes e :=
  (∃ n, steps n (∅, eval [] e) (∅, crash)).

(* -------------------------------------------------------------------------- *)

(* The tactic [step] solves a goal of the form [step e ?e']. *)

(* The construct [EAssert e] is evaluated as a choice between skipping the
   dynamic test and performing the dynamic test (eval.v). Here, we want the
   dynamic tests to be performed, so we choose the right-hand side. This is
   done by using [StepChooseRight]. It is brittle, but should do for now. *)

Local Ltac step :=
  first [
    eapply StepEval
  | eapply StepLoop
  | eapply StepChooseRight
  | eapply StepParRetRet
  | eapply StepParLeft; [ step ]
  | eapply StepParRight; [ step ]
  ].

(* The tactic [steps] solves a goal of the form [steps ?n e v]. *)

Local Ltac steps :=
  cbn;
  repeat first [
    rewrite bind_ret (* not sure why this is needed; [cbn] not enough *)
  | eapply (nsteps_O)
  | eapply nsteps_l; [ step | cbn ]
  | rewrite add_repr_repr
  | rewrite eq_repr_repr by representable
  ].

(* The tactic [reduces] solves a goal of the form [reduces e v]. *)

Local Ltac reduces :=
  intros; eexists; steps.

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
  let e := EMatchMkBranches e [
    Branch (PInt 0) (EInt 0);
    Branch (PVar "x") (EIntAdd (EVar "x") (EInt 1))
  ] in
  let v := VInt (repr 13) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_match_integer_and_alias_pattern :
  let e := EInt 0 in
  let e := EMatchMkBranches e [
    Branch (PAlias (PInt 0) "x") (EVar "x");
    Branch (PVar "x") (EIntAdd (EVar "x") (EInt 1))
  ] in
  let v := VInt (repr 0) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_match_integer_and_disjunction_pattern :
  let e := EInt 1 in
  let e := EMatchMkBranches e [
    Branch (PAlias (POr (PInt 0) (PInt 1)) "x") (EIntAdd (EInt 1) (EVar "x"));
    Branch (PVar "x") (EIntAdd (EVar "x") (EInt 33))
] in
  let v := VInt (repr 2) in
  reduces e v.
Proof. reduces. Qed.

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
      Branch (PInt 0) (EInt 32);
      Branch (PVar "x") (EIntAdd (EVar "x") (EInt 33))
    ]) $
    EApp (EVar "f") (EInt 1)
  in
  let v := VInt (repr 34) in
  reduces e v.
Proof. reduces. Qed.

Lemma test_EFun :
  let e :=
    ELet1Var "f" (
      EFunMultiPat [
        PPair (PVar "x1") (PVar "x2");
        PPair (PVar "y1") (PVar "y2")
      ] $
      EIntAdd (EVar "x1") (EVar "y2")
    ) $
    EMultiApp (EVar "f") [
      EPair (EInt 10) (EInt 20);
      EPair (EInt 30) (EInt 40)
    ]
  in
  let v := VInt (repr 50) in
  reduces e v.
Proof. reduces. Qed.

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
          ILet (Binding1 (PVar "z") (EMkPath ["B"; "y"]))
        ]
      ) $
      EMkPath ["A"; "z"]
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
            IOpenMkPath ["B"];
            ILet (Binding1 (PVar "z") (EMkPath ["y"]))
          ]
      ) $
      EMkPath ["A"; "z"]
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
            IIncludeMkPath ["B"];
            ILet (Binding1 (PVar "z") (EMkPath ["y"]))
          ]
      ) $
      EIntAdd (EMkPath ["A"; "x"]) (EMkPath ["A"; "z"])
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
      ELetOpen (MPath (MkPath ["A"])) $
      ELetOpen (MPath (MkPath ["B"])) $
      EVar "y"
  in
  let v := VInt (repr 1) in
  reduces e v.
Proof. reduces. Qed.
