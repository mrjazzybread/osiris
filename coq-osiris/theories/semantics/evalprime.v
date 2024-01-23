From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.

(* This file contains a definition of [eval'], a clone of [eval].

   The definition of [eval'] is not recursive: where [eval] calls [eval],
   [eval'] calls [eval].

   We prove that [eval'] and [eval] are equal. We declare [eval] opaque
   and [eval'] transparent; this allows us to unfold just one level of
   the recursive definition of [eval]. *)

(* ------------------------------------------------------------------------ *)

(* The definition of [eval']. *)

Definition eval' η e : micro val void :=
  match e with
  | EUnsupported =>
      unsupported_construct
  | EChar c =>
      ret (VChar c)
  | EPath π =>
      (* A path [π] is looked up in the environment [η]. *)
      lookup_path η π
  | EAnonFun a =>
      (* The creation of a closure captures the environment [η]. *)
      ret (VClo η a)
  | EApp e1 e2 =>
      (* The expressions [e1] and [e2] are evaluated in parallel. *)
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      call v1 v2
  | ETuple es =>
      (* The tuple components are evaluated in parallel. *)
      vs ← evals η es ;
      ret (VTuple vs)
  | EData c e =>
      v ← eval η e ;
      ret (VData c v)
  | ERecord fes =>
      (* The record components are evaluated in parallel. *)
      fvs ← evalfs η fes ;
      fvs ← sort fvs ;
      ret (VRecord fvs)
  | ERecordUpdate e fes =>
      (* The existing record and the new record components are evaluated in
         parallel. *)
      '(fvs, fvs') ← par (as_record (eval η e)) (evalfs η fes) ;
      (* The new components override existing components by the same name. *)
      fvs ← update fvs fvs' ;
      fvs ← sort fvs ;
      ret (VRecord fvs)
  | ERecordAccess e f =>
      fvs ← as_record (eval η e) ;
      lookup_name fvs f
  | EBoolConj e1 e2 =>
      b1 ← as_bool (eval η e1) ;
     if (b1 : bool) then eval η e2 else ret VFalse
  | EString s =>
      ret (VString s)
  | EInt i =>
      (* An integer literal is interpreted as a machine integer. *)
      (* We do not require this integer literal to lie within a certain
         range; we project it into the range of machine integers. *)
      ret (VInt (int.repr i))
  | EMaxInt =>
      ret (VInt (int.repr int.max_signed))
  | EMinInt =>
      ret (VInt (int.repr int.min_signed))
  | EIntNeg e =>
      i ← as_int (eval η e) ;
      ret (VInt (int.neg i))
  | EIntAdd e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.add i1 i2))
  | EIntSub e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.sub i1 i2))
  | EIntMul e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.mul i1 i2))
  | EIntDiv e1 e2 =>
      (* Signed division is used. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.divs i1 i2))
  | EIntMod e1 e2 =>
      (* Signed remainder is used. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      '() ← check_div_by_zero i2 ;
      ret (VInt (int.mods i1 i2))
  | EIntLand e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.land i1 i2))
  | EIntLor e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lor i1 i2))
  | EIntLxor e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      ret (VInt (int.lxor i1 i2))
  | EIntLnot e =>
      i ← as_int (eval η e) ;
      ret (VInt (int.lnot i))
  | EIntLsl e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsl i1 i2)))
  | EIntLsr e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.lsr i1 i2)))
  | EIntAsr e1 e2 =>
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      if_in_shift_range i2 (ret (VInt (int.asr i1 i2)))
  | EFloat f =>
      ret (VFloat f)
  | EOpPhysEq e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← phys_eq_val v1 v2 ;
      ret (VBool b)
  | EOpEq e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← eq_val v1 v2 ;
      ret (VBool b)
  | EOpNe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← ne_val v1 v2 ;
      ret (VBool b)
  | EOpLt e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← lt_val v1 v2 ;
      ret (VBool b)
  | EOpLe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← le_val v1 v2 ;
      ret (VBool b)
  | EOpGt e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← gt_val v1 v2 ;
      ret (VBool b)
  | EOpGe e1 e2 =>
      '(v1, v2) ← par (eval η e1) (eval η e2) ;
      b ← ge_val v1 v2 ;
      ret (VBool b)
  | EBoolDisj e1 e2 =>
      b1 ← as_bool (eval η e1) ;
      if (b1 : bool) then ret VTrue else eval η e2
  | EBoolNeg e =>
      b ← as_bool (eval η e) ;
      ret (VBool (negb b))
  | ELet bs e =>
      (* This is evaluated like a [match] construct with one branch. *)
      δ ← eval_bindings η bs ;
      η ← ret_concat δ η;
      eval η e
  | ELetRec rbs e =>
      (* Extend the environment with a mapping of each function name in [rbs]
         to a suitable recursive closure; then, evaluate [e]. *)
      let δ := eval_rec_bindings η rbs in
      η ← ret_concat δ η;
      eval η e
  | ELetModule M me e =>
      v ← eval_mexpr η me ;
      let δ := [(M, v)] in
      η ← ret_concat δ η;
      eval η e
  | ELetOpen me e =>
      δ ← as_struct (eval_mexpr η me) ;
      η ← ret_concat δ η;
      eval η e
  | ESeq e1 e2 =>
      _ ← eval η e1 ;
      eval η e2
  | EIfThen e e1 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else ok
  | EIfThenElse e e1 e2 =>
      b ← as_bool (eval η e) ;
      if (b : bool) then eval η e1 else eval η e2
  | EMatch e bs =>
      v ← eval η e ;
      eval_match η v bs
  | EWhile e body =>
      b ← as_bool (eval η e) ;
      if (b : bool) then
        _ ← eval η body ;
        stop CEval (η, EWhile e body)
      else
        ok
  | EFor x e1 e2 e =>
      (* The bounds are evaluated first. *)
      '(i1, i2) ← par (as_int (eval η e1)) (as_int (eval η e2)) ;
      (* Then, the loop is executed. *)
      stop CLoop (η, x, i1, i2, e)
  | EAssertFalse =>
      assertion_failure
  | EAssert e =>
      (* OCaml runtime assertions are erased when a module is compiled with
         the compiler flag [-noassert]; they are retained otherwise. We do not
         wish to depend on this flag, so we make a non-deterministic choice:
         either the runtime test is executed, or it is skipped. This forces
         the user to prove that the program is safe in both scenarios. *)
      let test : micro val void :=
        success ← as_bool (eval η e) ;
        if (success : bool) then ok else assertion_failure
      in
      choose ok test
  | ERef e =>
      v ← eval η e ;
      l ← stop CAlloc v ;
      ret (VLoc l)
  | ELoad e =>
      l ← as_loc (eval η e) ;
      stop CLoad l
  | EStore e1 e2 =>
      '(l, v) ← par (as_loc (eval η e1)) (eval η e2) ;
      _ ← stop CStore (l, v) ;
      ok
  end.

(* ------------------------------------------------------------------------ *)

(* [eval'] and [eval] are equal. *)

Lemma eval_eval' η e :
  eval η e = eval' η e.
Proof.
  destruct e; reflexivity.
Qed.
