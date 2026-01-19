From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.

Local Notation VClo1 body :=
  (
    VClo [] $
         AnonFun "x" $
         body (EVar "x")
  ).
Local Notation VClo2 body :=
  (
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         (body (EVar "x") (EVar "y"))
  ).
Local Notation dummy := (VClo [] $ AnonFun "_" EUnit).

Local Infix ":::" := (concat).


Section ExternalsDef.
  (* This section describes the supported and yet to be supported external
     functions. *)

  (* ------------------------------------------------------------------------ *)
  (* Real external functions; they are all dummies for now. *)
  Local Fixpoint mkdummy (l : list string) : env :=
    match l with
    | [] => []
    | h :: l =>
        (h, dummy) :: (mkdummy l)
    end.

  (* None of them are supported yet. They are replaced by dummy values. *)
  Definition externals_real : env :=
    mkdummy [ "caml_format_int" ;
              "caml_hash" ;
              "caml_register_named_value" ;
              "register_named_value" ;

              "%makemutable" ; "field0cheat" ; "%setfield0" ; "%incr" ; "%decr"
      ].


  (* ------------------------------------------------------------------------ *)
  (* Content of Externals used in [stdlib/int.ml]. *)

  Definition Externals__negint : val := VClo1 EIntNeg.
  Definition Externals__addint : val := VClo2 EIntAdd.
  Definition Externals__subint : val := VClo2 EIntSub.
  Definition Externals__mulint : val := VClo2 EIntMul.
  Definition Externals__divint : val := VClo2 EIntDiv.
  Definition Externals__modint : val := VClo2 EIntMod.
  Definition Externals__succint : val :=
    VClo1 (fun x => EIntAdd x (EInt 1)).
  Definition Externals__predint : val :=
    VClo1 (fun x => EIntSub x (EInt 1)).

  Definition Externals__lessthan : val := VClo2 EOpLt.
  Definition Externals__greaterthan : val := VClo2 EOpGt.
  Definition Externals__lessequal : val := VClo2 EOpLe.
  Definition Externals__greaterequal : val := VClo2 EOpGe.

  (* The following names are used in [stdlib/int.ml], but they are not supported
     yet: - %andint
          - %orint
          - %xorint
          - %lslint
          - %asrint
          - %lsrint
          - %floatofint
          - %intoffloat
          - caml_format_int
          - caml_hash
     They are replaced by a dummy function. *)
  Definition Externals__andint : val := dummy.
  Definition Externals__orint : val := dummy.
  Definition Externals__xorint : val := dummy.
  Definition Externals__lslint : val := dummy.
  Definition Externals__asrint : val := dummy.
  Definition Externals__lsrint : val := dummy.
  Definition Externals__floatofint : val := dummy.
  Definition Externals__intoffloat : val := dummy.

  Definition externals_int : env :=
    [("%negint", Externals__negint);
     ("%addint", Externals__addint);
     ("%subint", Externals__subint);
     ("%mulint", Externals__mulint);
     ("%divint", Externals__divint);
     ("%modint", Externals__modint);
     ("%succint", Externals__succint);
     ("%predint", Externals__predint);
     ("%lessthan", Externals__lessthan);
     ("%greaterthan", Externals__greaterthan);
     ("%lessequal", Externals__lessequal);
     ("%greaterequal", Externals__greaterequal);
     ("%andint", Externals__andint);
     ("%orint", Externals__orint);
     ("%xorint", Externals__xorint);
     ("%lslint", Externals__lslint);
     ("%asrint", Externals__asrint);
     ("%lsrint", Externals__lsrint);
     ("%floatofint", Externals__floatofint);
     ("%intoffloat", Externals__intoffloat)].

  (* ------------------------------------------------------------------------ *)

  (* On Booleans. *)

  Definition Externals__boolnot : val := VClo1 EBoolNeg.

  Definition externals_bool : env :=
    [("%boolnot", Externals__boolnot);
     (* [%seqand], and [%seqor] are *not* real functions!
        These are dummy values, which will never be used. *)

     (* The translator should replace any calls to [Stdlib!.&&] and [Stdlib!.||]
        by the correct AST construct, [EBoolConj] (resp. [EBoolDisj]). *)
     ("%sequand", dummy);
     ("%sequor", dummy)].

  (* ------------------------------------------------------------------------ *)

  Definition Externals__revapply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "y") (EVar "x").

  Definition Externals__apply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "x") (EVar "y").

  Definition Externals__identity : val :=
    VClo [] $
         AnonFun "x" $ EVar "x".

  Definition Externals__ignore : val :=
    VClo [] $ AnonFun "_" $ EUnit.

  (* Comparison. *)
  Definition Externals__eq : val := VClo2 EOpEq.
  Definition Externals__ne : val := VClo2 EOpNe.
  Axiom Externals__compare : val.

  Definition externals_misc : env :=
    [("%revapply", Externals__revapply);
     ("%apply", Externals__apply);
     ("%ignore", Externals__ignore);
     ("%identity", Externals__identity);
     ("%equal", Externals__eq);
     ("%notequal", Externals__ne);
     ("%eq", Externals__eq);
     ("%noteq", Externals__ne);
     ("%compare", Externals__compare)].

  (* ------------------------------------------------------------------------ *)

  (* On constructed types. *)

  Definition Externals__field0 : val :=
    VClo1 (λ (e : expr),
             ELet1 (PPair (PVar "x") PAny) e $
                   EVar "x").

  Definition Externals__field1 : val :=
    VClo1 (λ (e : expr),
             ELet1 (PPair PAny (PVar "x")) e $
                   EVar "x").

  Definition externals_pairs :=
    [("%field0", Externals__field0); ("%field1", Externals__field1)].

  (* ------------------------------------------------------------------------ *)

  Definition Externals :=
    VStruct
      (concat
         [externals_real;
          externals_int;
          externals_bool;
          externals_misc;
          externals_pairs]).

  Definition HasExternals (η : env) : Prop :=
    lookup_name η "Externals" = Ret Externals.

End ExternalsDef.
