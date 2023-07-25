From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.

Local Notation VClo1 body :=
  (
    VClo EnvNil $
         AnonFun "x" $
         body (EVar "x")
  ).
Local Notation VClo2 body :=
  (
    VClo EnvNil $
         AnonFun "x" $
         EFun1Var "y" $
         (body (EVar "x") (EVar "y"))
  ).
Local Notation dummy := (VClo EnvNil $ AnonFun "_" EUnit).

Local Infix ":::" := (concat).


Section ExternalsDef.
  (* This section describes the supported and yet to be supported external
     functions. *)

  (* ------------------------------------------------------------------------ *)
  (* Real external functions; they are all dummies for now. *)
  Local Fixpoint mkdummy (l : list string) : env :=
    match l with
    | [] => EnvNil
    | h :: l =>
        EnvCons h dummy $ mkdummy l
    end.

  (* None of them are supported yet. They are replaced by dummy values. *)
  Definition externals_real : env :=
    mkdummy [ "caml_format_int" ;
              "caml_hash" ;
              "caml_register_named_value" ;
              "register_named_value" ;

              (* TODO: references. *)
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
        EnvCons "%negint" Externals__negint $
                EnvCons "%addint" Externals__addint $
                EnvCons "%subint" Externals__subint $
                EnvCons "%mulint" Externals__mulint $
                EnvCons "%divint" Externals__divint $
                EnvCons "%modint" Externals__modint $
                EnvCons "%succint" Externals__succint $
                EnvCons "%predint" Externals__predint $
                EnvCons "%lessthan" Externals__lessthan $
                EnvCons "%greaterthan" Externals__greaterthan $
                EnvCons "%lessequal" Externals__lessequal $
                EnvCons "%greaterequal" Externals__greaterequal $
                EnvCons "%andint" Externals__andint $
                EnvCons "%orint" Externals__orint $
                EnvCons "%xorint" Externals__xorint $
                EnvCons "%lslint" Externals__lslint $
                EnvCons "%asrint" Externals__asrint $
                EnvCons "%lsrint" Externals__lsrint $
                EnvCons "%floatofint" Externals__floatofint $
                EnvCons "%intoffloat" Externals__intoffloat $
                EnvNil.

  (* ------------------------------------------------------------------------ *)

  (* On Booleans. *)

  Definition Externals__boolnot : val := VClo1 EBoolNeg.

  Definition externals_bool : env :=
    EnvCons "%boolnot" Externals__boolnot $

            (* [%seqand], and [%seqor] are *not* real functions!
               These are dummy values, which will never be used, as the
               translator should replace any calls to [Stdlib!.&&]
               (resp. [Stdlib!.||]) by the correct AST construct, namely
               [EBoolConj] (resp. [EBoolDisj]). *)
            EnvCons "%sequand" dummy $
            EnvCons "%sequor" dummy $

            EnvNil.

  (* ------------------------------------------------------------------------ *)

  Definition Externals__revapply : val :=
    VClo EnvNil $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "y") (EVar "x").

  Definition Externals__apply : val :=
    VClo EnvNil $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "x") (EVar "y").

  Definition Externals__identity : val :=
    VClo EnvNil $
         AnonFun "x" $ EVar "x".

  Definition Externals__ignore : val :=
    VClo EnvNil $ AnonFun "_" $ EUnit.

  (* Comparison. *)
  Definition Externals__eq : val := VClo2 EOpEq.
  Definition Externals__ne : val := VClo2 EOpNe.
  Axiom Externals__compare : val.

  Definition externals_misc : env :=
    EnvCons "%revapply" Externals__revapply $
            EnvCons "%apply" Externals__apply $
            EnvCons "%ignore" Externals__ignore $
            EnvCons "%identity" Externals__identity $


            (* FIXME (important): « = » and « == » should have very different
                                  behaviour. *)
            EnvCons "%equal" Externals__eq $
            EnvCons "%notequal" Externals__ne $
            EnvCons "%eq" Externals__eq $
            EnvCons "%noteq" Externals__ne $
            EnvCons "%compare" Externals__compare $
            EnvNil.

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
    EnvCons "%field0" Externals__field0 $
            EnvCons "%field1" Externals__field1 $
            EnvNil.

  (* ------------------------------------------------------------------------ *)

  Definition Externals :=
    VStruct $
            externals_real :::
            externals_int :::
            externals_bool :::
            externals_misc :::
            externals_pairs
  .

  Definition HasExternals (η : env) : Prop :=
    lookup_name η "Externals" = Ret Externals.

End ExternalsDef.
