From osiris Require Import base.
Require Import syntax.


(* More complete induction schemes on syntax constructs (maybe solved with Rocq 9.2 ?). *)

Section pat.

  Context
    (Ppat : pat → Prop)
    (Ppats : list pat → Prop)
    (Pfps : list (field * pat) → Prop)
  .

  Context
    (IH_PUnsupported : Ppat PUnsupported)
    (IH_PAny : Ppat PAny)
    (IH_PVar : ∀ v, Ppat (PVar v))
    (IH_PAlias : ∀ p v (IHp : Ppat p), Ppat (PAlias p v))
    (IH_POr : ∀ p1 p2 (IHp1 : Ppat p1) (IHp2 : Ppat p2), Ppat (POr p1 p2))
    (IH_PTuple : ∀ ps (IHps : Ppats ps), Ppat (PTuple ps))
    (IH_PData : ∀ d ps (IHps : Ppats ps), Ppat (PData d ps))
    (IH_PXData : ∀ π ps (IHps : Ppats ps), Ppat (PXData π ps))
    (IH_PRecord : ∀ fps (IHfps : Pfps fps), Ppat (PRecord fps))
    (IH_PInline : ∀ d p (IHp : Ppat p), Ppat (PInline d p))
    (IH_PArray : ∀ ps (IHps : Ppats ps), Ppat (PArray ps))
    (IH_PInt : ∀ z, Ppat (PInt z))
    (IH_PChar : ∀ c, Ppat (PChar c))
    (IH_PString : ∀ s, Ppat (PString s))
    (IH_pats_nil : Ppats [])
    (IH_pats_cons : ∀ p ps (IHp : Ppat p) (IHps : Ppats ps), Ppats (p :: ps))
    (IH_fps_nil : Pfps [])
    (IH_fps_cons : ∀ f p fps (IHp : Ppat p) (IHfps : Pfps fps), Pfps ((f, p) :: fps))
  .

  (* Bound ahead of the [match], as in [expr_ind] below. They cannot be
     mutual [Fixpoint]s: [list pat] is not part of the [pat] family, so the
     guard checker rejects the recursive call. *)

  Fixpoint pat_ind p : Ppat p :=
    let pats_ind := fix pats_ind ps : Ppats ps :=
        match ps with
        | [] => IH_pats_nil
        | p :: ps => IH_pats_cons p ps (pat_ind p) (pats_ind ps)
        end in
    let fps_ind := fix fps_ind fps : Pfps fps :=
        match fps with
        | [] => IH_fps_nil
        | (f, p) :: fps => IH_fps_cons f p fps (pat_ind p) (fps_ind fps)
        end in
    match p with
    | PUnsupported => IH_PUnsupported
    | PAny => IH_PAny
    | PVar v => IH_PVar v
    | PAlias p v => IH_PAlias p v (pat_ind p)
    | POr p1 p2 => IH_POr p1 p2 (pat_ind p1) (pat_ind p2)
    | PTuple ps => IH_PTuple ps (pats_ind ps)
    | PData d ps => IH_PData d ps (pats_ind ps)
    | PXData π ps => IH_PXData π ps (pats_ind ps)
    | PRecord fps => IH_PRecord fps (fps_ind fps)
    | PInline d p => IH_PInline d p (pat_ind p)
    | PArray ps => IH_PArray ps (pats_ind ps)
    | PInt z => IH_PInt z
    | PChar c => IH_PChar c
    | PString s => IH_PString s
    end.

End pat.


(* ------------------------------------------------------------------------ *)


(* Rocq's generated principle for [expr] is too weak: no hypothesis for
   subexpressions carried in a list ([list expr] is not a recursive
   occurrence), and none for the children in [expr]'s sibling families
   ([anonfun], [fexpr], [branch], [binding], [rec_binding], [mexpr],
   [sitem]).

   The principle below covers the whole family and the six kinds of list,
   traversing them with local [fix]es for the guard condition.
   Note that it shadows the generated names: [induction e] no longer
   works in importing files, write [apply (expr_ind ...)] instead. *)

Section expr.

  Context
    (Pexpr         : expr → Prop)
    (Pexprs        : list expr → Prop)
    (Pfexpr        : fexpr → Prop)
    (Pfexprs       : list fexpr → Prop)
    (Pbranch       : branch → Prop)
    (Pbranches     : list branch → Prop)
    (Pbinding      : binding → Prop)
    (Pbindings     : list binding → Prop)
    (Prec_binding  : rec_binding → Prop)
    (Prec_bindings : list rec_binding → Prop)
    (Panonfun      : anonfun → Prop)
    (Pmexpr        : mexpr → Prop)
    (Psitem        : sitem → Prop)
    (Psitems       : list sitem → Prop)
  .

  (* Expressions. *)

  Context
    (IH_EUnsupported : Pexpr EUnsupported)
    (IH_EPath : ∀ x, Pexpr (EPath x))
    (IH_EAnonFun : ∀ a (IHa : Panonfun a), Pexpr (EAnonFun a))
    (IH_EApp : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2), Pexpr (EApp e1 e2))
    (IH_ETuple : ∀ es (IHes : Pexprs es), Pexpr (ETuple es))
    (IH_EData : ∀ c es (IHes : Pexprs es), Pexpr (EData c es))
    (IH_EXData : ∀ π es (IHes : Pexprs es), Pexpr (EXData π es))
    (IH_ERecord : ∀ t es (IHes : Pexprs es), Pexpr (ERecord t es))
    (IH_ERecordUpdate : ∀ e fes (IHe : Pexpr e) (IHfes : Pfexprs fes),
       Pexpr (ERecordUpdate e fes))
    (IH_ERecordAccess : ∀ e f (IHe : Pexpr e), Pexpr (ERecordAccess e f))
    (IH_ERecordSet : ∀ e1 f e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (ERecordSet e1 f e2))
    (IH_EAtomicLoc : ∀ e f (IHe : Pexpr e), Pexpr (EAtomicLoc e f))
    (IH_EInline : ∀ c t es (IHes : Pexprs es), Pexpr (EInline c t es))
    (IH_EArrayLit : ∀ es (IHes : Pexprs es), Pexpr (EArrayLit es))
    (IH_EArrayLength : ∀ e (IHe : Pexpr e), Pexpr (EArrayLength e))
    (IH_EArrayGet : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EArrayGet e1 e2))
    (IH_EArraySet : ∀ e1 e2 e3
       (IHe1 : Pexpr e1) (IHe2 : Pexpr e2) (IHe3 : Pexpr e3),
       Pexpr (EArraySet e1 e2 e3))
    (IH_EArrayMake : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EArrayMake e1 e2))
    (IH_EFreeze : ∀ e (IHe : Pexpr e), Pexpr (EFreeze e))
    (IH_EUnfreeze : ∀ e (IHe : Pexpr e), Pexpr (EUnfreeze e))
    (IH_EBoolConj : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EBoolConj e1 e2))
    (IH_EBoolDisj : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EBoolDisj e1 e2))
    (IH_EBoolNeg : ∀ e (IHe : Pexpr e), Pexpr (EBoolNeg e))
    (IH_EInt : ∀ i, Pexpr (EInt i))
    (IH_EMaxInt : Pexpr EMaxInt)
    (IH_EMinInt : Pexpr EMinInt)
    (IH_EIntNeg : ∀ e (IHe : Pexpr e), Pexpr (EIntNeg e))
    (IH_EIntAdd : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntAdd e1 e2))
    (IH_EIntSub : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntSub e1 e2))
    (IH_EIntMul : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntMul e1 e2))
    (IH_EIntDiv : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntDiv e1 e2))
    (IH_EIntMod : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntMod e1 e2))
    (IH_EIntLand : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntLand e1 e2))
    (IH_EIntLor : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntLor e1 e2))
    (IH_EIntLxor : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntLxor e1 e2))
    (IH_EIntLnot : ∀ e (IHe : Pexpr e), Pexpr (EIntLnot e))
    (IH_EIntLsl : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntLsl e1 e2))
    (IH_EIntLsr : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntLsr e1 e2))
    (IH_EIntAsr : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIntAsr e1 e2))
    (IH_EFloat : ∀ f, Pexpr (EFloat f))
    (IH_EChar : ∀ c, Pexpr (EChar c))
    (IH_EString : ∀ s, Pexpr (EString s))
    (IH_EOpPhysEq : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpPhysEq e1 e2))
    (IH_EOpEq : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpEq e1 e2))
    (IH_EOpNe : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpNe e1 e2))
    (IH_EOpLt : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpLt e1 e2))
    (IH_EOpLe : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpLe e1 e2))
    (IH_EOpGt : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpGt e1 e2))
    (IH_EOpGe : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EOpGe e1 e2))
    (IH_ELet : ∀ bs e (IHbs : Pbindings bs) (IHe : Pexpr e), Pexpr (ELet bs e))
    (IH_ELetRec : ∀ rbs e (IHrbs : Prec_bindings rbs) (IHe : Pexpr e),
       Pexpr (ELetRec rbs e))
    (IH_ELetModule : ∀ M me e (IHme : Pmexpr me) (IHe : Pexpr e),
       Pexpr (ELetModule M me e))
    (IH_ELetOpen : ∀ me e (IHme : Pmexpr me) (IHe : Pexpr e),
       Pexpr (ELetOpen me e))
    (IH_ESeq : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2), Pexpr (ESeq e1 e2))
    (IH_EIfThen : ∀ e e1 (IHe : Pexpr e) (IHe1 : Pexpr e1),
       Pexpr (EIfThen e e1))
    (IH_EIfThenElse : ∀ e e1 e2
       (IHe : Pexpr e) (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EIfThenElse e e1 e2))
    (IH_EMatch : ∀ e bs (IHe : Pexpr e) (IHbs : Pbranches bs),
       Pexpr (EMatch e bs))
    (IH_EShallowMatch : ∀ e bs (IHe : Pexpr e) (IHbs : Pbranches bs),
       Pexpr (EShallowMatch e bs))
    (IH_ERaise : ∀ e (IHe : Pexpr e), Pexpr (ERaise e))
    (IH_EPerform : ∀ e (IHe : Pexpr e), Pexpr (EPerform e))
    (IH_EContinue : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EContinue e1 e2))
    (IH_EDiscontinue : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EDiscontinue e1 e2))
    (IH_EWhile : ∀ e body (IHe : Pexpr e) (IHbody : Pexpr body),
       Pexpr (EWhile e body))
    (IH_EFor : ∀ x e1 e2 e
       (IHe1 : Pexpr e1) (IHe2 : Pexpr e2) (IHe : Pexpr e),
       Pexpr (EFor x e1 e2 e))
    (IH_EAssertFalse : Pexpr EAssertFalse)
    (IH_EAssert : ∀ e (IHe : Pexpr e), Pexpr (EAssert e))
    (IH_ERef : ∀ e (IHe : Pexpr e), Pexpr (ERef e))
    (IH_ELoad : ∀ e (IHe : Pexpr e), Pexpr (ELoad e))
    (IH_EStore : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EStore e1 e2))
    (IH_EExchange : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EExchange e1 e2))
    (IH_ECAS : ∀ e1 e2 e3
       (IHe1 : Pexpr e1) (IHe2 : Pexpr e2) (IHe3 : Pexpr e3),
       Pexpr (ECAS e1 e2 e3))
    (IH_EFAA : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EFAA e1 e2))
    (IH_ENewProph : Pexpr ENewProph)
    (IH_EResolve : ∀ e π a (IHe : Pexpr e), Pexpr (EResolve e π a))
    (IH_EIgnore : ∀ e (IHe : Pexpr e), Pexpr (EIgnore e))
    (IH_EFork : ∀ e1 e2 (IHe1 : Pexpr e1) (IHe2 : Pexpr e2),
       Pexpr (EFork e1 e2))
    (IH_EJoin : ∀ e (IHe : Pexpr e), Pexpr (EJoin e))
  .

  (* The other members of the family. *)

  Context
    (IH_Fexpr : ∀ f e (IHe : Pexpr e), Pfexpr (Fexpr f e))
    (IH_Branch : ∀ cp e (IHe : Pexpr e), Pbranch (Branch cp e))
    (IH_Binding : ∀ p e (IHe : Pexpr e), Pbinding (Binding p e))
    (IH_RecBinding : ∀ f a (IHa : Panonfun a), Prec_binding (RecBinding f a))
    (IH_AnonFun : ∀ x e (IHe : Pexpr e), Panonfun (AnonFun x e))
    (IH_MUnsupported : Pmexpr MUnsupported)
    (IH_MPath : ∀ π, Pmexpr (MPath π))
    (IH_MStruct : ∀ items (IHitems : Psitems items), Pmexpr (MStruct items))
    (IH_MFunctor : ∀ x items (IHitems : Psitems items),
       Pmexpr (MFunctor x items))
    (IH_MCoercion : ∀ me c (IHme : Pmexpr me), Pmexpr (MCoercion me c))
    (IH_ILet : ∀ bs (IHbs : Pbindings bs), Psitem (ILet bs))
    (IH_ILetRec : ∀ rbs (IHrbs : Prec_bindings rbs), Psitem (ILetRec rbs))
    (IH_IModule : ∀ m me (IHme : Pmexpr me), Psitem (IModule m me))
    (IH_IOpen : ∀ me (IHme : Pmexpr me), Psitem (IOpen me))
    (IH_IInclude : ∀ me (IHme : Pmexpr me), Psitem (IInclude me))
    (IH_IExternal : ∀ x e (IHe : Pexpr e), Psitem (IExternal x e))
    (IH_IExtend : ∀ cs, Psitem (IExtend cs))
  .

  (* The lists. *)

  Context
    (IH_exprs_nil : Pexprs [])
    (IH_exprs_cons : ∀ e es (IHe : Pexpr e) (IHes : Pexprs es),
       Pexprs (e :: es))
    (IH_fexprs_nil : Pfexprs [])
    (IH_fexprs_cons : ∀ fe fes (IHfe : Pfexpr fe) (IHfes : Pfexprs fes),
       Pfexprs (fe :: fes))
    (IH_branches_nil : Pbranches [])
    (IH_branches_cons : ∀ b bs (IHb : Pbranch b) (IHbs : Pbranches bs),
       Pbranches (b :: bs))
    (IH_bindings_nil : Pbindings [])
    (IH_bindings_cons : ∀ b bs (IHb : Pbinding b) (IHbs : Pbindings bs),
       Pbindings (b :: bs))
    (IH_rec_bindings_nil : Prec_bindings [])
    (IH_rec_bindings_cons : ∀ rb rbs
       (IHrb : Prec_binding rb) (IHrbs : Prec_bindings rbs),
       Prec_bindings (rb :: rbs))
    (IH_sitems_nil : Psitems [])
    (IH_sitems_cons : ∀ i items (IHi : Psitem i) (IHitems : Psitems items),
       Psitems (i :: items))
  .

  Fixpoint expr_ind e : Pexpr e :=
    let exprs_ind := fix exprs_ind es : Pexprs es :=
      match es with
      | [] => IH_exprs_nil
      | e :: es => IH_exprs_cons e es (expr_ind e) (exprs_ind es)
      end in
    let fexprs_ind := fix fexprs_ind fes : Pfexprs fes :=
      match fes with
      | [] => IH_fexprs_nil
      | fe :: fes => IH_fexprs_cons fe fes (fexpr_ind fe) (fexprs_ind fes)
      end in
    let branches_ind := fix branches_ind bs : Pbranches bs :=
      match bs with
      | [] => IH_branches_nil
      | b :: bs => IH_branches_cons b bs (branch_ind b) (branches_ind bs)
      end in
    let bindings_ind := fix bindings_ind bs : Pbindings bs :=
      match bs with
      | [] => IH_bindings_nil
      | b :: bs => IH_bindings_cons b bs (binding_ind b) (bindings_ind bs)
      end in
    let rec_bindings_ind := fix rec_bindings_ind rbs : Prec_bindings rbs :=
      match rbs with
      | [] => IH_rec_bindings_nil
      | rb :: rbs =>
          IH_rec_bindings_cons rb rbs (rec_binding_ind rb) (rec_bindings_ind rbs)
      end in
    match e with
    | EUnsupported => IH_EUnsupported
    | EPath x => IH_EPath x
    | EAnonFun a => IH_EAnonFun a (anonfun_ind a)
    | EApp e1 e2 => IH_EApp e1 e2 (expr_ind e1) (expr_ind e2)
    | ETuple es => IH_ETuple es (exprs_ind es)
    | EData c es => IH_EData c es (exprs_ind es)
    | EXData π es => IH_EXData π es (exprs_ind es)
    | ERecord t es => IH_ERecord t es (exprs_ind es)
    | ERecordUpdate e fes =>
        IH_ERecordUpdate e fes (expr_ind e) (fexprs_ind fes)
    | ERecordAccess e f => IH_ERecordAccess e f (expr_ind e)
    | ERecordSet e1 f e2 => IH_ERecordSet e1 f e2 (expr_ind e1) (expr_ind e2)
    | EAtomicLoc e f => IH_EAtomicLoc e f (expr_ind e)
    | EInline c t es => IH_EInline c t es (exprs_ind es)
    | EArrayLit es => IH_EArrayLit es (exprs_ind es)
    | EArrayLength e => IH_EArrayLength e (expr_ind e)
    | EArrayGet e1 e2 => IH_EArrayGet e1 e2 (expr_ind e1) (expr_ind e2)
    | EArraySet e1 e2 e3 =>
        IH_EArraySet e1 e2 e3 (expr_ind e1) (expr_ind e2) (expr_ind e3)
    | EArrayMake e1 e2 => IH_EArrayMake e1 e2 (expr_ind e1) (expr_ind e2)
    | EFreeze e => IH_EFreeze e (expr_ind e)
    | EUnfreeze e => IH_EUnfreeze e (expr_ind e)
    | EBoolConj e1 e2 => IH_EBoolConj e1 e2 (expr_ind e1) (expr_ind e2)
    | EBoolDisj e1 e2 => IH_EBoolDisj e1 e2 (expr_ind e1) (expr_ind e2)
    | EBoolNeg e => IH_EBoolNeg e (expr_ind e)
    | EInt i => IH_EInt i
    | EMaxInt => IH_EMaxInt
    | EMinInt => IH_EMinInt
    | EIntNeg e => IH_EIntNeg e (expr_ind e)
    | EIntAdd e1 e2 => IH_EIntAdd e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntSub e1 e2 => IH_EIntSub e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntMul e1 e2 => IH_EIntMul e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntDiv e1 e2 => IH_EIntDiv e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntMod e1 e2 => IH_EIntMod e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntLand e1 e2 => IH_EIntLand e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntLor e1 e2 => IH_EIntLor e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntLxor e1 e2 => IH_EIntLxor e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntLnot e => IH_EIntLnot e (expr_ind e)
    | EIntLsl e1 e2 => IH_EIntLsl e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntLsr e1 e2 => IH_EIntLsr e1 e2 (expr_ind e1) (expr_ind e2)
    | EIntAsr e1 e2 => IH_EIntAsr e1 e2 (expr_ind e1) (expr_ind e2)
    | EFloat f => IH_EFloat f
    | EChar c => IH_EChar c
    | EString s => IH_EString s
    | EOpPhysEq e1 e2 => IH_EOpPhysEq e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpEq e1 e2 => IH_EOpEq e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpNe e1 e2 => IH_EOpNe e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpLt e1 e2 => IH_EOpLt e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpLe e1 e2 => IH_EOpLe e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpGt e1 e2 => IH_EOpGt e1 e2 (expr_ind e1) (expr_ind e2)
    | EOpGe e1 e2 => IH_EOpGe e1 e2 (expr_ind e1) (expr_ind e2)
    | ELet bs e => IH_ELet bs e (bindings_ind bs) (expr_ind e)
    | ELetRec rbs e => IH_ELetRec rbs e (rec_bindings_ind rbs) (expr_ind e)
    | ELetModule M me e => IH_ELetModule M me e (mexpr_ind me) (expr_ind e)
    | ELetOpen me e => IH_ELetOpen me e (mexpr_ind me) (expr_ind e)
    | ESeq e1 e2 => IH_ESeq e1 e2 (expr_ind e1) (expr_ind e2)
    | EIfThen e e1 => IH_EIfThen e e1 (expr_ind e) (expr_ind e1)
    | EIfThenElse e e1 e2 =>
        IH_EIfThenElse e e1 e2 (expr_ind e) (expr_ind e1) (expr_ind e2)
    | EMatch e bs => IH_EMatch e bs (expr_ind e) (branches_ind bs)
    | EShallowMatch e bs =>
        IH_EShallowMatch e bs (expr_ind e) (branches_ind bs)
    | ERaise e => IH_ERaise e (expr_ind e)
    | EPerform e => IH_EPerform e (expr_ind e)
    | EContinue e1 e2 => IH_EContinue e1 e2 (expr_ind e1) (expr_ind e2)
    | EDiscontinue e1 e2 => IH_EDiscontinue e1 e2 (expr_ind e1) (expr_ind e2)
    | EWhile e body => IH_EWhile e body (expr_ind e) (expr_ind body)
    | EFor x e1 e2 e =>
        IH_EFor x e1 e2 e (expr_ind e1) (expr_ind e2) (expr_ind e)
    | EAssertFalse => IH_EAssertFalse
    | EAssert e => IH_EAssert e (expr_ind e)
    | ERef e => IH_ERef e (expr_ind e)
    | ELoad e => IH_ELoad e (expr_ind e)
    | EStore e1 e2 => IH_EStore e1 e2 (expr_ind e1) (expr_ind e2)
    | EExchange e1 e2 => IH_EExchange e1 e2 (expr_ind e1) (expr_ind e2)
    | ECAS e1 e2 e3 =>
        IH_ECAS e1 e2 e3 (expr_ind e1) (expr_ind e2) (expr_ind e3)
    | EFAA e1 e2 => IH_EFAA e1 e2 (expr_ind e1) (expr_ind e2)
    | ENewProph => IH_ENewProph
    | EResolve e π a => IH_EResolve e π a (expr_ind e)
    | EIgnore e => IH_EIgnore e (expr_ind e)
    | EFork e1 e2 => IH_EFork e1 e2 (expr_ind e1) (expr_ind e2)
    | EJoin e => IH_EJoin e (expr_ind e)
    end

  with fexpr_ind fe : Pfexpr fe :=
    match fe with
    | Fexpr f e => IH_Fexpr f e (expr_ind e)
    end

  with branch_ind b : Pbranch b :=
    match b with
    | Branch cp e => IH_Branch cp e (expr_ind e)
    end

  with binding_ind b : Pbinding b :=
    match b with
    | Binding p e => IH_Binding p e (expr_ind e)
    end

  with rec_binding_ind rb : Prec_binding rb :=
    match rb with
    | RecBinding f a => IH_RecBinding f a (anonfun_ind a)
    end

  with anonfun_ind a : Panonfun a :=
    match a with
    | AnonFun x e => IH_AnonFun x e (expr_ind e)
    end

  with mexpr_ind me : Pmexpr me :=
    let sitems_ind := fix sitems_ind items : Psitems items :=
      match items with
      | [] => IH_sitems_nil
      | i :: items => IH_sitems_cons i items (sitem_ind i) (sitems_ind items)
      end in
    match me with
    | MUnsupported => IH_MUnsupported
    | MPath π => IH_MPath π
    | MStruct items => IH_MStruct items (sitems_ind items)
    | MFunctor x items => IH_MFunctor x items (sitems_ind items)
    | MCoercion me c => IH_MCoercion me c (mexpr_ind me)
    end

  with sitem_ind i : Psitem i :=
    let bindings_ind := fix bindings_ind bs : Pbindings bs :=
      match bs with
      | [] => IH_bindings_nil
      | b :: bs => IH_bindings_cons b bs (binding_ind b) (bindings_ind bs)
      end in
    let rec_bindings_ind := fix rec_bindings_ind rbs : Prec_bindings rbs :=
      match rbs with
      | [] => IH_rec_bindings_nil
      | rb :: rbs =>
          IH_rec_bindings_cons rb rbs (rec_binding_ind rb) (rec_bindings_ind rbs)
      end in
    match i with
    | ILet bs => IH_ILet bs (bindings_ind bs)
    | ILetRec rbs => IH_ILetRec rbs (rec_bindings_ind rbs)
    | IModule m me => IH_IModule m me (mexpr_ind me)
    | IOpen me => IH_IOpen me (mexpr_ind me)
    | IInclude me => IH_IInclude me (mexpr_ind me)
    | IExternal x e => IH_IExternal x e (expr_ind e)
    | IExtend cs => IH_IExtend cs
    end
  .

  (* The list traversals, as principles in their own right. A proof that
     needs one of them separately can use these rather than re-run the
     induction. *)

  Fixpoint exprs_ind es : Pexprs es :=
    match es with
    | [] => IH_exprs_nil
    | e :: es => IH_exprs_cons e es (expr_ind e) (exprs_ind es)
    end.

  Fixpoint fexprs_ind fes : Pfexprs fes :=
    match fes with
    | [] => IH_fexprs_nil
    | fe :: fes => IH_fexprs_cons fe fes (fexpr_ind fe) (fexprs_ind fes)
    end.

  Fixpoint branches_ind bs : Pbranches bs :=
    match bs with
    | [] => IH_branches_nil
    | b :: bs => IH_branches_cons b bs (branch_ind b) (branches_ind bs)
    end.

  Fixpoint bindings_ind bs : Pbindings bs :=
    match bs with
    | [] => IH_bindings_nil
    | b :: bs => IH_bindings_cons b bs (binding_ind b) (bindings_ind bs)
    end.

  Fixpoint rec_bindings_ind rbs : Prec_bindings rbs :=
    match rbs with
    | [] => IH_rec_bindings_nil
    | rb :: rbs =>
        IH_rec_bindings_cons rb rbs (rec_binding_ind rb) (rec_bindings_ind rbs)
    end.

  Fixpoint sitems_ind items : Psitems items :=
    match items with
    | [] => IH_sitems_nil
    | i :: items => IH_sitems_cons i items (sitem_ind i) (sitems_ind items)
    end.

End expr.


(* ------------------------------------------------------------------------ *)


(* [CStruct] holds a list of field coercions, so the generated principle
   offers nothing about its elements: the same nested-list gap once more, on
   the smallest scale. *)

Section coercion.

  Context
    (Pcoercion  : coercion → Prop)
    (Pfcoercions : list fcoercion → Prop)
  .

  Context
    (IH_CIdentity : Pcoercion CIdentity)
    (IH_CStruct : ∀ xcs (IHxcs : Pfcoercions xcs), Pcoercion (CStruct xcs))
    (IH_fcoercions_nil : Pfcoercions [])
    (IH_fcoercions_cons : ∀ x c xcs (IHc : Pcoercion c) (IHxcs : Pfcoercions xcs),
       Pfcoercions ((x, c) :: xcs))
  .

  Fixpoint coercion_ind c : Pcoercion c :=
    let fcoercions_ind :=
      fix fcoercions_ind xcs : Pfcoercions xcs :=
        match xcs with
        | [] => IH_fcoercions_nil
        | (x, c) :: xcs =>
            IH_fcoercions_cons x c xcs (coercion_ind c) (fcoercions_ind xcs)
        end in
    match c with
    | CIdentity => IH_CIdentity
    | CStruct xcs => IH_CStruct xcs (fcoercions_ind xcs)
    end.

End coercion.

(* ------------------------------------------------------------------------ *)


(* The same gap on a smaller scale: three constructors hold a [list val].
   The syntax a value carries is left opaque; a proof that must look inside
   wants [expr_ind] above, applied to that syntax. *)

Section val.

  Context
    (Pval  : val → Prop)
    (Pvals : list val → Prop)
  .

  Context
    (IH_VClo : ∀ η a, Pval (VClo η a))
    (IH_VCloRec : ∀ η rbs f, Pval (VCloRec η rbs f))
    (IH_VString : ∀ s, Pval (VString s))
    (IH_VInt : ∀ i, Pval (VInt i))
    (IH_VFloat : ∀ f, Pval (VFloat f))
    (IH_VTuple : ∀ vs (IHvs : Pvals vs), Pval (VTuple vs))
    (IH_VData : ∀ c vs (IHvs : Pvals vs), Pval (VData c vs))
    (IH_VXData : ∀ l vs (IHvs : Pvals vs), Pval (VXData l vs))
    (IH_VLoc : ∀ l, Pval (VLoc l))
    (IH_VRecord : ∀ l, Pval (VRecord l))
    (IH_VArray : ∀ l, Pval (VArray l))
    (IH_VInline : ∀ c l, Pval (VInline c l))
    (IH_VCont : ∀ k, Pval (VCont k))
    (IH_VThread : ∀ t, Pval (VThread t))
    (IH_VStruct : ∀ xvs, Pval (VStruct xvs))
    (IH_VFunctor : ∀ η x xvs, Pval (VFunctor η x xvs))
    (IH_VChar : ∀ c, Pval (VChar c))
    (IH_vals_nil : Pvals [])
    (IH_vals_cons : ∀ v vs (IHv : Pval v) (IHvs : Pvals vs), Pvals (v :: vs))
  .

  Fixpoint val_ind v : Pval v :=
    let vals_ind :=
      fix vals_ind vs : Pvals vs :=
        match vs with
        | [] => IH_vals_nil
        | v :: vs => IH_vals_cons v vs (val_ind v) (vals_ind vs)
        end in
    match v with
    | VClo η a => IH_VClo η a
    | VCloRec η rbs f => IH_VCloRec η rbs f
    | VString s => IH_VString s
    | VInt i => IH_VInt i
    | VFloat f => IH_VFloat f
    | VTuple vs => IH_VTuple vs (vals_ind vs)
    | VData c vs => IH_VData c vs (vals_ind vs)
    | VXData l vs => IH_VXData l vs (vals_ind vs)
    | VLoc l => IH_VLoc l
    | VRecord l => IH_VRecord l
    | VArray l => IH_VArray l
    | VInline c l => IH_VInline c l
    | VCont k => IH_VCont k
    | VThread t => IH_VThread t
    | VStruct xvs => IH_VStruct xvs
    | VFunctor η x xvs => IH_VFunctor η x xvs
    | VChar c => IH_VChar c
    end.

  Fixpoint vals_ind vs : Pvals vs :=
    match vs with
    | [] => IH_vals_nil
    | v :: vs => IH_vals_cons v vs (val_ind v) (vals_ind vs)
    end.

End val.
