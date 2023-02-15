Require Import lang.
Require Import free.

(* Conventional metavariables. *)

Implicit Type f x : var.
Implicit Type c : data.
Implicit Type p : pat.
Implicit Type ps : pats.
Implicit Type e : expr.
Implicit Type es : exprs.
Implicit Type b : branch.
Implicit Type bs : branches.
Implicit Type v : val.
Implicit Type vs : vals.
Implicit Type η : env.

(* ------------------------------------------------------------------------ *)

(* [lookup η x] looks up the variable [x] in the environment [env].
   The result is normally a value. A hard failure occurs if [x] is
   unbound. *)

Fixpoint lookup η x : mon val :=
  match η with
  | EnvCons x' v η =>
      if decide (x = x') then Ret v else lookup η x
  | EnvNil =>
      Fail
  end.

(* ------------------------------------------------------------------------ *)

(* [extend η p v] matches the value [v] against the pattern [p].

   In case of success, the result is an extension of the environment
   [η] with bindings for the bound variables of the pattern [p].

   A soft failure takes place if [p] does not match [v], e.g., if [p]
   selects a data constructor [c] but [v] carries a distinct data
   constructor [c'].

   A hard failure takes place if [p] and [v] have incompatible types,
   e.g., if [p] is a tuple pattern and [v] is not a tuple value or
   is a tuple value of an incorrect arity. *)

Fixpoint extend η p v : mon env :=
  match p, v with
  | PAny, _ =>
      (* A wildcard pattern always succeeds. *)
      Ret η
  | PVar x, _ =>
      (* A variable pattern always succeeds, and causes the environment
         to be extended. *)
      Ret (EnvCons x v η)
  | PTuple ps, VTuple vs =>
      (* A tuple pattern matches a tuple value. *)
      (* A hard failure occurs when [length ps ≠ length vs]. *)
      extends η ps vs
  | PData c p, VData c' v =>
      (* A data pattern matches a data value, provided the data constructors
         match. If the data constructors do not match, a soft failure takes
         place. *)
      if decide (c = c') then extend η p v else Next
  | PTuple _, _
  | PData _ _, _ =>
      (* A type mismatch between pattern and value causes a hard failure. *)
      Fail
  end

(* [extends η ps vs] matches the values [vs] against the patterns [ps].

   In case of success, the result is an extension of the environment
   [η] with bindings for the bound variables of the patterns [ps].

   A hard failure occurs when [length ps ≠ length vs]. *)

with extends η ps vs : mon env :=
  match ps, vs with
  | PNil, VNil =>
      Ret η
  | PCons p ps, VCons v vs =>
      bind (extend η p v) $ λ η,
      bind (extends η ps vs) $ λ η,
      Ret η
  | _, _ =>
      Fail
  end.

(* ------------------------------------------------------------------------ *)

(* [eval η e] evaluates the expression [e] in environment [η].

   In case of success, the result is a value.

   A hard failure reflects a dynamic type error (a crash).

   A soft failure is impossible.

   No substitutions are involved; this is an environment-based semantics.

   [eval] is inductively defined. In some cases, it invokes itself
   recursively on a subexpression of [e]. When an expression must be
   evaluated but is not a subexpression of [e], a [Stop] effect is
   used instead of a recursive call to [eval]. *)

Fixpoint eval η e : mon val :=
  match e with
  | EVar x =>
      (* A variable [x] is looked up in the environment [η]. *)
      lookup η x
  | ERec f x e =>
      (* The creation of a closure captures the environment [η]. *)
      Ret (VRec η f x e)
  | EApp e1 e2 =>
      (* The left-hand side of an application must evaluate
         to a closure. *)
      bind (eval η e1) $ λ v1,
      bind (eval η e2) $ λ v2,
      match v1 with
      | VRec η f x e =>
          (* The environment of the closure is extended with bindings
             for the variables [f] and [x]. *)
          let η := EnvCons f v1 η in
          let η := EnvCons x v2 η in
          (* In this extended environment, the function body [e] must
             be evaluated. A recursive call to [eval] cannot be used,
             so we request the evaluation of [e] via a [Stop] effect. *)
          Stop (REval η e) $ λ v,
          Ret v
     | _ =>
         Fail
     end
  | ETuple es =>
      bind (evals η es) $ λ vs,
      Ret (VTuple vs)
  | EData c e =>
      bind (eval η e) $ λ v,
      Ret (VData c v)
  | EMatch e bs =>
      bind (eval η e) $ λ v,
      eval_match η v bs
  end

(* [evals η es] evaluates the expressions in the list [es], from left
   to right, producing a list of values [vs]. *)

with evals η es : mon vals :=
  match es with
  | ENil =>
      Ret VNil
  | ECons e es =>
      bind (eval η e) $ λ v,
      bind (evals η es) $ λ vs,
      Ret (VCons v vs)
  end

(* [eval_match η v bs] evaluates [match v with bs] in the environment [η]. *)

with eval_match η v bs :=
  match bs with
  | BNil =>
      (* A nonexhaustive [match] construct causes a hard failure. *)
      Fail
  | BCons (Branch p e) bs =>
      (* Match the value [v] against the pattern [p]. *)
      try
        (extend η p v)
      (* Success: commit to this branch. Evaluate its body. *)
      (λ η, eval η e)
      (* Soft failure: abandon this branch. Try the following branches. *)
      (λ tt, eval_match η v bs)
  end.

(* A reduction semantics on top of the above evaluator. *)

(* The divergence monad. *)

CoInductive div A :=
  | CRet (a : A)
  | CFail
  | CSkip (m : div A).

Arguments CRet {A} a.
Arguments CFail {A}.
Arguments CSkip {A} m.

CoInductive ceq {A} : div A → div A → Prop :=
| CEqCRet a :
    ceq (CRet a) (CRet a)
| CEqCFail :
    ceq CFail CFail
| CEqCSkip m1 m2 :
    ceq m1 m2 →
    ceq (CSkip m1) (CSkip m2)
.

CoFixpoint dbind {A B} (m : div A) (f : A → div B) : div B :=
  match m with
  | CRet a =>
      f a
  | CFail =>
      CFail
  | CSkip m =>
      CSkip (dbind m f)
  end.

CoFixpoint handle {A} (m : mon A) : div A :=
  match m with
  | Ret a =>
      CRet a
  | Fail =>
      CFail
  | Next =>
      (* This must not happen. *)
      CFail
  | Stop req k =>
      match req with
      | REval η e =>
          CSkip (handle (bind (eval η e) k))
      end
  end.

Definition execute η e : div val :=
  handle (eval η e).

Lemma compatibility {B} m {k : val → mon B} :
  handle (bind m k) =
  dbind (handle m) (λ v, handle (k v)).
Proof.
Admitted.

(* The wp monad. *)

Definition wpm A :=
  (A → Prop) → Prop.

Definition wret {A} : A → wpm A :=
  λ (a : A) (φ : A → Prop),
    φ a.

Definition wfail {A} : wpm A :=
  λ (φ : A → Prop),
    False.

Definition wbind {A B} (m : wpm A) (f : A → wpm B) : wpm B :=
  λ (φ : B → Prop),
    m (λ a, f a φ).

Definition whandle {A} (self : mon A → wpm A) (m : mon A) : wpm A :=
  match m with
  | Ret a =>
      wret a
  | Fail =>
      wfail
  | Next =>
      (* This must not happen. *)
      wfail
  | Stop req k =>
      match req with
      | REval η e =>
          self (bind (eval η e) k)
      end
  end.

Lemma whandle_monotonic {A} (self1 self2 : mon A → wpm A) m φ :
  (∀ m φ, self1 m φ → self2 m φ) →
  whandle self1 m φ →
  whandle self2 m φ.
Proof.
  intros H.
  destruct m; simpl whandle; eauto.
  destruct req. eauto.
Qed.

(* We want the greatest fixed point of [whandle]. *)

(* TODO not accepted:
CoInductive wp {A} (m : mon A) : wpm A :=
| WpStep :
    ∀ φ,
    whandle wp m φ →
    wp m φ.
 *)

Definition wp {A} (m : mon A) : wpm A :=
  λ (φ : A → Prop),
    ∃ wp : mon A → wpm A,
      wp m φ ∧ (∀ m φ, wp m φ → whandle wp m φ).

Lemma deconstruction {A} (m : mon A) φ :
  wp m φ →
  whandle wp m φ.
Proof.
  intros (witness & Hwitness & Hprop).
  eapply whandle_monotonic; [| eauto ].
  unfold wp; eauto.
Qed.

Lemma construction {A} (m : mon A) φ :
  whandle wp m φ →
  wp m φ.
Proof.
  intros H.
  eexists. split; [ eauto |].
  clear m H φ.
  intros m φ H.
  eauto using whandle_monotonic, deconstruction.
Qed.

Lemma fixed_point {A} (m : mon A) φ :
  wp m φ ↔ whandle wp m φ.
Proof.
  split; eauto using construction, deconstruction.
Qed.

Opaque wp.

(* An example. *)

Definition ELet p e1 e2 :=
  EMatch e1 (BCons (Branch p e2) BNil).

Definition EUnit :=
  ETuple ENil.

Definition EConstant c :=
  EData c EUnit.

Definition EPair e1 e2 :=
  ETuple (ECons e1 (ECons e2 ENil)).

Definition PPair p1 p2 :=
  PTuple (PCons p1 (PCons p2 PNil)).

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  ELet (PVar "x") (EPair (EConstant "A") (EConstant "B")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Eval cbv in eval EnvNil example.

(* An example of reasoning about straight-line code. *)

Goal wp (eval EnvNil example) (λ v, v = VData "A" (VTuple VNil)).
Proof.
  cbv. rewrite fixed_point. cbv. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  ELet (PVar "x") (EPair (EVar "z1") (EVar "z2")) $
  ELet (PPair (PVar "x1") (PVar "x2")) (EVar "x") $
  EVar "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  wp (eval env example2) (λ v, v = v1).
Proof.
  intros. cbv. rewrite fixed_point. cbv. reflexivity.
Qed.
