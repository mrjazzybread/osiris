Require Import lang.
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

(* A free monad in which the evaluator is expressed. *)

(* The effects allowed by this free monad are:

   - [Fail], a hard failure, which represents a crash and must be avoided;
   - [Next], a soft failure, which represents a request to jump to the next
             branch in a [match] construct;
   - [Stop], an effect whose signature is [request → val];
             this effect can be viewed of consulting an oracle,
             which answers a request with a value.

   The definition of the type [mon A] is inductive:
   every computation must terminate.

   The requests allowed by this monad are:

   - [REval η e], a request to evaluate the expression [e]
                  under the environment [η]. *)

Inductive request :=
  | REval (η : env) (e : expr).

Inductive mon A :=
  | Ret (a : A)
  | Fail
  | Next
  | Stop (req : request) (k : val → mon A).

(* Make [A] an implicit argument. *)

Arguments Ret {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} req k.

(* ------------------------------------------------------------------------ *)

(* Monadic combinators. *)

(* [try m f g] runs the computation [m]. If [m] returns a result [v], then
   [f v] is executed. If [m] ends with a soft failure [Next], then [g()] is
   executed. *)

(* [g] must have type [unit → mon B], as opposed to just [mon B], because
   we execute monadic computations (in Coq) using call-by-value evaluation
   and we do not want to evaluate ALL branches in a [match] construct. *)

Fixpoint try {A B} (m : mon A) (f : A → mon B) (g : unit → mon B) : mon B :=
  match m with
  | Ret a =>
      f a
  | Fail =>
      (* A hard failure is transmitted. *)
      Fail
  | Next =>
      g()
  | Stop req k =>
      (* An effect is transmitted. The combinator [try _ f g] remains
         installed on top of the continuation. *)
      Stop req (λ v, try (k v) f g)
  end.

(* [bind m f] sequences the computations [m] and [f]. *)

(* [bind] is a special case of [try]. If [m] ends with a soft failure,
   it is transmitted. *)

Definition bind {A B} (m : mon A) (f : A → mon B) : mon B :=
  try m f (λ tt, Next).

(* ------------------------------------------------------------------------ *)

(* Equality of monadic computations. *)

(* This equality is needed to state some of the monad laws. That said, it
   may be the case that we actually do not need these laws. *)

(* This equality is just equality of trees whose internal nodes are the
   [Stop] nodes and whose leaves are [Ret], [Fail] and [Next]. *)

(* If the axiom of functional extensionality is accepted, then [eq]
   coincides with Coq's ordinary notion of equality. *)

Inductive eq {A} : mon A → mon A → Prop :=
| EqRet a :
    eq (Ret a) (Ret a)
| EqFail :
    eq Fail Fail
| EqNext :
    eq Next Next
| EqStop req k1 k2 :
    (∀ v, eq (k1 v) (k2 v)) →
    eq (Stop req k1) (Stop req k2)
.

Local Hint Constructors eq : eq.

Infix "~" := eq (at level 70, no associativity).

(* Equality is reflexive and transitive. *)

Lemma eq_reflexive {A} (m : mon A) :
  m ~ m.
Proof.
  induction m; constructor; eauto.
Qed.

Lemma eq_transitive {A} (m1 m2 : mon A) :
  m1 ~ m2 → ∀ m3, m2 ~ m3 → m1 ~ m3.
Proof.
  induction 1; inversion 1; subst; constructor; eauto.
Qed.

Local Hint Resolve eq_reflexive : eq.

(* The monadic laws. *)

Lemma monad_law_left_unit {A B} (a : A) (f : A → mon B) :
  bind (Ret a) f ~ f a.
Proof.
  apply eq_reflexive.
Qed.

Lemma monad_law_right_unit {A} (m : mon A) :
  bind m Ret ~ m.
Proof.
  unfold bind. induction m; simpl try; constructor; eauto.
Qed.

Lemma monad_law_associativity
  {A B C} (m : mon A) (g : A → mon B) (h : B → mon C) :
  bind (bind m g) h ~
  bind m (λ a, bind (g a) h).
Proof.
  unfold bind. induction m; simpl; eauto with eq.
Qed.

(* Evaluation. *)

Fixpoint lookup η x : mon val :=
  match η with
  | EnvCons x' v η =>
      if decide (x = x') then Ret v else lookup η x
  | EnvNil =>
      Fail
  end.

Fixpoint extend η p v : mon env :=
  match p, v with
  | PAny, _ =>
      Ret η
  | PVar x, _ =>
      Ret (EnvCons x v η)
  | PTuple ps, VTuple vs =>
      extends η ps vs
        (* This causes a hard failure when [length ps ≠ length vs]. *)
  | PTuple _, _ =>
      Fail
  | PData c p, VData c' v =>
      if decide (c = c') then extend η p v else Next (* soft failure *)
  | PData _ _, _ =>
      Fail
  end

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

Fixpoint eval η e : mon val :=
  match e with
  | EVar x =>
      lookup η x
  | ERec f x e =>
      Ret (VRec η f x e)
  | EApp e1 e2 =>
      bind (eval η e1) $ λ v1,
      bind (eval η e2) $ λ v2,
      match v1 with
      | VRec η f x e =>
          let η := EnvNil in
          let η := EnvCons f v1 η in
          let η := EnvCons x v2 η in
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
      eval_branches η v bs
  end

with evals η es : mon vals :=
  match es with
  | ENil =>
      Ret VNil
  | ECons e es =>
      bind (eval η e) $ λ v,
      bind (evals η es) $ λ vs,
      Ret (VCons v vs)
  end

with eval_branches η v bs :=
  match bs with
  | BNil =>
      Fail
  | BCons (Branch p e) bs =>
      (* Match the value [v] against the pattern [p]. *)
      try (extend η p v)
        (* Success: commit to this branch. Evaluate its body. *)
        (λ η, eval η e)
        (* Soft failure: abandon this branch. Try the following branches. *)
        (λ tt, eval_branches η v bs)
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
