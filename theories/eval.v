Require Import lang.

Implicit Type f x : var.
Implicit Type c : tag.
Implicit Type p : pat.
Implicit Type ps : pats.
Implicit Type e : expr.
Implicit Type es : exprs.
Implicit Type b : branch.
Implicit Type bs : branches.
Implicit Type v : val.
Implicit Type vs : vals.
Implicit Type η : env.

(* A free monad in which the evaluator will be expressed. *)

Inductive request :=
  | REval η e.

Implicit Type req : request.

Inductive mon A :=
  | Ret (a : A)
  | Fail (* hard failure *)
  | Next (* soft failure: please try the next branch in a [match] construct *)
  | Stop req (k : val → mon A).

Arguments Ret {A}.
Arguments Fail {A}.
Arguments Next {A}.
Arguments Stop {A} req k.

(* TODO if call-by-value evaluation is used
   then [g] should have type [unit → mon B]
   to avoid evaluating all branches in a [match] construct *)

Fixpoint try {A B : Type} (m : mon A) (f : A → mon B) (g : mon B) : mon B :=
  match m with
  | Ret a =>
      f a
  | Fail =>
      Fail
  | Next =>
      g
  | Stop req k =>
      Stop req (λ v, try (k v) f g)
  end.

Definition bind {A B : Type} (m : mon A) (f : A → mon B) : mon B :=
  try m f Next.

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

Lemma eq_reflexive {A} (m : mon A) :
  eq m m.
Proof.
  induction m; constructor; eauto.
Qed.

Lemma mon_law1 {A B : Type} (a : A) (f : A → mon B) :
  bind (Ret a) f = f a.
Proof.
  reflexivity.
Qed.

Lemma mon_law2 {A B : Type} (m : mon A) :
  eq
    (bind m Ret)
    m.
Proof.
  unfold bind. induction m; simpl try; constructor; eauto.
Qed.

Lemma mon_law3 {A B C} (m : mon A) (g : A → mon B) (h : B → mon C) :
  eq
    (bind (bind m g) h)
    (bind m (λ a, bind (g a) h)).
Proof.
  unfold bind.
  induction m; simpl.
  { apply eq_reflexive. }
  { constructor. }
  { constructor. }
  { constructor. eauto. }
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
  | PTup ps, VTup vs =>
      extends η ps vs
        (* This causes a hard failure when [length ps ≠ length vs]. *)
  | PTup _, _ =>
      Fail
  | PInj c p, VInj c' v =>
      if decide (c = c') then extend η p v else Next (* soft failure *)
  | PInj _ _, _ =>
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
  | Var x =>
      lookup η x
  | Rec f x e =>
      Ret (VRec η f x e)
  | App e1 e2 =>
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
  | Tup es =>
      bind (evals η es) $ λ vs,
      Ret (VTup vs)
  | Inj c e =>
      bind (eval η e) $ λ v,
      Ret (VInj c v)
  | Match e bs =>
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
        (eval_branches η v bs)
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

Definition Let p e1 e2 :=
  Match e1 (BCons (Branch p e2) BNil).

Definition Unit :=
  Tup ENil.

Definition Constant c :=
  Inj c Unit.

Definition Pair e1 e2 :=
  Tup (ECons e1 (ECons e2 ENil)).

Definition PPair p1 p2 :=
  PTup (PCons p1 (PCons p2 PNil)).

(* let x = (A (), B ()) in let (x1, x2) = x in x1 *)

Definition example :=
  Let (PVar "x") (Pair (Constant "A") (Constant "B")) $
  Let (PPair (PVar "x1") (PVar "x2")) (Var "x") $
  Var "x1".

Eval cbv in eval EnvNil example.

(* An example of reasoning about straight-line code. *)

Goal wp (eval EnvNil example) (λ v, v = VInj "A" (VTup VNil)).
Proof.
  cbv. rewrite fixed_point. cbv. reflexivity.
Qed.

(* let x = (z1, z2) in let (x1, x2) = x in x1 *)

Definition example2 :=
  Let (PVar "x") (Pair (Var "z1") (Var "z2")) $
  Let (PPair (PVar "x1") (PVar "x2")) (Var "x") $
  Var "x1".

Goal
  ∀ v1 v2,
  let env := EnvCons "z1" v1 (EnvCons "z2" v2 EnvNil) in
  wp (eval env example2) (λ v, v = v1).
Proof.
  intros. cbv. rewrite fixed_point. cbv. reflexivity.
Qed.
