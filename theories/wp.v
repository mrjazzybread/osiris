Require Import lang free eval.

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
