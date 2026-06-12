From osiris Require Import base.
From osiris.olang Require Import lang semantics.
Require Import pure_rules.
Require Import toplevel_rules.
Require Import fun_spec.

(** This file is to be used as motivation for the [Spec] predicate.
    As an example, we define [Spec'] as a way to specify unary functions.

    For the actual treatment of function specifications, see [fun_spec.v] *)

(* -------------------------------------------------------------------------- *)

(* [call_spec] is the type of specifications over function calls. It
   depends on two arguments: the argument of the function call, and the
   computation resulting from calling the function on that argument. *)

Local Definition call_spec' {X : Type} := X -> microvx -> Prop.

(* [Spec' c P] states that given a closure [c], the specification [P]
   holds for any call of [c] on an argument. *)

Local Definition Spec' `{Encode X} (c : val) (P : call_spec') :=
  ∀ (x : X), P x (call c #x).

(* -------------------------------------------------------------------------- *)

(* Consider for example the specification of a function [sort]:
   [ Spec' sort (λ l m, pure m (λ l', Sorted l' ∧ l' ≡ l) ⊥) ] *)

(* Example of a reasoning rule, for the creation of a [Spec' c P]. *)

Local Lemma pure_eval_anon' `{Encode X} `{Encode C} (P : call_spec') η (xvar : var) e (ζ : C → Prop) :
  (∀ (x : X),
      P x (please_eval ((xvar, #x) :: η) e)) ->
  pure (eval η (EAnonFun (AnonFun xvar e))) (λ c, Spec' c P) ζ.
Proof. by intros; simpl_eval; eapply pure_ret. Qed.


(* [pure_call_spec'] illustrates how we may want to use a [Spec c P]
   specification. *)

Local Lemma pure_call_spec' `{Encode X, Encode Y} `{Encode C} (P : X -> microvx -> Prop) c v (φ : Y -> Prop) (ζ : C → Prop) :
  Spec' c P ->
  (∀ m, P v m -> pure m φ ζ) ->
  pure (eval.E.call c #v) φ ζ.
Proof.
  intros HSpec Hmon.
  apply Hmon. apply HSpec.
Qed.

(* -------------------------------------------------------------------------- *)

(* [pure_eval_letrec'] allows us to prove that the body [e] of a letrec
   expression satisfies a specification given by [P].

   In a first subgoal, we prove that any function call satisfies [P],
   under the assumption that calls to smaller arguments (according to
   [R]) are well-behaved.
   In the second subgoal, we prove [e2] while abstracting over [e]. *)

Local Lemma pure_eval_letrec' `{Encode X, Encode Y} `{Encode C}
  (P : call_spec') (R : X -> X -> Prop) η f (x : var) e
  e2 (φ : Y -> Prop) (ζ : C → Prop) :
  (* Show that the relation on which arguments are decreasing is well-founded. *)
  well_founded R ->
  (* Show the specification [P] holds over a call to any argument
     [arg], under the assumption that [P] holds to a call over any
     argument [yval] smaller than [arg]. *)
  (∀ c (arg : X),
      Spec' c (λ yval m, R yval arg -> P yval m) ->
      P arg (please_eval ((x, #arg) :: (f, c) :: η) e)) ->
  (* Continue with [f] bound to [c], and [c] specified by [P]. *)
  (∀ c, Spec' c P -> pure (eval ((f, c) :: η) e2) φ ζ) ->
  (* When facing an expression of the form [let rec f x = e in e2]. *)
  pure (eval η (ELetRec [RecBinding f (AnonFun x e)] e2)) φ ζ.
Proof.
  intros Hwf Hmkspec He2. simpl_eval. eapply He2.
  unfold Spec'. intros v.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  simpl; rewrite String.eqb_refl; simpl.
  eapply Hmkspec. intros y. intros HR. by apply IH.
Qed.

(* [structs_letrec'] mirrors [pure_eval_letrec'],
   dealing with top-level let-recs [ILetRec] instead of
   inline let-recs [ELetRec]. *)

Local Lemma structs_letrec' `{Encode X} (R : X -> X -> Prop) η δ f (x : var) e
  (P : X -> microvx -> Prop)
  sitems φ :
  well_founded R ->
  (∀ c v',
      Spec' c (λ v m, R v v' -> P v m) ->
      P v' (please_eval ((x, #v') :: (f, c) :: η) e)) ->
  (∀ c, Spec' c P ->
       struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
  struct_items (η, δ) (ILetRec [RecBinding f (AnonFun x e)] :: sitems) φ.
Proof.
  intros Hwf Hmkspec He2.
  unfold struct_items; simpl_eval_sitems.
  eapply He2. intros v.
  induction v as [v IH] using (well_founded_induction Hwf); intros.
  simpl; rewrite String.eqb_refl; simpl.
  by eapply Hmkspec.
Qed.
