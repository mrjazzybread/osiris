From iris.proofmode Require Import proofmode.

From osiris Require Import osiris lang.

From osiris.examples Require Import og_fact_rec.

Open Scope nat_scope.

Context `{!osirisGS Σ}.

(** * General utility functions *)

(* Thread through a default value for the [None] case. *)
Definition option_default {A} (default : A) : option A -> A :=
  fun x => match x with | Some x => x | None => default end.

(** * Osiris utility functions *)

(* Checks whether the item [sitem] is a let declaration of the [name]. *)
Definition match_let_binding (name : string) (s : sitem) :=
  match s with
  | ILet (Binding (PVar x) _ :: _)
  | ILetRec (RecBinding x _ :: _) =>
      String.eqb x name
  | _ => false
  end.

(* Look up the let declaration of [name] within the expression [m] *)
Definition lookup_let (m : mexpr) (name : string) :=
  match m with
  | MStruct items =>
      List.find (match_let_binding name) items
  | _ => None
  end.

(* A variant of [lookup_let] where the default value a dummy let value is returned
  if not found. *)
Definition lookup_let_d (m : mexpr) (name : string) :=
  let res := lookup_let m name in
  option_default (ILet nil) res.

(* Evaluate a single [sitem] under a context *)
Definition eval η s := (eval_mexpr η (MStruct [s])).

(* Since a module expression returns a [VStruct], we need to lift a specification
  over a specific let-binding specifications over the whole module expression
  postcondition. *)

(* Lifting a specification over a specific let binding identified by [name]
    to a specification over [mexprs] *)
Definition let_spec (module_val : val) (name : var) (spec : val -> iProp Σ)
  : iProp Σ :=
  (* Find the let binding in the module value;
      If not found, the postcondition does not hold.
      If found, assert the specification. *)
  let _let_spec l :=
    (match List.find (fun '(x, _) => String.eqb x name) l with
      | Some (_, v) => spec v
      | None => False
      end)%I
  in
  (* The module value must be a [VStruct]. *)
  match module_val with | VStruct l => _let_spec l | _ => False end.

(** *Factorial specification and proof *)

(* --------------------------------------------------------------------- *)
(* First, let's specify the pure recursive implementation of factorial. *)

(* Set up for the [fact_rec_5] : a lookup in the [main] module *)
Definition fact_rec_5 :=
  let fact_rec := lookup_let_d __main "fact_rec" in
  let f := lookup_let_d __main "fact_rec_5" in
  (* The function does not depend on any prior function definitions *)
  eval_mexpr nil (MStruct [fact_rec; f]).

(* A simple specification of [fact_rec] :
    That [fact_rec 5] is equivalent to 120. *)
Definition fact_rec_5_spec (v : val) : iProp Σ :=
  let _spec v := (⌜v = # 120⌝)%I in
  let_spec v "fact_rec_5" _spec.

Local Ltac simpl_fact :=
  repeat (wp;
  rewrite ?sub_repr_repr;
  match goal with
    | |- context [if ?b then _ else _] =>
      try (assert (b = false) as ->;
      [ rewrite eq_repr_repr ; [ done | representable | representable ] | ]);
      try (assert (b = true) as ->;
      [ rewrite eq_repr_repr ; [ done | representable | representable ] | ])
  end).

Lemma fact_rec_5_correct :
  ⊢ WP fact_rec_5 {{ RET v, fact_rec_5_spec v }}.
Proof.
  (* Proof using the old wp tactics *)
  wp; wp_continue.

  (* Reduce each call to [fact] *)
  simpl_fact.

  wp_bind; wp_continue. (* Kind of feels random when we use [wp], [wp_bind] or
                           [wp_continue] *)

  (* We have reached the postcondition *)
  (* Deal with [ipure] goals somehow *)
  cbn; rewrite /fact_rec_5_spec; iPureIntro.

  (* Reduce down arithmetic expr *)
  match goal with
    | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
  end.
  { rewrite !mul_repr_repr; f_equiv; lia. }

  done.
Qed.

(* --------------------------------------------------------------------- *)
(* Next is the specification of the stateful implementation of factorial. *)

(* Set up for the [fact_5] : a lookup in the [main] module *)
Definition fact_5 :=
  (* Either we would like to:
      (1) get every dependency, in order... (TODO: clean up) or
      (2) generate appropriate subgoals per specification? *)
  eval_mexpr nil __main.

(* A simple specification of [fact] :
    That [fact 5] is equivalent to 120. *)
Definition fact_5_spec (v : val) : iProp Σ :=
  let _spec v := (⌜v = # 120⌝)%I in
  let_spec v "fact_5" _spec.

Lemma fact_5_correct :
  ⊢ WP fact_5 {{ RET v, fact_5_spec v }}.
Proof.
  (* Proof using the old wp tactics *)
  (* TODO: Can we skip proofs for functions that are not relevant? *)
  (* Processing [fact_rec] *)
  wp; wp_continue.

  (* We get to the [fact] *)

  (* Allocate a new variable that stores the dummy function value *)
  wp_alloc factv "[Hfact _]". (* Why do we get a [meta_token] here? *)

  do 2 wp_continue.

  wp_store "Hfact".

  wp_concat; wp.

  (* Reduce each call to [fact_rec] *)
  simpl_fact.

  wp; wp_bind; wp_continue.

  (* Reduce each call to [fact] *)
  repeat (simpl_fact; wp; wp_load "Hfact").

  simpl_fact.

  wp; wp_continue.

  (* Deal with [ipure] goals somehow *)
  cbn; rewrite /fact_rec_5_spec; iPureIntro.

  (* Reduce down arithmetic expr *)
  match goal with
    | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
  end.
  { rewrite !mul_repr_repr; f_equiv. lia. }
  done.
Qed. (* Long QED time for some reason *)
