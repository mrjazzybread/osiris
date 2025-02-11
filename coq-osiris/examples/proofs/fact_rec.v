From iris.proofmode Require Import proofmode.

From osiris Require Import osiris lang.

From osiris.examples Require Import og_fact_rec.

(* TODO: should we not rely on computation here? *)
Local Transparent eval_mexpr eval_bindings eval_pats eval_pat encode.

Open Scope nat_scope.

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
Definition let_spec {Σ} (module_val : val) (name : var) (spec : val -> iProp Σ)
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

From osiris.program_logic Require Import ewp.

Section fact_rec_example.

  Context `{!osirisGS Σ}.

  (** *Factorial specification and proof *)

  (* --------------------------------------------------------------------- *)
  (* First, let's specify the pure recursive implementation of factorial. *)

  (* Set up for the [fact_rec_5] : a lookup in the [main] module *)
  Definition fact_rec_5 :=
    let fact_rec := lookup_let_d __main "fact_rec" in
    let f := lookup_let_d __main "fact_rec_5" in
    (* The function does not depend on any prior function definitions *)
    eval_mexpr nil (MStruct [fact_rec; f]).

  (* A very simple and incomplete specification of [fact_rec] to test [WP]
      machinery :
      [fact_rec 5] should be equivalent to 120. *)
  Definition fact_rec_5_spec (v : val) : iProp Σ :=
    let _spec v := (⌜v = # 120⌝)%I in
    let_spec v "fact_rec_5" _spec.

  (* At each invocation of a factorial, we compute the if guard condition and
    reduce the expression until arrive at the base case *)
  Local Ltac simpl_fact :=
    repeat (
    rewrite ?sub_repr_repr;
    match goal with
      | |- context [if ?b then _ else _] =>
        try (assert (b = false) as ->;
        [ rewrite eq_repr_repr ; [ done | representable | representable ] | ]);
        try (assert (b = true) as ->;
        [ rewrite eq_repr_repr ; [ done | representable | representable ] | ])
    end).

  Example fact_rec_5_correct :
    ⊢ EWP fact_rec_5 <| ⊥ |> {{ RET v, fact_rec_5_spec v }}.
  Proof.
    iStartProof; rewrite /fact_rec_5. simpl_eval_mexpr.

    repeat (Simp; Bind; simpl_fact).

    Simp. Ret.

    repeat Ret; iPureIntro.

    match goal with
      | |- VInt ?i = #?x => assert (i = repr x) as ->
    end.
    { rewrite !mul_repr_repr; f_equiv. lia. }
    done.
  Qed. (* [Qed] time around ~1 second *)

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

  Example fact_5_correct :
    ⊢ EWP fact_5 <| ⊥ |> {{ RET v, fact_5_spec v }}.
  Proof.
    iStartProof. rewrite /fact_5.
    (simpl; try rewrite -> seal_eq; Simp).

    (* Allocate a new variable that stores the dummy function value *)
    Alloc factv "Hfact"; Simp; Ret.

    (* We store the value of [fact0] that ties the recursive knot. *)
    Store "Hfact"; Simp; Ret. 

    (* Symbolic execution *)
    repeat (simpl_fact; Bind; Simp).
    repeat (Ret; cbn).

    Par. Bind.

    (* Reduce each call to [fact] *)
    simpl_fact. Simp.
    ewp_tactics.Load "Hfact".

    (* More symbolic execution, then loading and reading the information each time *)
    repeat (Simp; simpl_fact; Bind; Simp; Load "Hfact").

    Bind; cbn; Simp;
    simpl_fact; Simp.
    repeat (Ret; cbn).

    iPureIntro.
    match goal with
      | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
    end.
    { rewrite !mul_repr_repr; f_equiv. lia. }
    done.
  Qed.
  (* TODO: Avoid term explosion;

      Finished transaction in 3.829 secs (3.733u,0.095s) (successful) *)

End fact_rec_example.

(* Some questions remain:

    To give a complete specification of both of these factorial functions, how
    do we want to give them?

   We could either:
     (1) Give a functional specification via Gallina, showing a correspondence
        between a Gallina specification of [factorial]
           => the reasoning will be pushed down to [pure] for [fact_rec]

     (2) Prove a simulation between [fact_rec] and [fact], ignoring store *)
