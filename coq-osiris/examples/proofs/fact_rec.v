From iris.proofmode Require Import proofmode.

From osiris Require Import osiris lang.

From osiris.examples Require Import og_fact_rec.

(* TODO: should we not rely on computation here? *)
Local Transparent eval_mexpr eval_bindings evals extend encode.

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

From osiris.program_logic Require Import ewp protocols protocol_instance.

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

  Opaque prot_bottom.

  Definition fmap {A B E} (f : A -> B) (m : micro A E) : micro B E :=
    bind m (fun x => ret (f x)).

  Definition eq_fmap {A B E} (f : A -> B) (m : micro A E) :
    bind m (fun x => ret (f x)) = fmap f m.
  Proof. done. Qed.

  Lemma eq_bind_bind {A B E E'} m
    (k k' : outcome2 B E' → micro A E) :
    (∀ o, k o = k' o) →
    bind m k = bind m k'.
  Proof.
    intros. f_equal.
    eapply FunctionalExtensionality.functional_extensionality; done.
  Qed.

  (** *Fmap rule *)
  Lemma ewp_fmap {A B X} E (f : A -> B) (m : micro A X) Ψ Φ :
    EWP m @ E <| Ψ |> {{ RET v, Φ (f v) }} -∗
    EWP fmap f m @ E <| Ψ |> {{ RET v, Φ v }}.
  Proof.
    iIntros "Hwp". rewrite -eq_fmap. iApply ewp_bind.
    iApply (ewp_mono with "[$]"). iIntros (?) "H".
    destruct a; last done. cbn.
    iApply ewp_value; by cbn.
  Qed.

  Example fact_rec_5_correct :
    ⊢ EWP fact_rec_5 <| prot_bottom |> {{ RET v, fact_rec_5_spec v }}.
  Proof.
    iStartProof; rewrite /fact_rec_5. simpl.
    Par.
    repeat (simpl_fact; Simp; Try; try Bind).

    simpl_fact; Simp.

    repeat (Ret; cbn).
    iPureIntro.

    match goal with
      | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
    end.
    { rewrite !mul_repr_repr; f_equiv. lia. }
    done.
  Admitted.

  (* Naive :

      Finished transaction in 11.607 secs (11.294u,0.312s) (successful) *)

  (* TODO: Better tactics for [EWP]. *)
  Example fact_rec_5_correct_opt :
    ⊢ EWP fact_rec_5 <| prot_bottom |> {{ RET v, fact_rec_5_spec v }}.
  Proof.
    iStartProof; rewrite /fact_rec_5. simpl.

    (* Normalization 1 : Normalize bind ("head normal form") *)
    setoid_rewrite eq_par_par; cycle 1.
    { intros; rewrite !bind_bind; cbn. reflexivity. }

    (* Normalization 2 : Normalize bind using unit rule and manual rewrite.. *)
    (* setoid_rewrite eq_par_par; cycle 1. *)
    (* { intros; rewrite !bind_bind. *)

      (* destruct o; cbn. *)
      (* { destruct a. rewrite bind_ret. *)
      (*   Unshelve. *)
      (*   2 : exact (fun o => *)
      (*    match o with *)
      (*    | O2Ret (v, e) => *)
      (*       ret (VStruct *)
      (*         (app (cons (pair "fact_rec_5" v) e) *)
      (*            (cons (pair "fact_rec" (VCloRec nil __bindings2 "fact_rec")) nil))) *)
      (*    | O2Throw  e => throw e *)
      (*    end). *)
      (* reflexivity. } *)
      (* reflexivity. } *)

    Par.

    (* Normalization 3 *)
    rewrite try2_join2. cbn. (* [cbn] results in a more efficient term than [Simp]. *)

    (* The exceptional continuation is equivalent to [throw], but only using
      functional extensionality *)
    match goal with
      | |- context[try _ _ ?k] =>
        replace k with (fun e => throw (A := val) (E := exn) e);
        [ | apply FunctionalExtensionality.functional_extensionality;
          reflexivity ]
    end.

    Simp. rewrite eq_fmap. iApply ewp_fmap.

    repeat (
    simpl_fact; Simp;
    rewrite -bind_as_try2 eq_fmap;
    iApply ewp_fmap;
    iApply ewp_bind).

    simpl_fact; Simp.

    repeat (Ret; cbn).
    iPureIntro.

    match goal with
      | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
    end.
    { rewrite !mul_repr_repr; f_equiv. lia. }
    done.
  Time Qed.

  (* With normalization 1:

      Finished transaction in 6.723 secs (6.503u,0.219s) (successful) *)

  (* With normalization 2:

      Finished transaction in 6.498 secs (6.305u,0.192s) (successful) *)

  (* With normalization 2 + 3:

      Finished transaction in 4.443 secs (4.338u,0.105s) (successful)
   *)

  (* With 2 + 3 + FMap :

      Finished transaction in 0.972 secs (0.945u,0.027s) (successful) *)

  (* With 1 + 3 + FMap :

      Finished transaction in 0.94 secs (0.914u,0.025s) (successful) *)

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

  (* TODO: Term explosion is really not great *)
  Example fact_5_correct :
    ⊢ EWP fact_5 <| prot_bottom |> {{ RET v, fact_5_spec v }}.
  Proof.
    iStartProof.
    rewrite /fact_rec_5 /eval_mexpr; cbn.
    Par; cbn.

    (* Allocate a new variable that stores the dummy function value *)
    Alloc factv "Hfact".

    Simp.

    (* We store the value of [fact0] that ties the recursive knot. *)
    Store "Hfact".
    iIntros "Hfactv".

    Simp.

    simpl_fact. Try. Simp. cbn.
    repeat (simpl_fact; Try; Bind; Simp).

    repeat (Ret; cbn).
    Par.

    (* Reduce each call to [fact] *)
    Try. simpl_fact. Simp.
    ewp_tactics.Load "Hfactv". iIntros "Hfactv".

    repeat (
    Try; Bind; cbn; Simp;
    simpl_fact; Simp;
    ewp_tactics.Load "Hfactv"; iIntros "Hfactv").

    Try. Bind. cbn. Simp.
    simpl_fact; Simp.

    repeat (Ret; cbn).

    iPureIntro.
    match goal with
      | |- VInt ?i = VInt (repr ?x) => assert (i = repr x) as ->
    end.
    { rewrite !mul_repr_repr; f_equiv. lia. }
    done.
  Admitted.

End fact_rec_example.

(* Some questions remain:

    To give a complete specification of both of these factorial functions, how
    do we want to give them?

   We could either:
     (1) Give a functional specification via Gallina, showing a correspondence
        between a Gallina specification of [factorial]
           => the reasoning will be pushed down to [pure] for [fact_rec]

     (2) Prove a simulation between [fact_rec] and [fact], ignoring store *)
