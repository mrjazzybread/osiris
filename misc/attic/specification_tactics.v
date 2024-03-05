From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_splay.

(* -------------------------------------------------------------------------- *)
(* Specification structures. *)

(* Given a name which corresponds to the declaration, there is some pspec *)
Class decl_spec (name : var) := { Decl_spec : pspec }.

(* Smart constructor *)
Definition val_spec (name : var) `{decl_spec name} (v : val) : Prop :=
  @Decl_spec name _ v.

(* Lifting specification over declaration to a specification over an environment:
    i.e. the declaration can be found the environment and satisfies the
    specification. *)
Definition spec (name : var) `{decl_spec name} (η : env) : Prop :=
  let val_spec := @Decl_spec name _ in
  pure (lookup_name η name) val_spec.

(* -------------------------------------------------------------------------- *)
(* Specification of [splay]. *)

(* Names for the functions we would like to specify *)
Definition SPLAY := "splay".
Definition SPLAY_LEAF := "splay_leaf".
Definition ZLOOKUP := "zlookup".

(* Specification for each function *)
Definition splay_spec :=
  fun splay =>
    ∀ A `(_ : Encode A) (ctx : zipper A) (l : tree A) (x : A) (r : tree A),
    pure
      (call splay #(l, x, r, ctx))
      (λ t', fringe t' = fringe (fill ctx (Node l x r))).

Definition splay_leaf_spec :=
  fun (splay_leaf : val) =>
    ∀ A `(_ : Encode A) (ctx : zipper A),
    pure
      (call splay_leaf #ctx)
      (λ t', fringe t' = fringe (fill ctx Leaf)).

Definition zlookup_spec :=
  fun (zlookup : val) =>
    ∀ A `(_ : Encode A) (le : A → A → Prop) `(_ : PreOrder _ le),
      compare_spec Stdlib__compare le →
      ∀ (t : tree A) (x : A) (ctx : zipper A),
      bst (strict le) t →
      pure
        (call zlookup #(t, x, ctx))
        (λ '(oy, t'),
          member le x (fringe t) oy ∧
          fringe t' = fringe (fill ctx t)).

#[local] Instance splay_decl_spec : decl_spec SPLAY :=
  {| Decl_spec := splay_spec |}.

#[local] Instance splay_leaf_decl_spec : decl_spec SPLAY_LEAF :=
  {| Decl_spec := splay_leaf_spec |}.

#[local] Instance zlookup_decl_spec : decl_spec ZLOOKUP :=
  {| Decl_spec := zlookup_spec |}.

(* -------------------------------------------------------------------------- *)

(* Top-level environment of [splay]. *)

Definition stdlib_env := ("Stdlib", Stdlib) :: Stdlib_env.

(* Ltac programming to compute the environment from [mexpr]'s. *)

(* Instantiates an evar and tries to apply the aggressive [simp_really] resolution
   spitting out a [micro] monad if it succeeds. *)
Ltac try_reduce_with_simp A E m :=
  let e := fresh "e" in
  let H := fresh "H" in
  evar (e : micro A E);
  assert (H:simp m ?e) by simp_really;
  clear H;
  exact e.

(* Given a module definition that has been evaluated, return the environment that
 is built from the evaluated module. *)
Ltac extract_env module_def :=
  let m := fresh "m" in
  let l := fresh "l" in
  pose module_def as m;
  unfold module_def in m;
  match goal with
  | m := ret (VStruct ?x) |- _ => pose x as l
  end; clear m; cbn in *; exact l.

(* We can extract the environment programmatically. *)
Definition splay_module_env' :=
  (ltac:(with_strategy transparent [eval_bindings eval_mexpr extend] try_reduce_with_simp val void (eval_mexpr stdlib_env __main))).
(* A more sane approach would be to state some well-formedness conditions *)

(* Extracted environment *)
Definition splay_module_env : env :=
  ltac:(extract_env splay_module_env').

(* -------------------------------------------------------------------------- *)

(* Util functions for specs *)
Ltac start_proof := unfold spec; cbn; pure1; red.

(* If a specification holds for an environment, we know that there exists some
   declaration in the environment that satisfies the specification. *)
(* TODO fp: It seems to me that this lemma goes too far.
        It essentially expands away the judgement
        [pure (lookup_name η name) val_spec]
        but we should we able to exploit this judgement
        without expanding it. *)
Lemma invert_spec :
  forall x `{decl_spec x} env,
    spec x env ->
    ∃ v, lookup_name env x = ret v /\ val_spec x v.
Proof.
  intros x Spec env; revert x Spec.
  induction env.
  intros * Hspec. red in Hspec; cbn in Hspec.
  - unfold lookup_name in Hspec.
    destruct Hspec as (?&Hspec&?).
    with_strategy transparent [missing_variable_or_field]
      unfold missing_variable_or_field in Hspec.
    clarify_simp.
  - intros * Hspec. red in Hspec.
    unfold lookup_name in *. destruct a.
    destruct (x =? v)%string.
    + destruct Hspec as (?&?&Hspec). clarify_simp.
      eexists; split; eauto.
    + fold lookup_name in *. eapply IHenv; eauto.
Qed.

(* Apply the specification of a function *)
Ltac apply_spec SPEC :=
  let H := fresh "H" in
  let vspec := fresh "vspec" in
  let Hlu := fresh "Hlu" in
  pose proof (invert_spec _ _ SPEC) as H;
  destruct H as (?&Hlu&vspec);
  inversion Hlu; subst;
  try solve [eapply vspec];
  try (eapply pure_consequence ; first eapply vspec).
