From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.

From osiris.program_logic.pure Require Export pure_rules.

Section total_rules.

(* A reasoning rule for [ret]. *)

(* The subgoal [v = #a] is explicitly isolated so as to make this lemma
   more widely applicable. A subgoal of the form [v = #a], where [a] is
   a Coq metavariable, can be solved by the tactic [encode]. *)

Lemma total_ret `{Encode A} {E} (φ : A → Prop) v a :
  v = #a →
  φ a →
  total (E := E) (ret v) φ.
Proof.
  intros; by eapply pure_ret.
Qed.

(* A reasoning rule for ret that can instantiate the goal when it is an evar *)

Lemma total_ret_eq `{Encode A} {X : Type} (a : A) :
  total (E := X) (ret #a) (λ a', a' = a).
Proof.
  intros; eapply total_ret; eauto.
Qed.

Lemma total_returns `{Encode A} {X : Type}
  (a : val) (k : val -> micro val X) (φ : A -> Prop):
  total (E := X) (k a) φ ->
  returns (λ v : val, total (k v) φ) a.
Proof.
  intros; eauto with pure.
Qed.

(* The consequence rule. *)

Lemma total_mono `{Encode A} {X} m (φ ψ : A → Prop) :
  total m φ →
  (∀ a, φ a → ψ a) →
  total (E := X) m ψ.
Proof.
  intros; by eapply pure_mono.
Qed.

(* A reasoning rule for [try2]. *)

(* The rule is degenerate; [m] is not allowed to reduce to [throw _],
   so the handler [z] is dead and no proof obligation bears on it. *)

Lemma total_try2 A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) h (φ : A → Prop) (ψ : B → Prop)
  :
  total m φ →
  (∀ a, φ a → total (continue h #a) ψ) →
  total (E := Y) (try2 m h) ψ.
Proof.
  intros.
  eapply pure_try2; [ apply H | | ]; eauto with pure; done.
Qed.

(* A reasoning rule for [try]; corollary of [total_try2] *)

Corollary total_try A X Y (_ : Encode A) B (_ : Encode B)
  (m : micro val X) k z (φ : A → Prop) (ψ : B → Prop)
:
  total m φ →
  (∀ a, φ a → total (k #a) ψ) →
  total (E := Y) (try m k z) ψ.
Proof.
  intros; eapply total_try2; eauto.
Qed.

(* A reasoning rule for [bind]. *)

(* This is [@bind val val]. Attempting to apply this lemma to [@bind A B]
   where [A] and [B] are types other than [val] will not work! *)

Lemma total_bind A X (_ : Encode A) B (_ : Encode B)
  m k (φ : A → Prop) (ψ : B → Prop)
:
  total m φ →
  (∀ a, φ a → total (k #a) ψ) →
  total (E := X) (bind m k) ψ.
Proof.
  rewrite bind_as_try. eauto using total_try.
Qed.

Lemma total_bind_unary A X (_ : Encode A) B (_ : Encode B)
  m k (ψ : B → Prop)
:
  total m (λ (a : A), total (k #a) ψ) →
  total (E := X) (bind m k) ψ.
Proof.
  eauto using total_bind.
Qed.

(* A reasoning rule for [Par m1 m2 k z]. *)

(* We cannot give a reasoning rule for [par m1 m2] because its type is
   [micro (val * val)], not [micro val]. However, we can give a rule
   for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

Lemma total_par `{Encode A1, Encode A2} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  total (E := X) m1 φ1 →
  total m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → total (k (#a1, #a2)) φ) →
  total (E := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros; eapply pure_par; by eauto.
Qed.

Lemma total_par' `{Encode A1, Encode A2} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  total (E := X) m1 φ1 →
  total m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → total (continue k (#a1, #a2)) φ) →
  total (E := Y) (Par m1 m2 k) φ.
Proof.
  intros; eapply pure_par'; by eauto.
Qed.

(* Sequentializations of previous lemmas, considering the LHS first *)

(* TODO: I do not seem to be able to use those, for example in pure_eval.v's
[pure_eval_pair] *)

Lemma total_par_seq `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ : A1 * A2 → Prop) z
:
  total (E := X) m1 (λ a1 : A1,
    total m2 (λ a2 : A2, total (k (#a1, #a2)) φ)) →
  total (E := Y) (Par m1 m2 (glue2 k z)) φ.
Proof. apply pure_par_seq. Qed.

Lemma total_par_seq' `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  total (E := X) m1 (λ a1 : A1,
    total m2 (λ a2 : A2, total (continue k (#a1, #a2)) φ)) →
  total (E := Y) (Par m1 m2 k) φ.
Proof. apply pure_par_seq'. Qed.

(* A reasoning rule for [choose]. *)

Lemma total_choose `{Encode A} m1 m2 (φ : A → Prop) :
  total m1 φ →
  total m2 φ →
  total (choose m1 m2) φ.
Proof. apply pure_choose. Qed.

(* This is the reciprocal bind rule for [pure]. *)

(* Because [pure m ##_ ⊥] requires the result of [m] to lie in the image of the
   function [encode], and because this image cannot include every inhabitant
   of the type [val], we cannot expect that [pure (bind m k) ##φ ⊥] implies
   [pure m ##_ ⊥]. Thus, we can establish the reciprocal bind rule only under
   the side condition [pure m ##(λ a, True) ⊥], which means that the result of
   the computation [m] lies in the image of the function [encode] at type
   [A]. *)

Lemma invert_total_bind `{Encode A, Encode B} X m k (φ : B → Prop) :
  total (bind m k) φ →
  total m (λ (a : A), True) →
  total (E := X) m (λ (a : A), total (k #a) φ).
Proof. apply invert_pure_bind. Qed.

(* That said, if we take the type [A] to be [val], then -- because [encode]
   at type [val] is the identity function -- this side condition becomes
   trivial, and we can prove a version of the rule that does not have this
   side condition. *)

Lemma invert_total_bind' `{Encode B} {X} m k (φ : B → Prop) :
  total (bind m k) φ →
  total (E := X) m (λ (v : val), total (k v) φ).
Proof. eapply invert_pure_bind'. Qed.

(* -------------------------------------------------------------------------- *)

(* Because the relation [pure] is inductively defined, the [pure] judgement
   implies that [m] terminates. This forms a Hoare logic of total correctness
   for pure computations. *)

(* This file offers lemmas and tactics that help work with [pure] goals.
   These lemmas and tactics form a simple "proof mode" for pure
   computations. *)

(* -------------------------------------------------------------------------- *)
Lemma total_prove_bind_bind `{Encode A} `{Encode X} {E} m (a : A)
  (f : A -> _) (g : val -> _) (φ : X -> Prop) :
  total ('c ← m;
        f c) (λ x, x = #a) ->
  total (g #a) φ ->
  total (E := E) ('v1 ← m;
        'v2 ← f v1;
        g v2) φ.
Proof. apply pure_prove_bind_bind. Qed.

Lemma total_bind_bind `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  total ('x ← m; f x) ψ ->
  (forall y, ψ y -> total (g #y) φ) ->
  total ('v1 ← m;
        v2 ← f v1;
        g v2) φ.
Proof.
  intros Hm Hga.
  apply invert_pure_wp_bind in Hm.
  eapply pure_wp_bind_conseq; eauto. simpl.
  intros v Hv.
  eapply pure_wp_bind_conseq; eauto. simpl.
  intros _ (y & -> & Hy).
  apply Hga, Hy.
Qed.

Lemma total_bind_binary `{Encode X} `{Encode Y} (m : micro val void) f g
  (φ : X -> Prop) (ψ : Y -> Prop) :
  total m (fun x => total (f x) ψ)->
  (forall y, ψ y -> total (g #y) φ) ->
  total ('x ← m;
        y ← f x;
        g y) φ.
Proof.
  intros.
  eapply total_bind_bind; last done.
  eapply total_bind; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Variants of the Bind rule. *)

(* [pure_enc_bind_as_bool] is already in [pure_eval.v] but it is useful there *)

(* [bind] composed with [as_int]. *)

(* Lemma pure_bind_as_int `{Encode Y} *)
(*   m (f : int → microvx) (φ : Z → Prop) (ψ : Y → Prop) : *)
(*   total m φ → *)
(*   (∀ (x : Z), φ x → total (f (repr x)) ψ) → *)
(*   total (bind (as_int m) f) ψ. *)
(*   (* This is [@bind int val]. *) *)
(* Proof. *)
(*   intros Hm%pure_as_int Hf. *)
(*   eapply pure_bind_conseq; eauto. *)
(*   intros _ (i & -> & Hi). *)
(*   eapply (pure_mono_ret _ (Hf i Hi)); auto. *)
(* Qed. *)

(* (* [bind] composed with [as_loc]. *) *)

(* Lemma pure_bind_as_loc `{Encode Y} *)
(*   m (f : loc → microvx) (φ : loc → Prop) (ψ : Y → Prop) : *)
(*   pure m ##φ ⊥ → *)
(*   (∀ (x : loc), φ x → pure (f x) ##ψ ⊥) → *)
(*   pure (bind (as_loc m) f) ##ψ ⊥. *)
(*   (* This is [@bind loc val]. *) *)
(* Proof. *)
(*   intros Hm Hf. *)
(*   apply pure_bind. *)
(*   eapply pure_bind_conseq; eauto. *)
(*   intros _ (l & -> & Hl). apply pure_ret, Hf, Hl. *)
(* Qed. *)

(* (* [bind] composed with [as_struct]. *) *)

(* Lemma pure_bind_as_struct Y (_ : Encode Y) *)
(*   m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) : *)
(*   pure m ##(λ y : val, (exists y', y = VStruct y' /\ φ y)) ⊥ → *)
(*   (∀ (x : env), φ (VStruct x) → pure (f x) ##ψ ⊥) → *)
(*   pure (bind (as_struct m) f) ##ψ ⊥. *)
(*   (* This is [@bind env val]. *) *)
(* Proof. *)
(*   intros Hm Hf. *)
(*   apply pure_bind. *)
(*   eapply pure_bind_conseq; eauto. *)
(*   intros _ (_ & -> & (env & -> & Henv)). *)
(*   apply pure_ret, Hf, Henv. *)
(* Qed. *)

(* [bind] composed with [as_record]. *)

(* Lemma pure_bind_as_record Y (_ : Encode Y) *)
(*   m (f : env → microvx) (φ : val → Prop) (ψ : Y → Prop) : *)
(*   total m (λ y : val, exists y', y = VRecord y' /\ φ y) → *)
(*   (∀ (x : env), φ (VRecord x) → total (f x) ψ) → *)
(*   total (bind (as_record m) f) ψ. *)
(*   (* This is also [@bind env val]. *) *)
(* Proof. *)
(*   (* same exact proof script *) *)
(*   intros Hm Hf. *)
(*   apply pure_bind. *)
(*   eapply pure_bind_conseq; eauto. *)
(*   intros _ (_ & -> & (env & -> & Henv)). *)
(*   apply pure_ret, Hf, Henv. *)
(* Qed. *)

(* TODO add similar lemmas for other constructs *)

(* TODO on 2024-08-14 the lemmas above are unused *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* This trivial lemma gives the user a chance to prove that the actual
   argument [v'2] is in fact the encoding of some value [x]. The subgoal
   [v'2 = #x] is typically solved by the tactic [encode]. Solving this
   subgoal instantiates both the metavariable [x] and the metavariable [X],
   which is the type of [x]. *)

(* Lemma pure_call `{Encode X} `{Encode Y} *)
(*   (φ : Y → Prop) v1 v'2 (x : X) : *)
(*   v'2 = #x → *)
(*   pure (call v1 #x) ##φ ⊥ → *)
(*   pure (call v1 v'2) ##φ ⊥. *)
(* Proof. *)
(*   intros. subst. eauto. *)
(* Qed. *)

(* (* This lemma combines [pure_enc_consequence] and [pure_call]. *) *)

(* Lemma pure_call_consequence `{Encode X} `{Encode Y} *)
(*   (φ ψ : Y → Prop) v1 v'2 (x : X) : *)
(*   v'2 = #x → *)
(*   pure (call v1 #x) ##φ ⊥ → *)
(*   (∀ y, φ y → ψ y) → *)
(*   pure (call v1 v'2) ##ψ ⊥. *)
(* Proof. *)
(*   eauto using pure_enc_consequence, pure_call. *)
(* Qed. *)

(* (* The following two lemmas paraphrase the definition of [call] in eval.v. *)
(*    When applied to a goal of the form [simp (call v1 v2) _] where [v1] is *)
(*    a concrete closure (as opposed to a rigid metavariable), they step into *)
(*    the call. *) *)

(* Lemma pure_enter_call_VClo `{Encode Y} η a v2 (φ : Y → Prop) ψ : *)
(*   pure (acall η a v2) ##φ ψ -> *)
(*   pure (call (VClo η a) v2) ##φ ψ. *)
(* Proof. *)
(*   tauto. *)
(* Qed. *)

(* Lemma pure_stop_eval {Y} `{Encode X} η e k (φ : X -> Prop) ψ : *)
(*   pure (try2 (eval η e) k) ##φ ψ -> *)
(*   pure (E := Y) (Stop CEval (η, e) k) ##φ ψ. *)
(* Proof. *)
(*   intros. *)
(*   eapply pure_simp; [ apply SimpEval | assumption ]. *)
(* Qed. *)

(* Lemma pure_enter_call_VCloRec `{Encode Y} η rbs g x e v2 (φ : Y → Prop) ψ : *)
(*   lookup_rec_bindings rbs g = ret (AnonFun x e) -> *)
(*   pure (eval ((x, v2) :: eval_rec_bindings η rbs ++ η) e) ##φ ψ -> *)
(*   pure (call (VCloRec η rbs g) v2) ##φ ψ. *)
(* Proof. *)
(*   intros Hlookup Hpure. *)
(*   simpl; rewrite Hlookup. *)
(*   eapply pure_CEval; rewrite try2_ret_right. *)
(*   done. *)
(* Qed. *)

(* Lemma invert_pure_call `{Encode Y} f v (φ : Y -> Prop) : *)
(*   pure (call f v) ##φ ⊥ -> *)
(*   (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g. *)
(* Proof. *)
(*   intros Hcall. *)
(*   unfold call in Hcall. *)
(*   destruct f; simpl in Hcall; *)
(*     ((exfalso; by eapply invert_pure_crash) || eauto). *)
(* Qed. *)

(* (* - [X] is the type of the argument. *)
(*    - [Y] is the type of result. *)
(*    - [a : A] is an auxiliary variable used to relate the pre and post. *) *)

(* Lemma pure_rec_call `{Encode X, Encode Y} *)
(*   (η : env) (f : var) arg e1 (x : X) Ψ *)
(*   (P : X -> Prop) (φ : X -> Y -> Prop) (R : X -> X -> Prop) : *)
(*   well_founded R -> *)
(*   P x -> *)
(*   (∀ vf x, *)
(*       (∀ (y : X), R y x -> P y -> pure (call vf #y) ##(φ y) Ψ) -> *)
(*       (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) ##(φ x) Ψ)) -> *)
(*   pure (call (VCloRec η [RecBinding f (AnonFun arg e1)] f) #x) ##(φ x) Ψ. *)
(* Proof. *)
(*   intros Hwf HPx Hrec. *)
(*   induction x as [x IH] using (well_founded_induction Hwf); intros. *)
(*   simpl; rewrite String.eqb_refl; apply pure_CEval; rewrite try2_ret_right. *)
(*   apply Hrec; [ intros y HR HPy | assumption ]. *)
(*   apply IH; auto. *)
(* Qed. *)

(* (* - [φ] is the toplevel specification. *)
(*    - [φf] is the specification of the function [f]. *) *)

(* Lemma pure_letrec `{Encode X, Encode Y} *)
(*   (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : X -> Y -> Prop) Ψ *)
(*   (P : X -> Prop) (R : X -> X -> Prop) : *)
(*   well_founded R -> *)
(*   (* Subgoal: *)
(*      Assuming that any recursive call of [f] on a smaller argument *)
(*      satisfies [φf], show that evaluating [e1] satisfies [φf]. *) *)
(*   (∀ vf (x : X), *)
(*       (∀ (y : X), R y x -> P y -> pure (call vf #y) ##(φf y) Ψ) -> *)
(*       (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) ##(φf x) Ψ)) -> *)
(*   (* Subogal: *)
(*      Proceed with the right hand of the [let rec], *)
(*      assuming f satisfies its spec. *) *)
(*   (∀ vf, *)
(*       (∀ x, P x -> pure (call vf #x) ##(φf x) Ψ) -> *)
(*       pure (eval ((f, vf) :: η) e2) ##φ Ψ) -> *)
(*   pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) ##φ Ψ. *)
(* Proof. *)
(*   intros Hwf He1 He2. *)
(*   simpl_eval. apply He2. clear He2. *)
(*   intros y HPy. *)
(*   eapply pure_rec_call; eauto. *)
(* Qed. *)

(* Lemma pure_rec_call_no_pre `{Encode X} `{Encode Y} *)
(*   (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : X -> Y -> Prop) *)
(*   (R : X -> X -> Prop) : *)
(*   well_founded R -> *)
(*   (* Subgoal: *)
(*      Assuming that any recursive call of [f] on a smaller argument *)
(*      satisfies [φf], show that evaluating [e1] satisfies [φf]. *) *)
(*   (∀ vf (x : X), *)
(*       (∀ (y : X), R y x -> pure (call vf #y) ##(φf y) ⊥) -> *)
(*       pure (eval ((arg, #x) :: (f, vf) :: η) e1) ##(φf x) ⊥) -> *)
(*   (* Subogal: *)
(*      Proceed with the right hand of the [let rec], *)
(*      assuming f satisfies its spec. *) *)
(*   (∀ vf, *)
(*       (∀ (x : X), pure (call vf #x) ##(φf x) ⊥) -> *)
(*       pure (eval ((f, vf) :: η) e2) ##φ ⊥) -> *)
(*   pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) ##φ ⊥. *)
(* Proof. *)
(*   intros Hwf He1 He2. *)
(*   simpl_eval. apply He2. clear He2. *)
(*   intros y. *)
(*   eapply pure_rec_call with (P := fun _ => True); eauto. *)
(* Qed. *)

(* Lemma pure_rec_call2 `{Encode X, Encode Y, Encode W} *)
(*   η f arg e1 (x : X) (y : Y) (φ : X -> Y -> W -> Prop) Ψ *)
(*   (R : (X * Y) -> (X * Y) -> Prop) (P : X -> Y -> Prop) *)
(*   : *)
(*   well_founded R -> *)
(*   P x y -> *)
(*   (∀ vf x1 y1, *)
(*       (∀ (x2 : X) (y2 : Y), *)
(*           R (x2, y2) (x1, y1) -> *)
(*           P x2 y2 -> *)
(*           pure_call2 vf #x2 #y2 (φ x2 y2) Ψ) -> *)
(*       ( *)
(*         P x1 y1 -> *)
(*         pure (eval ((arg, #x1) :: (f, vf) :: η) e1) (λ c, pure (call c #y1) ##(φ x1 y1) Ψ) Ψ)) -> *)
(*   pure_call2 (VCloRec η [RecBinding f (AnonFun arg e1)] f) #x #y (φ x y) Ψ. *)
(* Proof. *)
(*   intros Hwf HP Hrec. *)
(*   remember (x, y) as p eqn:Hpeq. *)
(*   rewrite (surjective_pairing p) in Hpeq. *)
(*   apply pair_eq in Hpeq as [<- <-]. *)
(*   revert HP. *)
(*   induction p as [p IH] using (well_founded_induction Hwf); intros. *)
(*   unfold pure_call2; simpl; *)
(*     rewrite String.eqb_refl; apply pure_CEval; rewrite try2_ret_right. *)
(*   apply Hrec; [ intros x2 y2 HR HP2 | apply HP ]. *)
(*   apply (IH (x2, y2)); auto. *)
(*   rewrite surjective_pairing; apply HR. *)
(* Qed. *)

End total_rules.
