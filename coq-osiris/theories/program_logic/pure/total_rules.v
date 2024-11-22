From osiris Require Import base.
From osiris.lang Require Import locations lang.
From osiris.semantics Require Import code eval.
From osiris.program_logic.pure Require Export pure_rules.

Section total_rules.

(* The consequence rule. *)

Lemma total_mono `{Encode A} {X} m (φ ψ : A → Prop) :
  total m φ →
  (∀ a, φ a → ψ a) →
  total (E := X) m ψ.
Proof.
  intros; by eapply pure_mono.
Qed.

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

Lemma total_ret_eq_and `{Encode A} {X : Type} (a : A) (ψ : Prop):
  ψ →
  total (E := X) (ret #a) (λ a', a' = a /\ ψ).
Proof.
  intros. eapply total_mono. apply total_ret_eq.
  cbn. intros; by subst.
Qed.

Lemma total_returns `{Encode A} {X : Type}
  (a : val) (k : val -> micro val X) (φ : A -> Prop):
  total (E := X) (k a) φ ->
  returns (λ v : val, total (k v) φ) a.
Proof.
  intros; eauto with pure.
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

Lemma total_Par {E E'}
  (m1 : micro val E') (m2 : micro val E') (φ : val * val -> Prop)
  (k : outcome2 (val * val) E' → micro val E) :
  total (E := E') m1
    (λ a1,
      total m2
        (λ a2, total (continue k (a1, a2)) φ)) →
  total m2
    (λ a2,
      total m1
        (λ a1, total (continue k (a1, a2)) φ)) →
  total (Par m1 m2 k) φ.
Proof.
  intros; eapply pure_wp_Par;
    eapply pure_wp_mono; eauto;
    intros; returns_eauto; eauto;
    eapply pure_wp_mono; eauto;
    intros; returns_eauto; eauto; try done.
Qed.

(* We cannot give a reasoning rule for [par m1 m2] because its type is
   [micro (val * val)], not [micro val]. However, we can give a rule
   for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

Lemma total_par_glue2 `{Encode A1, Encode A2} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop) z
:
  total (E := X) m1 φ1 →
  total m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → total (k (#a1, #a2)) φ) →
  total (E := Y) (Par m1 m2 (glue2 k z)) φ.
Proof.
  intros; eapply pure_par_glue2; by eauto.
Qed.

Lemma total_par_cont `{Encode A1, Encode A2} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 * A2 → Prop)
:
  total (E := X) m1 φ1 →
  total m2 φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → total (continue k (#a1, #a2)) φ) →
  total (E := Y) (Par m1 m2 k) φ.
Proof.
  intros; eapply pure_par_cont; by eauto.
Qed.

(* Sequentializations of previous lemmas, considering the LHS first *)

Lemma total_par_seq `{Encode A1, Encode A2, Encode A} {X Y}
  m1 m2 k (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A1 → Prop)
:
  total (E := X) m1 (λ a1 : A1,
    total m2 (λ a2 : A2, total (continue k (#a1, #a2)) φ)) →
  total (E := Y) (Par m1 m2 k) φ.
Proof. apply pure_par_seq. Qed.

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

Lemma invert_total_bind_unary `{Encode B} {X} m k (φ : B → Prop) :
  total (bind m k) φ →
  total (E := X) m (λ (v : val), total (k v) φ).
Proof. eapply invert_pure_bind_unary. Qed.

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

Lemma total_triple `{Encode A1, Encode A2, Encode A3} η e1 e2 e3 (ψ : A1 * A2 * A3 -> Prop) :
  total (eval η e1) (λ a1 : A1,
        total (eval η e2) (λ a2 : A2,
              total (eval η e3) (λ a3 : A3,
                    ψ (a1, a2, a3)))) ->
  total (eval η (ETuple [e1; e2; e3])) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto with pure.
Qed.

Lemma total_pair_val η e1 e2 (ψ : val → Prop) :
  total (eval η e1) (λ a1 : val, total (eval η e2) (λ a2 : val, ψ (VPair a1 a2))) →
  total (eval η (EPair e1 e2)) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret.
  eauto with pure.
Qed.

Lemma total_pair_conseq `{Encode A1, Encode A2} η e1 e2
  (φ1 : A1 → Prop) (φ2 : A2 → Prop) (ψ : A1 * A2 → Prop)
:
  total (eval η e1) φ1 →
  total (eval η e2) φ2 →
  (∀ a1 a2, φ1 a1 → φ2 a2 → ψ (a1, a2)) →
  total (eval η (EPair e1 e2)) ψ.
Proof.
  intros. simpl_eval.
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  eapply pure_wpv_Par_left_conseq; eauto. intros ? (? & -> & ?).
  repeat apply pure_wp_ret. eauto 10 with pure.
Qed.


End total_rules.
