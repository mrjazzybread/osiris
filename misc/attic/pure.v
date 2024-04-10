
(* The following lemmas existed before deprecating [simplify_step_diagram]. *)

(* -------------------------------------------------------------------------- *)

(* This is the reciprocal bind rule for [pure]. *)

(* Because [pure m _] requires the result of [m] to lie in the image of the
   function [encode], and because this image cannot include every inhabitant
   of the type [val], we cannot expect that [pure (bind m k) φ] implies
   [pure m _]. Thus, we can establish the reciprocal bind rule only under
   the side condition [pure m (λ a, True)], which means that the result of
   the computation [m] lies in the image of the function [encode] at type
   [A]. *)

Lemma invert_pure_bind `{Encode A, Encode B} X m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure m (λ (a : A), True) →
  pure (X := X) m (λ (a : A), pure (k #a) φ).
Proof.
  intros Hmk Hm.
  rewrite pure_totalv in Hmk.
  apply invert_totalv_bind in Hmk.
  destruct_total v e.

  (* The problem that we now face is to prove that the value [v] produced
     by [m] must be of the form [#a]. The hypothesis [Hm] is necessary for
     this purpose. *)
  destruct_pure a.

  (* We can then conclude. *)
  unfold pure. exists a. split; [ eauto |].
  destruct_total v e. destruct_encode_image b. eauto.
Qed.

(* That said, if we take the type [A] to be [val], then -- because [encode]
   at type [val] is the identity function -- this side condition becomes
   trivial, and we can prove a version of the rule that does not have this
   side condition. *)

Lemma invert_pure_bind' `{Encode B} {X} m k (φ : B → Prop) :
  pure (bind m k) φ →
  pure (X := X) m (λ (v : val), pure (k v) φ).
Proof.
  intros Hmk.
  rewrite pure_totalv in Hmk.
  apply invert_totalv_bind in Hmk.
  destruct_total v e.
  unfold pure. exists v. split; [ eauto |].
  destruct_total v' e'. destruct_encode_image b. eauto.
Qed.
