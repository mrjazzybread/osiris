Require Import lang eval.
Require free div.

(* ------------------------------------------------------------------------ *)

(* An interpretation of the free monad into the divergence monad. *)

CoFixpoint handle {A} (m : free.mon A) : div.div A :=
  match m with
  | free.Ret a =>
      (* Termination is mapped to termination. *)
      div.Ret a
  | free.Fail =>
      (* Hard failure is mapped to hard failure. *)
      div.Fail
  | free.Next =>
      (* Soft failure is not expected to happen. *)
      div.Fail
  | free.Stop req k =>
      (* A [Stop] effect is mapped to an invocation of [eval]
         under a [Skip] constructor. The presence of [Skip]
         allows this potentially diverging recursive call to
         be made. The call [eval η e] is composed with the
         continuation [k]. This computation is (recursively)
         transported by [handle] from the free monad into the
         divergence monad. *)
      match req with
      | free.REval η e =>
          div.Skip (handle (free.bind (eval η e) k))
      end
  end.

(* ------------------------------------------------------------------------ *)

(* The composition of [handle] and [eval] is an interpreter of expressions
   in the divergence monad. *)

Definition run η e : div.div val :=
  handle (eval η e).

(* ------------------------------------------------------------------------ *)

(* [handle] commutes with [bind]. *)

Local Infix "~" := div.eq (at level 70, no associativity).

Lemma compatibility {A B} (m : free.mon A) {k : A → free.mon B} :
  handle (free.bind m k) ~
  div.bind (handle m) (λ v, handle (k v)).
Proof.
  induction m. (* This cannot work. A co-inductive proof is needed. *)
  { unfold free.bind, free.try.
    replace (handle (free.Ret a)) with (div.Ret a). 2: admit.
    eapply div.eq_transitive.
      2: eapply div.eq_symmetric.
      2: eapply div.monad_law_left_unit.
    eapply div.eq_reflexive. }
  { unfold free.bind, free.try.
    replace (handle (free.Fail : free.mon A)) with (div.Fail : div.div A). 2: admit.
    replace (handle (free.Fail : free.mon B)) with (div.Fail : div.div B). 2: admit.
    admit. }
  { admit. }
  (* last case todo *)
Abort.
