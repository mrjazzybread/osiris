From stdpp Require Import telescopes.
From iris.proofmode Require Import base tactics classes environments.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.stdlib Require Import Stdlib.
From osiris.examples Require Import og_inversion.

(* ========================================================================== *)
(** * Iteration Descriptors. *)

Class Iterable (G : Type → Type) := {
  (* [permitted T Xs] holds if [Xs] is a possible prefix
     of visited elements of the collection [T]. *)
  permitted {A : Type} : G A → list A → Prop;

  (* [complete T Xs] holds if [Xs] is the complete list
     of elements of the collection [T]. *)
  complete  {A : Type} : G A → list A → Prop;
}.

(* A finitely iterable data structure is one whose elements can
   be named in advance, before the iteration has terminated. *)
Class FinIterable G `{Iterable G, ∀ A, Elements A (G A)} := {
  permitted_elements {A : Type} :
    ∀ (T : G A) (Xs : list A), permitted T Xs → Xs ⊆ elements T;

  complete_elements {A : Type} :
    ∀ (T : G A) (Xs : list A), complete T Xs → Xs ≡ₚ elements T;
}.


(* ========================================================================== *)
(** * Higher-Order Iteration Methods. *)

Section iteration_methods.
  Context `{!osirisGS Σ}.
  Context {G : Type → Type} `{DataStructure Σ G, Iterable G}
          {A : Type}         `{Encode A} `{Encode (G A)}.

  Variables (t : G A).

  Definition isIter (Ψ : iEff Σ) (iter : val) : iProp Σ :=
    ∀ E (I : list A → iProp Σ) (f : val),
      □ (∀ (Xs : list A) (X : A),
           ⌜ permitted t (Xs ++ [X]) ⌝ -∗
             I Xs -∗
                 EWP (call f #X) @ E <| Ψ |> {{ λ _, I (Xs ++ [X]) }})
      -∗
          I [] -∗
          EWP (c ← call iter f;
               call c #t) @ E <| Ψ |> {{ λ _, ∃ Xs, I Xs ∗ ⌜ complete t Xs ⌝ }}.

End iteration_methods.


(* ========================================================================== *)
(** * Lazy Sequences. *)

Section lazy_sequences.
  Context `{!osirisGS Σ}.
  Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}
           {A : Type}         `{Encode A} `{Encode (G A)}.

  Variables (t : G A).

  (* ------------------------------------------------------------------------ *)
  (** Specification of Heads. *)

  (* The predicate [isHead] is defined as [isHead_pre isSeq], where [isSeq] is
     the fixpoint of [isSeq_pre]. *)
  (* A head is either a [Cons] pair or a [Nil] marker. *)
  Definition isHead_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           :  iEff Σ -d> val -d> list A -d> iPropO Σ  :=
    λ Ψ h Xs,
      match h with
      | VData "None" (VTuple [])       =>
          ⌜ complete t Xs ⌝
      | VData "Some" p =>
          ∃ X k, ⌜ p = #(X, k) ⌝ ∧
                 ⌜ permitted t (Xs ++ [X]) ⌝ ∗ ▷ isSeq Ψ k (Xs ++ [X])
      | _ =>
          False
      end%I.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead Ψ1 Ψ2 h Xs]. *)
  Definition isSeq_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           : (iEff Σ -d> val -d> list A -d> iPropO Σ) :=
    λ Ψ k Xs,
      EWP (call k #()) <| Ψ |> {{ RET h, isHead_pre isSeq Ψ h Xs }}%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isHead_pre_contractive : Contractive isSeq_pre.
  Proof.
    rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq Ψ k us.
    f_equiv=>?. simpl. repeat (f_contractive || f_equiv). by apply HisSeq.
  Qed.
  Definition isSeq_def :
    iEff Σ -d> val -d> list A -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold Ψ k us :
    isSeq Ψ k us ⊣⊢ isSeq_pre isSeq Ψ k us.
  Proof. by rewrite isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
  Global Lemma isHead_unfold Ψ :
    isHead Ψ = isHead_pre isSeq Ψ.
  Proof. done. Qed.

End lazy_sequences.


(* ========================================================================== *)
(** * Protocol. *)

Context (yield_eff : loc).
Definition yield x : val := VXData yield_eff (VTuple [x]).

(* This protocol describes the effects performed by [yield]. *)

Section inversion_protocol.
  Context `{!osirisGS Σ}.
  Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}.
  Context {A : Type} `{Encode A}.

  Definition Ψ_yield T (iterView : list A → iProp Σ) : iEff Σ :=
    (>> Xs X >>
       ! (yield #X)
         {{ iterView Xs ∗ ⌜ permitted T (Xs ++ [X]) ⌝ }};
       ? (O2Ret #())
         {{ iterView (Xs ++ [X]) }} @ OS).

End inversion_protocol.


(* ========================================================================== *)
(** * Verification. *)

Section verification.

  (* ------------------------------------------------------------------------ *)
  (** Ghost Theory. *)

  Section ghost_theory.
    Context {A : Type}.

    (* We use ghost variables with contents in the CMRA [Auth(Ex(List A))]. *)
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    (* The assertion [own γ (●E Ys)] states that the handler
       has seen the elements [Ys]. *)
    Definition handlerView γ Ys : iProp Σ :=
      own γ (●E (Ys : ofe_car (leibnizO (list A)))).
    (* The assertion [own γ (◯E Xs)] states that [iter]
       has seen the elements [Xs]. *)
    Definition iterView γ Xs : iProp Σ :=
      own γ (◯E (Xs : ofe_car (leibnizO (list A)))).

    (* Create a new ghost cell from this CMRA. *)
    (* In the verification of [invert], the ghost variable [γ]
       initially holds the empty list. *)
    Lemma new_cell Zs : ⊢ (|==> ∃ γ, handlerView γ Zs ∗ iterView γ Zs)%I.
    Proof.
      iMod (own_alloc ((●E (Zs : ofe_car (leibnizO (list A)))) ⋅
                       (◯E (Zs : ofe_car (leibnizO (list A)))))) as (γ) "[??]";
      [ apply excl_auth_valid | eauto with iFrame ]; done.
    Qed.

    (* Handler and [iter]'s views are in agreement. *)
    Lemma confront_views γ Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs -∗ ⌜ Xs = Ys ⌝.
    Proof.
      iIntros "Hγ● Hγ◯".
      by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
    Qed.

    (* With the ownership of both views, one can update the contents of [γ]. *)
    Lemma update_cell γ Zs Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs ==∗ handlerView γ Zs  ∗ iterView γ Zs.
    Proof.
      iIntros "Hγ● Hγ◯".
      iMod (own_update_2 _ _ _ (●E (Zs : ofe_car (leibnizO (list A))) ⋅
                                ◯E (Zs : ofe_car (leibnizO (list A))))
        with "Hγ● Hγ◯") as "[$$]";
      [ apply excl_auth_update |]; done.
    Qed.

  End ghost_theory.

  (* ========================================================================== *)
  (** * Specification. *)

  (* The specification of [invert] depends on (1) the specification of a
   iteration method [isIter] and (2) the specification of a lazy sequence
   [isSeq], both of which are introduced in the theory [iteration.v]. *)

  Section specification.
    Context `{!osirisGS Σ}.
    Context {G : Type → Type} `{DataStructure Σ G, Iterable G}.
    Context {A : Type}         `{Encode A} `{Encode (G A)}.

    (* ------------------------------------------------------------------------ *)
    (** Specification of [invert]. *)

    (* [λ f, iter f t] *)
    Definition itere :=
      EAnonFun
        (AnonFun
           "f"
           (EApp
              (EApp
                 (EPath ["iter"])
                 (EPath ["f"]))
              (EPath ["t"]))).

    Definition invert_spec invert : iProp Σ :=
      ∀ (t : G A) (iter : val),
      isIter t ⊥ iter -∗
      EWP (iterv ← eval [("iter", #iter); ("t", #t)] itere;
           call invert iterv) {{ lift_ret_spec (λ k, isSeq t ⊥ k []) }}.

  End specification.

End verification.
