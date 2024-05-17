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
(** * Data Structure. *)

(* We formalize a data structure as a type family [G], such that
   [G A] is representable for every repesentable type [A]. *)
Class DataStructure (G : Type → Type) :=
  is_representable A `{Encode A} :> Encode (G A).


(* ========================================================================== *)
(** * Higher-Order Iteration Methods. *)

Section iteration_methods.
  Context `{!osirisGS Σ}.
  Context {G : Type → Type} `{DataStructure G, Iterable G}
          {A : Type}         `{Encode A}.

  Variables (T : G A).

  Definition isIter (ψ : iEff Σ) (iter : val) : iProp Σ :=
    ∀ E (I : list A → iProp Σ) (f : val),
      □ (∀ (Xs : list A) (X : A),
           ⌜ permitted T (Xs ++ [X]) ⌝ -∗
           I Xs -∗
           EWP (call f #X) @ E <| ψ |> {{ λ _, I (Xs ++ [X]) }})
      -∗
      I [] -∗
      EWP (call iter f) @E <| ψ |> {{ RET c,
      EWP (call c #T) @ E <| ψ |>
        {{ λ _, ∃ Xs, I Xs ∗ ⌜ complete T Xs ⌝ }} }}.

End iteration_methods.

(* ------------------------------------------------------------------------ *)
(** Lift Data Structure. *)

Global Instance lift_data_structure G `{DataStructure G} :
  DataStructure (G ∘ G).
Proof. intros ??. simpl. by apply _. Defined.


(* ========================================================================== *)
(** * Lift Iteration Method. *)

Section lift_iteration_method.
  Context `{!osirisGS Σ}.
  Context G `{DataStructure G, Iterable G}.

  Definition lift_permitted {A} (TT : (G (G A))) (Xs : list A) : Prop :=
    (* We match over [last Xs] to facilitate the simplification of
         assertions of the form [permitted _ (_ ++ [X])]. *)
    match last Xs with
    | None => True
    | _ =>
        ∃ (Ts : list (G A)) (T : G A) (Xss : list (list A)) (Ys : list A),
        Xs = concat Xss ++ Ys    ∧
        permitted TT (Ts ++ [T]) ∧
        permitted T Ys           ∧
        Forall2 complete Ts Xss
  end.

  Definition lift_complete {A} (TT : G (G A)) (Xs : list A) : Prop :=
    ∃ (Ts : list (G A)) (Xss : list (list A)),
      Xs = concat Xss         ∧
        complete TT Ts          ∧
        Forall2 complete Ts Xss.

  Global Instance lift_iterable : Iterable (G ∘ G) := {
      permitted := @lift_permitted;
      complete  := @lift_complete;
    }.

  (* Value representing [fun f tt -> iter (fun t -> iter f t) tt]. *)
  Definition lift_iter (iter : val) : val :=
    (VClo [("iter", iter)]
            (Anon ("f" =>
                 EAnonFun
                   (Anon ("tt" =>
                            EApp
                              (EApp
                                 (EPath ["iter"])
                                 (EAnonFun (Anon ("t" => EApp (EApp (EPath ["iter"]) (EPath ["f"])) (EPath ["t"])))))
                              (EPath ["tt"])))))).

  Lemma lift_iter_isIter (iter : val) (Ψ : iEff Σ) :
      □ (∀ (A : Type) `{Encode A} (T : G A),
          isIter T Ψ iter)
        -∗
      □ (∀ (A : Type) `{Encode A} (TT : (G ∘ G) A),
          isIter TT Ψ (lift_iter iter)).
  Proof.
    iIntros "#Hiter" (????) "!#".
    iIntros (I f) "#Hf HI". unfold lift_iter.
    Simp. Ret. Simp. Bind. simpl in *.
    iApply (ewp_pers_mono with "[HI]").
    iApply ("Hiter" $!
              ((* Type of the elements. *) G A) (is_representable A)
              ((* Data structure. *) TT)
              ((* Mask. *) E)
              ((* Invariant. *) λ (Ts : list (G A)), ∃ Xss,
                  I (concat Xss) ∗ ⌜ Forall2 complete Ts Xss ⌝)%I
              ((* Iteratee. *) _ )
             with "[] [HI]"); [|by iExists []; iFrame].
    - iIntros "!#" (Ts T) "%Hpermitted [%Xss [HI %Hcomplete]]".
      Simp. Bind.
      iApply (ewp_pers_mono with "[HI]").
      iApply ("Hiter" $! A H1 T E
                ((* Invariant. *) λ (Xs : list A), I (concat Xss ++ Xs))%I
                ((* Iteratee. *) f)
               with "[] [HI]"); [|rewrite app_nil_r; by iFrame].
      + iIntros "!#" (Xs X) "%Hpermitted_T HI".
        rewrite app_assoc.
        iApply ("Hf" $! _ X with "[] HI").
        iPureIntro. rewrite /= /lift_permitted last_app last_cons //=.
        exists Ts, T, Xss, (Xs ++ [X]).
        rewrite app_assoc. by repeat split.
      + iIntros "!#" ([|]); [ simpl | done]; iIntros "Hc !>".
        iApply (ewp_pers_mono with "Hc").
        iIntros "!#" (_) "[%Xs [HI %Hcomplete_T]] !>".
        iExists (Xss ++ [Xs]). rewrite concat_app //= app_nil_r.
        iFrame. iPureIntro. by decompose_Forall.
    - iIntros "!#" ([y|]); [ simpl | done]; iIntros "Hc !>".
      iApply (ewp_pers_mono with "Hc").
      iIntros "!#" (_) "[%Ts [[%Xss [HI %Hxs]] %Hcomplete_TT]] !>".
      iExists (concat Xss). iFrame. iPureIntro.
      rewrite /lift_complete. by exists Ts, Xss.
    Qed.

End lift_iteration_method.


(* ========================================================================== *)
(** * Lazy Sequences. *)

Section lazy_sequences.
  Context `{!osirisGS Σ}.
  Context  {G : Type → Type} `{DataStructure G, Iterable G}
           {A : Type}         `{Encode A}.

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
      | VData "Nil" (VTuple [])       =>
          ⌜ complete t Xs ⌝
      | VData "Cons" p =>
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
  Context  {G : Type → Type} `{DataStructure G, Iterable G}.
  Context  {A : Type} `{Encode A}.

  Definition ψ_yield T (iterView : list A → iProp Σ) : iEff Σ :=
    (>> Xs X >>
       ! (yield #X)
         {{ iterView Xs ∗ ⌜ permitted T (Xs ++ [X]) ⌝ }};
       ? (@O2Ret val exn #())
         {{ iterView (Xs ++ [X]) }} @ OS).

  Lemma upcl_yield T iterView v Φ :
    iEff_car (upcl OS (ψ_yield T iterView)) v Φ ⊣⊢
      (∃ Xs (X : A), ⌜ v = yield #X ⌝ ∗
                             (iterView Xs ∗
                             ⌜ permitted T (Xs ++ [X]) ⌝) ∗
                             (iterView (Xs ++ [X]) -∗ Φ (O2Ret (VUnit))))%I.
  Proof. by rewrite /ψ_yield  (upcl_tele' [tele _ _] [tele]) //=. Qed.

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
    Context {G : Type → Type} `{DataStructure G, Iterable G}.
    Context {A : Type}         `{Encode A} `{Encode (G A)}.

    (* ------------------------------------------------------------------------ *)
    (** Specification of [invert]. *)

    (* ∀ iter t, iterv iter t ≜ [fun f -> iter f t]. *)
    Definition iterv iter t :=
      VClo [("iter", iter); ("t", t)]
        (Anon ("f" => EApp
                       (EApp
                          (EPath ["iter"])
                          (EPath ["f"]))
                       (EPath ["t"]))).

    Definition env := ("Yield", (VLoc yield_eff)) :: stdlib_env.

    Definition invert_spec invert : iProp Σ :=
      ∀ (T : G A) (iter : val),
      (∀ ψ, isIter T ψ iter) -∗
      EWP (call_anonfun env invert [iterv iter #T])
        {{ lift_ret_spec (λ k, isSeq T ⊥ k []) }}.

  End specification.


  Section invert_correct.
    Context `{!osirisGS Σ}.
    Context  {G : Type → Type} `{DataStructure G, Iterable G}
             {A : Type}         `{Encode A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.


    Ltac get_outcome_from_match e :=
    lazymatch e with
    | (pre_eval_match_aux _ _ _ ?o _ _) => constr:(o)
    | (deep_handler_body _ ?o _ _) => constr:(o)
    | (shallow_handler_body _ ?o _ _) => constr:(o)
    end.
    Ltac trivial_post_instantiation :=
      lazymatch goal with
      | |- envs_entails _ ?G =>
          lazymatch G with
          | ewp_def _ ?e _ _ =>
              lazymatch (get_outcome_from_match e) with
              | O3Ret _ => constr:(True)
              | O3Throw _ => constr:(True)
              | O3Perform _ _ => constr:(True \/ True)
              end
          end
      end.
    Ltac skip_matching_branch :=
      let φ2 := trivial_post_instantiation in
      iApply (handle_cons _ _ _ _ _ _ _ _ _ (λ _, False) φ2);
      [ specify_cpattern; pattern_match
      | iIntros (? [])
      | iIntros (_) ].
    Ltac skip_non_matching_branch :=
      iApply handle_cons_skip; [ reflexivity | ].
    Ltac skip_branch :=
      (skip_non_matching_branch || skip_matching_branch);
      fold deep_handler_body; fold shallow_handler_body.
    Ltac enter_branch :=
      iApply (handle_cons with "[-]");
      [ specify_cpattern; pattern_match; try (apply eq_refl)
      | (iIntros (? ->) || iIntros (? <-))
      | let F := fresh in iIntros (F); tauto ].

    (* Try to reduce a [match] expression by skipping all branches seen and then
     entering a branch on match. *)
    Ltac red_match := repeat (skip_branch; [ idtac ]); enter_branch.

    Ltac ewp_call_anonfun :=
      (* Unfold [call_anonfun], and get a tower of binds. *)
      rewrite /call_anonfun; simpl; rewrite ?bind_bind;
      (* Unfold [eval_anonfun]. *)
      rewrite /eval_anonfun;
      (* Simplify the tower of binds,
        this should elaborate a closure capturing all arguments.  *)
      repeat (iApply ewp_bind; Simp; Ret);
      simpl.

    (* Non-recursive call. *)
    Ltac Call :=
      match goal with
      | |- envs_entails _ (ewp_def _ (call_anonfun _ _ _) _ _) =>
          ewp_call_anonfun; iApply ewp_call_nonrec
      end.

    Definition invert := __fun9.

    Definition ieq {PROP : bi} {A : Type} y := λ (x : A), @bi_pure PROP (x = y).

    Lemma yield_handler_correct (iter : val) γ (Ys : list A) (T : G A) :
      handlerView γ Ys -∗
      deep_handler_spec ⊤ (ψ_yield T (iterView γ))
        (λ _ : outcome2 val exn, ∃ Xs : list A, iterView γ Xs ∗ ⌜complete T Xs⌝)
        (λ o : code.outcome3 val exn,
            deep_handler_body
              ("__osiris_anonymous_arg" ~> VUnit;
               "yield" ~> VClo ("iter" ~> iterv iter #T;
                                "__osiris_anonymous_arg" ~> iterv iter #T;
                                env) __fun0;
               "iter" ~> iterv iter #T;
               "__osiris_anonymous_arg" ~> iterv iter #T;
               env) o __branches3 __branches3) ⊥ (RET h, isHead T ⊥ h Ys).
    Proof.
      iLöb as "IH" forall (Ys γ).
      iIntros "HhandlerView".
      rewrite deep_handler_spec_unfold /deep_handler_spec_pre.
      iSplit.
      { iIntros (o) "[%Xs [HiterView %Hcomplete]]".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        iModIntro.
        destruct o; red_match;
          with_strategy transparent [evals] Simp; Ret;
          by iPureIntro. }

      { iIntros (v k) "HProt".
        rewrite /prot; iPoseProof (upcl_yield with "HProt") as "HProt".
        iDestruct "HProt" as "[%Xs [%X [-> [[HiterView %Hpermitted] HProt]]]]".
        iModIntro.
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        iApply ewp_fupd. iMod (update_cell γ (Ys ++ [X]) with "HhandlerView HiterView")
          as "[HhandlerView HiterView]"; iModIntro.
        red_match.
        with_strategy transparent [evals] Simp. Ret. simpl.
        iExists _, _. iSplit; [ iPureIntro; reflexivity | ]. iSplit; [ by iPureIntro | ].
        iModIntro.
        rewrite !isSeq_unfold /isSeq_pre.
        with_strategy transparent [extend] Simp.
        Bind. rewrite /as_cont. Bind. Simp. Ret. Bind.
        with_strategy transparent [evals] Simp. Ret. simpl.
        iApply ("HProt" with "HiterView").
        iModIntro.
        iSpecialize ("IH" $! (Ys ++ [X]) γ with "HhandlerView").
        rewrite /deep_handler_spec seal_eq.
        iApply "IH". }
    Qed.

   Lemma ewp_invert : ⊢ @invert_spec _ _ G _ _ A _ _ invert. simpl.
      iIntros (T iter) "Hiter".
      iApply ewp_fupd.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]"; iModIntro.

      rewrite /call_anonfun; simpl; rewrite ?bind_bind.
      rewrite /eval_anonfun.
      iApply ewp_bind. Simp. Ret. simpl.

      iApply ewp_call_nonrec.
      iApply ewp_EMatch.
      iApply (ewp_deep_handler _ ⊥ (ieq ?[y])).

      { Simp. by Ret. }

      rewrite /ieq.

      rewrite deep_handler_spec_unfold; iSplit; last first.
      (* Effectful case: we don't allow effect (TODO: automate). *)
      { iModIntro. iIntros (??) "HF".
        by iPoseProof (upcl_bottom with "HF") as "F". }

      iModIntro. iIntros (? ->). iModIntro.
      enter_branch.

      (* [let open struct ...] *)
      iApply ewp_ELetOpen.
      with_strategy transparent [eval_mexpr] Ret. simpl.
      iExists _; iSplit; [ done | ].

      (* [let yield x = ...] *)
      iApply (ewp_ELet_singleton_total (ieq ?[y])).
      { Simp. by Ret. }
      iIntros (? ->).
      iExists _; iSplit.
      { iPureIntro.
        eapply prove_simp_try.
        { with_strategy transparent [extend] apply SimpReflexive. }
        apply SimpReflexive. }

      (* fun () -> match iter yield with ... *)
      Simp. Ret. simpl. rewrite isSeq_unfold /isSeq_pre.

      iApply ewp_call_nonrec.
      iModIntro.
      iApply ewp_EMatch.
      iApply (ewp_deep_handler _ _ (ieq ?[y])).

      { Simp. by Ret. }

      rewrite /__branches4.
      rewrite deep_handler_spec_unfold; iSplit; last first.
      { iIntros (??) "HF".
        by iPoseProof (upcl_bottom with "HF") as "F". }
      iIntros (? ->). iModIntro.

      enter_branch.

      (* [match_with iter yield { ...] *)
      iApply ewp_EMatch.
      iApply (ewp_deep_handler
                (* E: *)
                ⊤
                (* Handlee's protocol: *)
                (ψ_yield T (iterView γ))
                (* Handlee's postcondition: *)
                (λ _, ∃ (Xs : list A), iterView γ Xs ∗ ⌜ complete T Xs ⌝)%I
                (* Handler's protocol: *)
                ⊥
                (* Handler's postcondition: *)
                (lift_ret_spec (λ h, isHead T ⊥ h [])) with "[Hiter HiterView] [HhandlerView]").

      { Simp. Bind.
        iApply (ewp_pers_mono with "[-]").
        { iApply ("Hiter" with "[] HiterView").
          iIntros "!#" (Xs X) "%Hpermitted HI".
          with_strategy transparent [evals] Simp.
          iApply ewp_perform.
          rewrite /prot. iApply upcl_yield.
          iExists _, _.
          iSplit; [ equality | ]. iFrame. iSplit; [ by iPureIntro | by iIntros "?" ]. }
        iIntros "!#" ([|]); [ by iIntros "?" | done ]. }

      { iApply (yield_handler_correct with "HhandlerView"). }
   Qed.

End verification.
