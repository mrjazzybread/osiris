From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test.records Require Import records records_code.

(* -------------------------------------------------------------------------- *)

(* Table of content of the file:
   1. Definition of an instance of [Encode] for the a Coq-type representing
      OCaml records of type [{ b: bool; i: int }].
   2. Definitions of values (of type [val]) representing OCaml values appearing
      in the proofs.
   3. Definitions of specifications for elements of the module.
   4. Proofs that each function body respects its specification
      (These are used in the caller-side-reasoning style proof below.)
   5. Proofs that each function respects its specification
      (These are used in the callee-side-reasoning style proof below.)
   6. Proof of the module (Caller-side reasoning).
   7. Proof of the module (Callee-side reasoning).
   8. Direct proof of the module (in one lemma).

Efficiency of 4--5: TODO.

Efficiency of 6--8: TODO. *)

(* -------------------------------------------------------------------------- *)

(* Make sure that the modules [Record] (defined in [records.v]) and
   [opacified_Records] (defined in [records_code.v]) coincide. *)
Goal opacified_Records = Records.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

Local Transparent eval. (* TODO. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS_gen hlc Σ}.

(* -------------------------------------------------------------------------- *)

(* (1) Local defintion of the record type used in [records.ml]. *)

Record R :=
  { b: bool ;
    i: Z }.

Local Instance r_encode : Encode R :=
  { encode :=
    fun (r: R) =>
      VRecord $
              EnvCons "b" #(r.(b)) $
              EnvCons "i" #( r.(i)) $
              EnvNil }.

Lemma solve_encode_R b i vb vi :
  vb = #b →
  vi = #i →
  VRecord $
    EnvCons "b" vb $
    EnvCons "i" vi $
    EnvNil
  = #{| b := b; i := i |}.
Proof. intros. subst. reflexivity. Qed.

Local Hint Resolve solve_encode_R : encode.

(* TODO FIXME there is already an instance of [Encode nat] in encode.v *)
Fixpoint nat_encode_f (n : nat) : val :=
  match n with
  | O => VData "O" $ VTuple VNil
  | S n => VData "S" $ VTuple $ VCons (nat_encode_f n) VNil
  end.

Local Instance nat_encode : Encode nat :=
  { encode := nat_encode_f }.

(* -------------------------------------------------------------------------- *)

(* (2) Definition of some values; useful to write the specs below. *)
Definition enc_r_elt : val := #{| b := true; i := 10 |}.
Definition enc_r_elt' : val := #{|b := false; i := 10|}.
Definition enc_lily : val := # [enc_r_elt; enc_r_elt'].

(* -------------------------------------------------------------------------- *)

(* (3) Definition of specifications. *)

(* [is_equal] asserts the equality of two values. *)
Definition is_equal v : val → iProp Σ :=
  λ res, ⌜ res = v ⌝%I.

(* [trivial_spec] is a dummy specification. *)
Definition trivial_spec (v: val) : iProp Σ :=
  ⌜ True ⌝.

(* [flip] negates [b] in records of type [{ b: bool; i: int}]. *)
Definition flip_spec (v : val) : iProp Σ :=
  ∀ (b: bool) (i: Z),
    WP call v #{| b := b; i := i |}
    {{ λ r, is_equal r #{| b := negb b; i := i |} }}.

(* [r_val_spec] performs a different arithmetic computation depending on the
   fiels [b] of a record. *)
Definition r_val_pure (r: R) : Z :=
  match r.(b) with
  | true => r.(i) * 2 - 1
  | false => r.(i)
  end.

Definition r_val_spec (r_val: val): iProp Σ :=
  ∀ (r: R),
    WP call r_val #r
       {{ λ result, is_equal result #(r_val_pure r) }}.

Definition sum_pure (r1 r2: R) : Z :=
  r_val_pure r1 + r_val_pure r2.
Definition sum_spec (vsum: val) : iProp Σ :=
  ∀ (r1 r2 : R),
    WP call vsum #r1 {{
          λ vpart,
          WP call vpart #r2 {{
                λ res,
                is_equal res # (sum_pure r1 r2) }} }}.

Fixpoint is_odd_pure (n: nat) :bool :=
  match n with
  | O => true
  | S n => negb (is_odd_pure n)
  end.

Definition is_odd_spec (vis_odd: val) : iProp Σ:=
  ∀ (n : nat),
  WP call vis_odd #n {{ is_equal #(is_odd_pure n) }}.

(* -------------------------------------------------------------------------- *)

(* Specification of the module. *)
Definition Λ :=
  [
    ("is_odd", trivial_spec) ;
    ("is_odd_naive", trivial_spec) ;
    ("sum", sum_spec) ;
    ("r_val", r_val_spec) ;
    ("lily", is_equal enc_lily) ;
    ("flip", flip_spec) ;
    ("r_elt", is_equal enc_r_elt) ;
    ("is_odd'", is_odd_spec)
  ].

(* -------------------------------------------------------------------------- *)

(* Staging area. *)

(* TODO making definitions opaque blocks the [simp] tactics
        and seems counter-productive. *)
Opaque
  r_elt_expr
  flip_body flip_function
  lily_expr
  r_val_body r_val_function
  sum_body sum_function
  is_odd'_body is_odd'_function
.

(* [explicit name] unfolds [name], even if transparent. *)
Ltac explicit name :=
  with_strategy transparent [ name ] unfold name.

(* [wp_simp] simplifies the element of type [free A] we are working on. *)
Ltac wp_simp :=
  progress (iApply wp_simp; first by simp).

Ltac wp_simp_using H :=
  iApply wp_simp; [ by apply H; try done | wp ].

Ltac wp_simp_eusing H :=
  iApply wp_simp; [ by eapply H; try done | wp ].

(* -------------------------------------------------------------------------- *)

(* (4) Specifications of function bodies. *)

Lemma r_elt_spec η :
  simp (eval η r_elt_expr) (ret enc_r_elt).
Proof.
  explicit r_elt_expr.
  simp.
Qed.

Lemma flip_body_spec :
  ∀ (b: bool) (r: var) (i: Z) η v,
    lookup_name η "Stdlib" = ret Stdlib →
    lookup_name η r = ret v →
    v = #{| b := b; i := i |} →
    simp (eval η (flip_body r))
         (ret #{| b := negb b; i := i |}).
Proof.
  explicit flip_body.
  intros b. destruct b; intros; subst; simp; simp_enter.
    (* [simp_enter] steps into the call to [Stdlib.not]. *)
Qed.

Local Hint Resolve flip_body_spec : simp_specs.

Lemma lily_body_spec η η' :
  let clo_flip := VClo η' (AnonFun1Pat (PVar "r") (flip_body "r")) in
  (* Requirements of [flip_body_spec]. *)
  lookup_name η' "Stdlib" = ret Stdlib →
  (* Requirements of [lily_body_spec] *)
  lookup_name η "r_elt" = ret enc_r_elt →
  lookup_name η "flip" = ret clo_flip →
  lookup_name η "Stdlib" = ret Stdlib →
  (* Actual spec. *)
  simp (eval η lily_expr) (ret enc_lily).
Proof.
  intros ? ? Hrelt Hflip Hstdlib.
  explicit lily_expr.
  simp.
  simp_enter.
  (* TODO more cleanup needed here *)
  eapply prove_simp_bind.
  { simp_continue. eapply flip_body_spec.
    + eauto with simp_specs.
    + eauto with simp_specs.
    + encode.  }
  simp.
Qed.

Lemma r_val_body_spec η (r: R) (rvar: var) :
  lookup_name η "Stdlib" = ret Stdlib →
  lookup_name η rvar = ret #r →
  simp (eval η (r_val_body rvar)) (ret #(r_val_pure r)).
Proof.
  explicit r_val_body.
  intros??. destruct (r.(b)) eqn:E;
    simp; rewrite E; simp; simp_continue;
    rewrite /r_val_pure E; simp. explicit call.
  simp.
Qed.

Lemma sum_body_spec η (r1 r2: R):
  lookup_name η "r1" = ret #r1 →
  lookup_name η "r2" = ret #r2 →
  lookup_name η "Stdlib" = ret Stdlib →
  lookup_name η "r_val" = (eval η (EAnonFun $ AnonFun "r" (r_val_body "r"))) →
  simp (eval η (sum_body "r1" "r2")) (ret #(sum_pure r1 r2)).
Proof.
  intros H1 H2 H3 H4.
  explicit sum_body. simp.
  explicit call. (* TODO weird *)
  simp.
  (* TODO more cleanup needed here *)
  etransitivity;
    first (apply SimpPar;
           [ apply simp_bind; by apply r_val_body_spec
           | solve [simp] ]).
  simp.
  etransitivity; first (apply simp_bind; by apply r_val_body_spec).
  simp.
Qed.

Lemma is_odd'_body_spec η η' r n :
  lookup_name η "Stdlib" = Ret Stdlib →
  lookup_name η' "Stdlib" = Ret Stdlib →
  lookup_name η "is_odd'" =
    Ret (VCloRec η' (RecBinding1 "is_odd'" is_odd'_function) "is_odd'") →
  lookup_name η r = Ret #n →
  simp (eval η (is_odd'_body r)) (Ret #(is_odd_pure n)).
Proof.
  generalize η r; clear η r;
  induction n as [ | n' IH ];
    intros η r H1 H2 H3 H4;
    explicit is_odd'_body.
  { simp. }
  { (* [n = S n'] *)
    destruct (is_odd_pure n') eqn:E;
    remember (nat_encode_f n') as enc_n.
    - (* [n'] is even. *)
      simp. simp_continue.
      eapply prove_simp_bind.
      + explicit is_odd'_function. (* TODO why is it opaque? *)
        simp_enter.
        eapply IH; eauto.
      + simp_enter.
        rewrite E.
        simp.
    - (* [n'] is odd. *)
      simp. simp_continue.
      eapply prove_simp_bind.
      + explicit is_odd'_function. (* TODO why is it opaque? *)
        simp_enter.
        eapply IH; eauto.
      + simp_enter.
        rewrite E.
        simp. }
Qed.

(* -------------------------------------------------------------------------- *)

(* (5) Specifications of functions. *)

Lemma flip_function_spec :
  ∀ η,
    lookup_name η "Stdlib" = Ret Stdlib →
    ⊢ ∃ vflip,
    ⌜simp (eval η flip_function) (Ret vflip)⌝
          ∗ flip_spec vflip.
Proof.
  intros? H1.
  iExists _.
  iSplit; first (iPureIntro; by simp).
  explicit flip_body.
  iIntros (b i).
  wp_call. wp_continue.
  rewrite H1. wp.
  simpl (build _ _). wp.
  iPureIntro. reflexivity.
Qed.

Lemma r_val_function_spec η :
  lookup_name η "Stdlib" = Ret Stdlib →
  ⊢ ∃ vr_val,
    ⌜simp (eval η r_val_function) (Ret vr_val)⌝
          ∗ r_val_spec vr_val.
Proof.
  intros H1.
  iExists _.
  iSplit; first (iPureIntro; by simp).
  by iIntros (r); explicit r_val_body; explicit r_val_pure;
  wp_call; destruct (b r); do 2 wp_continue; [ rewrite H1; wp | ].
Qed.

Lemma sum_function_spec η vr_val :
  lookup_name η "Stdlib" = Ret Stdlib →
  lookup_name η "r_val" = Ret vr_val →
  (* TODO: add the requirements of [sum_function]. *)
  ⊢ □ r_val_spec vr_val -∗
    ∃ vsum,
      ⌜simp (eval η sum_function) (Ret vsum)⌝ ∗ sum_spec vsum.
Proof.
  iIntros(??) "#Hr_val".
  iExists _.
  iSplit; first (iPureIntro; by simp).
  iIntros (r1 r2).
  explicit sum_body.
  wp_call; do 2 wp_continue.
  wp_simp.
  wp_par.
  { wp_use "Hr_val". iIntros (?<-). wp_call. wp_set_postcondition. }
  { wp_use "Hr_val". }
  iIntros (??-><-). wp.
  wp_call.

  explicit sum_pure.
  iPureIntro. rewrite int.add_repr_repr. reflexivity.
Qed.

Lemma is_odd'_function_spec η :
  let vis_odd' :=
    VCloRec η (RecBinding1 "is_odd'" is_odd'_function) "is_odd'" in
  lookup_name η "Stdlib" = Ret Stdlib →
  ⊢ is_odd_spec vis_odd'.
Proof.
  intros a H1; subst a. explicit is_odd'_function.
  iIntros (n); wp_call.
  by wp_simp_eusing is_odd'_body_spec.
Qed.

(* -------------------------------------------------------------------------- *)

(* (6) The following proof is written in caller-reasoning style. It exploits the
   above proofs on the function bodies. *)

Transparent
  flip_function
  r_val_function
  sum_function
.

Goal
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η opacified_Records {{ module_spec Λ }}.
Proof.
  (* Proof using [simp]. *)
  intros η. unfold η; clear η. wp.
  simpl (build _ _). wp.

  wp_simp_using r_elt_spec.
  wp_specify "r_elt" (is_equal enc_r_elt); first done.
  iIntros(?->). wp_continue.

  wp_continue.
  iApply wp_simp.
  { by eapply lily_body_spec; try done. }

  wp. wp_continue.

  (* [r_val] has the expected value. *)
  wp_specify "r_val" r_val_spec.
  { iIntros (r). explicit r_val_pure; destruct (b r) eqn:E;
      wp_call; wp_continue;
      (iApply wp_simp; first eapply r_val_body_spec); try done;
      explicit r_val_pure; rewrite E; by wp. }
  iIntros (r_val) "#Hr_val". wp_continue.


  (* [sum] is given the trivial spec for now. *)
  wp_continue.

  (* [is_odd_naive] is given the trivial spec for now. *)
  wp_specify "is_odd_naive" trivial_spec; first done.
  iIntros (is_odd_naive) "#His_odd_naive". wp_continue.

  (* [is_odd] is given the trivial spec for now. *)
  wp_specify "is_odd" trivial_spec; first done.
  iIntros (is_odd) "#His_odd". wp_continue.

  Opaque eval. (* TODO? *)
  wp_specify "is_odd'" is_odd_spec.
  { iIntros(n). explicit is_odd'_function.
    wp_call.
    by wp_simp_eusing is_odd'_body_spec. }
  iIntros (vis_odd') "#His_odd'"; wp_continue.
  Transparent eval.

  lazymatch goal with
  | |- environments.envs_entails _ (?φ (VStruct ?η)) =>
      iExists _; iSplit ; first (iPureIntro; reflexivity)
  end.
  cbn; repeat iSplitL; try (iExists _; iSplit; first done); try done.
  { (* Proof of the [sum] function.*)
    iIntros(r1 r2).
    wp_call. wp_continue. wp_continue.
    wp_par.
    - wp_use "Hr_val".
      iIntros(?<-).
      wp_call. wp_set_postcondition.
    - wp_use "Hr_val".
    - iIntros (v1 v2 -> <-). wp.
      wp_call.
      iPureIntro. unfold sum_pure;
        destruct (b r1), (b r2); cbn;
        by rewrite int.add_repr_repr. }
  { (* Proof of the [flip] function. *)
    iIntros(??); wp_call. wp_continue.
    iApply wp_simp.
    { eapply flip_body_spec; eauto with simp_specs. }
    by wp. }
Time Qed.

(* TODO making definitions opaque blocks the [simp] tactics
        and seems counter-productive. *)
Opaque
  flip_function
  r_val_function
  sum_function
.

(* -------------------------------------------------------------------------- *)


(* (7) The following proof is written in callee-reasoning style. It exploits the
   above proofs on the function expressions. *)

Goal
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η opacified_Records {{ module_spec Λ }}.
Proof.
  intros?.
  wp.

  wp_simp_using r_elt_spec.
  wp_specify "r_elt" (is_equal enc_r_elt); first done.
  iIntros (?->). wp_continue.

  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (eval ?η flip_function) _) =>
      iPoseProof (flip_function_spec η)
      as "[%vflip [%Hflip_simp #Hflip_spec]]";
      first reflexivity
  end.
  wp_simp_using Hflip_simp. wp_continue.

  explicit lily_expr.
  wp. wp_simp. wp.

  replace (VRecord _) with #{| b := true ;i := 10|}; last reflexivity.
  wp_use "Hflip_spec". iIntros(?<-). wp.
  wp_continue.


  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (eval ?η r_val_function) _) =>
      iPoseProof (r_val_function_spec η)
      as "[%vr_val [%Hr_val_simp #Hr_val_spec]]";
      first reflexivity
  end.
  wp_simp_using Hr_val_simp. wp_continue.

  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (eval ?η sum_function) _) =>
      iPoseProof ((sum_function_spec η) with "Hr_val_spec")
      as "[%vsum [%Hsum_simp #Hsum_spec]]";
      try reflexivity
  end.
  wp_simp_using Hsum_simp. wp_continue.

  wp_specify "is_odd_naive" trivial_spec; first done.
  iIntros (?) "?". wp_continue.
  wp_specify "is_odd" trivial_spec; first done.
  iIntros (?) "?". wp_continue.

  wp_specify "is_odd'" is_odd_spec.
  { by iApply is_odd'_function_spec. }
  iIntros (?) "#?". wp_continue.

  wp_module_spec.
Time Qed.

(* -------------------------------------------------------------------------- *)

(* (8) Proof of the module [Records] in which the function bodies have not been
   turned opaque. *)

Lemma Records_spec :
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Records {{ module_spec Λ }}.
Proof.
  intros η. wp.
  simpl (build _ _). wp.

  (* [r_elt] is a known value. *)
  wp_specify "r_elt" (is_equal enc_r_elt); first done.
  (* There is no need to keep the "spec" of [r_elt] around.*)
  iIntros (r_elt) "->". wp_continue.

  (* [flip] has the expected spec. *)
  wp_specify "flip" flip_spec.
  { iIntros (b i); wp_call.
    wp_continue. simpl (build _ _). wp. done. }
  iIntros (flip) "#Hflip". wp_continue.

  (* [flip] is applied to [r_elt]. *)
  wp_simp. wp.
  replace
    (VRecord (EnvCons "b" VTrue (EnvCons "i" (VInt (int.repr 10)) EnvNil)))
    with #{| b := true; i := 10 |}; last reflexivity.
  wp_use "Hflip".
  iIntros (? <-). wp.

  (* [lily] has the expected value. *)
  wp_specify "lily" (is_equal enc_lily).
  { iPureIntro. reflexivity. }
  iIntros (lily) "#Hlily". wp_continue.


  (* TODO: uncomment the call to [List.rev]. *)

  (* [r_val] has the expected value. *)
  wp_specify "r_val" r_val_spec.
  { iIntros ([[|] i]).
    (* Case: [b] is true. *)
    { wp_call. by do 2 wp_continue. }
    { wp_call. by do 2 wp_continue. } }
  iIntros (r_val) "#Hr_val". wp_continue.


  (* [sum] is given the trivial spec for now. *)
  wp_specify "sum" sum_spec.
  { iIntros([b1 i1] [b2 i2]). wp_call. do 2 wp_continue.
    wp.
    wp_simp.
    wp_par;
    (replace (VRecord (EnvCons "b" (VBool b1) $ EnvCons "i" (VInt (int.repr i1)) EnvNil))
      with (#{| b:=b1; i:= i1|}); last reflexivity);
    (replace (VRecord (EnvCons "b" (VBool b2) $ EnvCons "i" (VInt (int.repr i2)) EnvNil))
      with (#{| b:=b2; i:= i2|}); last reflexivity).
    2: by wp_use "Hr_val".
    { wp_use "Hr_val". iIntros(?<-).
      wp. iIntros (vpartial).
      iIntros "H"; iExact "H". }
    { iIntros (v1 v2) "Hadd <-".
      wp. iApply (wp_covariant with "Hadd").
      iIntros (?->). iPureIntro. reflexivity. } }
  iIntros (sum) "#Hsum". wp_continue.

  (* [is_odd_naive] is given the trivial spec for now. *)
  wp_specify "is_odd_naive" trivial_spec; first done.
  iIntros (is_odd_naive) "#His_odd_naive". wp_continue.

  (* [is_odd] is given the trivial spec for now. *)
  wp_specify "is_odd" trivial_spec; first done.
  iIntros (is_odd) "#His_odd". wp_continue.

  wp_specify "is_odd'" is_odd_spec.
  { iLöb as "IH". iIntros([|]); wp_call; wp_continue.
    { done. }
    { replace (nat_encode_f n) with #n; last reflexivity.
      iApply (wp_covariant with "IH").
      iIntros (?->).
      destruct (is_odd_pure n) eqn:E;
      by wp_call. } }
  iIntros (vis_odd') "#His_odd'". wp_continue.

  (* Every spec has been proven: [wp_module_spec] can finish the proof. *)
  wp_module_spec.
Time Qed.
