From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import osiris.
From osiris.libs Require Import Stdlib.
From test Require Import records.

Local Transparent eval. (* TODO. *)

(* -------------------------------------------------------------------------- *)

Context `{!osirisGS_gen hlc Σ}.

(* -------------------------------------------------------------------------- *)

(* Local defintiion of the record type used in [records.ml]. *)

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

(* -------------------------------------------------------------------------- *)

(* Definition of some values; useful to write the specs below. *)
Definition enc_r_elt : val := #{| b := true; i := 10 |}.
Definition enc_r_elt' : val := #{|b := false; i := 10|}.
Definition enc_lily : val := # [enc_r_elt; enc_r_elt'].

(* -------------------------------------------------------------------------- *)

(* Definition of the specifications. *)

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
  ∀ (i: Z) (b: bool),
    let r := {| b := b; i := i |} in
    WP call r_val #r
       {{ λ result, is_equal result #(r_val_pure r) }}.

Definition sum_pure (r1 r2: R) : Z :=
  r_val_pure r1 + r_val_pure r2.
Definition sum_spec (vsum: val) : iProp Σ :=
  ∀ (b1 b2: bool) (i1 i2: Z),
    let r1 := {| b := b1; i := i1 |} in
    let r2 := {| b := b2; i := i2 |} in
    WP call vsum #r1 {{
          λ vpart,
          WP call vpart #r2 {{
                λ res,
                is_equal res # (sum_pure r1 r2) }} }}.

(* -------------------------------------------------------------------------- *)

(* Proof of the module [Records] in which the function bodies have not been
   turned opaque. *)

Ltac wp_simp :=
  progress (iApply wp_simp; first by simp); wp.

Lemma Records_spec :
    let Λ :=
      [
        ("is_odd", trivial_spec) ;
        ("is_odd_naive", trivial_spec) ;
        ("sum", sum_spec) ;
        ("r_val", r_val_spec) ;
        ("lily", is_equal enc_lily) ;
        ("flip", flip_spec) ;
        ("r_elt", is_equal enc_r_elt)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Records {{ module_spec Λ }}.
Proof.
  intros Λ η. wp.
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
  wp_simp.
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
  { iIntros (i [|]).
    (* Case: [b] is true. *)
    { wp_call. by do 2 wp_continue. }
    { wp_call. by do 2 wp_continue. } }
  iIntros (r_val) "#Hr_val". wp_continue.


  (* [sum] is given the trivial spec for now. *)
  wp_specify "sum" sum_spec.
  { iIntros(b1 b2 i1 i2). wp_call. do 2 wp_continue.
    wp.
    wp_par.
    2: by wp_use "Hr_val".
    { wp_use "Hr_val". iIntros(?<-).
      apply tc_change_goal. iIntros (vpartial).
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

  (* TODO: uncomment the calls to [sum] and [List.fold_left] *)

  (* Every spec has been proven: [wp_module_spec] can finish the proof. *)
  wp_module_spec.
Time Qed.

(* -------------------------------------------------------------------------- *)

(* Definition of function bodies.  These are the bodies of functions which will
   be proven. The goal is to see if it is easier to specify each of these bodies
   before the main proof. *)

(* Body of [flip]. *)
Definition flip_body (r: var) :expr :=
  ERecordUpdate (EPath (PathBase r))
                (FECons
                   "b"
                   (EApp (EPath (PathDot (PathBase "Stdlib") "not"))
                         (ERecordAccess (EPath (PathBase r)) "b")) FENil).

Definition is_odd_body : expr :=
  EApp
    (EApp (EPath (PathDot (PathBase "Stdlib") "=")) $
          EApp (
            EApp (EPath (PathDot (PathBase "Stdlib")
                                 "mod")) $
                 EPath (PathBase "n"))
          (EInt 2))
    (EInt 0).

Definition is_odd_naive_body : expr :=
  ESeq
    (EAssert $
             EApp
             (EApp (EPath (PathDot (PathBase "Stdlib") ">="))
                   (EPath (PathBase "n"))) $
             EInt 0) $
    EIfThenElse (
      EApp
        (EApp (EPath (PathDot (PathBase "Stdlib") ">"))
              (EPath (PathBase "n")))
        (EInt 1))
    (EApp (EPath (PathBase "is_odd_naive")) $
          EApp
          (EApp (EPath (PathDot (PathBase "Stdlib")
                                "-"))
                (EPath (PathBase "n")))
          (EInt 2)) $
    EIfThenElse (
      EApp (
          EApp (EPath (PathDot (PathBase "Stdlib")
                               "="))
               (EPath (PathBase "n")))
           (EInt 0))
    (EData "false" (ETuple ENil))
    (EData "true" (ETuple ENil))
.

Definition sum_body : expr :=
  EApp (
      EApp (EPath (PathDot (PathBase "Stdlib") "+")) $
           EApp (EPath (PathBase "r_val"))
           (EPath (PathBase "r1"))
    ) $
       EApp (EPath (PathBase "r_val"))
       (EPath (PathBase "r2"))
.
Definition r_elt_body : expr :=
  ERecord (
      FECons "i"
             (EInt 10)
              (FECons "b" (EData "true" (ETuple ENil)) FENil)).

Definition lily_body : expr :=
  EData "::"
        $ ETuple  $
        ECons (EPath (PathBase "r_elt")) $
        ECons
        (EData "::"
               (ETuple $
                       ECons (
                         EApp (EPath (PathBase "flip"))
                              (EPath (PathBase "r_elt"))) $
                       ECons (EData "[]" (ETuple ENil))
                       ENil))
        ENil
.

Definition r_val_body (r: var) : expr :=
  EMatch (ERecordAccess (EPath (PathBase r)) "b") $
         MkBranches
         [ Branch (PBool true) $
                  EApp (
                    EApp (EPath (PathDot (PathBase "Stdlib") "-"))
                         (EApp (
                              EApp (EPath (PathDot (PathBase "Stdlib")
                                                   "*"))
                                   (ERecordAccess (EPath (PathBase r)) "i")
                            )
                               (EInt 2)
                         )
                  )
                  (EInt 1)
           ; Branch (PBool false)
                    (ERecordAccess (EPath (PathBase r)) "i")
         ]
.

Definition Opacified_Records : mexpr :=
  MkStruct [
      ILet (Binding1 (PVar "r_elt") r_elt_body)
      ;
      ILet (Binding1 (PVar "flip")
                     (EAnonFun (
                          AnonFun1Pat (PVar "r")
                                      (flip_body "r"))))
      ;
      ILet (Binding1 (PVar "lily") lily_body)
      ;
      ILet $
          Binding1 (PVar "r_val") $
                   EAnonFun ( AnonFun1Pat (PVar "r") (r_val_body "r"))
      ;
      ILet $
           Binding1 (PVar "sum") $
           EAnonFun $
           AnonFun1Pat (PVar "r1") $
           EAnonFun $
           AnonFun1Pat (PVar "r2") $
           sum_body
      ;
      ILetRec $
          RecBiCons
          (RecBinding "is_odd_naive" $
           AnonFun1Pat (PVar "n") $
           is_odd_naive_body)
          RecBiNil
      ;
      ILet $
           Binding1 (PVar "is_odd") $
           EAnonFun $
           AnonFun1Pat (PVar "n") $
           is_odd_body
    ].

Lemma Records_eq :
  Records =
    Opacified_Records.
Proof. reflexivity. Qed.


(* Bodies are turned opaque. *)
Opaque
  flip_body
  lily_body
  is_odd_body
  is_odd_naive_body
  r_val_body
.

(* -------------------------------------------------------------------------- *)

(* Specifications of function bodies. *)

Lemma flip_body_spec :
  ∀ (r: var) (b: bool) (i: Z) η,
    lookup_name η "Stdlib" = ret Stdlib →
    lookup_name η r = ret #{| b := b; i := i |} →
    simp (eval η (flip_body r))
         (ret #{| b := negb b; i := i |}).
Proof.
  with_strategy transparent [flip_body] unfold flip_body.
  intros r [] i η Hstdlib Hr; simp;
    (eapply prove_simp_bind;
     [ with_strategy transparent [ Stdlib__not ] unfold Stdlib__not;
       with_strategy transparent [ call ] unfold call; simp
     | simp ]).
Qed.

Lemma lily_body_spec η η' :
  let clo_flip := VClo η' (AnonFun1Pat (PVar "r") (flip_body "r")) in
  (* Thefollowing is required to use [flip_body_spec]. *)
  lookup_name η' "Stdlib" = ret Stdlib →
  lookup_name η "r_elt" = ret enc_r_elt →
  lookup_name η "flip" = ret clo_flip →
  lookup_name η "Stdlib" = ret Stdlib →
  simp (eval η lily_body) (ret enc_lily).
Proof.
  intros ? ? Hrelt Hflip Hstdlib.
  with_strategy transparent [lily_body] unfold lily_body.
  simp.
  rewrite Hrelt; simp.
  eapply prove_simp_bind.
  { with_strategy transparent [call] unfold call.
    simpl. simp.
    with_strategy transparent [ concatenating ] (unfold concatenating at 1).
    eapply flip_body_spec; try done.
    (* FIXME. *)
    instantiate (1 := 10). instantiate (1 := true).
    done. }
  simp.
Qed.

Ltac rew name :=
  with_strategy transparent [ name ] unfold name.

Arguments String.eqb !s1 !s2 : simpl nomatch. (* TODO *)
Lemma r_val_body_spec η (r: R) (rvar: var) :
  lookup_name η "Stdlib" = ret Stdlib →
  lookup_name η rvar = ret #r →
  simp (eval η (r_val_body rvar)) (ret #(r_val_pure r)).
Proof.
  rew r_val_body.
  intros??. destruct (r.(b)) eqn:E;
    simp; rewrite E; simp; simp_continue;
    rewrite /r_val_pure E; simp.
  rew Stdlib__mul. rew Stdlib__sub. rew call.
  simp.
  rewrite int.mul_repr_repr
          int.sub_repr_repr.
  simp.
Qed.

Global Instance simp_reflexive {A} : Reflexive (@simp A) :=
  SimpReflexive.
Global Instance simp_transitive {A} : Transitive (@simp A) :=
  SimpTransitive.

Lemma sum_body_spec η (r1 r2: R):
  lookup_name η "r1" = ret #r1 →
  lookup_name η "r2" = ret #r2 →
  lookup_name η "Stdlib" = ret Stdlib →
  lookup_name η "r_val" = (eval η (EAnonFun $ AnonFun "r" (r_val_body "r"))) →
  simp (eval η sum_body) (ret #(sum_pure r1 r2)).
Proof.
  intros H1 H2 H3 H4.
  rew sum_body. simp. rewrite H1 H2 H4. rew call.
  cbn.
  etransitivity; first (apply SimpPar; simp).
  etransitivity;
    first (apply SimpPar;
           [ apply simp_bind; by apply r_val_body_spec
           | solve [simp] ]).
  simp.
  etransitivity; first (apply simp_bind; by apply r_val_body_spec).
  simp.
  unfold sum_pure.
  rewrite int.add_repr_repr.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [wp] and [wp_continue] do *not* respect the opacity of the above expressions.
   This is caused by [apply tc_change_goal] in [wp]which tries to simplify the
   goal using any instance of [TC_change_goal]. *)

Ltac wp' := wp.
Ltac wp'_continue := wp_continue.

Ltac wp :=
  iStartProof; cbn;
   repeat
    lazymatch goal with
    | |- environments.envs_entails _ (▷ _) => iNext
    | _ => wp_step; try progress cbn
    end.

Ltac wp_continue :=
  lazymatch goal with
  | |- environments.envs_entails
         _ (wp _ _ (concatenating eval _ _ ?δ) _) =>
      with_strategy transparent [ concatenating ] (unfold concatenating at 1)
  | |- environments.envs_entails
         _ (wp _ _ (dconcatenating ?δ _) _) =>
      with_strategy transparent [ dconcatenating ] (unfold dconcatenating at 1)
  end; wp.

Ltac wp_simp_using H :=
  iApply wp_simp; [ by apply H | wp ].

Lemma Records_spec_bodies :
    let Λ :=
      [
        ("is_odd", trivial_spec) ;
        ("is_odd_naive", trivial_spec) ;
        ("sum", sum_spec) ;
        ("r_val", r_val_spec) ;
        ("lily", is_equal enc_lily) ;
        ("flip", flip_spec) ;
        ("r_elt", is_equal enc_r_elt)
    ]
  in
  let η := EnvCons "Stdlib" Stdlib $
           EnvNil in
  ⊢ WP eval_mexpr η Records {{ module_spec Λ }}.
Proof.
  rewrite Records_eq.

  (* Proof using [simp]. *)
  intros ??. wp.
  simpl (build _ _). wp.

  wp_specify "r_elt" (is_equal enc_r_elt); first done.
  iIntros(?->). wp_continue.

  wp_continue.
  iApply wp_simp.
  { by eapply lily_body_spec; try done. }

  wp. wp_continue.

  (* [r_val] has the expected value. *)
  wp_specify "r_val" r_val_spec.
  { iIntros (i[|]).
    (* Case: [b] is true. *)
    { wp_call. wp'_continue.
      iApply wp_simp; first eapply r_val_body_spec.
      - done.
      - by instantiate (1 := {| b := true; i := i |}).
      - by wp. }
    { wp_call. wp'_continue.
      iApply wp_simp; first eapply r_val_body_spec.
      - done.
      - by instantiate (1 := {| b := false; i := i |}).
      - by wp. } }
  iIntros (r_val) "#Hr_val". wp_continue.


  (* [sum] is given the trivial spec for now. *)
  wp_continue.

  (* [is_odd_naive] is given the trivial spec for now. *)
  wp_specify "is_odd_naive" trivial_spec; first done.
  iIntros (is_odd_naive) "#His_odd_naive". wp_continue.

  (* [is_odd] is given the trivial spec for now. *)
  wp_specify "is_odd" trivial_spec; first done.
  iIntros (is_odd) "#His_odd". wp_continue.


  lazymatch goal with
  | |- environments.envs_entails _ (?φ (VStruct ?η)) =>
      iExists _; iSplit ; first (iPureIntro; reflexivity)
  end.
  cbn; repeat iSplitL; try (iExists _; iSplit; first done); try done.
  { (* Proof of the [sum] function.*)
    iIntros(b1 b2 i1 i2).
    wp_call. wp_continue. wp_continue.
    wp_par.
    - wp_use "Hr_val".
      iIntros(?<-).
      wp_call. wp_set_postcondition.
    - wp_use "Hr_val".
    - iIntros (v1 v2 -> <-). wp.
      wp_call.
      iPureIntro. unfold sum_pure;
        destruct b1, b2; cbn;
        by rewrite int.add_repr_repr. }
  { (* Proof of the [flip] function. *)
    iIntros(??); wp_call. wp_continue.
    by wp_simp_using flip_body_spec. }
Time Qed.
