From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import weakestpre.
From iris.prelude Require Import options.
Import uPred.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import program_logic.

(* This file should move to the [proofmode] directory. *)

(* --------------------------------------------------------------------------*)
(* The following part defines module specifications. *)

From iris.base_logic Require Import iprop.

Section Modules.
 Context {Σ : gFunctors}.

 (* [spec_env] is the type of module specifications. *)
 Definition spec_env : Type :=
   list (var * (val → iProp Σ)).

 (* Last two points of the description of [module_spec] below. *)
 Let module_spec_list (Λ : spec_env) (η: env) : iProp Σ :=
   [∗ list] '(x, φx) ∈ Λ,
     ∃ v, ⌜lookup_name η x = Ret v⌝ ∗ φx v.

 (* [module_spec Λ] is a predicate over values which asserts that:
    1. the value represents a module
    2. the module contains least the elements present in [Λ]
    3. every field present in [Λ] satisfy its spec. *)
 Definition module_spec (Λ : spec_env) (v: val) : iProp Σ :=
   ∃ η, ⌜ v = VStruct η ⌝ ∗ module_spec_list Λ η.

 (* [is_module] is the pure counterpart of [module_spec]. It asserts the first
    two points listed above. *)
 Definition is_module (Λ : list name) (v : val) : Prop :=
   ∃ (η : env),
     v = VStruct η ∧
     foldr (λ n P, (∃ (vn : val), lookup_name η n = Ret vn) ∧ P) True Λ.

 (* -------------------------------------------------------------------------- *)

 (* [spec_env_erase] takes a module specification and only keeps the
    under-approximation of its domain. *)
 Fixpoint spec_env_erase  (Λ : spec_env) : list name :=
   match Λ with
   | (n, _) :: Λ => n :: (spec_env_erase Λ)
   | [] => []
   end.

 (* ------------------------------------------------------------------------- *)

 (* If a module satisfies some specification [Λ], it at least defines the domain
    specified in [Λ]. *)
 Lemma module_spec_is_module vmod  (Λ : spec_env) :
   module_spec Λ vmod ⊢
   ⌜is_module (spec_env_erase Λ) vmod⌝.
 Proof.
   iInduction Λ as [|[h ?] t] "IHΛ".
   { iDestruct 1 as "(% & -> & _)". by iExists _. }

   { iDestruct 1 as "(% & -> & H)".
     iExists _.
     iSplit; first (iPureIntro; reflexivity).
     rewrite/module_spec_list/=.
     iDestruct "H" as "[(%vname&%Hvname&_) Ht]".
     iSplit; first by iExists vname.

     iAssert (module_spec t (VStruct η)) with "[Ht]" as "Ht".
     { iExists _; iSplit; [ iPureIntro; reflexivity | iExact "Ht" ]. }

     iPoseProof ("IHΛ" with "Ht") as "[% [%Heq H]]".
     simplify_eq/=.
     iExact "H". }
 Qed.

 (* ------------------------------------------------------------------------- *)
 (* This part of the section defines total applications to convert a value seen
    as a module-value into its environment and to fetch a value in an
    environment. *)

 Let totalify {A B} (f: A → free B) (dummy : B) : A → B :=
   λ (a : A), match f a with
              | Ret b => b
              | _ => dummy
              end.

 Definition val_as_struct_total := totalify val_as_struct EnvNil.
 Definition lookup_name_total η := totalify (lookup_name η) VUnit.

 (* Inversion lemma on a lookup: *)
 Local Lemma lookup_name_inv η n v :
   (* If [η !! n = Some v], *)
   lookup_name η n = ret v →
   (* Then, the environment is not empty, ie. it is an [EnvCons _ _ _] *)
   ∃ n' v' η',
     η = EnvCons n' v' η'
     ∧ (* And either: *) (
         ( (* - the lookup returned on the first cons ; *)
           v = v' ∧ n = n')
         ∨ ( (* - or not. *)
             n <> n' ∧ lookup_name η' n = ret v)).
 Proof.
   induction η as [ | n' v' η' ];
     first (* Impossible case. *)
       inversion 1.

   destruct (n =? n')%string eqn:E.
   { unfold lookup_name at 1; rewrite E.
     inversion 1; simplify_eq/=.
     eexists _, _, _.
     split;[ | left ]; split; first reflexivity.
     by apply String.eqb_eq. }
   { unfold lookup_name at 1; rewrite E.
     fold lookup_name.
     intros Hη'.
     eexists _, _, _; split; [ reflexivity | right ].
     split.
     - by apply String.eqb_neq.
     - assumption. }
 Qed.

 (* This lemma is equivalent as the one above. The difference is that we do not
    existentially quantify over the arguments to [EnvCons]. *)
 Local Lemma lookup_name_inv' η n n' v v' :
   lookup_name (EnvCons n v η) n' = ret v' →
   (v = v' ∧ n = n')
   ∨ (n' <> n ∧ lookup_name η n' = ret v').
 Proof.
   intros (n0&v0&η0&Heq&[ [->->] | H ])%lookup_name_inv;
     inversion Heq; simplify_eq/=; [ by left | by right ].
 Qed.

 (* If [is_module _ v] holds, then [val_as_struct v] should succeed. *)
 Lemma is_module_val_of_struct (v : val) (Λ : list name) :
   is_module Λ v →
   val_as_struct v = Ret (val_as_struct_total v).
 Proof. intros (?&->&?); reflexivity. Qed.

 (* If [is_module Λ v] holds,
    any lookup of an element of [Λ] into the module represented by [v]
    must succeed. *)
 Lemma is_module_lookup_name (v : val) n Λ :
   is_module Λ v →
   In n Λ →
   ∃ velt, lookup_name (val_as_struct_total v) n = Ret velt.
 Proof.
   induction Λ as [ | h t];
     first (* Impossible case. *)
       by inversion 2.

   intros (η&->&(vh&Hh)&Ht) [-> |Hin]%in_inv;
     first (exists vh; exact Hh).
   refine (IHt _ Hin).
   exists η; split; [ reflexivity | exact Ht ].
 Qed.

 (* Ditto, except that the value returned by [lookup_name] is known: it is
    the result of the total lookup function. *)
 Lemma is_module_lookup_name_total (v : val) (Λ : list name) (n : name) :
   is_module Λ v →
   In n Λ →
   lookup_name (val_as_struct_total v) n =
   Ret (lookup_name_total (val_as_struct_total v) n).
 Proof.
   induction Λ as [ | h t ];
     first (* Impossible case. *)
       inversion 2.

   intros (η & -> & (vh&Hh) & Ht) [Heq | Hin]%in_inv; last first.
   { apply IHt; last assumption.
     eexists _; split; [ reflexivity | assumption ]. }
   cbn.
   unfold lookup_name_total, totalify.
   rewrite -Heq Hh; f_equal.
 Qed.

 (* If one known that [lookup_name] succeeds, then its result coincides with
    that of [lookup_name_total]. This follows from the definition of
    [totalify]. *)
 Lemma lookup_name_total_ret η n v :
   lookup_name η n = Ret v →
   lookup_name_total η n = v.
 Proof.
   unfold lookup_name_total, totalify.
   intros ->. reflexivity.
 Qed.

 (* ------------------------------------------------------------------------- *)

 (* [module_spec_fetch] retrieves a spec of a given symbol from a [spec_env]. *)
 Fixpoint module_spec_fetch (Λ : spec_env) (n : name) : val → iProp Σ :=
   match Λ with
   | (h, φ) :: Λ =>
       if (n =? h)%string
       then φ
       else module_spec_fetch Λ n
   | [] => λ _, emp%I
   end.

 (* Should a module specification be available, one can fetch the specification
    of any symbol described by the spec.
    A dummy value is returned if none is found. *)
 Lemma module_spec_spec (Λ : spec_env) (v : val) (n: name) :
   module_spec Λ v ⊢
   (module_spec_fetch Λ n) (lookup_name_total (val_as_struct_total v) n).
 Proof.
   iInduction Λ as [ | [n' φ] Λ' ] "IH"; first by iIntros"_".
   iIntros "(%η&->&H)".
   change (module_spec_list ((n', φ) :: Λ') η)
     with ((∃ v : val, ⌜lookup_name η n' = ret v⌝ ∗ φ v) ∗
           module_spec_list Λ' η)%I.
   iDestruct "H" as "[(%v0&%Hv0&H0)H]".
   destruct (decide (n = n')) as [-> | Hneq].
   { cbn. rewrite String.eqb_refl.
     by rewrite (lookup_name_total_ret _ _ _ Hv0). }
   { replace (module_spec_fetch ((n', φ) :: Λ') n (lookup_name_total (val_as_struct_total (VStruct η)) n))
       with (module_spec_fetch Λ' n (lookup_name_total (val_as_struct_total (VStruct η)) n));
       last (cbn; by apply String.eqb_neq in Hneq as ->).
     iApply "IH".
     iExists _; iSplit; [ done | iAssumption ]. }
 Qed.
End Modules.

(* -------------------------------------------------------------------------- *)

(* The following section provides helper lemmas to reason on mutually-recursive
   functions ([let rec ... and ...] and [let ... = ...] constructs). *)
Section MutuallyRecursive.

  Context `{!osirisGS Σ}.

  (* ------------------------------------------------------------------------ *)

  (* The idea of this section is to allow to prove goals of the form
     [wp s E (concatenating ...) φ] and [wp s E (ret_dconcat ...) φ] by
     proving that it is enough to prove:
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ spec1 v1 ],
      ... ,
     [ ▷ spec1 v1 -∗ ... -∗ ▷ specn vn -∗ specn vn ], and
     [ (spec1 v1 -∗ ... -∗ specn vn -∗ P) ],
     where [P] represents the initial goal to prove.

     Note: this lemma follows directly from a few tautologies. *)

  (* ------------------------------------------------------------------------ *)

  (* Definitions to build the lemmas on mutually-recursive functions. *)

  (* [sepn] is similar to the iterated separating conjunction on lists.
     Using this ad-hoc definition makes the following proofs easier.
     Note: it would be possible to avoid the [emp] term in the conjunctions, but
           this would alter the structure of the definition, which has been
           chosen to mimic that of [wandn] below.
           As [sepn] should never be exposed to users, this is not an issue. *)
  Local Definition sepn (pl: list (iProp Σ)) : iProp Σ :=
    foldr (fun e res => e ∗ res)%I emp%I pl.

  (* [wandn] is an iterated magic wand:
     [wandn [a; b; c] P ] reduces to [a -∗ b -∗ c -∗ P] *)
  Definition wandn (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    foldr (fun e res => e -∗ res)%I P pl.

  Definition sepn_wand (pl: list (iProp Σ)) (P: iProp Σ) : iProp Σ :=
    sepn pl -∗ P.

  (* ------------------------------------------------------------------------ *)

  (* Simple lemmas on the above definitions to prepare the main proof. *)

  (* [wandn_sepn_wand_1] and [wandn_sepn_wand_2] state that it is equivalent to
     have nested wands or a conjunction followed by a wand. *)

  Lemma wandn_sepn_wand_1 (pl: list (iProp Σ)) (P: iProp Σ) :
    wandn pl P -∗ sepn_wand pl P.
  Proof.
    iInduction (pl) as [ | p pl ] "IH";
      unfold wandn; unfold sepn_wand; simpl; auto.
    iIntros "H_impl [Hp H_conj]".
    iApply ("IH" with "[H_impl Hp] H_conj").
    iApply ("H_impl" with "Hp").
  Qed.

  Lemma wandn_sepn_wand_2 (pl: list (iProp Σ)) (P: iProp Σ) :
    sepn_wand pl P -∗ wandn pl P.
  Proof.
    iInduction (pl) as [ | p pl ] "IH";
      unfold wandn; unfold sepn_wand; simpl.

    { iIntros "H". iApply ("H" with "[//]"). }

    iIntros "H_sepn Hp".
    iPoseProof (wand_curry with "H_sepn Hp") as "H_sepn".
    iApply ("IH" with "H_sepn").
  Qed.

  (* The [▷] modality can enter inside a separating conjunction. *)
  Lemma sepn_later_1 (pl: list (iProp Σ)) :
    ▷ sepn pl -∗ sepn (map (fun e => ▷ e)%I pl).
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  (* The [▷] modality can be factorized in front of a separating conjunction. *)
  Lemma sepn_later_2 (pl: list (iProp Σ)) :
    sepn (map (fun e => ▷ e)%I pl) -∗ ▷ sepn pl.
  Proof.
    iInduction pl as [ | p pl ] "IH"; simpl; auto.
    iIntros "[$ Hpl]".
    iApply ("IH" with "Hpl").
  Qed.

  (* [sepn_pers] states that the conjunction of persistent propositions is
     persistent. *)
  Lemma sepn_pers (pl: list (iProp Σ)) :
    Forall Persistent pl →
    Persistent (sepn pl).
  Proof.
    induction pl as [ | p pl IH].
    { simpl. intros. apply emp_persistent. }
    { intros [Hp Hpl]%Forall_cons.
      simpl. apply sep_persistent; first exact Hp.
      exact (IH Hpl). }
  Qed.

  (* [sepn_löb] paraphrases the Löb-induction principle on conjunctions. *)
  Lemma sepn_löb pl :
    (□ (sepn (map (fun e => ▷ e)%I pl) -∗ sepn pl)) -∗
    sepn pl.
  Proof.
    iIntros "#H1".
    iLöb as "Hl".
    iApply "H1".
    iApply (sepn_later_1 with "Hl").
  Qed.

  (* [wand_sepn_l] states that for any persistent proposition [P], to prove a
     conjunction under the assumption [P], it suffices to show each element of
     the conjunction under the assumption [P]. *)
  Lemma wand_sepn_l (pl: list (iProp Σ)) (P: iProp Σ) :
    Persistent P →
    sepn (map (fun p => P -∗ p) pl)%I -∗
    (P -∗ sepn pl).
  Proof.
    intros Hpers.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    iIntros "[Hp Hpl] #HP".
    iPoseProof ("IH" with "Hpl HP") as "$".
    iApply ("Hp" with "HP").
  Qed.

  (* [sepn_persistent_l] states that to prove that a conjunction is persistent,
     it suffices to show that each proposition of the conjunction is. *)
  Lemma sepn_persistent_l (pl: list (iProp Σ)) :
    sepn (map (λ e, □ e)%I pl) -∗ (□ sepn pl).
  Proof.
    iInduction (pl) as [ | p pl ] "IH"; auto; simpl.
    assert (Persistent (sepn (map (λ e, □ e)%I pl))).
    { apply sepn_pers. induction pl as [ | ? ? IHpl ]; simpl;
        [ by apply Forall_nil | apply Forall_cons; split].
      - apply intuitionistically_persistent.
      - apply IHpl. }
    iIntros "[#Hp #Hpl]".
    iSplitL; first by auto.
    iApply ("IH" with "Hpl").
  Qed.

  (* [sepn_weaken2] allows to weaken the elements of a conjunction. *)
  Lemma sepn_weaken2 (f g: iProp Σ → iProp Σ) (pl: list (iProp Σ)) :
    (forall e, f e -∗ g e) → sepn (map f pl) -∗ sepn (map g pl).
  Proof.
    iIntros (Hf).
    induction pl as [ | p pl IH ]; simpl; auto.
    iIntros "[Hp Hpl]".
    iSplitL "Hp".
    { iApply (Hf with "Hp"). }
    { iApply (IH with "Hpl"). }
  Qed.

  (* ------------------------------------------------------------------------ *)

  (* Main result.
     [assumming_list] (* TODO: find a better suited name for this lemma. *)
     states that for any persistent propositions [p1], ..., [pn] and any
     proposition [P] (which does not have to be persistent),
     [
     □ (▷ p1 -∗ ... -∗ ▷ pn -∗ p1) -∗
       ... -∗
     □ (▷ p1 -∗ ... -∗ ▷ pn -∗ pn) -∗
     (p1 -∗ ... -∗ pn -∗ P) -∗
     P
     ].
   *)


  Lemma assumming_list_nonrec (pl: list (iProp Σ)) (P: iProp Σ) :
    ⊢ wandn pl ((wandn pl P) -∗ P).
  Proof.
    iApply wandn_sepn_wand_2.
    iIntros "??".
    iApply (wandn_sepn_wand_1 with "[$][$]").
  Qed.

  Lemma assumming_list (pl: list (iProp Σ)) (P: iProp Σ) :
    Forall Persistent pl → ⊢
    (wandn
       (map (λ p, □ p)
       (map (λ p, wandn (map (λ e : iPropI Σ, ▷ e) pl) p) pl)))%I
    ((wandn pl P) -∗
    P).
  Proof.
    intros Hpers.
    iApply wandn_sepn_wand_2.
    iIntros "Hspecs1 HP"; unfold sepn_wand.
    iPoseProof (sepn_persistent_l with "Hspecs1") as "#Hspecs3".
    iPoseProof (wandn_sepn_wand_1 with "HP") as "HP".
    unfold sepn_wand.

    assert (Persistent (sepn (map (λ e, ▷ e)%I pl))).
    { apply sepn_pers.
      induction pl as [ | p pl IH]; first by apply Forall_nil.
      apply Forall_cons in Hpers as [Hp Hpl].
      apply Forall_cons; split;
        [ exact (later_persistent _ Hp)
        | exact (IH Hpl) ]. }
    iPoseProof (sepn_weaken2 with "Hspecs3") as "#Hspecs".
    { iIntros (e) "H".
      iApply (wandn_sepn_wand_1 with "H"). }
    iPoseProof ((wand_sepn_l pl (sepn (map (λ e : iPropI Σ, ▷ e)%I pl))
                              H) with "Hspecs") as "Hspecs2".
    iPoseProof (sepn_löb with "Hspecs2") as "Hspecs4".
    iApply ("HP" with "Hspecs4").
  Qed.
End MutuallyRecursive.
