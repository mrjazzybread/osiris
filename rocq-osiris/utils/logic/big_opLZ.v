From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Import list gmap.
From iris.bi Require Import derived_laws_later big_op updates.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.
Require Export logic.big_opZ logic.list_z.

Local Abbreviation length := list_z.length.

Section ofe.

Context {SI : sidx} {A : ofe}.
Implicit Types l : list A.

Global Instance Z_length_ne  n : Proper (dist n ==> (=)) (@length A).
Proof. induction 1; length; lia. Qed.

End ofe.

From Stdlib.Logic Require Import FunctionalExtensionality.

Open Scope Z.
Set Printing Coercions.

(** ** Big ops over lists with Z-valued indices *)

(** [big_sepLZ] is a variant of [big_sepL] where the index type is [Z] *)

Abbreviation big_sepLZ := (big_opLZ bi_sep) (only parsing).
Notation "'[∗' 'listZ]' k ↦ x ∈ l , P" := (big_sepLZ (λ k x, P%I) l)
  (at level 200, l at level 200, k, x at level 1, right associativity) : bi_scope.
Notation "'[∗' 'listZ]' x ∈ l , P" := (big_sepLZ (λ _ x, P%I) l)
  (at level 200, l at level 200, x at level 1, right associativity) : bi_scope.

Abbreviation big_andLZ := (big_opLZ bi_and) (only parsing).
Notation "'[∧' 'listZ]' k ↦ x ∈ l , P" := (big_andLZ (λ k x, P%I) l)
  (at level 200, l at level 200, k, x at level 1, right associativity) : bi_scope.
Notation "'[∧' 'listZ]' x ∈ l , P" := (big_andLZ (λ _ x, P%I) l)
  (at level 200, l at level 200, x at level 1, right associativity) : bi_scope.

Abbreviation big_orLZ := (big_opLZ bi_or) (only parsing).
Notation "'[∨' 'listZ]' k ↦ x ∈ l , P" := (big_orLZ (λ k x, P%I) l)
  (at level 200, l at level 200, k, x at level 1, right associativity) : bi_scope.
Notation "'[∨' 'listZ]' x ∈ l , P" := (big_orLZ (λ _ x, P%I) l)
  (at level 200, l at level 200, x at level 1, right associativity) : bi_scope.

Fixpoint big_sepLZ2 {PROP : bi} {A B}
    (Φ : Z → A → B → PROP) (l1 : list A) (l2 : list B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: l1, x2 :: l2 => Φ 0 x1 x2 ∗ big_sepLZ2 (λ k, Φ (k + 1)) l1 l2
  | _, _ => False
  end%I.
Global Instance: Params (@big_sepLZ2) 3 := {}.
Global Arguments big_sepLZ2 {PROP A B} _ !_ !_ /.
Global Typeclasses Opaque big_sepLZ2.
Notation "'[∗' 'listZ]' k ↦ x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepLZ2 (λ k x1 x2, P%I) l1 l2)
  (at level 200, l1, l2 at level 200, k, x1, x2 at level 1, right associativity) : bi_scope.
Notation "'[∗' 'listZ]' x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepLZ2 (λ _ x1 x2, P%I) l1 l2)
  (at level 200, l1, l2 at level 200, x1, x2 at level 1, right associativity) : bi_scope.

Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Local Open Scope bi_scope.

Section sep_listZ.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : Z → A → PROP.

  Lemma big_sepLZ_sepL l (Φ : A → PROP) :
    ([∗ listZ] x ∈ l, Φ x) ⊣⊢ ([∗ list] x ∈ l, Φ x).
  Proof. apply big_opLZ_opL. Qed.

  Lemma big_sepLZ_nil Φ : ([∗ listZ] k↦y ∈ nil, Φ k y) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepLZ_nil' P `{!Affine P} Φ : P ⊢ [∗ listZ] k↦y ∈ nil, Φ k y.
  Proof. apply: affine. Qed.

  Lemma big_sepLZ_cons Φ x l :
    ([∗ listZ] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ listZ] k↦y ∈ l, Φ (k + 1) y.
  Proof. done. Qed.

  Lemma big_sepLZ_singleton Φ x : ([∗ listZ] k↦y ∈ list_z.singleton x, Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opLZ_singleton. Qed.

  Lemma big_sepLZ_app Φ l1 l2 :
    ([∗ listZ] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∗ listZ] k↦y ∈ l1, Φ k y) ∗ ([∗ listZ] k↦y ∈ l2, Φ (list_z.length l1 + k) y).
  Proof. by rewrite big_opLZ_app. Qed.

  Lemma big_sepLZ_snoc Φ l x :
    ([∗ listZ] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗ listZ] k↦y ∈ l, Φ k y) ∗ Φ (list_z.length l) x.
  Proof. by rewrite big_opLZ_snoc. Qed.

  Lemma big_sepLZ_seg Φ l (i : Z) :
    valid i l →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊣⊢
    ([∗ listZ] k↦y ∈ list_z.take i l, Φ k y) ∗
    ([∗ listZ] k↦y ∈ list_z.drop i l, Φ (i + k) y).
  Proof.
    intros Hvalid.
    rewrite -{1}(list_z.take_drop i l) big_sepLZ_app.
    by length.
  Qed.

  Lemma big_sepLZ_submseteq (Φ : A → PROP) `{!∀ x, Affine (Φ x)} l1 l2 :
    l1 ⊆+ l2 → ([∗ listZ] y ∈ l2, Φ y) ⊢ [∗ listZ] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. rewrite big_sepLZ_app.
    induction l as [|x l IH]; simpl; [by rewrite right_id|by rewrite sep_elim_r].
  Qed.

  Lemma big_sepLZ_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊢ [∗ listZ] k↦y ∈ l, Ψ k y.
  Proof. apply big_opLZ_gen_proper; apply _. Qed.
  Lemma big_sepLZ_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∗ listZ] k↦y ∈ l, Φ k y)%I ≡{n}≡ ([∗ listZ] k↦y ∈ l, Ψ k y)%I.
  Proof. apply big_opLZ_ne. Qed.
  Lemma big_sepLZ_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊣⊢ ([∗ listZ] k↦y ∈ l, Ψ k y).
  Proof. apply big_opLZ_proper. Qed.

  Global Instance big_sepLZ_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opLZ (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepLZ_mono. intros k y _. apply Hf. Qed.
  Global Instance big_sepLZ_flip_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (flip (⊢))) ==> (=) ==> flip (⊢))
           (big_opLZ (@bi_sep PROP) (A:=A)).
  Proof. solve_proper. Qed.

  Global Instance big_sepLZ_nil_persistent Φ :
    Persistent ([∗ listZ] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ_persistent Φ l :
    (∀ k x, l !! k = Some x → Persistent (Φ k x)) →
    Persistent ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. apply big_opLZ_closed; apply _. Qed.
  Global Instance big_sepLZ_persistent' Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_sepLZ_persistent, _. Qed.

  Global Instance big_sepLZ_nil_affine Φ :
    Affine ([∗ listZ] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ_affine Φ l :
    (∀ k x, l !! k = Some x → Affine (Φ k x)) →
    Affine ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. apply big_opLZ_closed; apply _. Qed.
  Global Instance big_sepLZ_affine' Φ l :
    (∀ k x, Affine (Φ k x)) → Affine ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_sepLZ_affine, _. Qed.

  Global Instance big_sepLZ_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ listZ] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ_timeless `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, l !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. apply big_opLZ_closed; apply _. Qed.
  Global Instance big_sepLZ_timeless' `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, Timeless (Φ k x)) →
    Timeless ([∗ listZ] k↦x ∈ l, Φ k x).
  Proof. intros. apply big_sepLZ_timeless, _. Qed.

  Lemma big_sepLZ_emp l : ([∗ listZ] k↦y ∈ l, emp) ⊣⊢@{PROP} emp.
  Proof. by rewrite big_opLZ_unit. Qed.

  (** Lookup and update. *)

  Lemma big_sepLZ_insert_acc Φ l i x :
    l !! i = Some x →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ ([∗ listZ] k↦y ∈ <[i:=y]>l, Φ k y)).
  Proof.
    intro Hi.
    rewrite -(list_z.take_drop_middle l i x) // !big_sepLZ_app big_sepLZ_singleton.
    pose proof (list_z.lookup_lt_Some _ _ _ Hi) as Hvalid.
    length. rewrite Z.add_0_r.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. apply sep_mono_r, forall_intro=> y.
    update.
    apply wand_intro_l.
    rewrite assoc !(comm _ (Φ _ _)) -assoc !big_sepLZ_app big_sepLZ_singleton /=.
    length. rewrite Z.add_0_r.
    done.
  Qed.

  Lemma big_sepLZ_lookup_acc Φ l i x :
    l !! i = Some x →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ listZ] k↦y ∈ l, Φ k y)).
  Proof.
    intros.
    rewrite {1}big_sepLZ_insert_acc // (forall_elim x) list_insert_id //.
  Qed.

  Lemma big_sepLZ_lookup Φ l i x
    `{!TCOr (∀ j y, Affine (Φ j y)) (Absorbing (Φ i x))} :
    l !! i = Some x → ([∗ listZ] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros Hi. destruct select (TCOr _ _).
    - rewrite -(list_z.take_drop_middle l i x) //.
      rewrite !big_sepLZ_app big_sepLZ_singleton.
      apply list_z.lookup_lt_Some in Hi.
      length. rewrite Z.add_0_r.
      by rewrite sep_elim_r sep_elim_l.
    - rewrite big_sepLZ_lookup_acc // sep_elim_l //.
  Qed.

  Lemma big_sepLZ_elem_of_acc (Φ : A → PROP) l x :
    x ∈ l → ([∗ listZ] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ listZ] y ∈ l, Φ y)).
  Proof.
    intros [i ?]%list_z.list_elem_of_lookup.
    by apply: big_sepLZ_lookup_acc.
  Qed.

  Lemma big_sepLZ_elem_of (Φ : A → PROP) l x
    `{!TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))} :
    x ∈ l → ([∗ listZ] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%list_z.list_elem_of_lookup.
    destruct select (TCOr _ _); by apply: big_sepLZ_lookup.
  Qed.

  Lemma big_sepLZ_fmap {B} (f : A → B) (Φ : Z → B → PROP) l :
    ([∗ listZ] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∗ listZ] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opLZ_fmap. Qed.

  Lemma big_sepLZ_sep Φ Ψ l :
    ([∗ listZ] k↦x ∈ l, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ listZ] k↦x ∈ l, Φ k x) ∗ ([∗ listZ] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opLZ_op. Qed.

  Lemma big_sepLZ_sep_2 Φ Ψ l :
    ([∗ listZ] k↦x ∈ l, Φ k x) ⊢
    ([∗ listZ] k↦x ∈ l, Ψ k x) -∗
    ([∗ listZ] k↦x ∈ l, Φ k x ∗ Ψ k x).
  Proof. apply wand_intro_r. rewrite big_sepLZ_sep //. Qed.

  Lemma big_sepLZ_and Φ Ψ l :
    ([∗ listZ] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∗ listZ] k↦x ∈ l, Φ k x) ∧ ([∗ listZ] k↦x ∈ l, Ψ k x).
  Proof. auto using and_intro, big_sepLZ_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepLZ_pure_1 (φ : Z → A → Prop) l :
    ([∗ listZ] k↦x ∈ l, ⌜φ k x⌝) ⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    induction l as [|x l IH] using rev_ind.
    { apply pure_intro=>??. lookup. discriminate 1. }
    rewrite big_sepLZ_snoc // IH sep_and -pure_and.
    f_equiv=>-[Hl Hx] k y /list_z.lookup_app_Some =>-[Hy|[Hlen Hy]].
    - by apply Hl.
    - apply list_z.list_lookup_singleton_Some in Hy as [Hk ->].
      replace k with (list_z.length l) by lia. assumption.
  Qed.

  Lemma big_sepLZ_affinely_pure_2 (φ : Z → A → Prop) l :
    <affine> ⌜∀ k x, l !! k = Some x → φ k x⌝ ⊢@{PROP} ([∗ listZ] k↦x ∈ l, <affine> ⌜φ k x⌝).
  Proof.
    induction l as [|x l IH] using rev_ind.
    { rewrite big_sepLZ_nil. apply affinely_elim_emp. }
    rewrite big_sepLZ_snoc // -IH.
    rewrite -persistent_and_sep_1 -affinely_and -pure_and.
    f_equiv. f_equiv=>- Hlx. split.
    - intros k y Hy. apply Hlx. rewrite list_z.lookup_app Hy //.
    - apply Hlx. by lookup.
  Qed.

  Lemma big_sepLZ_pure `{!BiAffine PROP} (φ : Z → A → Prop) l :
    ([∗ listZ] k↦x ∈ l, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_sepLZ_pure_1.
    rewrite -(affine_affinely ⌜_⌝).
    rewrite big_sepLZ_affinely_pure_2. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepLZ_persistently `{!BiAffine PROP} Φ l :
    <pers> ([∗ listZ] k↦x ∈ l, Φ k x) ⊣⊢ [∗ listZ] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.

  Lemma big_sepLZ_intro Φ l :
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∗ listZ] k↦x ∈ l, Φ k x.
  Proof.
    revert Φ. induction l as [|x l IH]=> Φ /=; [by apply (affine _)|].
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // bi.True_impl.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv.
      apply forall_intro=> k; rewrite (forall_elim (k + 1)).
      case (decide (k = -1)).
      + intros ->. lookup. apply forall_intro=>a.
        rewrite (forall_elim a).
        rewrite impl_mono //. apply pure_mono. discriminate 1.
      + intros Hneq. lookup. by replace (k + 1 - 1) with k by lia.
  Qed.

  Lemma big_sepLZ_forall `{!BiAffine PROP} Φ l :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ listZ] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepLZ_lookup. }
    revert Φ HΦ. induction l as [|x l IH]=> Φ HΦ /=.
    { apply: affine. }
    rewrite -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // bi.True_impl. done.
    - rewrite -IH. apply forall_intro => k. rewrite (forall_elim (k + 1)).
      case (decide (k = -1)).
      + intros ->. lookup. apply forall_intro=>a.
        rewrite (forall_elim a).
        rewrite impl_mono //. apply pure_mono. discriminate 1.
      + intros Hneq. lookup. by replace (k + 1 - 1) with k by lia.
  Qed.

  Lemma big_sepLZ_impl Φ Ψ l :
    ([∗ listZ] k↦x ∈ l, Φ k x) ⊢
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ listZ] k↦x ∈ l, Ψ k x.
  Proof.
    apply wand_intro_l. rewrite big_sepLZ_intro -big_sepLZ_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepLZ_wand Φ Ψ l :
    ([∗ listZ] k↦x ∈ l, Φ k x) ⊢
    ([∗ listZ] k↦x ∈ l, Φ k x -∗ Ψ k x) -∗
    [∗ listZ] k↦x ∈ l, Ψ k x.
  Proof.
    apply wand_intro_r. rewrite -big_sepLZ_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepLZ_dup P `{!Affine P} l :
    □ (P -∗ P ∗ P) ⊢ P -∗ ([∗ listZ] k ↦ x ∈ l, P).
  Proof.
    apply wand_intro_l.
    induction l as [|x l IH]; simpl; first by apply: affine.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepLZ_delete Φ l i x :
    l !! i = Some x →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊣⊢
    Φ i x ∗ [∗ listZ] k↦y ∈ l, if decide (k = i) then emp else Φ k y.
  Proof.
    intros Hlookup.
    rewrite -(list_z.take_drop_middle l i x) // !big_sepLZ_app !big_sepLZ_singleton Z.add_0_r /=.
    apply list_z.lookup_lt_Some in Hlookup.
    length.
    rewrite decide_True // left_id.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. do 2 f_equiv.
    - apply big_sepLZ_proper=> k y Hk. apply list_z.lookup_lt_Some in Hk.
      rewrite list_z.length_take in Hk. by rewrite decide_False; last lia.
    - apply big_sepLZ_proper=> k y Hk.
      apply list_z.lookup_lt_Some in Hk.
      by rewrite decide_False; last lia.
  Qed.

  Lemma big_sepLZ_delete' `{!BiAffine PROP} Φ l i x :
    l !! i = Some x →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗ listZ] k↦y ∈ l, ⌜k ≠ i⌝ → Φ k y.
  Proof.
    intros. rewrite big_sepLZ_delete //. (do 2 f_equiv). intros k y.
    rewrite -decide_emp. by repeat case_decide.
  Qed.

  Lemma big_sepLZ_lookup_acc_impl {Φ l} i x :
    l !! i = Some x →
    ([∗ listZ] k↦y ∈ l, Φ k y) ⊢
    Φ i x ∗
    ∀ Ψ,
      □ (∀ k y, ⌜l !! k = Some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y) -∗
      Ψ i x -∗
      [∗ listZ] k↦y ∈ l, Ψ k y.
  Proof.
    intros.
    rewrite big_sepLZ_delete //. apply sep_mono_r, forall_intro. intro Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepLZ_delete Ψ l i x) //. apply sep_mono_r.
    eapply wand_apply; [apply big_sepLZ_impl|apply sep_mono_r].
    apply intuitionistically_intro', forall_intro. intro k.
    apply forall_intro. intro y.
    apply impl_intro_l, pure_elim_l. intro Hlookup. apply wand_intro_r.
    rewrite (forall_elim k) (forall_elim y) pure_True // left_id.
    destruct (decide _) as [->|]; [by apply: affine|].
    by rewrite pure_True //left_id intuitionistically_elim wand_elim_l.
  Qed.

  Lemma big_sepLZ_replicate l P :
    [∗] replicate (length l) P ⊣⊢ [∗ listZ] y ∈ l, P.
  Proof.
    induction l as [|x l]=> //=. length.
    rewrite (split_replicate P _ (length l)); last (length_nonneg l; lia).
    rewrite (replicate_singleton P (length l + 1 - _)); last lia.
    rewrite big_sepL_app singleton_unfold.
    by rewrite IHl comm /= right_id.
  Qed.

  Lemma big_sepLZ_later `{!BiAffine PROP} Φ l :
    ▷ ([∗ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ listZ] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.
  Lemma big_sepLZ_later_2 Φ l :
    ([∗ listZ] k↦x ∈ l, ▷ Φ k x) ⊢ ▷ [∗ listZ] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opLZ_commute _). Qed.

  Lemma big_sepLZ_laterN `{!BiAffine PROP} Φ n l :
    ▷^n ([∗ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ listZ] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.
  Lemma big_sepLZ_laterN_2 Φ n l :
    ([∗ listZ] k↦x ∈ l, ▷^n Φ k x) ⊢ ▷^n [∗ listZ] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opLZ_commute _). Qed.

  Lemma big_sepLZ_sep_zip {B : Type} (Φ1 : Z → A → PROP) (Φ2 : Z → B → PROP) (l1 : list A) (l2 : list B) :
  length l1 = length l2 →
  ([∗ listZ] k↦xy ∈ zip l1 l2, Φ1 k xy.1 ∗ Φ2 k xy.2) ⊣⊢
  ([∗ listZ] k↦x ∈ l1, Φ1 k x) ∗ ([∗ listZ] k↦y ∈ l2, Φ2 k y).
  Proof. apply big_opLZ_sep_zip. Qed.

  Lemma big_sepLZ_bupd `{!BiBUpd PROP} (Φ : Z → A → PROP) l :
    ([∗ listZ] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ listZ] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opLZ_commute _). Qed.

  Lemma big_sepLZ_fupd `{!BiFUpd PROP} E (Φ : Z → A → PROP) l :
    ([∗ listZ] k↦x ∈ l, |={E}=> Φ k x) ⊢ |={E}=> [∗ listZ] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opLZ_commute _). Qed.

End sep_listZ.


(** ** Big ops over two lists *)
Lemma big_sepLZ2_alt {A B} (Φ : Z → A → B → PROP) l1 l2 :
  ([∗ listZ] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ⊣⊢
  ⌜ list_z.length l1 = list_z.length l2 ⌝ ∧ [∗ listZ] k ↦ xy ∈ zip l1 l2, Φ k (xy.1) (xy.2).
Proof.
  apply (anti_symm _).
  - apply and_intro.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      rewrite IH sep_elim_r. apply pure_mono; length; lia.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      by rewrite IH.
  - apply pure_elim_l=> /Forall2_same_length Hl. revert Φ.
    induction Hl as [|x1 l1 x2 l2 _ _ IH]=> Φ //=. by rewrite -IH.
Qed.

Section sep_list2.
  Context {A B : Type}.
  Implicit Types Φ Ψ : Z → A → B → PROP.

  Lemma big_sepLZ2_sepL2 (Φ : A → B → PROP) l1 l2 :
    ([∗ listZ] x;y ∈ l1;l2, Φ x y) ⊣⊢ ([∗ list] x;y ∈ l1;l2, Φ x y).
  Proof.
    rewrite big_sepLZ2_alt big_sepL2_alt /length big_opLZ_opL.
    apply equiv_entails_2; apply and_mono_l, pure_mono; lia.
  Qed.

  Lemma big_sepLZ2_nil Φ : ([∗ listZ] k↦y1;y2 ∈ []; [], Φ k y1 y2) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepLZ2_nil' P `{!Affine P} Φ : P ⊢ [∗ listZ] k↦y1;y2 ∈ [];[], Φ k y1 y2.
  Proof. apply: affine. Qed.
  Lemma big_sepLZ2_nil_inv_l Φ l2 :
    ([∗ listZ] k↦y1;y2 ∈ []; l2, Φ k y1 y2) ⊢ ⌜l2 = []⌝.
  Proof. destruct l2; simpl; auto using False_elim, pure_intro. Qed.
  Lemma big_sepLZ2_nil_inv_r Φ l1 :
    ([∗ listZ] k↦y1;y2 ∈ l1; [], Φ k y1 y2) ⊢ ⌜l1 = []⌝.
  Proof. destruct l1; simpl; auto using False_elim, pure_intro. Qed.

  Lemma big_sepLZ2_cons Φ x1 x2 l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2)
    ⊣⊢ Φ 0 x1 x2 ∗ [∗ listZ] k↦y1;y2 ∈ l1;l2, Φ (k + 1) y1 y2.
  Proof. done. Qed.
  Lemma big_sepLZ2_cons_inv_l Φ x1 l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ x1 :: l1; l2, Φ k y1 y2) ⊢
    ∃ x2 l2', ⌜ l2 = x2 :: l2' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ listZ] k↦y1;y2 ∈ l1;l2', Φ (k + 1) y1 y2.
  Proof.
    destruct l2 as [|x2 l2]; simpl; auto using False_elim.
    by rewrite -(exist_intro x2) -(exist_intro l2) pure_True // left_id.
  Qed.
  Lemma big_sepLZ2_cons_inv_r Φ x2 l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1; x2 :: l2, Φ k y1 y2) ⊢
    ∃ x1 l1', ⌜ l1 = x1 :: l1' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ listZ] k↦y1;y2 ∈ l1';l2, Φ (k + 1) y1 y2.
  Proof.
    destruct l1 as [|x1 l1]; simpl; auto using False_elim.
    by rewrite -(exist_intro x1) -(exist_intro l1) pure_True // left_id.
  Qed.

  Lemma big_sepLZ2_singleton Φ x1 x2 :
    ([∗ listZ] k↦y1;y2 ∈ [x1];[x2], Φ k y1 y2) ⊣⊢ Φ 0 x1 x2.
  Proof. by rewrite /= right_id. Qed.

  Lemma big_sepLZ2_length Φ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ⊢ ⌜ list_z.length l1 = list_z.length l2 ⌝.
  Proof. by rewrite big_sepLZ2_alt and_elim_l. Qed.

  Lemma big_sepLZ2_singleton_inv_l Φ x1 (l : list B) :
    ([∗ listZ] k↦y1;y2 ∈ [x1];l, Φ k y1 y2) ⊢ ∃ x2, ⌜l = singleton x2⌝ ∗ Φ 0 x1 x2.
  Proof.
    rewrite big_sepLZ2_alt.
    apply pure_elim_l.
    destruct l as [|x2 l]; length; first lia.
    destruct l as [|? l]; length; last (length_nonneg l; lia).
    intros _. rewrite -(exist_intro x2).
    rewrite pure_True; last by rewrite singleton_unfold.
    rewrite /= right_id.
    apply True_sep_2.
  Qed.
  Lemma big_sepLZ2_singleton_inv_r Φ x2 (l : list A) :
    ([∗ listZ] k↦y1;y2 ∈ l;[x2], Φ k y1 y2) ⊢ ∃ x1, ⌜l = singleton x1⌝ ∗ Φ 0 x1 x2.
  Proof.
    rewrite big_sepLZ2_alt.
    apply pure_elim_l.
    destruct l as [|x1 l]; length; first lia.
    destruct l as [|? l]; length; last (length_nonneg l; lia).
    intros _. rewrite -(exist_intro x1).
    rewrite pure_True; last by rewrite singleton_unfold.
    rewrite /= right_id.
    apply True_sep_2.
  Qed.

  (* [big_sepLZ2_pair_inv_r] is the two-element analogue of
     [big_sepLZ2_singleton_inv_r]: when the right-hand list is a known
     pair, the left-hand list — typically the as-yet-unknown field
     locations of a freshly-allocated record — is exactly a pair too,
     matched up field-by-field with the known values. This is the shape
     that arises when unpacking a record allocation of two fields
     without going through a [RecordRepr] instance. *)

  Lemma big_sepLZ2_pair_inv_r Φ x2 x3 (l : list A) :
    ([∗ listZ] k↦y1;y2 ∈ l;[x2;x3], Φ k y1 y2) ⊢
    ∃ x1 x1', ⌜l = [x1;x1']⌝ ∗ Φ 0 x1 x2 ∗ Φ 1 x1' x3.
  Proof.
    rewrite big_sepLZ2_alt.
    apply pure_elim_l.
    destruct l as [|x1 l]; length; first lia.
    destruct l as [|x1' l]; length; first lia.
    destruct l as [|? l]; length; last (length_nonneg l; lia).
    intros _. rewrite -(exist_intro x1) -(exist_intro x1').
    rewrite pure_True //.
    rewrite /= right_id.
    apply True_sep_2.
  Qed.

  Lemma big_sepLZ2_fst_snd Φ l :
    ([∗ listZ] k↦y1;y2 ∈ l.*1; l.*2, Φ k y1 y2) ⊣⊢
    [∗ listZ] k ↦ xy ∈ l, Φ k (xy.1) (xy.2).
  Proof.
    rewrite big_sepLZ2_alt !length_fmap.
    by rewrite pure_True // bi.True_and zip_fst_snd.
  Qed.

  Lemma big_sepLZ2_app Φ l1 l2 l1' l2' :
    ([∗ listZ] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ⊢
    ([∗ listZ] k↦y1;y2 ∈ l2; l2', Φ (list_z.length l1 + k) y1 y2) -∗
    ([∗ listZ] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2).
  Proof.
    apply wand_intro_r. revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] /=.
    - by rewrite left_id.
    - rewrite left_absorb. apply False_elim.
    - rewrite left_absorb. apply False_elim.
    - rewrite -assoc. length.
      specialize (IH (λ k, Φ (k + 1))). simpl in IH.
      replace
        (λ k x y, Φ (list_z.length l1 + 1 + k) x y) with
        (λ k x y, Φ (list_z.length l1 + k + 1) x y); last first.
      { extensionality k; f_equal; lia. }
      by rewrite IH.
  Qed.

  Lemma big_sepLZ2_app_inv_l Φ l1' l1'' l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1' ++ l1''; l2, Φ k y1 y2) ⊢
    ∃ l2' l2'', ⌜ l2 = l2' ++ l2'' ⌝ ∧
                ([∗ listZ] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ listZ] k↦y1;y2 ∈ l1'';l2'', Φ (list_z.length l1' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (list_z.take (length l1') l2))
      -(exist_intro (drop (list_z.length l1') l2)) take_drop pure_True // left_id.
    revert Φ l2. induction l1' as [|x1 l1' IH]=> Φ -[|x2 l2];
       [by rewrite /= left_id|by rewrite /= left_id|apply False_elim|].
    length. rewrite !cons_is_append. length_nonneg l1'.
    take. drop. simpl. rewrite -!cons_is_append. length. simpl.
    replace
      (λ k x y, Φ (list_z.length l1' + 1 + k) x y) with
      (λ k x y, Φ (list_z.length l1' + k + 1) x y); last first.
    { extensionality k; f_equal; lia. }
    by rewrite IH -assoc !Z.add_simpl_r.
  Qed.
  Lemma big_sepLZ2_app_inv_r Φ l1 l2' l2'' :
    ([∗ listZ] k↦y1;y2 ∈ l1; l2' ++ l2'', Φ k y1 y2) ⊢
    ∃ l1' l1'', ⌜ l1 = l1' ++ l1'' ⌝ ∧
                ([∗ listZ] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ listZ] k↦y1;y2 ∈ l1'';l2'', Φ (length l2' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (take (length l2') l1))
      -(exist_intro (drop (length l2') l1)) take_drop pure_True // left_id.
    revert Φ l1. induction l2' as [|x2 l2' IH]=> Φ -[|x1 l1];
       [by rewrite /= left_id|by rewrite /= left_id|apply False_elim|].
    length. length_nonneg l2'. take. drop. length.
    rewrite -!cons_is_append /= !Z.add_simpl_r.
    replace
      (λ k x y, Φ (list_z.length l2' + 1 + k) x y) with
      (λ k x y, Φ (list_z.length l2' + k + 1) x y); last first.
    { extensionality k; f_equal; lia. }
    by rewrite IH -assoc.
  Qed.
  Lemma big_sepLZ2_app_inv Φ l1 l2 l1' l2' :
    length l1 = length l1' ∨ length l2 = length l2' →
    ([∗ listZ] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) ⊢
    ([∗ listZ] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ listZ] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k) y1 y2).
  Proof.
    revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] /= Hlen.
    - by rewrite left_id.
    - destruct Hlen as [[=]|Hlen]. rewrite big_sepLZ2_length Hlen /=.
      apply pure_elim'; length; length_nonneg l1'; lia.
    - destruct Hlen as [[=]|Hlen]. rewrite big_sepLZ2_length -Hlen /=.
      apply pure_elim'; length; length_nonneg l1; lia.
    - length.
      replace
        (λ k x y, Φ (length l1 + 1 + k) x y) with
        (λ k x y, Φ (length l1 + k + 1) x y); last first.
      { extensionality k; f_equal; lia. }
      rewrite -assoc IH //.
      revert Hlen; length.
      length_nonneg l1; length_nonneg l1'; lia.
  Qed.
  Lemma big_sepLZ2_app_same_length Φ l1 l2 l1' l2' :
    length l1 = length l1' ∨ length l2 = length l2' →
    ([∗ listZ] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) ⊣⊢
    ([∗ listZ] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ listZ] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k) y1 y2).
  Proof.
    intros. apply (anti_symm _).
    - by apply big_sepLZ2_app_inv.
    - apply wand_elim_l', big_sepLZ2_app.
  Qed.

  Lemma big_sepLZ2_snoc Φ x1 x2 l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1 ++ [x1]; l2 ++ [x2], Φ k y1 y2) ⊣⊢
    ([∗ listZ] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ∗ Φ (length l1) x1 x2.
  Proof.
    rewrite big_sepLZ2_app_same_length; last by auto.
    by rewrite big_sepLZ2_singleton Z.add_0_r.
  Qed.

  (** The lemmas [big_sepLZ2_mono], [big_sepLZ2_ne] and [big_sepLZ2_proper] are more
  generic than the instances as they also give [li !! k = Some yi] in the premise. *)
  Lemma big_sepLZ2_mono Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊢ Ψ k y1 y2) →
    ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ [∗ listZ] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros H. rewrite !big_sepLZ2_alt. f_equiv. apply big_sepLZ_mono=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepLZ2_ne Φ Ψ l1 l2 n :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ≡{n}≡ Ψ k y1 y2) →
    ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2)%I.
  Proof.
    intros H. rewrite !big_sepLZ2_alt. f_equiv. apply big_sepLZ_ne=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepLZ2_proper Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
    ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ listZ] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros; apply (anti_symm _);
      apply big_sepLZ2_mono; auto using equiv_entails_1_1, equiv_entails_1_2.
  Qed.
  Lemma big_sepLZ2_proper_2 `{!Equiv A, !Equiv B} Φ Ψ l1 l2 l1' l2' :
    l1 ≡ l1' → l2 ≡ l2' →
    (∀ k y1 y1' y2 y2',
      l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡ y1' →
      l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') →
    ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ listZ] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2.
  Proof.
    intros Hl1 Hl2 Hf. rewrite !big_sepLZ2_alt. f_equiv.
    { do 2 f_equiv; by apply Z_length_proper. }
    apply big_opLZ_proper_2; [by f_equiv|].
    intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
      (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
  Qed.

  Global Instance big_sepLZ2_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n)))
      ==> (=) ==> (=) ==> (dist n))
           (big_sepLZ2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepLZ2_ne; intros; apply Hf. Qed.
  Global Instance big_sepLZ2_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
      ==> (=) ==> (=) ==> (⊢))
           (big_sepLZ2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepLZ2_mono; intros; apply Hf. Qed.
  Global Instance big_sepLZ2_flip_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (flip (⊢))))
            ==> (=) ==> (=) ==> flip (⊢))
           (big_sepLZ2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. solve_proper. Qed.
  Global Instance big_sepLZ2_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊣⊢)))
      ==> (=) ==> (=) ==> (⊣⊢))
           (big_sepLZ2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepLZ2_proper; intros; apply Hf. Qed.

  (** Shows that some property [P] is closed under [big_sepLZ2]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_sepLZ2_closed (P : PROP → Prop) Φ l1 l2 :
    P emp%I → P False%I →
    (∀ Q1 Q2, P Q1 → P Q2 → P (Q1 ∗ Q2)%I) →
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → P (Φ k x1 x2)) →
    P ([∗ listZ] k↦x1;x2 ∈ l1; l2, Φ k x1 x2)%I.
  Proof.
    intros ?? Hsep. revert l2 Φ. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ HΦ //=.
    apply Hsep; first by auto. apply IH=> k.
    specialize (HΦ (k + 1)).
    case (decide (k = -1)).
    - intros ->.
      lookup. intros??. discriminate 1.
    - intros Hneq.
      intros. apply HΦ; lookup; by rewrite Z.add_simpl_r.
  Qed.

  Global Instance big_sepLZ2_nil_persistent Φ :
    Persistent ([∗ listZ] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ2_persistent Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Persistent (Φ k x1 x2)) →
    Persistent ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepLZ2_closed; apply _. Qed.
  Global Instance big_sepLZ2_persistent' Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    Persistent ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepLZ2_persistent, _. Qed.

  Global Instance big_sepLZ2_nil_affine Φ :
    Affine ([∗ listZ] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ2_affine Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Affine (Φ k x1 x2)) →
    Affine ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepLZ2_closed; apply _. Qed.
  Global Instance big_sepLZ2_affine' Φ l1 l2 :
    (∀ k x1 x2, Affine (Φ k x1 x2)) →
    Affine ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepLZ2_affine, _. Qed.

  Global Instance big_sepLZ2_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ listZ] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepLZ2_timeless `{!Timeless (emp%I : PROP)} Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Timeless (Φ k x1 x2)) →
    Timeless ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepLZ2_closed; apply _. Qed.
  Global Instance big_sepLZ2_timeless' `{!Timeless (emp%I : PROP)} Φ l1 l2 :
    (∀ k x1 x2, Timeless (Φ k x1 x2)) →
    Timeless ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepLZ2_timeless, _. Qed.

  Lemma big_sepLZ2_insert_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (∀ y1 y2, Φ i y1 y2 -∗ ([∗ listZ] k↦y1;y2 ∈ <[i:=y1]>l1;<[i:=y2]>l2, Φ k y1 y2)).
  Proof.
    intros Hl1 Hl2. rewrite big_sepLZ2_alt. apply pure_elim_l=> Hl.
    rewrite {1}big_sepLZ_insert_acc; last by rewrite lookup_zip_with; simplify_option_eq.
    apply sep_mono_r. apply forall_intro => y1. apply forall_intro => y2.
    rewrite big_sepLZ2_alt !length_insert pure_True // left_id -insert_zip_with.
    by rewrite (forall_elim (y1, y2)).
  Qed.

  Lemma big_sepLZ2_lookup_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)).
  Proof.
    intros. rewrite {1}big_sepLZ2_insert_acc // (forall_elim x1) (forall_elim x2).
    by rewrite !list_insert_id.
  Qed.

  Lemma big_sepLZ2_lookup Φ l1 l2 i x1 x2
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))} :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2.
  Proof.
    intros Hx1 Hx2. destruct select (TCOr _ _).
    - rewrite -(take_drop_middle l1 i x1) // -(take_drop_middle l2 i x2) //.
      apply lookup_lt_Some in Hx1. apply lookup_lt_Some in Hx2.
      rewrite !big_sepLZ2_app_same_length /=; try (length; lia).
      length.
      rewrite sep_elim_r sep_elim_l //.
      rewrite big_sepLZ2_singleton. by rewrite Z.add_0_r.
    - rewrite big_sepLZ2_lookup_acc // sep_elim_l //.
  Qed.

  Lemma big_sepLZ2_lookup_l Φ l1 l2 i x1
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x2, Absorbing (Φ i x1 x2))} :
    l1 !! i = Some x1 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊢ ∃ x2, ⌜l2 !! i = Some x2⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hl1. destruct (l2 !! i) as [x2|] eqn:Hl2.
    { rewrite -(bi.exist_intro x2) bi.pure_True // left_id.
      apply big_sepLZ2_lookup; [|done..]. destruct select (TCOr _ _); apply _. }
    rewrite big_sepLZ2_length. apply bi.pure_elim'=> Hlen.
    apply lookup_lt_Some in Hl1. apply lookup_None_invalid in Hl2.
    rewrite Hlen in Hl1.
    contradiction.
  Qed.

  Lemma big_sepLZ2_lookup_r Φ l1 l2 i x2
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x1, Absorbing (Φ i x1 x2))} :
    l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊢ ∃ x1, ⌜l1 !! i = Some x1⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hl2. destruct (l1 !! i) as [x1|] eqn:Hl1.
    { rewrite -(bi.exist_intro x1) bi.pure_True // left_id.
      apply big_sepLZ2_lookup; [|done..]. destruct select (TCOr _ _); apply _. }
    rewrite big_sepLZ2_length. apply bi.pure_elim'=> ?.
    apply lookup_lt_Some in Hl2. apply lookup_None_invalid in Hl1. lia.
  Qed.

  Lemma big_sepLZ2_fmap_l {A'} (f : A → A') (Φ : Z → A' → B → PROP) l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ f <$> l1; l2, Φ k y1 y2)
    ⊣⊢ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k (f y1) y2).
  Proof.
    rewrite !big_sepLZ2_alt length_fmap zip_with_fmap_l zip_with_zip big_sepLZ_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.
  Lemma big_sepLZ2_fmap_r {B'} (g : B → B') (Φ : Z → A → B' → PROP) l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1; g <$> l2, Φ k y1 y2)
    ⊣⊢ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 (g y2)).
  Proof.
    rewrite !big_sepLZ2_alt length_fmap zip_with_fmap_r zip_with_zip big_sepLZ_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.

  Lemma big_sepLZ2_reverse_2 (Φ : A → B → PROP) l1 l2 :
    ([∗ listZ] y1;y2 ∈ l1;l2, Φ y1 y2) ⊢ ([∗ listZ] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2).
  Proof.
    revert l2. induction l1 as [|x1 l1 IH]; intros [|x2 l2]; simpl; auto using False_elim.
    rewrite !reverse_cons (comm bi_sep) IH.
    by rewrite (big_sepLZ2_app _ _ [x1] _ [x2]) big_sepLZ2_singleton wand_elim_l.
  Qed.
  Lemma big_sepLZ2_reverse (Φ : A → B → PROP) l1 l2 :
    ([∗ listZ] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2) ⊣⊢ ([∗ listZ] y1;y2 ∈ l1;l2, Φ y1 y2).
  Proof. apply (anti_symm _); by rewrite big_sepLZ2_reverse_2 ?reverse_involutive. Qed.

  Lemma big_sepLZ2_replicate_l l x Φ n :
    length l = n →
    ([∗ listZ] k↦x1;x2 ∈ replicate n x; l, Φ k x1 x2) ⊣⊢ [∗ listZ] k↦x2 ∈ l, Φ k x x2.
  Proof.
    intros <-.
    revert Φ. induction l as [|y l IH]=> //= Φ. length.
    length_nonneg l.
    rewrite (split_replicate x (length l + 1) 1); last lia.
    rewrite replicate_singleton; last lia. rewrite -cons_is_append.
    by rewrite Z.add_simpl_r /= IH.
  Qed.
  Lemma big_sepLZ2_replicate_r l x Φ n :
    length l = n →
    ([∗ listZ] k↦x1;x2 ∈ l;replicate n x, Φ k x1 x2) ⊣⊢ [∗ listZ] k↦x1 ∈ l, Φ k x1 x.
  Proof.
    intros <-. revert Φ. induction l as [|y l IH]=> //= Φ. length.
    length_nonneg l.
    rewrite (split_replicate x (length l + 1) 1); last lia.
    rewrite replicate_singleton; last lia. rewrite -cons_is_append.
    by rewrite Z.add_simpl_r /= IH.
  Qed.

  Lemma big_sepLZ2_sep Φ Ψ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2)
    ⊣⊢ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof.
    rewrite !big_sepLZ2_alt big_sepLZ_sep !persistent_and_affinely_sep_l.
    rewrite -assoc (assoc _ _ (<affine> _)%I). rewrite -(comm bi_sep (<affine> _)%I).
    rewrite -assoc (assoc _ _ (<affine> _)%I) -!persistent_and_affinely_sep_l.
    by rewrite affinely_and_r persistent_and_affinely_sep_l idemp.
  Qed.

  Lemma big_sepLZ2_sep_2 Φ Ψ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2) -∗
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2).
  Proof. apply wand_intro_r. rewrite big_sepLZ2_sep //. Qed.

  Lemma big_sepLZ2_and Φ Ψ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∧ Ψ k y1 y2)
    ⊢ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∧ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof. auto using and_intro, big_sepLZ2_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepLZ2_pure_1 (φ : Z → A → B → Prop) l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, ⌜φ k y1 y2⌝) ⊢@{PROP}
      ⌜∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝.
  Proof.
    rewrite big_sepLZ2_alt big_sepLZ_pure_1.
    rewrite -pure_and. f_equiv=>-[Hlen Hlookup] k y1 y2 Hy1 Hy2.
    eapply (Hlookup k (y1, y2)).
    rewrite lookup_zip_with Hy1 /= Hy2 /= //.
  Qed.
  Lemma big_sepLZ2_affinely_pure_2 (φ : Z → A → B → Prop) l1 l2 :
    length l1 = length l2 →
    <affine> ⌜∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝ ⊢@{PROP}
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, <affine> ⌜φ k y1 y2⌝).
  Proof.
    intros Hdom. rewrite big_sepLZ2_alt.
    rewrite -big_sepLZ_affinely_pure_2.
    rewrite affinely_and_r -pure_and. f_equiv. f_equiv=>-Hforall.
    split; first done.
    intros k [y1 y2] (? & ? & [= <- <-] & Hy1 & Hy2)%lookup_zip_with_Some.
    by eapply Hforall.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepLZ2_pure `{!BiAffine PROP} (φ : Z → A → B → Prop) l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, ⌜φ k y1 y2⌝) ⊣⊢@{PROP}
      ⌜length l1 = length l2 ∧
       ∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝.
  Proof.
    apply (anti_symm (⊢)).
    { rewrite pure_and. apply and_intro.
      - apply big_sepLZ2_length.
      - apply big_sepLZ2_pure_1. }
    rewrite -(affine_affinely ⌜_⌝%I).
    rewrite pure_and -affinely_and_r.
    apply pure_elim_l=>Hdom.
    rewrite big_sepLZ2_affinely_pure_2 //. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepLZ2_persistently `{!BiAffine PROP} Φ l1 l2 :
    <pers> ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊣⊢ [∗ listZ] k↦y1;y2 ∈ l1;l2, <pers> (Φ k y1 y2).
  Proof.
    by rewrite !big_sepLZ2_alt persistently_and persistently_pure big_sepLZ_persistently.
  Qed.

  Lemma big_sepLZ2_intro Φ l1 l2 :
    list_z.length l1 = list_z.length l2 →
    □ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2) ⊢
    [∗ listZ] k↦x1;x2 ∈ l1;l2, Φ k x1 x2.
  Proof.
    revert l2 Φ. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ;
                                               length; try length_nonneg l2; try length_nonneg l1.
    { by intro; apply (affine _). }
    { lia. }
    { lia. }
    intro Hlen=>/=.
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2).
      by rewrite !pure_True // !bi.True_impl intuitionistically_elim.
    - rewrite -IH; last lia. f_equiv.
      apply forall_intro=> k.
      rewrite (forall_elim (k + 1)).
      case (decide (k = -1)).
      + intros ->.
        apply forall_intro=>?; apply forall_intro=>?.
        rewrite pure_False; last by lookup.
        rewrite bi.False_impl. apply True_intro.
      + intros Hneq.
        lookup. by rewrite Z.add_simpl_r.
  Qed.

  Lemma big_sepLZ2_forall `{!BiAffine PROP} Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    ([∗ listZ] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ⌜list_z.length l1 = list_z.length l2⌝
      ∧ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply and_intro; [apply big_sepLZ2_length|].
      apply forall_intro=> k. apply forall_intro=> x1. apply forall_intro=> x2.
      do 2 (apply impl_intro_l; apply pure_elim_l=> ?). by apply: big_sepLZ2_lookup. }
    apply pure_elim_l=> Hlen.
    revert l2 Φ HΦ Hlen. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ HΦ Hlen; simplify_eq/=.
    { by apply (affine _). }
    rewrite -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2).
      by rewrite !pure_True // !bi.True_impl.
    - rewrite -IH; last by (unfold length; lia).
      apply forall_intro=> k; rewrite (forall_elim (k + 1)).
      case (decide (k = -1)).
      + intros ->.
        apply forall_intro=>?; apply forall_intro=>?.
        rewrite pure_False; last by lookup.
        rewrite bi.False_impl. apply True_intro.
      + intros Hneq.
        lookup. by rewrite Z.add_simpl_r.
  Qed.

  Lemma big_sepLZ2_impl Φ Ψ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    □ (∀ k x1 x2,
      ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
    [∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    rewrite -(idemp bi_and (big_sepLZ2 _ _ _)) {1}big_sepLZ2_length.
    apply pure_elim_l=> ?. rewrite big_sepLZ2_intro //.
    apply bi.wand_intro_l. rewrite -big_sepLZ2_sep. by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepLZ2_wand Φ Ψ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 -∗ Ψ k y1 y2) -∗
    [∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    apply wand_intro_r. rewrite -big_sepLZ2_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepLZ2_delete Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    Φ i x1 x2 ∗ [∗ listZ] k↦y1;y2 ∈ l1;l2, if decide (k = i) then emp else Φ k y1 y2.
  Proof.
    intros H1 H2. rewrite -(take_drop_middle l1 i x1) // -(take_drop_middle l2 i x2) //.
    apply lookup_lt_Some in H1. apply lookup_lt_Some in H2.
    rewrite !big_sepLZ2_app_same_length /=; length; [|lia..].
    rewrite !big_sepLZ2_singleton Z.add_0_r.
    rewrite assoc -!(comm _ (Φ _ _ _)) -assoc. do 2 f_equiv.
    - apply big_sepLZ2_proper=> k y1 y2 Hk. apply lookup_lt_Some in Hk.
      rewrite length_take in Hk. by rewrite decide_False; last lia.
    - rewrite decide_True; last lia. rewrite left_id.
      apply big_sepLZ2_proper=> k y1 y2 Hk1 Hk2.
      case (decide (k = -1)).
      + intros ->. revert Hk2; lookup; discriminate 1.
      + intros Hneq.
        by rewrite decide_False; last lia.
  Qed.
  Lemma big_sepLZ2_delete' `{!BiAffine PROP} Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    Φ i x1 x2 ∗ [∗ listZ] k↦y1;y2 ∈ l1;l2, ⌜ k ≠ i ⌝ → Φ k y1 y2.
  Proof.
    intros. rewrite big_sepLZ2_delete //. (do 2 f_equiv)=> k y1 y2.
    rewrite -decide_emp. by repeat case_decide.
  Qed.

  Lemma big_sepLZ2_lookup_acc_impl {Φ l1 l2} i x1 x2 :
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    (* We obtain [Φ] for the [x1] and [x2] *)
    Φ i x1 x2 ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y1 y2,
        ⌜ l1 !! k = Some y1 ⌝ → ⌜ l2 !! k = Some y2 ⌝ → ⌜ k ≠ i ⌝ →
        Φ k y1 y2 -∗ Ψ k y1 y2) -∗
      Ψ i x1 x2 -∗
      [∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros. rewrite big_sepLZ2_delete //. apply sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepLZ2_delete Ψ l1 l2 i) //. apply sep_mono_r.
    eapply wand_apply; [apply big_sepLZ2_impl|apply sep_mono_r].
    apply intuitionistically_intro', forall_intro=> k;
      apply forall_intro=> y1; apply forall_intro=> y2.
    do 2 (apply impl_intro_l, pure_elim_l=> ?); apply wand_intro_r.
    rewrite (forall_elim k) (forall_elim y1) (forall_elim y2).
    rewrite !(pure_True (_ = Some _)) // !left_id.
    destruct (decide _) as [->|]; [by apply: affine|].
    by rewrite pure_True //left_id intuitionistically_elim wand_elim_l.
  Qed.

  Lemma big_sepLZ2_later_1 `{!BiAffine PROP} Φ l1 l2 :
    (▷ [∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ◇ [∗ listZ] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2.
  Proof.
    rewrite !big_sepLZ2_alt later_and big_sepLZ_later (timeless ⌜ _ ⌝).
    rewrite except_0_and. auto using and_mono, except_0_intro.
  Qed.

  Lemma big_sepLZ2_later_2 Φ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2) ⊢ ▷ [∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepLZ2_alt later_and big_sepLZ_later_2.
    auto using and_mono, later_intro.
  Qed.

  Lemma big_sepLZ2_laterN_2 Φ n l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, ▷^n Φ k y1 y2) ⊢ ▷^n [∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepLZ2_alt laterN_and big_sepLZ_laterN_2.
    auto using and_mono, laterN_intro.
  Qed.

  Lemma big_sepLZ2_flip Φ l1 l2 :
    ([∗ listZ] k↦y1;y2 ∈ l2; l1, Φ k y2 y1) ⊣⊢ ([∗ listZ] k↦y1;y2 ∈ l1; l2, Φ k y1 y2).
  Proof.
    revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2]//=; simplify_eq.
    by rewrite IH.
  Qed.

  Lemma big_sepLZ2_sepLZ (Φ1 : Z → A → PROP) (Φ2 : Z → B → PROP) l1 l2 :
    length l1 = length l2 →
    ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ1 k y1 ∗ Φ2 k y2) ⊣⊢
    ([∗ listZ] k↦y1 ∈ l1, Φ1 k y1) ∗ ([∗ listZ] k↦y2 ∈ l2, Φ2 k y2).
  Proof.
    intros. rewrite -big_sepLZ_sep_zip // big_sepLZ2_alt pure_True // left_id //.
  Qed.
  Lemma big_sepLZ2_sepLZ_2 (Φ1 : Z → A → PROP) (Φ2 : Z → B → PROP) l1 l2 :
    length l1 = length l2 →
    ([∗ listZ] k↦y1 ∈ l1, Φ1 k y1) ⊢
    ([∗ listZ] k↦y2 ∈ l2, Φ2 k y2) -∗
    [∗ listZ] k↦y1;y2 ∈ l1;l2, Φ1 k y1 ∗ Φ2 k y2.
  Proof. intros. apply wand_intro_r. by rewrite big_sepLZ2_sepLZ. Qed.

  Lemma big_sepLZ2_bupd `{!BiBUpd PROP} (Φ : Z → A → B → PROP) l1 l2 :
    ([∗ listZ] k↦x;y ∈ l1;l2, |==> Φ k x y) ⊢
    |==> [∗ listZ] k↦x;y ∈ l1;l2, Φ k x y.
  Proof.
    rewrite !big_sepLZ2_alt !persistent_and_affinely_sep_l.
    etrans; [| by apply bupd_frame_l]. apply sep_mono_r. apply big_sepLZ_bupd.
  Qed.

  Lemma big_sepLZ2_fupd `{!BiFUpd PROP} E (Φ : Z → A → B → PROP) l1 l2 :
    ([∗ listZ] k↦x;y ∈ l1;l2, |={E}=> Φ k x y) ⊢
    |={E}=> [∗ listZ] k↦x;y ∈ l1;l2, Φ k x y.
  Proof.
    rewrite !big_sepLZ2_alt !persistent_and_affinely_sep_l.
    etrans; [| by apply fupd_frame_l]. apply sep_mono_r. apply big_sepLZ_fupd.
  Qed.

End sep_list2.

Lemma big_sepLZ2_const_sepLZ_l {A B} (Φ : Z → A → PROP) (l1 : list A) (l2 : list B) :
  ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1)
  ⊣⊢ ⌜length l1 = length l2⌝ ∧ ([∗ listZ] k↦y1 ∈ l1, Φ k y1).
Proof.
  rewrite big_sepLZ2_alt.
  trans (⌜length l1 = length l2⌝ ∧ [∗ listZ] k↦y1 ∈ (zip l1 l2).*1, Φ k y1)%I.
  { rewrite big_sepLZ_fmap //. }
  apply (anti_symm (⊢)); apply pure_elim_l=> Hl; rewrite fst_zip;
    rewrite ?Hl //;
    (apply and_intro; [by apply pure_intro|done]).
Qed.
Lemma big_sepLZ2_const_sepLZ_r {A B} (Φ : Z → B → PROP) (l1 : list A) (l2 : list B) :
  ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y2)
  ⊣⊢ ⌜length l1 = length l2⌝ ∧ ([∗ listZ] k↦y2 ∈ l2, Φ k y2).
Proof. by rewrite big_sepLZ2_flip big_sepLZ2_const_sepLZ_l (symmetry_iff (=)). Qed.

Lemma big_sepLZ2_sep_sepLZ_l {A B} (Φ : Z → A → PROP)
    (Ψ : Z → A → B → PROP) l1 l2 :
  ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 ∗ Ψ k y1 y2)
  ⊣⊢ ([∗ listZ] k↦y1 ∈ l1, Φ k y1) ∗ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
Proof.
  rewrite big_sepLZ2_sep big_sepLZ2_const_sepLZ_l. apply (anti_symm _).
  { rewrite and_elim_r. done. }
  rewrite !big_sepLZ2_alt [(_ ∗ _)%I]comm -!persistent_and_sep_assoc.
  apply pure_elim_l=>Hl. apply and_intro.
  { apply pure_intro. done. }
  rewrite [(_ ∗ _)%I]comm. apply sep_mono; first done.
  apply and_intro; last done.
  apply pure_intro. done.
Qed.
Lemma big_sepLZ2_sep_sepLZ_r {A B} (Φ : Z → A → B → PROP)
    (Ψ : Z → B → PROP) l1 l2 :
  ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y2)
  ⊣⊢ ([∗ listZ] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ ([∗ listZ] k↦y2 ∈ l2, Ψ k y2).
Proof.
  rewrite !(big_sepLZ2_flip _ _ l1). setoid_rewrite (comm bi_sep).
  by rewrite big_sepLZ2_sep_sepLZ_l.
Qed.

Lemma big_sepLZ_sepLZ2_diag {A} (Φ : Z → A → A → PROP) (l : list A) :
  ([∗ listZ] k↦y ∈ l, Φ k y y) ⊢
  ([∗ listZ] k↦y1;y2 ∈ l;l, Φ k y1 y2).
Proof.
  rewrite big_sepLZ2_alt. rewrite pure_True // left_id.
  rewrite zip_diag big_sepLZ_fmap /=. done.
Qed.

Lemma big_sepLZ2_ne_2 {A B : ofe}
    (Φ Ψ : Z → A → B → PROP) l1 l2 l1' l2' n :
  l1 ≡{n}≡ l1' → l2 ≡{n}≡ l2' →
  (∀ k y1 y1' y2 y2',
    l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡{n}≡ y1' →
    l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡{n}≡ y2' →
    Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') →
  ([∗ listZ] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ listZ] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2)%I.
Proof.
  intros Hl1 Hl2 Hf. rewrite !big_sepLZ2_alt. f_equiv.
  { do 2 f_equiv; by apply: Z_length_ne. }
  apply big_opLZ_ne_2; [by f_equiv|].
  intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
    (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
Qed.


Section and_listZ.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : Z → A → PROP.
  Local Open Scope Z_scope.

  Lemma big_andLZ_andL l (Φ : A → PROP) :
    ([∧ listZ] x ∈ l, Φ x) ⊣⊢ ([∧ list] x ∈ l, Φ x).
  Proof. apply big_opLZ_opL. Qed.

  Lemma big_andLZ_nil Φ : ([∧ listZ] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_andLZ_nil' P Φ : P ⊢ [∧ listZ] k↦y ∈ nil, Φ k y.
  Proof. by apply pure_intro. Qed.

  Lemma big_andLZ_cons Φ x l :
    ([∧ listZ] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∧ [∧ listZ] k↦y ∈ l, Φ (k + 1) y.
  Proof. by rewrite big_opLZ_cons. Qed.

  Lemma big_andLZ_singleton Φ x : ([∧ listZ] k↦y ∈ singleton x, Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opLZ_singleton. Qed.

  Lemma big_andLZ_app Φ l1 l2 :
    ([∧ listZ] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∧ listZ] k↦y ∈ l1, Φ k y) ∧ ([∧ listZ] k↦y ∈ l2, Φ (list_z.length l1 + k) y).
  Proof. by rewrite big_opLZ_app. Qed.

  Lemma big_andLZ_snoc Φ l x :
    ([∧ listZ] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∧ listZ] k↦y ∈ l, Φ k y) ∧ Φ (list_z.length l) x.
  Proof. by rewrite big_opLZ_snoc. Qed.

  Lemma big_andLZ_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∧ listZ] k↦y ∈ l, Φ k y) ⊢ [∧ listZ] k↦y ∈ l, Ψ k y.
  Proof. apply big_opLZ_gen_proper; apply _. Qed.
  Lemma big_andLZ_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∧ listZ] k↦y ∈ l, Φ k y) ⊣⊢ ([∧ listZ] k↦y ∈ l, Ψ k y).
  Proof. apply big_opLZ_proper. Qed.

  Lemma big_andLZ_lookup Φ l i x :
    l !! i = Some x → ([∧ listZ] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // !big_andLZ_app big_andLZ_singleton.
    apply lookup_lt_Some in H.
    length. rewrite Z.add_0_r.
    eauto using and_elim_l', and_elim_r'.
  Qed.

  Lemma big_andLZ_fmap {B} (f : A → B) (Φ : Z → B → PROP) l :
    ([∧ listZ] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∧ listZ] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opLZ_fmap. Qed.

  Lemma big_andLZ_and Φ Ψ l :
    ([∧ listZ] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊣⊢ ([∧ listZ] k↦x ∈ l, Φ k x) ∧ ([∧ listZ] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opLZ_op. Qed.

  Lemma big_andLZ_persistently Φ l :
    <pers> ([∧ listZ] k↦x ∈ l, Φ k x) ⊣⊢ [∧ listZ] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.

  Lemma big_andLZ_forall Φ l :
    ([∧ listZ] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
     apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_andLZ_lookup. }
    revert Φ. induction l as [|x l IH]=> Φ; [by auto using big_andLZ_nil'|].
    rewrite big_andLZ_cons. apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // bi.True_impl.
    - rewrite -IH. apply forall_intro=> k; rewrite (forall_elim (k + 1)).
      case (decide (k = -1)).
      + intros ->. lookup.
        apply forall_intro=>a. rewrite (forall_elim a) impl_mono //.
        apply pure_mono. discriminate 1.
      + intros Hneq.
        lookup. by rewrite Z.add_simpl_r.
  Qed.

  Lemma big_andLZ_pure_1 (φ : Z → A → Prop) l :
    ([∧ listZ] k↦x ∈ l, ⌜φ k x⌝) ⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    induction l as [|x l IH] using rev_ind.
    { apply pure_intro=>??. by rewrite lookup_nil. }
    rewrite big_andLZ_snoc // IH -pure_and.
    f_equiv=>-[Hl Hx] k y /lookup_app_Some =>-[Hy|[Hlen Hy]].
    - by apply Hl.
    - apply list_lookup_singleton_Some in Hy as [Hk ->].
      replace k with (length l) by lia. done.
  Qed.
  Lemma big_andLZ_pure_2 (φ : Z → A → Prop) l :
    ⌜∀ k x, l !! k = Some x → φ k x⌝ ⊢@{PROP} ([∧ listZ] k↦x ∈ l, ⌜φ k x⌝).
  Proof.
    rewrite big_andLZ_forall pure_forall_1. f_equiv. intro k.
    rewrite pure_forall_1. f_equiv. intro x. apply pure_impl_1.
  Qed.
  Lemma big_andLZ_pure (φ : Z → A → Prop) l :
    ([∧ listZ] k↦x ∈ l, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_andLZ_pure_1.
    apply big_andLZ_pure_2.
  Qed.

  Lemma big_andLZ_later Φ l :
    ▷ ([∧ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∧ listZ] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.
  Lemma big_andLZ_laterN Φ n l :
    ▷^n ([∧ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∧ listZ] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.

End and_listZ.

Section or_listZ.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : Z → A → PROP.
  Local Open Scope Z_scope.

  Lemma big_orLZ_orL l (Φ : A → PROP) :
    ([∨ listZ] x ∈ l, Φ x) ⊣⊢ ([∨ list] x ∈ l, Φ x).
  Proof. apply big_opLZ_opL. Qed.

  Lemma big_orLZ_nil Φ : ([∨ listZ] k↦y ∈ nil, Φ k y) ⊣⊢ False.
  Proof. done. Qed.

  Lemma big_orLZ_cons Φ x l :
    ([∨ listZ] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∨ [∨ listZ] k↦y ∈ l, Φ (k + 1) y.
  Proof. by rewrite big_opLZ_cons. Qed.

  Lemma big_orLZ_singleton Φ x : ([∨ listZ] k↦y ∈ singleton x, Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opLZ_singleton. Qed.

  Lemma big_orLZ_app Φ l1 l2 :
    ([∨ listZ] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∨ listZ] k↦y ∈ l1, Φ k y) ∨ ([∨ listZ] k↦y ∈ l2, Φ (list_z.length l1 + k) y).
  Proof. by rewrite big_opLZ_app. Qed.

  Lemma big_orLZ_snoc Φ l x :
    ([∨ listZ] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∨ listZ] k↦y ∈ l, Φ k y) ∨ Φ (list_z.length l) x.
  Proof. by rewrite big_opLZ_snoc. Qed.

  Lemma big_orLZ_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∨ listZ] k↦y ∈ l, Φ k y) ⊢ [∨ listZ] k↦y ∈ l, Ψ k y.
  Proof. apply big_opLZ_gen_proper; apply _. Qed.
  Lemma big_orLZ_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∨ listZ] k↦y ∈ l, Φ k y) ⊣⊢ ([∨ listZ] k↦y ∈ l, Ψ k y).
  Proof. apply big_opLZ_proper. Qed.

  Lemma big_orLZ_intro Φ l i x :
    l !! i = Some x → Φ i x ⊢ ([∨ listZ] k↦y ∈ l, Φ k y).
  Proof.
    intros Hi.
    assert (Hi0 : (0 ≤ i)) by (apply list_z.lookup_lt_Some in Hi; lia).
    rewrite -(list_z.take_drop_middle l i x Hi) big_orLZ_app /=.
    rewrite big_orLZ_cons.
    rewrite list_z.length_take_le; [|apply list_z.lookup_lt_Some in Hi; lia].
    rewrite Z.add_0_r.
    eauto using or_intro_l', or_intro_r'.
  Qed.

  Lemma big_orLZ_fmap {B} (f : A → B) (Φ : Z → B → PROP) l :
    ([∨ listZ] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∨ listZ] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opLZ_fmap. Qed.

  Lemma big_orLZ_or Φ Ψ l :
    ([∨ listZ] k↦x ∈ l, Φ k x ∨ Ψ k x)
    ⊣⊢ ([∨ listZ] k↦x ∈ l, Φ k x) ∨ ([∨ listZ] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opLZ_op. Qed.

  Lemma big_orLZ_persistently Φ l :
    <pers> ([∨ listZ] k↦x ∈ l, Φ k x) ⊣⊢ [∨ listZ] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opLZ_commute _). Qed.

  Lemma big_orLZ_exist Φ l :
    ([∨ listZ] k↦x ∈ l, Φ k x) ⊣⊢ (∃ k x, ⌜l !! k = Some x⌝ ∧ Φ k x).
  Proof.
    apply (anti_symm _).
    { revert Φ. induction l as [|x l IH]; intro Φ.
      { rewrite big_orLZ_nil. apply False_elim. }
      rewrite big_orLZ_cons. apply or_elim.
      - by rewrite -(exist_intro 0) -(exist_intro x) pure_True // left_id.
      - rewrite IH. apply exist_elim. intro k. rewrite -(exist_intro (k + 1)).
        apply exist_elim. intro y.
        rewrite -(exist_intro y).
        case (decide (k = -1)).
        + intros ->. lookup.
          rewrite and_mono_l //.
          apply pure_mono. discriminate 1.
        + intros Hneq.
          lookup. by rewrite Z.add_simpl_r. }
    apply exist_elim. intro k. apply exist_elim. intro x. apply pure_elim_l.
    by apply: big_orLZ_intro.
  Qed.

  Lemma big_orLZ_sep_l P Φ l :
    P ∗ ([∨ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ listZ] k↦x ∈ l, P ∗ Φ k x).
  Proof.
    rewrite !big_orLZ_exist sep_exist_l.
    f_equiv. intro k. rewrite sep_exist_l. f_equiv. intro x.
    by rewrite !persistent_and_affinely_sep_l !assoc (comm _ P).
  Qed.
  Lemma big_orLZ_sep_r Q Φ l :
    ([∨ listZ] k↦x ∈ l, Φ k x) ∗ Q ⊣⊢ ([∨ listZ] k↦x ∈ l, Φ k x ∗ Q).
  Proof. setoid_rewrite (comm bi_sep). apply big_orLZ_sep_l. Qed.

  Lemma big_orLZ_later Φ l :
    l ≠ [] →
    ▷ ([∨ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ listZ] k↦x ∈ l, ▷ Φ k x).
  Proof.  apply (big_opLZ_commute1 _). Qed.
  Lemma big_orLZ_laterN Φ n l :
    l ≠ [] →
    ▷^n ([∨ listZ] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ listZ] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opLZ_commute1 _). Qed.

End or_listZ.

(** Commuting lemmas for Z-indexed list big ops. *)
Lemma big_sepLZ_sepLZ {A B} (Φ : Z → A → Z → B → PROP) (l1 : list A) (l2 : list B) :
  ([∗ listZ] k1↦x1 ∈ l1, [∗ listZ] k2↦x2 ∈ l2, Φ k1 x1 k2 x2) ⊣⊢
  ([∗ listZ] k2↦x2 ∈ l2, [∗ listZ] k1↦x1 ∈ l1, Φ k1 x1 k2 x2).
Proof. apply big_opLZ_opLZ. Qed.

End big_op.
