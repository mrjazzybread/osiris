From stdpp Require Export functions.
From iris.algebra Require Export monoid list big_op.
From iris.prelude Require Import options.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.
Require Import logic.list_z.

Open Scope Z.

Fixpoint big_opLZ {SI : sidx} {M : ofe} (o : M → M → M) `{!MonoidOps o u} {A} (f : Z → A → M) (xs : list A) : M :=
  match xs with
  | [] => u
  | x :: xs => o (f 0 x) (big_opLZ o (λ k, f (k + 1)%Z) xs)
  end.
Global Instance : Params (@big_opLZ) 6 := {}.
Global Arguments big_opLZ {SI} {M} o {u _ A} _ !_ /.
Global Typeclasses Opaque big_opLZ.
Notation "'[^' o 'listZ]' k ↦ x ∈ l , P" :=
  (big_opLZ o (fun (k : Z) x => P) l)
    (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity,
       format "[^ o  listZ]  k ↦ x  ∈  l ,  P") : stdpp_scope.
Notation "'[^' o 'listZ]' x ∈ l , P" :=
  (big_opLZ o (fun _ x => P) l)
    (at level 200, o at level 1, l at level 10, x at level 1, right associativity,
       format "[^ o  listZ]  x  ∈  l ,  P") : stdpp_scope.

Section big_op.
  Context {SI : sidx} {M : ofe} {o : M → M → M} `{!Monoid o u}.
  Implicit Types xs : list M.
  Infix "`o`" := o (at level 50, left associativity).
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : Z → A → M.

  Lemma big_opLZ_gen_proper_2 {B} (R : relation M) f (g : Z → B → M) l1 (l2 : list B) :
    R u u →
    Proper (R ==> R ==> R) o →
    (∀ (k : Z),
       match l1 !! k, l2 !! k with
       | Some y1, Some y2 => R (f k y1) (g k y2)
       | None, None => True
       | _, _ => False
       end) →
    R ([^o listZ] k ↦ y ∈ l1, f k y) ([^o listZ] k ↦ y ∈ l2, g k y).
  Proof.
    intros ??. revert l2 f g. induction l1 as [|x1 l1 IH]=> -[|x2 l2] //= f g Hfg.
    - by specialize (Hfg 0).
    - by specialize (Hfg 0).
    - f_equiv; [apply (Hfg 0)|]. apply IH. intros k.
      specialize (Hfg (k + 1)).
      case (decide (k = -1)).
      + intros ->. by lookup.
      + intros Hneq.
        revert Hfg. lookup. by replace (k + 1 - 1) with k by lia.
  Qed.
  Lemma big_opLZ_gen_proper R f g l :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k y, l !! k = Some y → R (f k y) (g k y)) →
    R ([^o listZ] k ↦ y ∈ l, f k y) ([^o listZ] k ↦ y ∈ l, g k y).
  Proof.
    intros. apply big_opLZ_gen_proper_2; [done..|].
    intros k. destruct (l !! k) eqn:?; auto.
  Qed.

  Lemma big_opLZ_ne f g l n :
    (∀ k y, l !! k = Some y → f k y ≡{n}≡ g k y) →
    ([^o listZ] k ↦ y ∈ l, f k y) ≡{n}≡ ([^o listZ] k ↦ y ∈ l, g k y).
  Proof. apply big_opLZ_gen_proper; apply _. Qed.
  Lemma big_opLZ_proper f g l :
    (∀ (k : Z) y, l !! k = Some y → f k y ≡ g k y) →
    ([^o listZ] k ↦ y ∈ l, f k y) ≡ ([^o listZ] k ↦ y ∈ l, g k y).
  Proof. apply big_opLZ_gen_proper; apply _. Qed.

  Lemma big_opLZ_proper_2 `{!Equiv A} f g l1 l2 :
    l1 ≡ l2 →
    (∀ k y1 y2,
      l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡ y2 → f k y1 ≡ g k y2) →
    ([^o listZ] k ↦ y ∈ l1, f k y) ≡ ([^o listZ] k ↦ y ∈ l2, g k y).
  Proof.
    intros Hl Hf. apply big_opLZ_gen_proper_2; try (apply _ || done).
    intros k.
    assert (l1 !! k ≡@{option A} l2 !! k) as Hlk by (by f_equiv).
    destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance big_opLZ_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (=) ==> dist n)
           (big_opLZ o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opLZ_ne; intros; apply Hf. Qed.
  Global Instance big_opLZ_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (=) ==> (≡))
           (big_opLZ o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opLZ_proper; intros; apply Hf. Qed.

  Lemma big_opLZ_fmap {B} (h : A → B) (f : Z → B → M) l :
    ([^o listZ] k↦y ∈ h <$> l, f k y) ≡ ([^o listZ] k↦y ∈ l, f k (h y)).
  Proof. revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite IH. Qed.

  Lemma big_opLZ_op f g l :
    ([^o listZ] k↦x ∈ l, f k x `o` g k x)
    ≡ ([^o listZ] k↦x ∈ l, f k x) `o` ([^o listZ] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g /=; first by rewrite left_id.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(g _ _ `o` _)]comm -!assoc.
  Qed.

  Lemma big_opLZ_nil f : ([^o listZ] k↦y ∈ [], f k y) = u.
  Proof. done. Qed.
  Lemma big_opLZ_cons f x l :
    ([^o listZ] k↦y ∈ x::l, f k y) = f 0 x `o` [^o listZ] k↦y ∈ l, f (k + 1) y.
  Proof. done. Qed.
  Lemma big_opLZ_singleton f x : ([^o listZ] k↦y ∈ singleton x, f k y) ≡ f 0 x.
  Proof.
    replace (list_z.singleton x) with (list_z.singleton x ++ []) by auto.
    rewrite <- cons_is_append; by rewrite /= right_id.
  Qed.
  Lemma big_opLZ_app f l1 l2 :
    ([^o listZ] k↦y ∈ l1 ++ l2, f k y)
      ≡ ([^o listZ] k↦y ∈ l1, f k y) `o` ([^o listZ] k↦y ∈ l2, f (list_z.length l1 + k) y).
  Proof.
    revert f. induction l1 as [|x l1 IH]=> f /=; first by rewrite left_id.
    rewrite IH assoc.
    f_equiv. apply big_opLZ_proper; firstorder.
    replace (length (x :: l1) + k) with (length l1 + k + 1) by (length; lia).
    reflexivity.
  Qed.
  Lemma big_opLZ_snoc f l x :
    ([^o listZ] k↦y ∈ l ++ singleton x, f k y) ≡ ([^o listZ] k↦y ∈ l, f k y) `o` f (length l) x.
  Proof.
    rewrite big_opLZ_app big_opLZ_singleton.
    replace (length l + 0) with (length l) by lia.
    reflexivity.
  Qed.

  Lemma big_opLZ_unit l : ([^o listZ] k↦y ∈ l, u) ≡@{M} u.
  Proof. induction l; rewrite /= ?left_id //. Qed.

  Lemma big_opLZ_permutation (f : A → M) l1 l2 :
    l1 ≡ₚ l2 → ([^o listZ] x ∈ l1, f x) ≡ ([^o listZ] x ∈ l2, f x).
  Proof.
    induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
    - by rewrite IH.
    - by rewrite !assoc (comm _ (f x)).
    - by etrans.
  Qed.
  Global Instance big_opLZ_permutation' (f : A → M) :
    Proper ((≡ₚ) ==> (≡)) (big_opLZ o (λ _, f)).
  Proof. intros xs1 xs2. apply big_opLZ_permutation. Qed.

  Lemma big_opLZ_closed (P : M → Prop) f l :
    P u →
    (∀ x y, P x → P y → P (x `o` y)) →
    (∀ k x, l !! k = Some x → P (f k x)) →
    P ([^o listZ] k↦x ∈ l, f k x).
  Proof.
    intros Hunit Hop. revert f. induction l as [|x l IH]=> f Hf /=; [done|].
    apply Hop; first by auto. apply IH=> k y.
    case (decide (k = -1)).
    - intros ->.
      lookup.
      discriminate 1.
    - intros Hneq Hlookup.
      apply Hf. lookup.
      by replace (k + 1 - 1) with k by lia.
  Qed.

  Lemma big_opLZ_opL l (f : A → M) :
    ([^o listZ] x ∈ l, f x) ≡ ([^o list] x ∈ l, f x).
  Proof.
    induction l; first done.
    by rewrite big_opLZ_cons big_opL_cons IHl.
  Qed.

End big_op.

Section ofe.
Context {SI : sidx} {A : ofe}.

Global Instance list_lookup_ne i : NonExpansive (lookup (M:=list A) i).
Proof. intros ????. by apply option_dist_Forall2, Forall2_lookup. Qed.

Lemma big_opLZ_ne_2 {M : ofe}
    {o : M → M → M} `{!Monoid o u} (f g : Z → A → M) (l1 l2 : list A) n :
  l1 ≡{n}≡ l2 →
  (∀ k y1 y2,
     l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡{n}≡ y2 → f k y1 ≡{n}≡ g k y2) →
  ([^o listZ] k ↦ y ∈ l1, f k y) ≡{n}≡ ([^o listZ] k ↦ y ∈ l2, g k y).
Proof.
  intros Hl Hf. apply big_opLZ_gen_proper_2; [ done | apply _ | ].
  intros k. assert (l1 !! k ≡{n}≡ l2 !! k) as Hlk by (by f_equiv).
  destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

End ofe.

Section big_op.
  Context {SI : sidx} {M : ofe} {o : M → M → M} `{!Monoid o u}.
  Implicit Types xs : list M.
  Infix "`o`" := o (at level 50, left associativity).
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : Z → A → M.

  Lemma big_opLZ_sep_zip_with {B C : Type} (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : Z → A → M) (h2 : Z → B → M) (l1 : list A) (l2 : list B) :
    (∀ x y, g1 (f x y) = x) →
    (∀ x y, g2 (f x y) = y) →
    length l1 = length l2 →
    ([^o listZ] k↦xy ∈ zip_with f l1 l2, h1 k (g1 xy) `o` h2 k (g2 xy)) ≡
      ([^o listZ] k↦x ∈ l1, h1 k x) `o` ([^o listZ] k↦y ∈ l2, h2 k y).
  Proof.
    intros Hlen Hg1 Hg2. rewrite big_opLZ_op.
    rewrite -(big_opLZ_fmap g1) -(big_opLZ_fmap g2).
    rewrite fmap_zip_with_r; [|auto with lia..].
    by rewrite fmap_zip_with_l; [|auto with lia..].
  Qed.

  Lemma big_opLZ_sep_zip {B} (h1 : Z → A → M) (h2 : Z → B → M) l1 (l2 : list B) :
    length l1 = length l2 →
    ([^o listZ] k↦xy ∈ zip l1 l2, h1 k xy.1 `o` h2 k xy.2) ≡
      ([^o listZ] k↦x ∈ l1, h1 k x) `o` ([^o listZ] k↦y ∈ l2, h2 k y).
  Proof. by apply big_opLZ_sep_zip_with. Qed.

  Lemma big_opLZ_opLZ {B} (f : Z → A → Z → B → M) (l1 : list A) (l2 : list B) :
    ([^o listZ] k1↦x1 ∈ l1, [^o listZ] k2↦x2 ∈ l2, f k1 x1 k2 x2) ≡
      ([^o listZ] k2↦x2 ∈ l2, [^o listZ] k1↦x1 ∈ l1, f k1 x1 k2 x2).
  Proof.
    revert f l2. induction l1 as [|x1 l1 IH]; simpl; intros Φ l2.
    { by rewrite big_opLZ_unit. }
    by rewrite IH big_opLZ_op.
  Qed.

End big_op.

Section homomorphisms.
  Context {SI : sidx} {M1 M2 : ofe}.
  Context {o1 : M1 → M1 → M1} {o2 : M2 → M2 → M2} `{!Monoid o1 u1, !Monoid o2 u2}.
  Infix "`o1`" := o1 (at level 50, left associativity).
  Infix "`o2`" := o2 (at level 50, left associativity).

  Local Instance: ∀ {A} (R : relation A), RewriteRelation R := {}.

  Lemma big_opLZ_commute {A} (h : M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
    (f : Z → A → M1) l :
    R (h ([^o1 listZ] k↦x ∈ l, f k x)) ([^o2 listZ] k↦x ∈ l, h (f k x)).
  Proof.
    revert f. induction l as [|x l IH]=> f /=.
    - apply monoid_homomorphism_unit.
    - by rewrite monoid_homomorphism IH.
  Qed.
  Lemma big_opLZ_commute1 {A} (h : M1 → M2) `{!WeakMonoidHomomorphism o1 o2 R h}
    (f : Z → A → M1) l :
    l ≠ [] → R (h ([^o1 listZ] k↦x ∈ l, f k x)) ([^o2 listZ] k↦x ∈ l, h (f k x)).
  Proof.
    intros ?. revert f. induction l as [|x [|x' l'] IH]=> f //.
    - by rewrite !big_opLZ_singleton.
    - by rewrite !(big_opLZ_cons _ x) monoid_homomorphism IH.
  Qed.

End homomorphisms.
