From osiris.lang Require Import type_nel encode notations int.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import proofmode.

From osiris.stdlib Require Import og_array Externals.

From iris Require Import ltac_tactics.

From osiris.logic Require Export big_opLZ.
From osiris.tactics Require Import osiris_utils.

Section init_proof.

  Context `{!osirisGS Σ}.

  Definition init_spec : Z → val → microvx → iProp Σ :=
    λ n f m,
      (∀ (A : Type) `(Encode A, Inhabited A) I,
         ⌜0 ≤ n ≤ max_array⌝ -∗
         (* [f] is a function [Z → A], such that [f i] preserves
            an invariant [I] over the results of all calls to [f i] so far. *)
         □ iSpec τ[Z] f (λ i m, ∀ xs, ⌜0 ≤ i < n⌝ -∗ ⌜length xs = i⌝ -∗ I xs -∗
                                      imp m {{ λ x, I (xs ++ singleton x) }}) -∗
         (* Calling [init f n] returns an array [a] such that [ownArray a xs],
            and such that [Φ i] holds for the [i]'th element of xs. *)
         I [] -∗
         imp m {{ λ a, ∃ (xs : list A), ⌜length xs = n⌝ ∗ ownArray a xs ∗ I xs }})%I.

  Definition init_spec' : Z → val → microvx → iProp Σ :=
    λ n f m,
      (∀ (A : Type) `(Encode A, Inhabited A) (Φ : Z → A → iProp Σ),
         ⌜0 ≤ n ≤ max_array⌝ -∗
         (* [f] is a function [Z → A], such that [f i] satisfies [Φ i]. *)
         □ iSpec τ[Z] f (λ i m, ⌜0 ≤ i < n⌝ -∗ imp m {{ λ x, Φ i x }}) -∗
         (* Calling [init f n] returns an array [a] such that [ownArray a xs],
            and such that [Φ i] holds for the [i]'th element of xs. *)
         imp m {{ λ a, ∃ (xs : list A), ⌜length xs = n⌝ ∗ ownArray a xs ∗ [∗ listZ] i↦x ∈ xs, Φ i x }})%I.

  Lemma weaken_init_spec n f m :
    init_spec n f m -∗ init_spec' n f m.
  Proof.
    iIntros "Hinit" (A HencA HinhA Φ Hbounds) "#Hf".
    iApply ("Hinit" $! A HencA HinhA (λ xs, [∗ listZ] i↦x ∈ xs, Φ i x)%I Hbounds).
    - iIntros "!>".
      iApply (iSpec_mono with "Hf").
      iIntros (i m') "Himp". unfold tapp.
      iIntros (xs Hboundsi Hlenxs) "HΦs".
      iSpecialize ("Himp" $! Hboundsi).
      iApply (imp_mono_ret with "Himp").
      iIntros (x) "HΦ".
      iCombine ("HΦs HΦ") as "HΦs".
      rewrite <- Hlenxs; rewrite /length.
      iApply (big_sepLZ_snoc with "HΦs").
    - by iApply big_sepLZ_nil.
  Qed.

  Definition init := (EAnonFun __fun21).

  Lemma imp_init η :
    in_env "make" array_make_spec η -∗
    in_env "unsafe_set" array_set_spec η -∗
    imp (eval η init) {{ λ c, □ iSpec τ[Z; val] c init_spec }}.
  Proof.
    iIntros "#Hlookup1 #Hlookup2".
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros (n f).
    change (VInt (int.repr n)) with #n.
    unfold init_spec.
    iIntros (A HencA HinhA I) "%Hbounds #Hf HI".
    iApply imp_please; iNext.
    iApply imp_EIfThenElse.
    { imp_arith. }
    iIntros ([|]) "%Heq0".

    { (* Case: [n = 0]. *)
      iApply imp_mono_ret. iApply (imp_EArrayEmpty (A:=A)).
      iIntros (a) "$".
      iFrame. iPureIntro; length; lia. }

    iApply imp_EIfThenElse.
    { imp_arith. }
    iIntros ([|]) "%Hlt0".

    { (* Case: [n < 0]. *)
      (* This case is forbidden by the spec. *) lia. }

    iApply (imp_ELet_var (B:=array) with "[HI]").
    { (* Subgoal: [make l (f 0)] *)
      imp_app τ[Z;A] with "[] [] [HI]".
      - (* (f 0) *)
        imp_app τ[Z].
        iIntros "H".
        iApply ("H" with "[] [] HI"); iPureIntro; length; lia.
      - iIntros "HI Hm".
        iApply ("Hm" with "[] HI"). iPureIntro; lia. }
    iIntros (res) "(%x & HΦx & HownArr)".
    iDestruct "HownArr" as "(#Harr & Hslice)". length.

    (* Subgoal: [for i = 1 to ... done; res]. *)
    iApply (imp_ESeq with "[Hslice HΦx]").
    { (* Subgoal: [for i = 1 to ... done]. *)
      imp_for 1 to (n - 1) $!
        (λ i,
           isSlice (DfracOwn 1) res i (replicate (n - i) x) ∗
           ∃ xs, ⌜length xs = i⌝ ∗ isSlice (DfracOwn 1) res 0 xs ∗ I xs)%I
        with "[] [] [Hslice HΦx]".
      { (* Prove that the loop invariant holds at index [1]. *)
        iPoseProof (split_Slice 1 with "Hslice")
          as "[Hslice1 Hslice2]"; first (length; lia).
        seg. length. iFrame.
        iPureIntro; length; reflexivity. }

      (* Prove the loop's body produces the loop invariant at index
         [i' + 1], assuming that the loop invariant holds at index
         [i']. *)
      iIntros (i Hbound) "(Hslice2 & %xs & %Hlenxs & Hslice1 & HI)".

      (* Transfer the head of slice2 to the tail of slice1. *)
      iPoseProof (split_Slice 1 with "Hslice2")
        as "[Hslice Hslice2]"; first (length; lia).
      seg. length. replicate.
      iCombine ("Hslice1 Hslice") as "Hslice1".
      iPoseProof (Slice_app with "Hslice1") as "Hslice1"; first lia.

      (* Subgoal: [unsafe_set res i (f i)]. *)
      imp_app τ[array;Z;A] with "[] [] [] [HI]".
      { (* unsafe_set *) iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* (f i) *)
        imp_app τ[Z].
        iIntros "Hm".
        iApply ("Hm" with "[] [] HI"); iPureIntro; length; lia. }
      iIntros "HI Hm".
      iSpecialize ("Hm" with "Harr Hslice1 [HI] [] []").
      { instantiate (1:=(λ y, I (xs ++ singleton y))). iFrame. }
      { iPureIntro; lia. }
      { iPureIntro; length; lia. }
      iApply (imp_mono_ret with "Hm").
      iIntros (_) "(% & HI & Hslice1)".
      update. replace (n - (i + 1)) with (n - i - 1) by lia.
      iFrame. iPureIntro; length; lia. }

    iIntros "(Hslempty & %xs & %Hlen & Hslice & HI)".
    imp_path.
    unfold ownArray. length.
    iFrame. rewrite Hlen.
    replace (n - 1 + 1) with n by lia.
    assert (n `max` 1 = n) as -> by lia.
    by iFrame "#".
  Qed.

End init_proof.


Section iter_proof.

  Context `{!osirisGS Σ}.

  (* TODO: we may want to have a "moraly parallel" spec of [iter],
     where we don't specify the order of iteration. *)
  Definition iter_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) dq (xs : list A) (I : list A → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] f (λ (X : A) m,
                           ∀ (Xs : list A),
                           ⌜Xs ++ singleton X `prefix_of` xs⌝ -∗
                           I Xs -∗
                           imp m {{ λ (_ : unit), I (Xs ++ singleton X) }}) -∗
         I [] -∗
         imp m {{ λ (_ : unit), I xs ∗ isSlice dq a 0 xs }})%I.


  Definition iter := (EAnonFun __fun74).

  Lemma singleton_prefix `{Inhabited A} x (xs : list A) :
    0 < length xs →
    x = xs !!! 0 →
    singleton x `prefix_of` xs.
  Proof.
    intros Hlen ->.
    exists (seg 1 (length xs) xs).
    rewrite -(seg_is_singleton 0 1 xs); try lia.
    rewrite -split_seg; try lia.
    by seg.
  Qed.

  Lemma complete_prefix {A} (xs ys : list A) :
    length xs = length ys →
    xs `prefix_of` ys →
    xs = ys.
  Proof.
    intros Hlen (xs' & ->).
    rewrite length_app in Hlen.
    assert (length xs' = 0) as Hlen0 by lia.
    apply nil_length_inv in Hlen0 as ->.
    by rewrite app_nil_r.
  Qed.

  Lemma prefix_snoc `{Inhabited A} (xs ys : list A) :
    ys `prefix_of` xs →
    length ys < length xs →
    ys ++ singleton (xs !!! length ys) `prefix_of` xs.
  Proof.
    intros (xs' & ->) Hlens.
    apply prefix_app.
    apply singleton_prefix.
    - revert Hlens; length; lia.
    - by lookup.
  Qed.

  Lemma imp_iter η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    imp (eval η iter) {{ λ c, □ iSpec τ[val; array] c iter_spec }}.
  Proof.
    iIntros "#Hlength #Hget".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA dq xs I) "(%Hlen & %Hbound) Hslice #Hf HI".
    iApply imp_please; iNext.
    iApply (imp_mono_ret with "[-]").
    - imp_for 0 to (length xs - 1) $!
        (λ i, isSlice dq a 0 xs ∗
              ∃ Xs, I Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [HI Hslice]".
      { imp_arith.
        imp_app τ[array].
        iIntros "Hm".
        iApply (imp_mono_ret with "[-]").
        - iApply "Hm".
          iPureIntro; split; eassumption.
        - iIntros (?) "->". auto. }

      { (* Establish the invariant for [i = 0]. *)
        iFrame. iPureIntro. split; [ by length | apply prefix_nil ]. }

      (* Body of the [for] loop. *)
      iIntros (i') "%Hi' (Hslice & (%Xs & HI & <- & %Hprefix))".
      (* Subgoal: f (unsafe_get a i) *)
      imp_app τ[A] with "[] [Hslice]".
      { (* unsafe_get a i *)
        imp_app τ[array;Z].
        iIntros "Hm".
        iApply ("Hm" $! A with "[] Hslice").
        { iPureIntro. split; eassumption. }
        iPureIntro; lia. iPureIntro; lia. }
      iIntros "(-> & Hslice) Hm". rewrite Z.sub_0_r.
      apply prefix_snoc in Hprefix; try lia.
      iSpecialize ("Hm" with "[//] HI").
      iApply (imp_mono_ret with "Hm").
      iIntros ([]) "$". iFrame. iPureIntro.
      split; [ length; lia | assumption ].
    - iIntros ([]) "($ & %Xs & HI & %HlenXs & %Hprefix)".
      (* Show that we have covered the full list. *)
      rewrite (complete_prefix Xs xs); [ | lia | assumption ].
      iApply "HI".
  Qed.

End iter_proof.


(* TODO: copy, append, sub, fill, blit use unsupported primitives
   (unsafe_sub, append_prim, unsafe_blit, unsafe_fill). *)

Section iter2_spec.

  Context `{!osirisGS Σ}.


  (** [iter2 f a b] applies function [f] to all elements of [a] and [b]
      pairwise. Raises if the arrays have different lengths. *)
  Definition iter2_spec : val → array → array → microvx → iProp Σ :=
    λ f a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (I : list (A * B) → iProp Σ),
         ⌜length xs = length ys⌝ -∗
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; B] f (λ (x : A) (y : B) m,
                              ∀ (visited : list (A * B)),
                              ⌜visited ++ singleton (x, y) `prefix_of` zip xs ys⌝ -∗
                              I visited -∗
                              imp m {{ λ (_ : unit), I (visited ++ singleton (x, y)) }}) -∗
         I [] -∗
         imp m {{ λ (_ : unit), I (zip xs ys) ∗ isSlice dq1 a 0 xs ∗ isSlice dq2 b 0 ys }})%I.

End iter2_spec.


Section map_spec.

  Context `{!osirisGS Σ}.


  (** [map f a] applies function [f] to all elements of [a], and builds
      an array with the results returned by [f]. *)
  Definition map_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) `(Encode A, Inhabited A) `(Encode B, Inhabited B)
         dq (xs : list A) (Φ : A → B → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] f (λ (x : A) m, imp m {{ λ (y : B), Φ x y }}) -∗
         imp m {{ λ a', ∃ (ys : list B),
                    ownArray a' ys ∗
                    isSlice dq a 0 xs ∗
                    [∗ listZ] x;y ∈ xs;ys, Φ x y }})%I.

  Definition map := (EAnonFun __fun88).

  Lemma imp_map η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    in_env "unsafe_set" array_set_spec η -∗
    in_env "make" array_make_spec η -∗
    imp (eval η map) {{ λ c, □ iSpec τ[val; array] c map_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset #Hmake".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A B HencA HinhA HencB HinhB dq xs Φ) "(%Hlen & %Hbound) Hslice #Hf".
    iApply imp_please; iNext.

    (* let l = length a in ... *)
    iApply (imp_ELet_var (B:=Z) with "[] [Hslice]").
    { imp_app τ[array].
      iIntros "Hm". iApply "Hm".
      iPureIntro; split; eassumption. }
    iIntros (l) "->".

    (* if l = 0 then [||] else ... *)
    iApply imp_EIfThenElse.
    { imp_arith. }
    iIntros ([|]) "%Heq0".

    { (* Case: length xs = 0, so xs = [] *)
      iApply imp_mono_ret.
      iApply (imp_EArrayEmpty (A:=B)).
      iIntros (a') "$". iFrame.
      rewrite (nil_length_inv xs); last lia.
      by rewrite big_sepLZ2_nil. }

    (* Case: length xs > 0 *)

    (* let r = make l (f (unsafe_get a 0)) in ... *)
    iApply (imp_ELet_var (B:=array) with "[Hslice]").
    { set_postcondition
        (λ r, ∃ y, isSlice dq a 0 xs ∗ Φ (xs !!! 0) y ∗ ownArray r (replicate (length xs) y))%I.
      imp_app τ[Z; B] with "[] [] [Hslice]".
      { (* f (unsafe_get a 0) *)
        imp_app τ[A] with "[] [Hslice]".
        (* function: f *)
        (* arg: unsafe_get a 0 *)
        imp_app τ[array; Z].
        (* continuation for unsafe_get *)
        iIntros "Hm".
        iSpecialize ("Hm" $! A with "[%] Hslice").
        { split; eassumption. }
        iApply "Hm". iPureIntro; lia. iPureIntro; length; lia.
        (* continuation for f *)
        iIntros "(%Hlookup & Hslice) Hm".
        set_postcondition (λ y, isSlice dq a 0 xs ∗ Φ (xs !!! 0) y)%I.
        iApply (imp_mono_ret with "Hm [Hslice]").
        rewrite Hlookup Z.sub_0_r.
        iIntros (y) "$". iFrame. }
      (* continuation for make *)
      iIntros "(Hslice & HΦy0) Hm".
      iSpecialize ("Hm" with "[%] HΦy0"); first lia.

      iApply (imp_mono_ret with "Hm [Hslice]").
      iIntros (r) "(%y0' & HΦy0 & HownR)". iFrame. }

    iIntros (r) "(%y & Hslice & HΦy & HownR)".
    iDestruct "HownR" as "(#HarrR & HsliceR)".
    rewrite length_replicate.
    iDestruct "HarrR" as "(%Hlenr & %Hboundr)".

    (* for i = 1 to l - 1 do unsafe_set r i (f (unsafe_get a i)) done; r *)
    iApply (imp_ESeq with "[Hslice HsliceR HΦy]").
    { imp_for 1 to (length xs - 1) $!
        (λ i, isSlice dq a 0 xs ∗
              ∃ (ys : list B),
                isSlice (DfracOwn 1) r 0 (ys ++ replicate (length xs - i) y) ∗
                [∗ listZ] x;y ∈ seg 0 i xs;ys, Φ x y)%I
        with "[] [] [Hslice HsliceR HΦy]".

      { (* Initial invariant at i = 1 *)
        iFrame "Hslice". rewrite (split_Slice 1); last (length; lia).
        seg. setoid_rewrite Slice_app; last reflexivity. length.
        iFrame.
        rewrite seg_is_singleton; try lia.
        iApply (big_sepLZ2_singleton with "HΦy"). }

      (* Loop body: unsafe_set r i (f (unsafe_get a i)) *)
      iIntros (i') "%Hi' (Hslice & %ys & HsliceR & HΦs)".
      imp_app τ[array; Z; B] with "[] [] [] [Hslice HsliceR HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! B HencB HinhB). iAssumption. }
      { (* f (unsafe_get a i) *)
        imp_app τ[A] with "[] [Hslice]".
        (* function: f *)
        (* arg: unsafe_get a i *)
        { imp_app τ[array;Z].
          (* continuation for unsafe_get on source array a *)
          iIntros "Hm".
          iApply ("Hm" $! A with "[%] Hslice").
          - split; eassumption.
          - iPureIntro; lia.
          - iPureIntro; length; lia. }
        (* continuation for f *)
        iIntros "(%Hlookup & Hslice) Hm".
        set_postcondition
          (λ x,
             isSlice dq a 0 xs ∗
             isSlice (DfracOwn 1) r 0 (ys ++ replicate (length xs - i') y) ∗
             Φ (xs !!! i') x ∗
             [∗ listZ] x;y ∈ (seg 0 i' xs);ys, Φ x y)%I.
        iApply (imp_mono_ret with "Hm [Hslice HsliceR HΦs]").
        iIntros (x') "HΦ".
        rewrite Hlookup Z.sub_0_r. iFrame. }
      (* continuation for unsafe_set *)
      iIntros "(Hslice & HsliceR & HΦy & HΦs) Hm".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      rewrite length_seg in Hlenys.
      iSpecialize ("Hm" $! (length xs) 0 (ys ++ replicate (length xs - i') y) (λ x', ⌜x'=x⌝)%I
                    with "[%] HsliceR [//] [%] [%]").
      { split; [length; lia | lia]. }
      { lia. }
      { length; lia. }
      iApply (imp_mono_ret with "Hm [Hslice HΦy HΦs]").
      iIntros ([]) "(% & -> & HsliceR)".
      iFrame "Hslice".
      iExists (ys ++ singleton x).
      update.
      replace (length xs - i' -1 - (i' - 0 -length ys))
        with (length xs - (i' + 1)) by lia.
      rewrite app_assoc. iFrame.
      rewrite (split_seg i' xs 0 (i' + 1)); try lia.
      iApply (big_sepLZ2_app with "HΦs").
      rewrite seg_is_singleton; try lia.
      iApply (big_sepLZ2_singleton with "HΦy"). }

    (* After the loop: return r *)
    iIntros "(Hslice & %ys & HsliceR & HΦs)".
    imp_path. seg. replicate.
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
    iFrame.
    iSplit. { iPureIntro; length; lia. } { iPureIntro; lia. }
  Qed.

End map_spec.


Section map_inplace_spec.

  Context `{!osirisGS Σ}.


  (** [map_inplace f a] applies function [f] to all elements of [a],
      replacing each element with the result in place. *)
  Definition map_inplace_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) (xs : list A) (Φ : A → A → iProp Σ),
         ownArray a xs -∗
         □ iSpec τ[A] f (λ (x : A) m, imp m {{ λ (y : A), Φ x y }}) -∗
         imp m {{ λ (_ : unit), ∃ (ys : list A),
                    ownArray a ys ∗
                    [∗ listZ] x;y ∈ xs;ys, Φ x y }})%I.

  Definition map_inplace := (EAnonFun __fun91).

  Lemma imp_map_inplace η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    in_env "unsafe_set" array_set_spec η -∗
    imp (eval η map_inplace) {{ λ c, □ iSpec τ[val; array] c map_inplace_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA xs Φ) "Hown #Hf".
    iApply imp_please; iNext.
    unfold ownArray.
    iDestruct "Hown" as "((%Hlen & %Hbound) & Hslice)".

    iApply (imp_mono_ret with "[-]").
    - imp_for 0 to (length xs - 1) $!
        (λ i, ∃ (ys : list A),
            isSlice (DfracOwn 1) a 0 (ys ++ seg i (length xs) xs) ∗
            [∗ listZ] x;y ∈ (seg 0 i xs);ys, Φ x y)%I
        with "[] [] [Hslice]".
      { imp_arith.
        imp_app τ[array].
        iIntros "Hm".
        iApply (imp_mono_ret with "[-]").
        - iApply "Hm".
          iPureIntro; split; eassumption.
        - iIntros (?) "->". auto. }

      { (* Establish the invariant for [i = 0]. *)
        iExists []. seg. rewrite big_sepLZ2_nil. iFrame. }

      iIntros (i) "%Hi (%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      revert Hlenys; length; rewrite Z.sub_0_r; intros Hlenys.
      (* unsafe_set a i (f (unsafe_get a i)) *)
      imp_app τ[array; Z; A] with "[] [] [] [Hslice HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* arg 3: f (unsafe_get a i) *)
        set_postcondition (λ y, isSlice (DfracOwn 1) a 0 (ys ++ seg i (length xs) xs) ∗
                                Φ ((ys ++ seg i (length xs) xs) !!! i) y ∗
                                [∗ listZ] x;y ∈ (seg 0 i xs);ys, Φ x y)%I.
        imp_app τ[A] with "[] [Hslice]".
        (* function: f *)
        { (* arg: unsafe_get a i *)
          imp_app τ[array;Z].
          (* continuation for unsafe_get *)
          iIntros "Hm".
          iApply ("Hm" $! A with "[%] Hslice").
          - split; eassumption.
          - iPureIntro; lia.
          - iPureIntro; length; lia. }
        (* continuation for f:
           v = (ys ++ seg i (length xs) xs) !!! i', with slice back *)
        iIntros "(%Hlookup & Hslice) Hm".
        iApply (imp_mono_ret with "Hm [Hslice HΦs]").
        rewrite Hlookup. lookup.
        iIntros (y) "$". iFrame. }
      (* continuation for unsafe_set: all three args resolved *)
      iIntros "(Hslice & HΦy & HΦs) Hm".
      iSpecialize ("Hm" $! (length xs) 0 (ys ++ seg i (length xs) xs) (λ x', ⌜x'=x⌝)%I
                    with "[%] Hslice [//] [%] [%]"); try (length; lia).

      iApply (imp_mono_ret with "Hm [HΦy HΦs]").
      iIntros ([]) "(% & -> & Hslice)". rewrite Z.sub_0_r.
      iExists (ys ++ [x]).
      iSplitL "Hslice".
      + rewrite (split_seg (i+1)); try lia.
        rewrite (seg_is_singleton i (i + 1)); try lia. update.
        rewrite app_assoc. iFrame.
      + rewrite (split_seg i xs 0 (i+1)); try lia.
        iApply (big_sepLZ2_app with "HΦs").
        rewrite (seg_is_singleton i (i+1)); try lia.
        iApply big_sepLZ2_singleton.
        lookup. replace (i + (i - length ys)) with i by lia.
        iApply "HΦy".

    - iIntros ([]) "(%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      revert Hlenys; length; intros.
      seg. iFrame.
      iSplit; iPureIntro; lia.
  Qed.

End map_inplace_spec.


Section mapi_inplace_spec.

  Context `{!osirisGS Σ}.


  (** [mapi_inplace f a] applies function [f] to the index and all elements
      of [a], replacing each element with the result in place. *)
  Definition mapi_inplace_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) (xs : list A) (Φ : Z → A → A → iProp Σ),
         ownArray a xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ⌜0 ≤ i < length xs⌝ -∗
                              imp m {{ λ (y : A), Φ i x y }}) -∗
         imp m {{ λ (_ : unit), ∃ (ys : list A),
                    ownArray a ys ∗
                    [∗ listZ] i↦x;y ∈ xs;ys, Φ i x y }})%I.

  Definition mapi_inplace := (EAnonFun __fun94).

  Lemma imp_mapi_inplace η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    in_env "unsafe_set" array_set_spec η -∗
    imp (eval η mapi_inplace) {{ λ c, □ iSpec τ[val; array] c mapi_inplace_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA xs Φ) "Hown #Hf".
    iApply imp_please; iNext.
    unfold ownArray.
    iDestruct "Hown" as "((%Hlen & %Hbound) & Hslice)".

    iApply (imp_mono_ret with "[-]").
    - imp_for 0 to (length xs - 1)
        $! (λ i, ∃ (ys : list A),
            isSlice (DfracOwn 1) a 0 (ys ++ seg i (length xs) xs) ∗
            [∗ listZ] j↦x;y ∈ (seg 0 i xs);ys, Φ j x y)%I
        with "[] [] [Hslice]".
      { imp_arith.
        imp_app τ[array].
        iIntros "Hm". iApply (imp_mono_ret with "[-]").
        iApply "Hm".
        - iPureIntro; split; eassumption.
        - iIntros (?) "->". auto. }

      { (* Establish the invariant for [i = 0]. *)
        iExists []. seg. rewrite big_sepLZ2_nil. iFrame. }

      iIntros (i) "%Hi (%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      revert Hlenys; length; intros.
      (* unsafe_set a i (f i (unsafe_get a i)) *)
      imp_app τ[array; Z; A] with "[] [] [] [Hslice HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* arg 3: f i (unsafe_get a i) *)
        set_postcondition
          (λ y, isSlice (DfracOwn 1) a 0 (ys ++ seg i (length xs) xs) ∗
                Φ i ((ys ++ seg i (length xs) xs) !!! i) y ∗
                [∗ listZ] j↦x;y ∈ (seg 0 i xs);ys, Φ j x y)%I.
        imp_app τ[Z; A] with "[] [] [Hslice]".
        (* function: f *)
        { (* arg 2 to f: unsafe_get a i *)
          imp_app τ[array;Z].
          (* continuation for unsafe_get *)
          iIntros "Hm".
          iApply ("Hm" $! A with "[%] Hslice").
          - split; eassumption.
          - iPureIntro; lia.
          - iPureIntro; length; lia. }
        (* continuation for f: gets i and element *)
        iIntros "(%Hlookup & Hslice) Hm".
        iSpecialize ("Hm" with "[%]"); first lia.
        iApply (imp_mono_ret with "Hm [Hslice HΦs]").
        rewrite Hlookup. lookup.
        iIntros (y) "$". iFrame. }

      (* continuation for unsafe_set: all three args resolved *)
      iIntros "(Hslice & HΦy & HΦs) Hm".
      iSpecialize ("Hm" $! (length xs) 0 (ys ++ seg i (length xs) xs) (λ x', ⌜x'=x⌝)%I
                     with "[%] Hslice [//] [%] [%]"); try (length; lia).
      iApply (imp_mono_ret with "Hm [HΦy HΦs]").
      iIntros ([]) "(% & -> & Hslice)".
      iExists (ys ++ [x]). iSplitL "Hslice".
      + rewrite (split_seg (i+1)); try lia.
        rewrite seg_is_singleton'; try lia. update.
        rewrite app_assoc. iFrame.
      + rewrite (split_seg i xs 0 (i+1)); try lia.
        iApply (big_sepLZ2_app with "HΦs").
        rewrite seg_is_singleton'; try lia.
        iApply big_sepLZ2_singleton. length. lookup.
        replace (i + (i - length ys)) with i by lia. by rewrite Z.add_0_r.

    - iIntros ([]) "(%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      revert Hlenys; length; intros.
      seg. iFrame.
      iSplit; iPureIntro; lia.
  Qed.

End mapi_inplace_spec.


Section map2_spec.

  Context `{!osirisGS Σ}.

  (** [map2 f a b] applies function [f] to all elements of [a] and [b]
      pairwise, and builds an array with the results. *)
  Definition map2_spec : val → array → array → microvx → iProp Σ :=
    λ f a b m,
      (∀ (A B C : Type) (_ : Encode A) (_ : Encode B) (_ : Encode C)
         (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (Φ : A → B → C → iProp Σ),
         ⌜length xs = length ys⌝ -∗
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; B] f (λ (x : A) (y : B) m, imp m {{ λ (z : C), Φ x y z }}) -∗
         imp m {{ λ a', ∃ (zs : list C),
                    ⌜length zs = length xs⌝ ∗
                    ownArray a' zs ∗
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    [∗ list] t ∈ zip (zip xs ys) zs, Φ t.1.1 t.1.2 t.2 }})%I.

End map2_spec.


Section iteri_spec.

  Context `{!osirisGS Σ}.


  (** [iteri f a] applies function [f] to the index and all elements of [a],
      in order. Like [iter] but [f] also receives the index. *)
  Definition iteri_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) dq (xs : list A) (I : list A → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ∀ (Xs : list A),
                              ⌜Xs ++ singleton x `prefix_of` xs⌝ -∗
                              ⌜length Xs = i⌝ -∗
                              I Xs -∗
                              imp m {{ λ (_ : unit), I (Xs ++ singleton x) }}) -∗
         I [] -∗
         imp m {{ λ (_ : unit), I xs ∗ isSlice dq a 0 xs }})%I.

  Definition iteri := (EAnonFun __fun109).

  Lemma imp_iteri η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    imp (eval η iteri) {{ λ c, □ iSpec τ[val; array] c iteri_spec }}.
  Proof.
    iIntros "#Hlookup #Hlookup'".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA dq xs I) "(%Hlen & %Hbound) Hslice #Hf HI".
    iApply imp_please; iNext.
    iApply (imp_mono_ret with "[-]").
    - imp_for 0 to (length xs - 1)
        $! (λ i, isSlice dq a 0 xs ∗ ∃ Xs, I Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [HI Hslice]".
      { imp_arith.
        imp_app τ[array].
        iIntros "Hm". iApply (imp_mono_ret with "[Hm]").
        - iApply "Hm".
          iPureIntro; split; eassumption.
        - iIntros (?) "->". auto. }

      { (* Establish the invariant when [i = 0]. *)
        iFrame. iPureIntro. split; [ by length | apply prefix_nil ]. }

      iIntros (i') "%Hi' (Hslice & (%Xs & HI & %HlenXs & %Hprefix))".
      (* f i (unsafe_get a i) *)
      imp_app τ[Z;A] with "[] [] [Hslice]".
      (* unsafe_get a i *)
      { imp_app τ[array;Z].
        iIntros "Hm".
        iApply ("Hm" $! A with "[] Hslice").
        - iPureIntro. split; eassumption.
        - iPureIntro; lia.
        - iPureIntro; lia. }
      iIntros "(%Hget & Hslice) Hm".
      assert (Xs ++ singleton x `prefix_of` xs).
      { destruct Hprefix as (xrest & ->); rewrite length_app in Hi'.
        apply prefix_app.
        apply singleton_prefix; first lia.
        rewrite Hget. lookup.
        by rewrite HlenXs Z.sub_diag. }
      iSpecialize ("Hm" with "[//] [//] HI").

      iApply (imp_mono_ret with "Hm").
      iIntros ([]) "$". iFrame.
      iPureIntro; split; [ length; lia | assumption ].

    - iIntros ([]) "($ & %Xs & HI & %HlenXs & %Hprefix)".
      by rewrite (complete_prefix Xs xs); [ | lia | assumption ].
  Qed.

End iteri_spec.


Section mapi_spec.

  Context `{!osirisGS Σ}.


  (** [mapi f a] applies function [f] to the index and all elements of [a],
      and builds an array with the results. *)
  Definition mapi_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (Φ : Z → A → B → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ⌜0 ≤ i < length xs⌝ -∗
                              imp m {{ λ (y : B), Φ i x y }}) -∗
         imp m {{ λ a', ∃ (ys : list B),
                    ownArray a' ys ∗
                    isSlice dq a 0 xs ∗
                    [∗ listZ] i↦x;y ∈ xs;ys, Φ i x y }})%I.

End mapi_spec.


Section to_list_spec.

  Context `{!osirisGS Σ}.


  (** [to_list a] returns a list containing the elements of [a]. *)
  Definition to_list_spec : array → microvx → iProp Σ :=
    λ a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) dq (xs : list A),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         imp m {{ λ (ys : list A), ⌜ys = xs⌝ ∗ isSlice dq a 0 xs }})%I.

End to_list_spec.


Section of_list_spec.

  Context `{!osirisGS Σ}.


  (** [of_list l] returns a fresh array containing the elements of [l]. *)
  Definition of_list_spec : val → microvx → iProp Σ :=
    λ l m,
      (∀ (A : Type) (_ : Encode A) (xs : list A),
         ⌜l = #xs⌝ -∗
         ⌜length xs ≤ max_array⌝ -∗
         imp m {{ λ a, ownArray a xs }})%I.

End of_list_spec.


Section equal_spec.

  Context `{!osirisGS Σ}.


  (** [equal eq a b] tests whether [a] and [b] are element-wise equal,
      using [eq] to compare elements. *)
  Definition equal_spec : val → array → array → microvx → iProp Σ :=
    λ eq a b m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq1 dq2 (xs ys : list A) (P : A → A → Prop) (_ : ∀ x y, Decision (P x y)),
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; A] eq (λ (x : A) (y : A) m,
                               imp m {{ λ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         imp m {{ λ (r : bool),
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    ⌜r = true ↔ length xs = length ys ∧ Forall2 P xs ys⌝ }})%I.

End equal_spec.


Section compare_spec.

  Context `{!osirisGS Σ}.


  (** [compare cmp a b] compares arrays lexicographically using [cmp]
      for elements. Returns an integer: negative, zero, or positive. *)
  Definition compare_spec : val → array → array → microvx → iProp Σ :=
    λ cmp a b m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq1 dq2 (xs ys : list A) (f : A → A → Z),
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; A] cmp (λ (x : A) (y : A) m,
                                imp m {{ λ (c : Z), ⌜c = f x y⌝ }}) -∗
         imp m {{ λ (r : Z),
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    ⌜(length xs ≠ length ys → r = if bool_decide (length xs < length ys) then -1 else 1) ∧
                     (length xs = length ys → (r = 0 ↔ Forall2 (λ x y, f x y = 0) xs ys))⌝ }})%I.

End compare_spec.


Section fold_left_spec.

  Context `{!osirisGS Σ}.


  (** [fold_left f init a] computes [f (... (f (f init a.(0)) a.(1)) ...) a.(n-1)]. *)
  Definition fold_left_spec A `{Encode A} : val → A → array → microvx → iProp Σ :=
    λ f x a m,
      (∀ (B : Type) (_ : Encode B) (_ : Inhabited B)
         dq (xs : list B) (I : A → list B → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A; B] f (λ (acc : A) (b : B) m,
                              ∀ (visited : list B),
                              ⌜visited ++ singleton b `prefix_of` xs⌝ -∗
                              I acc visited -∗
                              imp m {{ λ (acc' : A), I acc' (visited ++ singleton b) }}) -∗
         I x [] -∗
         imp m {{ λ (r : A), I r xs ∗ isSlice dq a 0 xs }})%I.

  Definition fold_left := (EAnonFun __fun162).

  Lemma imp_fold_left η :
    in_env "length" array_length_spec η -∗
    in_env "unsafe_get" array_get_spec η -∗
    imp (eval η fold_left) {{ λ c, ∀ `(Encode A), □ iSpec τ[val; A; array] c (fold_left_spec A) }}.
  Proof.
    iIntros "#Hlookup #Hlookup'".
    iApply imp_EAnon_poly_pers.
    iIntros (A HencA) "!>".
    iIntros (f x a B HencB HinhB dq xs I) "(%Hlen & %Hbound) Hslice #Hf HI".
    iApply imp_please; iNext.

    (* let r = ref x in ... *)
    iApply (imp_ELet_var (B:=locations.loc)).
    { imp_ref x. }
    iIntros (r) "Hr".

    (* for i = 0 to length a - 1 do r := f !r (unsafe_get a i) done; !r *)
    iApply (imp_ESeq with "[Hslice HI Hr]").
    { imp_for 0 to (length xs - 1) $!
        (λ i, isSlice dq a 0 xs ∗
              ∃ (acc : A) (Xs : list B),
                r ↦ #acc ∗ I acc Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [Hr HI Hslice]".
      { imp_arith.
        imp_app τ[array].
        iIntros "Hm". iApply (imp_mono_ret with "[-]").
        - iApply "Hm".
          iPureIntro; split; eassumption.
        - iIntros (?) "->". auto. }

      { (* Establish the invariant for [i = 0]. *)
        iFrame. iPureIntro. split; first by length. apply prefix_nil. }

      iIntros (i') "%Hi' (Hslice & %acc & %Xs & Hr & HI & <- & %Hprefix)".
      (* r := f !r (unsafe_get a i) *)
      iApply (imp_mono_ret with "[Hr HI Hslice]").
      set_postcondition
        (λ (_ : unit), ∃ x X, ⌜Xs ++ singleton X `prefix_of` xs⌝ ∗
                              r ↦ #x ∗ isSlice dq a 0 xs ∗ I x (Xs ++ singleton X))%I.
      - iApply (imp_EStore2 (A:=A) with "[] [Hr HI Hslice]").
        imp_path.
        + (* f !r (unsafe_get a i) *)
          set_postcondition
            (λ x, ∃ X, ⌜Xs ++ singleton X `prefix_of` xs⌝ ∗
                       r ↦ #acc ∗ isSlice dq a 0 xs ∗ I x (Xs ++ singleton X))%I.
          imp_app τ[A; B] with "[] [Hr] [Hslice]".
          { (* unsafe_get a i *)
            imp_app τ[array;Z].
            iIntros "Hm".
            iApply ("Hm" $! B with "[] Hslice").
            - iPureIntro. split; eassumption.
            - iPureIntro; lia.
            - iPureIntro; lia. }
          (* continuation after getting the element *)
          iIntros "(-> & Hr) (-> & Hslice) Hm". rewrite Z.sub_0_r.
          apply prefix_snoc in Hprefix; last lia.
          iSpecialize ("Hm" with "[//] HI").

          iApply (imp_mono_ret with "Hm").
          iIntros (acc'') "HI".
          iFrame. iPureIntro; assumption.
        + iIntros (?) "(%acc' & Hpref & Hr & Hslice & HI)".
          iFrame.
          iIntros "!> !> $". iFrame.
      - iIntros ([]) "(% & % & Hpref & Hr & Hslice & HI)".
        iFrame. iPureIntro; length; lia. }

    iIntros "(Hslice & %acc' & %Xs & Hr & HI & %HlenXs & %Hprefix)".
    iApply (imp_mono_ret with "[Hr]"). { imp_load r. }
    iIntros (?) "(-> & Hr)". iFrame.
    rewrite (complete_prefix Xs xs); [ | lia | assumption ].
    iApply "HI".
  Qed.

End fold_left_spec.


Section fold_left_map_spec.

  Context `{!osirisGS Σ}.
  Context (A : Type) `{!Encode A}.


  (** [fold_left_map f acc input_array] is like [fold_left] but also builds
      an output array from the second component of [f]'s return value. *)
  Definition fold_left_map_spec : val → A → array → microvx → iProp Σ :=
    λ f x input_array m,
      (∀ (B C : Type) (_ : Encode B) (_ : Encode C) (_ : Inhabited B)
         dq (xs : list B) (Φ : A → B → A → C → iProp Σ),
         isArray input_array (length xs) -∗
         isSlice dq input_array 0 xs -∗
         □ iSpec τ[A; B] f (λ (acc : A) (b : B) m,
                              imp m {{ λ (p : A * C), Φ acc b p.1 p.2 }}) -∗
         imp m {{ λ (p : A * array), ∃ (ys : list C),
                    ⌜length ys = length xs⌝ ∗
                    isSlice dq input_array 0 xs ∗
                    ownArray p.2 ys ∗
                    ⌜True⌝ (* TODO: characterize the final accumulator and output *) }})%I.

End fold_left_map_spec.


Section fold_right_spec.

  Context `{!osirisGS Σ}.
  Context (B : Type) `{!Encode B}.


  (** [fold_right f a init] computes [f a.(0) (f a.(1) (... (f a.(n-1) init) ...))]. *)
  Definition fold_right_spec : val → array → B → microvx → iProp Σ :=
    λ f a x m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (I : B → Z → iProp Σ),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A; B] f (λ (a : A) (b : B) m,
                              ∀ i, ⌜0 ≤ i < length xs⌝ -∗
                                   ⌜xs !!! i = a⌝ -∗
                                   I b (i + 1) -∗
                                   imp m {{ λ (b' : B), I b' i }}) -∗
         I x (length xs) -∗
         imp m {{ λ (r : B), I r 0 ∗ isSlice dq a 0 xs }})%I.

End fold_right_spec.


Section exists_spec.

  Context `{!osirisGS Σ}.


  (** [exists p a] checks if at least one element of [a] satisfies [p]. *)
  Definition exists_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           imp m {{ λ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         imp m {{ λ (b : bool),
                    isSlice dq a 0 xs ∗
                    ⌜b = true ↔ Exists P xs⌝ }})%I.

End exists_spec.


Section for_all_spec.

  Context `{!osirisGS Σ}.


  (** [for_all p a] checks if all elements of [a] satisfy the predicate [p]. *)
  Definition for_all_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           imp m {{ λ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         imp m {{ λ (b : bool),
                    isSlice dq a 0 xs ∗
                    ⌜b = true ↔ Forall P xs⌝ }})%I.

End for_all_spec.


Section for_all2_spec.

  Context `{!osirisGS Σ}.


  (** [for_all2 p a b] checks if all corresponding elements of [a] and [b]
      satisfy the predicate [p]. Raises if the arrays have different lengths. *)
  Definition for_all2_spec : val → array → array → microvx → iProp Σ :=
    λ p a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (P : A → B → Prop) (_ : ∀ x y, Decision (P x y)),
         ⌜length xs = length ys⌝ -∗
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; B] p (λ (x : A) (y : B) m,
                              imp m {{ λ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         imp m {{ λ (r : bool),
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    ⌜r = true ↔ Forall2 P xs ys⌝ }})%I.

End for_all2_spec.


Section exists2_spec.

  Context `{!osirisGS Σ}.


  (** [exists2 p a b] checks if there exist corresponding elements of [a]
      and [b] that satisfy [p]. Raises if the arrays have different lengths. *)
  Definition exists2_spec : val → array → array → microvx → iProp Σ :=
    λ p a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (P : A → B → Prop) (_ : ∀ x y, Decision (P x y)),
         ⌜length xs = length ys⌝ -∗
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         □ iSpec τ[A; B] p (λ (x : A) (y : B) m,
                              imp m {{ λ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         imp m {{ λ (r : bool),
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    ⌜r = true ↔ Exists (λ p, P p.1 p.2) (zip xs ys)⌝ }})%I.

End exists2_spec.


(* TODO: mem and memq use stdlib compare / physical equality,
   which are not yet modeled. *)


Section find_opt_spec.

  Context `{!osirisGS Σ}.


  (** [find_opt p a] returns the first element of [a] that satisfies [p],
      or [None] if no such element exists. *)
  Definition find_opt_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           imp m {{ λ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         imp m {{ λ (r : option A),
                    isSlice dq a 0 xs ∗
                    match r with
                    | Some x => ⌜x ∈ xs ∧ P x⌝
                    | None => ⌜Forall (λ x, ¬ P x) xs⌝
                    end }})%I.

End find_opt_spec.


Section find_index_spec.

  Context `{!osirisGS Σ}.


  (** [find_index p a] returns the index of the first element that
      satisfies [p], or [None]. *)
  Definition find_index_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           imp m {{ λ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         imp m {{ λ (r : option Z),
                    isSlice dq a 0 xs ∗
                    match r with
                    | Some i => ⌜0 ≤ i < length xs ∧ P (xs !!! i) ∧
                                  Forall (λ x, ¬ P x) (take i xs)⌝
                    | None => ⌜Forall (λ x, ¬ P x) xs⌝
                    end }})%I.

End find_index_spec.


Section find_map_spec.

  Context `{!osirisGS Σ}.


  (** [find_map f a] applies [f] to each element and returns the first
      [Some] result, or [None] if [f] returns [None] on all elements. *)
  Definition find_map_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (g : A → option B),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[A] f (λ (x : A) m,
                           imp m {{ λ (r : option B), ⌜r = g x⌝ }}) -∗
         imp m {{ λ (r : option B),
                    isSlice dq a 0 xs ∗
                    match r with
                    | Some y => ⌜∃ x, x ∈ xs ∧ g x = Some y⌝
                    | None => ⌜Forall (λ x, g x = None) xs⌝
                    end }})%I.

End find_map_spec.


Section find_mapi_spec.

  Context `{!osirisGS Σ}.


  (** [find_mapi f a] applies [f] to the index and each element and returns
      the first [Some] result, or [None]. *)
  Definition find_mapi_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (g : Z → A → option B),
         isArray a (length xs) -∗
         isSlice dq a 0 xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ⌜0 ≤ i < length xs⌝ -∗
                              imp m {{ λ (r : option B), ⌜r = g i x⌝ }}) -∗
         imp m {{ λ (r : option B),
                    isSlice dq a 0 xs ∗
                    match r with
                    | Some y => ⌜∃ i, 0 ≤ i < length xs ∧ g i (xs !!! i) = Some y⌝
                    | None => ⌜∀ i, 0 ≤ i < length xs → g i (xs !!! i) = None⌝
                    end }})%I.

End find_mapi_spec.


Section split_spec.

  Context `{!osirisGS Σ}.


  (** [split x] takes an array of pairs and returns a pair of arrays. *)
  Definition split_spec : array → microvx → iProp Σ :=
    λ x m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited (A * B))
         dq (ps : list (A * B)),
         isArray x (length ps) -∗
         isSlice dq x 0 ps -∗
         imp m {{ λ (r : array * array),
                    isSlice dq x 0 ps ∗
                    ownArray r.1 (fst <$> ps) ∗
                    ownArray r.2 (snd <$> ps) }})%I.

End split_spec.


Section combine_spec.

  Context `{!osirisGS Σ}.


  (** [combine a b] takes two arrays and returns an array of pairs.
      Raises if the arrays have different lengths. *)
  Definition combine_spec : array → array → microvx → iProp Σ :=
    λ a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B),
         ⌜length xs = length ys⌝ -∗
         isArray a (length xs) -∗ isSlice dq1 a 0 xs -∗
         isArray b (length ys) -∗ isSlice dq2 b 0 ys -∗
         imp m {{ λ r,
                    isSlice dq1 a 0 xs ∗
                    isSlice dq2 b 0 ys ∗
                    ownArray r (zip xs ys) }})%I.

End combine_spec.


(* TODO: sort, stable_sort, stable_sort_sub, fast_sort. *)

(* TODO: shuffle is EUnsupported in the translation. *)

(* TODO: to_seq, to_seqi, of_rev_list, of_seq depend on Seq module. *)

Section module_proof.
  Context `{!osirisGS Σ}.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Definition array_module_dom : gset var :=
    {[ "length";
        "get";
        "set";
        "unsafe_get";
        "unsafe_set";
        "make";
        "unsafe_sub";
        "append_prim";
        "concat";
        "unsafe_blit";
        "unsafe_fill";
        "create_float";
        "Floatarray";
        "init";
        "make_matrix";
        "init_matrix";
        "copy";
        "append";
        "sub";
        "fill";
        "blit";
        "iter";
        "iter2";
        "map";
        "map_inplace";
        "mapi_inplace";
        "map2";
        "iteri";
        "mapi";
        "to_list";
        "list_length";
        "of_list";
        "equal";
        "stdlib_compare";
        "compare";
        "fold_left";
        "fold_left_map";
        "fold_right";
        "fold_left2";
        "fold_right2";
        "exists";
        "for_all";
        "for_all2";
        "exists2";
        "mem";
        "memq";
        "find_opt";
        "find_index";
        "find_map";
        "find_mapi";
        "split";
        "combine";
        "Bottom";
        "sort";
        "cutoff";
        "unsafe_stable_sort_sub";
        "stable_sort_sub";
        "stable_sort";
        "fast_sort";
        "shuffle_contract_violation";
        "shuffle";
        "to_seq";
        "to_seqi";
        "of_rev_list";
        "of_seq"
    ]}.

  Definition array_module_spec : env → iProp Σ :=
    (context [
         var_spec "init" (λ init, □ iSpec τ[Z; val] init init_spec);
         var_spec "iter" (λ iter, □ iSpec τ[val;array] iter iter_spec);
         var_spec "iteri" (λ iteri, □ iSpec τ[val;array] iteri iteri_spec);
         var_spec "fold_left" (λ fold_left, ∀ A (HencA : Encode A), □ iSpec τ[val;A;array] fold_left (fold_left_spec A));
         var_spec "map" (λ map, □ iSpec τ[val;array] map map_spec);
         var_spec "map_inplace" (λ map_inplace, □ iSpec τ[val;array] map_inplace map_inplace_spec);
         var_spec "mapi_inplace" (λ mapi_inplace, □ iSpec τ[val;array] mapi_inplace mapi_inplace_spec)
      ] array_module_dom)%I.

  Global Instance array_spec_pers η : Persistent (array_module_spec η).
  Proof. apply _. Qed.

  Lemma module_proof η :
    ⊢ imp (eval_mexpr η __main) {{ array_module_spec }}.
  Proof.
    iApply imp_module.
    iApply imp_externals_length. iIntros (length) "#Hlength".
    iApply imp_externals_get. iIntros (get) "#Hget".
    iApply imp_externals_set. iIntros (set) "#Hset".
    iApply imp_externals_get. iIntros (safe_get) "#Hsafe_get".
    iApply imp_externals_set. iIntros (safe_set) "#Hsafe_set".
    iApply imp_externals_make. iIntros (make) "#Hmake".

    iApply (imp_sitems_module).
    { simpl_eval_mexpr.
      iApply imp_ret; first encode.
      instantiate (1 := (λ δ, ⌜δ = []⌝)%I). done. }
    iIntros (? ->).

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_init; (iFrame "#"; auto). }
    iIntros (init) "#Hinit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (make_matrix) "Hmake_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (init_matrix) "Hinit_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (copy) "Hcopy".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (append) "Happend".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sub) "Hsub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fill) "Hfill".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (blit) "Hblit".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_iter; (iFrame "#"; auto). }
    iIntros (iter) "#Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter2) "Hiter2".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_map; (iFrame "#"; auto). }
    iIntros (map) "#Hmap".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_map_inplace; (iFrame "#"; auto). }
    iIntros (map_inplace) "#Hmap_inplace".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_mapi_inplace; (iFrame "#"; auto). }
    iIntros (mapi_inplace) "#Hmapi_inplace".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map2) "Hmap2".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_iteri; (iFrame "#"; auto). }
    iIntros (iteri) "#Hiteri".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mapi) "Hmapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_list) "Hto_list".

    iApply (imp_sitems_letrec).
    { admit. }
    iIntros (list_length) "Hlist_length".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_list) "Hof_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (equal) "Hequal".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stdlib_compare) "Hstdlib_compare".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (compare) "Hcompare".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_fold_left; (iFrame "#"; auto). }
    iIntros (fold_left) "#Hfold_left".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_left_map) "Hfold_left_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_right) "Hfold_right".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_right_map) "Hfold_right_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all) "Hfor_all".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all2) "Hfor_all2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (vexists2) "Hexists2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mem) "Hmem".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (memq) "Hmemq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_opt) "Hfind_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_index) "Hfind_index".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_map) "Hfind_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_mapi) "Hfind_mapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (split) "Hsplit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (combine) "Hcombine".

    iApply (imp_sitems_extend).
    iIntros (bottom) "Hbottom".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sort) "Hsort".

    iApply (imp_sitems_let (A:=Z)).
    { iApply imp_EInt. }
    iIntros (?) "->".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (unstable_sort) "Hunstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort_sub) "Hstable_sort_sub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort) "Hstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_EPath; first auto. admit. }
    iIntros (fast_sort) "Hfast_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle_contract_violation) "Hshuffle_contract_violation".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle) "Hshuffle".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seqi) "Hto_seqi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_rev_list) "Hof_rev_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.

  Admitted.

End module_proof.
