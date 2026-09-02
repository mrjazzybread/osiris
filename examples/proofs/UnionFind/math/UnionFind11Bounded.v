From osiris Require Import osiris.

Require Import UnionFind01Data UnionFind03Link.

Local Abbreviation elem := record.

(* Graph-theoretic facts about growing [F] by one edge. These feed the
   linking case of the CAS lemma [uf_cas_fupd] below. *)

(* [F]'s edges strictly decrease the identifier. This rules out cycles
   even when the target of a freshly-installed edge is no longer a root
   by the time the edge goes in. *)

Definition id_bounded (M : gmap elem Z) (F : elem → elem → Prop) : Prop :=
  ∀ w z iw iz, F w z → M !! w = Some iw → M !! z = Some iz → (iz < iw)%Z.

(* Following [F]-edges strictly decreases the identifier, given
   [id_bounded]: an easy induction along the path, confining each
   intermediate vertex into [dom M] (hence giving it an id to compare)
   via [DSF]'s own [Confined] component. *)

Lemma path_id_decrease (M : gmap elem Z) (F : elem -> elem -> Prop) :
  DSF F (dom M) ->
  id_bounded M F ->
  forall w z, rtc F w z -> forall iw iz, M !! w = Some iw -> M !! z = Some iz -> w <> z -> (iz < iw)%Z.
Proof.
  intros Hdsf Hid w z Hpath.
  induction Hpath as [w | w w' z HF Hpath IH]; intros iw iz Hiw Hiz Hne.
  - contradiction.
  - destruct Hdsf as [[Hconf'] _ _].
    destruct (Hconf' w w' HF) as [_ Hw'd].
    apply elem_of_dom in Hw'd as [iw' Hiw'].
    destruct (decide (w' = z)) as [->|Hne'].
    + exact (Hid w z iw iz HF Hiw Hiz).
    + specialize (IH iw' iz Hiw' Hiz Hne').
      pose proof (Hid w w' iw iw' HF Hiw Hiw') as Hstep.
      lia.
Qed.

Lemma dsf_link_general (M : gmap elem Z) (F : elem -> elem -> Prop) (a y' : elem) (ia iy : Z) :
  DSF F (dom M) ->
  id_bounded M F ->
  M !! a = Some ia ->
  M !! y' = Some iy ->
  Root F a ->
  (iy < ia)%Z ->
  a <> y' ->
  DSF (link F a y') (dom M) /\ id_bounded M (link F a y').
Proof.
  intros Hdsf Hid HMa HMy HRoota Hlt Hne.
  assert (HaD : a ∈ dom M) by (eapply elem_of_dom_2; eauto).
  assert (HyD : y' ∈ dom M) by (eapply elem_of_dom_2; eauto).
  pose proof (dsf_confined F) as [Hconf'].
  pose proof (dsf_defined F) as [Hdef].
  split.
  - constructor.
    + constructor. intros w z Hlink. destruct Hlink as [HF|[-> ->]].
      * exact (Hconf' w z HF).
      * split; assumption.
    + eapply functional_link; eauto.
    + constructor. intros w.
      destruct (Hdef w) as [r Hr].
      destruct (decide (r = a)) as [->|Hra].
      * destruct (Hdef y') as [ry Hry].
        destruct Hry as [Hpathyry Hrootry].
        destruct Hr as [Hpathwa _].
        assert (Hryne : ry <> a).
        { intros Heqrya.
          assert (Hneq : y' <> a) by (intros Heq; apply Hne; symmetry; exact Heq).
          rewrite Heqrya in Hpathyry.
          pose proof (path_id_decrease M F Hdsf Hid y' a Hpathyry iy ia HMy HMa Hneq) as Hgt.
          lia. }
        exists ry.
        assert (Hpathwa' : rtc (link F a y') w a).
        { eapply rtc_subrel; [|exact Hpathwa]. intros x0 y0 HFxy. left. exact HFxy. }
        assert (Hpathwy : rtc (link F a y') w y').
        { eapply rtc_r; [exact Hpathwa' | exact (link_appears F a y')]. }
        assert (Hpathyry' : rtc (link F a y') y' ry).
        { eapply rtc_subrel; [|exact Hpathyry]. intros x0 y0 HFxy. left. exact HFxy. }
        assert (Hpathwry : rtc (link F a y') w ry) by (eapply rtc_trans; eauto).
        assert (Hrootry' : Root (link F a y') ry).
        { apply is_root_link; [exact Hrootry | exact (not_eq_sym Hryne)]. }
        exact (Build_Repr _ w ry Hpathwry Hrootry').
      * exists r.
        apply is_repr_link_2; [exact Hr | exact Hra].
  - intros w z iw iz Hlink Hiw Hiz.
    destruct Hlink as [HF|[-> ->]].
    + exact (Hid w z iw iz HF Hiw Hiz).
    + simplify_eq. lia.
Qed.
