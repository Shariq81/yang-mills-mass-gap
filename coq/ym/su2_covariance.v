(* =========================================================================
   ym/su2_covariance.v

   Covariance of the finite-volume Gibbs expectations of the 4D SU(2)
   Wilson lattice gauge theory under the lattice symmetries of
   `verification/ChallengeSU2MassGap.v`:

     - `expect_translate`: the expectation of a translated observable in the
       volume Lam is the expectation of the observable in the volume Lam
       translated the other way;
     - `expect_reflect`: the expectation of the time-reflected observable in
       Lam is the expectation of the observable in the reflected volume,
       when the a-priori link distribution is invariant under inversion.

   Both follow from the change-of-variables lemma `csum_relabel` of
   rg/product_measure_relabel.v and the covariance of the Wilson action
   (ym/lattice_symmetry.v).

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + rg.product_measure + rg.product_measure_perm
   + rg.product_measure_relabel + ym.z2_gauge_expansion + ym.z2_polymer_gas
   + ym.su2_algebra + ym.su2_area_law + ym.lattice_symmetry.
   Zero postulates: every statement below is a closed theorem.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import rg.product_measure_relabel.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_polymer_gas.
Require Import ym.su2_algebra.
Require Import ym.su2_area_law.
Require Import ym.lattice_symmetry.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import DupClustering Z2GaugeExpansion SU2Algebra LatticeSymmetry.
Open Scope R_scope.

Module SU2Covariance.

  (* =======================================================================
     1. The link set of a translated / reflected volume
     ======================================================================= *)

  Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
  Proof.
    intros A B f l Hinj H. induction H as [| x l Hx Hl IH]; cbn [map]; constructor.
    - intro Hin. apply (proj1 (in_map_iff _ _ _)) in Hin. destruct Hin as [y [Hy Hin]].
      apply Hinj in Hy. subst y. exact (Hx Hin).
    - exact IH.
  Qed.

  Lemma link_unshift_inj : forall d a b, link_unshift d a = link_unshift d b -> a = b.
  Proof.
    intros d a b H.
    rewrite <- (link_shift_unshift d a), <- (link_shift_unshift d b), H. reflexivity.
  Qed.

  Lemma link_reflect_inj : forall a b, link_reflect a = link_reflect b -> a = b.
  Proof.
    intros a b H.
    rewrite <- (link_reflect_invol a), <- (link_reflect_invol b), H. reflexivity.
  Qed.

  Lemma links_unshift_perm : forall d (Lam : list Plaq4D),
    Permutation (map (link_unshift d) (z2_links Lam)) (z2_links (map (plaq_unshift d) Lam)).
  Proof.
    intros d Lam. unfold z2_links. apply NoDup_Permutation.
    - apply NoDup_map_inj; [apply link_unshift_inj | apply SU2AreaLaw.dedup_NoDup].
    - apply SU2AreaLaw.dedup_NoDup.
    - intro l. split; intro H.
      + apply (proj1 (in_map_iff _ _ _)) in H. destruct H as [l0 [Hl0 Hin]]. subst l.
        apply (proj1 (Z2PolymerGas.dedup_In _ _)) in Hin.
        apply (proj1 (in_flat_map _ _ _)) in Hin. destruct Hin as [p [Hp Hlp]].
        apply (proj2 (Z2PolymerGas.dedup_In _ _)). apply (proj2 (in_flat_map _ _ _)).
        exists (plaq_unshift d p). split; [apply in_map; exact Hp |].
        rewrite links_plaq_unshift. apply in_map. exact Hlp.
      + apply (proj1 (Z2PolymerGas.dedup_In _ _)) in H.
        apply (proj1 (in_flat_map _ _ _)) in H. destruct H as [p' [Hp' Hl]].
        apply (proj1 (in_map_iff _ _ _)) in Hp'. destruct Hp' as [p [Hpp Hp]]. subst p'.
        rewrite links_plaq_unshift in Hl.
        apply (proj1 (in_map_iff _ _ _)) in Hl. destruct Hl as [l0 [Hl0 Hin]]. subst l.
        apply in_map. apply (proj2 (Z2PolymerGas.dedup_In _ _)).
        apply (proj2 (in_flat_map _ _ _)). exists p. split; assumption.
  Qed.

  Lemma links_reflect_perm : forall Lam : list Plaq4D, Forall wf_plaq_4D Lam ->
    Permutation (map link_reflect (z2_links Lam)) (z2_links (map plaq_reflect Lam)).
  Proof.
    intros Lam HLam. unfold z2_links. apply NoDup_Permutation.
    - apply NoDup_map_inj; [apply link_reflect_inj | apply SU2AreaLaw.dedup_NoDup].
    - apply SU2AreaLaw.dedup_NoDup.
    - intro l. split; intro H.
      + apply (proj1 (in_map_iff _ _ _)) in H. destruct H as [l0 [Hl0 Hin]]. subst l.
        apply (proj1 (Z2PolymerGas.dedup_In _ _)) in Hin.
        apply (proj1 (in_flat_map _ _ _)) in Hin. destruct Hin as [p [Hp Hlp]].
        apply (proj2 (Z2PolymerGas.dedup_In _ _)). apply (proj2 (in_flat_map _ _ _)).
        exists (plaq_reflect p). split; [apply in_map; exact Hp |].
        apply (proj2 (links_plaq_reflect p (link_reflect l0)
                        (proj1 (Forall_forall _ _) HLam p Hp))).
        rewrite link_reflect_invol. exact Hlp.
      + apply (proj1 (Z2PolymerGas.dedup_In _ _)) in H.
        apply (proj1 (in_flat_map _ _ _)) in H. destruct H as [p' [Hp' Hl]].
        apply (proj1 (in_map_iff _ _ _)) in Hp'. destruct Hp' as [p [Hpp Hp]]. subst p'.
        apply (proj1 (links_plaq_reflect p l (proj1 (Forall_forall _ _) HLam p Hp))) in Hl.
        rewrite <- (link_reflect_invol l). apply in_map.
        apply (proj2 (Z2PolymerGas.dedup_In _ _)).
        apply (proj2 (in_flat_map _ _ _)). exists p. split; assumption.
  Qed.

  (* =======================================================================
     2. Translations
     ======================================================================= *)

  (* the Wilson action of Lam is the action of the unshifted volume at the
     translated field *)
  Lemma action_unshift : forall beta d Lam U,
    su2_wilson_action beta Lam U =
    su2_wilson_action beta (map (plaq_unshift d) Lam) (su2_translate d U).
  Proof.
    intros beta d Lam U. rewrite action_translate, map_map.
    rewrite (map_ext (fun p => plaq_shift d (plaq_unshift d p)) (fun p => p))
      by (intro p; apply plaq_shift_unshift).
    rewrite map_id. reflexivity.
  Qed.

  (* change of variables U -> U o shift_d in the a-priori sum *)
  Lemma csum_translate : forall (G : list Quat) (d : Dir4D) (Lam : list Plaq4D)
      (H : SU2Config -> R),
    csum Link4D Quat link4D_eqb G (z2_links Lam)
      (fun U => H (su2_translate d U)) (fun _ => qone) =
    csum Link4D Quat link4D_eqb G (z2_links (map (plaq_unshift d) Lam)) H (fun _ => qone).
  Proof.
    intros G d Lam H.
    assert (Hsig : forall (l : Link4D) (h : Quat -> R),
              rsum G (fun v => h ((fun (_ : Link4D) (q : Quat) => q) l v)) = rsum G h).
    { intros l h. reflexivity. }
    pose proof (ProductMeasureRelabel.csum_relabel Link4D Quat link4D_eqb link4D_eqb_spec G
                  (link_shift d) (link_unshift d)
                  (link_unshift_shift d) (link_shift_unshift d)
                  (fun (_ : Link4D) (q : Quat) => q) Hsig
                  (z2_links Lam) H (fun _ => qone)) as E.
    etransitivity; [exact E |].
    apply (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G).
    apply links_unshift_perm.
  Qed.

  (* translating an observable = translating the volume the other way *)
  Theorem expect_translate : forall (G : list Quat) (beta : R) (Lam : list Plaq4D) (d : Dir4D)
      (F : SU2Config -> R),
    su2_expect_on G beta Lam (obs_translate d F) =
    su2_expect_on G beta (map (plaq_unshift d) Lam) F.
  Proof.
    intros G beta Lam d F. rewrite !expect_csum.
    apply (f_equal2 Rdiv).
    - etransitivity;
        [| apply (csum_translate G d Lam
                    (fun V => F V * exp (- su2_wilson_action beta (map (plaq_unshift d) Lam) V)))].
      apply csum_ext. intro U. cbv beta. unfold obs_translate.
      rewrite (action_unshift beta d Lam U). reflexivity.
    - etransitivity;
        [| apply (csum_translate G d Lam
                    (fun V => exp (- su2_wilson_action beta (map (plaq_unshift d) Lam) V)))].
      apply csum_ext. intro U. cbv beta.
      rewrite (action_unshift beta d Lam U). reflexivity.
  Qed.

  (* =======================================================================
     3. Time reflection
     ======================================================================= *)

  Lemma action_unreflect : forall beta Lam U, Forall wf_plaq_4D Lam ->
    su2_wilson_action beta Lam U =
    su2_wilson_action beta (map plaq_reflect Lam) (su2_reflect U).
  Proof.
    intros beta Lam U HLam.
    assert (HLam' : Forall wf_plaq_4D (map plaq_reflect Lam)).
    { apply (proj2 (Forall_forall _ _)). intros p' Hp'.
      apply (proj1 (in_map_iff _ _ _)) in Hp'. destruct Hp' as [p [Hpp Hp]]. subst p'.
      apply plaq_reflect_wf. exact (proj1 (Forall_forall _ _) HLam p Hp). }
    rewrite (action_reflect beta (map plaq_reflect Lam) U HLam'), map_map.
    rewrite (map_ext_in (fun p => plaq_reflect (plaq_reflect p)) (fun p => p)).
    - rewrite map_id. reflexivity.
    - intros p Hp. apply plaq_reflect_invol. exact (proj1 (Forall_forall _ _) HLam p Hp).
  Qed.

  (* the reflection of the values preserves the a-priori sums *)
  Lemma refl_sigma_sum : forall G : list Quat, Permutation (map qconj G) G ->
    forall (l : Link4D) (h : Quat -> R),
    rsum G (fun v => h (refl_sigma l v)) = rsum G h.
  Proof.
    intros G HG [s dd] h. destruct dd; unfold refl_sigma; cbn [snd]; try reflexivity.
    rewrite <- (rsum_map qconj G h). apply ProductMeasure.rsum_perm. exact HG.
  Qed.

  Lemma pull_reflect_one :
    ProductMeasureRelabel.pull Link4D Quat link_reflect refl_sigma (fun _ => qone) =
    (fun _ => qone).
  Proof.
    apply functional_extensionality. intros [s dd].
    unfold ProductMeasureRelabel.pull, refl_sigma. cbn [snd].
    destruct dd; try reflexivity. apply qconj_one.
  Qed.

  (* change of variables U -> Theta U in the a-priori sum *)
  Lemma csum_reflect : forall (G : list Quat) (Lam : list Plaq4D) (H : SU2Config -> R),
    Permutation (map qconj G) G -> Forall wf_plaq_4D Lam ->
    csum Link4D Quat link4D_eqb G (z2_links Lam)
      (fun U => H (su2_reflect U)) (fun _ => qone) =
    csum Link4D Quat link4D_eqb G (z2_links (map plaq_reflect Lam)) H (fun _ => qone).
  Proof.
    intros G Lam H HG HLam.
    pose proof (ProductMeasureRelabel.csum_relabel Link4D Quat link4D_eqb link4D_eqb_spec G
                  link_reflect link_reflect link_reflect_invol link_reflect_invol
                  refl_sigma (refl_sigma_sum G HG)
                  (z2_links Lam) H (fun _ => qone)) as E.
    rewrite pull_reflect_one in E.
    etransitivity; [exact E |].
    apply (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G).
    apply links_reflect_perm. exact HLam.
  Qed.

  (* reflecting an observable = reflecting the volume, when the a-priori
     distribution is invariant under inversion *)
  Theorem expect_reflect : forall (G : list Quat) (beta : R) (Lam : list Plaq4D)
      (F : SU2Config -> R),
    Permutation (map qconj G) G -> Forall wf_plaq_4D Lam ->
    su2_expect_on G beta Lam (obs_reflect F) =
    su2_expect_on G beta (map plaq_reflect Lam) F.
  Proof.
    intros G beta Lam F HG HLam. rewrite !expect_csum.
    apply (f_equal2 Rdiv).
    - etransitivity;
        [| apply (csum_reflect G Lam
                    (fun V => F V * exp (- su2_wilson_action beta (map plaq_reflect Lam) V))
                    HG HLam)].
      apply csum_ext. intro U. cbv beta. unfold obs_reflect.
      rewrite (action_unreflect beta Lam U HLam). reflexivity.
    - etransitivity;
        [| apply (csum_reflect G Lam
                    (fun V => exp (- su2_wilson_action beta (map plaq_reflect Lam) V))
                    HG HLam)].
      apply csum_ext. intro U. cbv beta.
      rewrite (action_unreflect beta Lam U HLam). reflexivity.
  Qed.

End SU2Covariance.
