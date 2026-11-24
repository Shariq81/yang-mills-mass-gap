(* =========================================================================
   verification/Verify.v

   SOLUTION VERIFICATION MODULE.

   Assigns the repository's submitted Coq proofs:
     - ym.geometry_frontier.connects_to_simple_path
     - ym.geometry_frontier.ym_connects_implies_dist_bound_from_frontier
     - rg.cluster_expansion.sum_connecting_triangle
     - rg.cluster_expansion.connecting_geometry
     - rg.cluster_expansion.exp_monotone
     - rg.cluster_expansion.exponential_decay_from_cluster
   to the exact frozen propositions declared in `verification/Challenge.v`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import Lra.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Logic.FunctionalExtensionality.

Require Import verification.Challenge.
Require Import rg.polymer_types.
Require Import rg.cluster_expansion.
Require Import rg.penrose_tree_bound.
Require Import rg.poly_exp_bound.
Require Import rg.tree_cut_bijection.
Require Import rg.kotecky_preiss.
Require Import rg.exp_series_limit.
Require Import rg.cluster_log_partition.
Require Import ym.geometry_frontier.
Require Import ym.lattice.
Require Import ym.lattice_4d_coordination.
Require Import ym.lattice_4d_kp.

Import ListNotations.
Open Scope R_scope.

Module Verify.

  (* =======================================================================
     1. Structural Equivalence Lemmas (Challenge defs <-> Submitted repo defs)
     ======================================================================= *)

  Section Bridge.
    Context {P : Type} `{PolymerSystem P} `{MetricSystem P} `{ConnectivitySystem P} `{UrsellSystem P}.

    Lemma path_challenge_to_repo :
      forall X p1 p2,
        Challenge.path_in_cluster adj X p1 p2 ->
        cluster_expansion.path_in_cluster X p1 p2.
    Proof.
      intros X p1 p2 Hpath.
      induction Hpath as [X' p Hin | X' p q r Hin Hadj _ IH].
      - exact (cluster_expansion.path_refl X' p Hin).
      - exact (cluster_expansion.path_step X' p q r Hin Hadj IH).
    Qed.

    Lemma path_repo_to_challenge :
      forall X p1 p2,
        cluster_expansion.path_in_cluster X p1 p2 ->
        Challenge.path_in_cluster adj X p1 p2.
    Proof.
      intros X p1 p2 Hpath.
      induction Hpath as [X' p Hin | X' p q r Hin Hadj _ IH].
      - exact (Challenge.path_refl adj X' p Hin).
      - exact (Challenge.path_step adj X' p q r Hin Hadj IH).
    Qed.

    Lemma connects_iff :
      forall X p1 p2,
        Challenge.connects adj X p1 p2 <->
        cluster_expansion.connects X p1 p2.
    Proof.
      intros X p1 p2.
      unfold Challenge.connects, cluster_expansion.connects.
      split; intros [Hp1 [Hp2 Hpath]]; repeat split; try assumption.
      - apply path_challenge_to_repo. exact Hpath.
      - apply path_repo_to_challenge. exact Hpath.
    Qed.

    Lemma lists_of_length_eq :
      forall (eq_dec : forall x y : P, {x = y} + {x <> y}) k pool,
        Challenge.lists_of_length eq_dec k pool =
        cluster_expansion.lists_of_length P eq_dec k pool.
    Proof.
      intros eq_dec k.
      induction k as [| k' IH]; intros pool; simpl.
      - reflexivity.
      - f_equal. apply functional_extensionality.
        intro p. f_equal. apply IH.
    Qed.

    Lemma lists_up_to_length_eq :
      forall (eq_dec : forall x y : P, {x = y} + {x <> y}) n pool,
        Challenge.lists_up_to_length eq_dec n pool =
        cluster_expansion.lists_up_to_length P eq_dec n pool.
    Proof.
      intros eq_dec n pool.
      induction n as [| n' IH].
      - reflexivity.
      - cbn [Challenge.lists_up_to_length cluster_expansion.lists_up_to_length].
        rewrite IH, lists_of_length_eq. reflexivity.
    Qed.

    Lemma clusters_Λ_N_eq :
      forall (eq_dec : forall x y : P, {x = y} + {x <> y}) polymers_Λ N_max,
        Challenge.clusters_Λ_N eq_dec polymers_Λ N_max =
        cluster_expansion.clusters_Λ_N P eq_dec polymers_Λ N_max.
    Proof.
      intros eq_dec polymers_Λ N_max.
      unfold Challenge.clusters_Λ_N, cluster_expansion.clusters_Λ_N.
      apply lists_up_to_length_eq.
    Qed.

    Lemma cluster_size_eq :
      forall c,
        Challenge.cluster_size size c = cluster_expansion.cluster_size c.
    Proof.
      induction c as [| p rest IH]; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    Lemma prod_activity_eq :
      forall c,
        Challenge.prod_activity activity c = cluster_expansion.prod_activity c.
    Proof.
      induction c as [| p rest IH]; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    Lemma cluster_weight_eq :
      forall c,
        Challenge.cluster_weight ursell_factor activity c =
        cluster_expansion.cluster_weight c.
    Proof.
      intro c.
      unfold Challenge.cluster_weight, cluster_expansion.cluster_weight.
      rewrite prod_activity_eq. reflexivity.
    Qed.

    Definition repo_connects_dec
      (cdec : forall (X : Challenge.Cluster P) (p1 p2 : P),
          {Challenge.connects adj X p1 p2} + {~ Challenge.connects adj X p1 p2})
      : forall (X : cluster_expansion.Cluster P) (p1 p2 : P),
          {cluster_expansion.connects X p1 p2} + {~ cluster_expansion.connects X p1 p2}.
    Proof.
      intros X p1 p2.
      destruct (cdec X p1 p2) as [Hc | Hnc].
      - left. apply connects_iff. exact Hc.
      - right. intro Hc. apply Hnc. apply connects_iff. exact Hc.
    Defined.

    Lemma sum_connecting_eq :
      forall (eq_dec : forall x y : P, {x = y} + {x <> y})
             (polymers_Λ : list P) (N_max : nat)
             (cdec : forall (X : Challenge.Cluster P) (p1 p2 : P),
                 {Challenge.connects adj X p1 p2} + {~ Challenge.connects adj X p1 p2})
             (p1 p2 : P) (f g : list P -> R),
        (forall X, f X = g X) ->
        Challenge.sum_connecting adj eq_dec polymers_Λ N_max cdec p1 p2 f =
        cluster_expansion.sum_connecting_concrete eq_dec polymers_Λ N_max
          (repo_connects_dec cdec) p1 p2 g.
    Proof.
      intros eq_dec polymers_Λ N_max cdec p1 p2 f g Hfg.
      unfold Challenge.sum_connecting, cluster_expansion.sum_connecting_concrete.
      rewrite clusters_Λ_N_eq.
      f_equal. apply map_ext. intro X.
      unfold repo_connects_dec.
      destruct (cdec X p1 p2) as [Hc | Hnc]; [apply Hfg | reflexivity].
    Qed.

    Lemma correlator_eq :
      forall (eq_dec : forall x y : P, {x = y} + {x <> y})
             (polymers_Λ : list P) (N_max : nat)
             (cdec : forall (X : Challenge.Cluster P) (p1 p2 : P),
                 {Challenge.connects adj X p1 p2} + {~ Challenge.connects adj X p1 p2})
             (p1 p2 : P),
        Challenge.correlator adj eq_dec polymers_Λ N_max cdec ursell_factor activity p1 p2 =
        cluster_expansion.correlator eq_dec polymers_Λ N_max (repo_connects_dec cdec) p1 p2.
    Proof.
      intros eq_dec polymers_Λ N_max cdec p1 p2.
      unfold Challenge.correlator, cluster_expansion.correlator, cluster_expansion.sum_connecting.
      apply sum_connecting_eq.
      exact cluster_weight_eq.
    Qed.

  End Bridge.

  (* =======================================================================
     2. Verification of Target 1: Constructive BFS Connects -> Dist Bound
     ======================================================================= *)

  Theorem verified_connects_implies_dist_bound
    : Challenge.Challenge_ConnectsImpliesDistBound.
  Proof.
    unfold Challenge.Challenge_ConnectsImpliesDistBound.
    intros P eq_dec adj_rel adj_dec_f adj_sym_f
           dist_f dist_nonneg_f dist_sym_f dist_refl_f dist_triangle_f adj_dist_bound_f
           size_f size_pos_f X p1 p2 Hconn.
    set (PS := {|
      overlap := fun _ _ => True;
      overlap_sym := fun _ _ _ => I;
      overlap_refl := fun _ => I;
      activity := fun _ => 0;
      activity_nonneg := fun _ => Rle_ge 0 0 (Rle_refl 0)
    |} : PolymerSystem P).
    set (MS := {|
      dist := dist_f;
      dist_nonneg := dist_nonneg_f;
      dist_sym := dist_sym_f;
      size := size_f;
      size_pos := size_pos_f
    |} : @MetricSystem P PS).
    set (CS := {|
      adj := adj_rel;
      adj_dec := adj_dec_f;
      adj_sym := adj_sym_f
    |} : ConnectivitySystem P).
    set (GF := @Build_YMGeometryConnectsFrontier P PS MS CS
      dist_triangle_f adj_dist_bound_f dist_refl_f
      (@connects_to_simple_path P CS eq_dec)).
    rewrite (@cluster_size_eq P PS MS).
    exact (@ym_connects_implies_dist_bound_from_frontier P PS MS CS eq_dec GF X p1 p2
             (proj1 (@connects_iff P CS X p1 p2) Hconn)).
  Qed.

  (* =======================================================================
     3. Verification of Target 2: Conditional Exponential Decay
     ======================================================================= *)

  Theorem verified_conditional_exponential_decay
    : Challenge.Challenge_ConditionalExponentialDecay.
  Proof.
    unfold Challenge.Challenge_ConditionalExponentialDecay.
    intros P eq_dec overlap_rel overlap_sym_f overlap_refl_f
           activity_f activity_nonneg_f
           adj_rel adj_dec_f adj_sym_f
           dist_f dist_nonneg_f dist_sym_f dist_refl_f dist_triangle_f adj_dist_bound_f
           size_f size_pos_f
           ursell_f ursell_bounded_f
           polymers_Λ N_max cdec a S_max Ha HSmax Hsize_le Hpinned p1 p2.
    set (PS := {|
      overlap := overlap_rel;
      overlap_sym := overlap_sym_f;
      overlap_refl := overlap_refl_f;
      activity := activity_f;
      activity_nonneg := activity_nonneg_f
    |} : PolymerSystem P).
    set (MS := {|
      dist := dist_f;
      dist_nonneg := dist_nonneg_f;
      dist_sym := dist_sym_f;
      size := size_f;
      size_pos := size_pos_f
    |} : @MetricSystem P PS).
    set (CS := {|
      adj := adj_rel;
      adj_dec := adj_dec_f;
      adj_sym := adj_sym_f
    |} : ConnectivitySystem P).
    set (US := {|
      ursell_factor := ursell_f;
      ursell_bounded := ursell_bounded_f
    |} : UrsellSystem P).
    set (GF := @Build_YMGeometryConnectsFrontier P PS MS CS
      dist_triangle_f adj_dist_bound_f dist_refl_f
      (@connects_to_simple_path P CS eq_dec)).
    assert (Hdist_bound : forall X q1 q2,
      @cluster_expansion.connects P CS X q1 q2 ->
      @dist P PS MS q1 q2 <= @cluster_expansion.cluster_size P PS MS X).
    { intros X q1 q2 Hc.
      exact (@ym_connects_implies_dist_bound_from_frontier P PS MS CS eq_dec GF X q1 q2 Hc). }
    pose proof (@correlator_eq P PS CS US eq_dec polymers_Λ N_max cdec p1 p2) as Hcorr.
    cbn [adj activity ursell_factor PS CS US] in Hcorr.
    rewrite Hcorr.
    unfold cluster_expansion.correlator.
    apply Rle_trans with
      (@cluster_expansion.sum_connecting P CS eq_dec polymers_Λ N_max
         (@repo_connects_dec P CS cdec) p1 p2
         (fun X => Rabs (@cluster_expansion.cluster_weight P PS US X))).
    { apply (@cluster_expansion.sum_connecting_triangle P CS eq_dec polymers_Λ N_max
               (@repo_connects_dec P CS cdec)). }
    apply Rle_trans with
      (exp (- a * dist_f p1 p2) *
       @cluster_expansion.sum_connecting P CS eq_dec polymers_Λ N_max
         (@repo_connects_dec P CS cdec) p1 p2
         (fun X => Rabs (@cluster_expansion.cluster_weight P PS US X) *
                   exp (a * @cluster_expansion.cluster_size P PS MS X))).
    { exact (@cluster_expansion.connecting_geometry P PS MS CS US
               eq_dec polymers_Λ N_max (@repo_connects_dec P CS cdec)
               Hdist_bound a p1 p2 Ha). }
    apply Rle_trans with
      (exp (- a * dist_f p1 p2) * (exp (a * size_f p1) * exp (a * size_f p2))).
    { apply Rmult_le_compat_l; [left; apply exp_pos |].
      unfold cluster_expansion.sum_connecting.
      assert (Hsum_eq :
        Challenge.sum_connecting adj_rel eq_dec polymers_Λ N_max cdec p1 p2
          (fun X => Rabs (Challenge.cluster_weight ursell_f activity_f X) *
                    exp (a * Challenge.cluster_size size_f X)) =
        @cluster_expansion.sum_connecting_concrete P CS eq_dec polymers_Λ N_max
          (@repo_connects_dec P CS cdec) p1 p2
          (fun X => Rabs (@cluster_expansion.cluster_weight P PS US X) *
                    exp (a * @cluster_expansion.cluster_size P PS MS X))).
      { apply (@sum_connecting_eq P CS eq_dec polymers_Λ N_max cdec p1 p2).
        intro X.
        pose proof (@cluster_weight_eq P PS US X) as Hw.
        pose proof (@cluster_size_eq P PS MS X) as Hs.
        cbn [activity ursell_factor size PS MS US] in Hw, Hs.
        rewrite Hw, Hs. reflexivity. }
      rewrite <- Hsum_eq.
      exact (Hpinned p1 p2). }
    rewrite (Rmult_comm (exp (2 * a * S_max))).
    apply Rmult_le_compat_l; [left; apply exp_pos |].
    rewrite <- exp_plus.
    apply cluster_expansion.exp_monotone.
    assert (Hs1 : a * size_f p1 <= a * S_max).
    { apply Rmult_le_compat_l; [lra | apply Hsize_le]. }
    assert (Hs2 : a * size_f p2 <= a * S_max).
    { apply Rmult_le_compat_l; [lra | apply Hsize_le]. }
    lra.
  Qed.

  (* =======================================================================
     4. Verification of Target 3: Exact Hoisted wightman_mass_gap_master
     ======================================================================= *)

  Theorem verified_master_conditional_statement
    : Challenge.Challenge_MasterConditionalStatement.
  Proof.
    unfold Challenge.Challenge_MasterConditionalStatement.
    intros P beta eq_dec overlap_rel overlap_sym_f overlap_refl_f
           adj_rel adj_dec_f adj_sym_f
           dist_f dist_nonneg_f dist_sym_f dist_refl_f dist_triangle_f adj_dist_bound_f
           neighbors_f neighbors_spec_f coordination_bound_f
           polymers_Λ N_max cdec
           Hpinned a Ha Hkp Hkp2a Hab Hbeta.
    set (activity_f := (fun _ : P => exp (- beta / 10)) : P -> R).
    set (size_f := (fun _ : P => 1) : P -> R).
    set (ursell_f := (fun _ : list P => 1) : list P -> R).
    set (sum_overlap_f :=
      (fun p f => fold_right Rplus 0 (map f (neighbors_f p))) : P -> (P -> R) -> R).
    set (PS := {|
      overlap := overlap_rel;
      overlap_sym := overlap_sym_f;
      overlap_refl := overlap_refl_f;
      activity := activity_f;
      activity_nonneg := fun _ => Rle_ge 0 (exp (- beta / 10)) (Rlt_le 0 _ (exp_pos (- beta / 10)))
    |} : PolymerSystem P).
    set (MS := {|
      dist := dist_f;
      dist_nonneg := dist_nonneg_f;
      dist_sym := dist_sym_f;
      size := size_f;
      size_pos := fun _ => Rle_ge 1 1 (Rle_refl 1)
    |} : @MetricSystem P PS).
    set (CS := {|
      adj := adj_rel;
      adj_dec := adj_dec_f;
      adj_sym := adj_sym_f
    |} : ConnectivitySystem P).
    assert (Hso_nonneg : forall p f, (forall p', 0 <= f p') -> 0 <= sum_overlap_f p f).
    { intros p f Hf. unfold sum_overlap_f.
      induction (neighbors_f p) as [| h t IH]; simpl; [lra |].
      specialize (Hf h). lra. }
    assert (Hso_lin : forall p c f, sum_overlap_f p (fun p' => c * f p') = c * sum_overlap_f p f).
    { intros p c f. unfold sum_overlap_f.
      induction (neighbors_f p) as [| h t IH]; simpl; [lra | rewrite IH; lra]. }
    set (SS := {|
      sum_overlap := sum_overlap_f;
      sum_overlap_nonneg := Hso_nonneg;
      sum_overlap_linear := Hso_lin
    |} : SummationSystem P).
    set (US := {|
      ursell_factor := ursell_f;
      ursell_bounded := fun _ =>
        eq_ind_r (fun r => r <= 1) (Rle_refl 1) (Rabs_pos_eq 1 Rle_0_1)
    |} : UrsellSystem P).
    set (GF := @Build_YMGeometryConnectsFrontier P PS MS CS
      dist_triangle_f adj_dist_bound_f dist_refl_f
      (@connects_to_simple_path P CS eq_dec)).
    assert (Hdist_bound : forall X q1 q2,
      @cluster_expansion.connects P CS X q1 q2 ->
      @dist P PS MS q1 q2 <= @cluster_expansion.cluster_size P PS MS X).
    { intros X q1 q2 Hc.
      exact (@ym_connects_implies_dist_bound_from_frontier P PS MS CS eq_dec GF X q1 q2 Hc). }
    assert (Hpin_repo :
      forall (a' : R) (q1 q2 : P),
        a' > 0 ->
        @cluster_expansion.kp_sum_condition P PS MS SS a' ->
        (forall q : P,
           @sum_overlap P SS q (fun x => @activity P PS x * exp (2 * a' * @size P PS MS x)) <=
           a' * @size P PS MS q) ->
        a' <= beta / 20 ->
        @cluster_expansion.sum_connecting P CS eq_dec polymers_Λ N_max
          (@repo_connects_dec P CS cdec) q1 q2
          (fun X => Rabs (@cluster_expansion.cluster_weight P PS US X) *
                    exp (a' * @cluster_expansion.cluster_size P PS MS X)) <=
        exp (a' * @size P PS MS q1) * exp (a' * @size P PS MS q2)).
    { intros a' q1 q2 Ha' Hkp' Hkp2a' Hab'.
      unfold cluster_expansion.sum_connecting.
      assert (Hsum_eq :
        Challenge.sum_connecting adj_rel eq_dec polymers_Λ N_max cdec q1 q2
          (fun X => Rabs (Challenge.cluster_weight ursell_f activity_f X) *
                    exp (a' * Challenge.cluster_size size_f X)) =
        @cluster_expansion.sum_connecting_concrete P CS eq_dec polymers_Λ N_max
          (@repo_connects_dec P CS cdec) q1 q2
          (fun X => Rabs (@cluster_expansion.cluster_weight P PS US X) *
                    exp (a' * @cluster_expansion.cluster_size P PS MS X))).
      { apply (@sum_connecting_eq P CS eq_dec polymers_Λ N_max cdec q1 q2).
        intro X.
        pose proof (@cluster_weight_eq P PS US X) as Hw.
        pose proof (@cluster_size_eq P PS MS X) as Hs.
        cbn [activity ursell_factor size PS MS US] in Hw, Hs.
        rewrite Hw, Hs. reflexivity. }
      rewrite <- Hsum_eq.
      exact (Hpinned a' q1 q2 Ha' Hbeta Hkp' Hkp2a' Hab'). }
    pose proof (@cluster_expansion.exponential_decay_from_cluster
                  P PS MS CS SS US eq_dec polymers_Λ N_max beta
                  (@repo_connects_dec P CS cdec)
                  Hdist_bound Hpin_repo a 1
                  Ha (Rle_ge 1 1 (Rle_refl 1)) (fun _ => Rle_refl 1)
                  Hkp Hkp2a Hab) as Hgap.
    exists a. split; [exact Ha |].
    destruct Hgap as [C [HC Hdecay]].
    unfold Challenge.has_mass_gap.
    exists C. split; [exact HC |].
    intros p1 p2.
    pose proof (@correlator_eq P PS CS US eq_dec polymers_Λ N_max cdec p1 p2) as Hcorr.
    cbn [adj activity ursell_factor PS CS US] in Hcorr.
    rewrite Hcorr.
    exact (Hdecay p1 p2).
  Qed.

  (* =======================================================================
     5. Verification of Targets 4a & 4b: Concrete 4D Lattice 21/24 Bound
        (Bijection between Challenge.Plaq4D and ym.lattice.Lattice.plaquette)
     ======================================================================= *)

  Definition dir_to_repo (d : Challenge.Dir4D) : Lattice.direction :=
    match d with
    | Challenge.D4_t => Lattice.Dir_t
    | Challenge.D4_x => Lattice.Dir_x
    | Challenge.D4_y => Lattice.Dir_y
    | Challenge.D4_z => Lattice.Dir_z
    end.

  Definition dir_from_repo (d : Lattice.direction) : Challenge.Dir4D :=
    match d with
    | Lattice.Dir_t => Challenge.D4_t
    | Lattice.Dir_x => Challenge.D4_x
    | Lattice.Dir_y => Challenge.D4_y
    | Lattice.Dir_z => Challenge.D4_z
    end.

  Lemma dir_roundtrip_1 : forall d, dir_from_repo (dir_to_repo d) = d.
  Proof. destruct d; reflexivity. Qed.

  Lemma dir_roundtrip_2 : forall d, dir_to_repo (dir_from_repo d) = d.
  Proof. destruct d; reflexivity. Qed.

  Definition site_to_repo (s : Challenge.Site4D) : Lattice.site :=
    Lattice.mk_site (Challenge.s4_t s) (Challenge.s4_x s)
                    (Challenge.s4_y s) (Challenge.s4_z s).

  Definition site_from_repo (s : Lattice.site) : Challenge.Site4D :=
    Challenge.mkSite4D (Lattice.site_t s) (Lattice.site_x s)
                       (Lattice.site_y s) (Lattice.site_z s).

  Lemma site_roundtrip_1 : forall s, site_from_repo (site_to_repo s) = s.
  Proof. destruct s; reflexivity. Qed.

  Lemma site_roundtrip_2 : forall s, site_to_repo (site_from_repo s) = s.
  Proof. destruct s; reflexivity. Qed.

  Lemma site_to_repo_inj : forall s1 s2, site_to_repo s1 = site_to_repo s2 -> s1 = s2.
  Proof.
    intros s1 s2 H. rewrite <- (site_roundtrip_1 s1), <- (site_roundtrip_1 s2), H. reflexivity.
  Qed.

  Lemma shift_to_repo : forall s d,
    site_to_repo (Challenge.shift4D s d) = Lattice.shift_site (site_to_repo s) (dir_to_repo d).
  Proof. intros [t x y z] []; reflexivity. Qed.

  Definition plaq_to_repo (p : Challenge.Plaq4D) : Lattice.plaquette :=
    Lattice.mk_plaq (site_to_repo (Challenge.p4_site p))
                    (dir_to_repo (Challenge.p4_mu p))
                    (dir_to_repo (Challenge.p4_nu p)).

  Definition plaq_from_repo (p : Lattice.plaquette) : Challenge.Plaq4D :=
    Challenge.mkPlaq4D (site_from_repo (Lattice.plaq_site p))
                       (dir_from_repo (Lattice.plaq_mu p))
                       (dir_from_repo (Lattice.plaq_nu p)).

  Lemma plaq_roundtrip_1 : forall p, plaq_from_repo (plaq_to_repo p) = p.
  Proof.
    intros [s mu nu]. unfold plaq_from_repo, plaq_to_repo; simpl.
    rewrite site_roundtrip_1, dir_roundtrip_1, dir_roundtrip_1. reflexivity.
  Qed.

  Lemma plaq_roundtrip_2 : forall p, plaq_to_repo (plaq_from_repo p) = p.
  Proof.
    intros [s mu nu]. unfold plaq_from_repo, plaq_to_repo; simpl.
    rewrite site_roundtrip_2, dir_roundtrip_2, dir_roundtrip_2. reflexivity.
  Qed.

  Lemma plaq_to_repo_inj : forall p1 p2, plaq_to_repo p1 = plaq_to_repo p2 -> p1 = p2.
  Proof.
    intros p1 p2 H. rewrite <- (plaq_roundtrip_1 p1), <- (plaq_roundtrip_1 p2), H. reflexivity.
  Qed.

  Lemma plaq_from_repo_inj : forall p1 p2, plaq_from_repo p1 = plaq_from_repo p2 -> p1 = p2.
  Proof.
    intros p1 p2 H. rewrite <- (plaq_roundtrip_2 p1), <- (plaq_roundtrip_2 p2), H. reflexivity.
  Qed.

  Lemma wf_plaq_iff : forall p,
    Challenge.wf_plaq_4D p <-> Lattice4DCoord.wf_plaq (plaq_to_repo p).
  Proof.
    intros [s mu nu].
    unfold Challenge.wf_plaq_4D, Challenge.canonical_planes_4D,
           Lattice4DCoord.wf_plaq, Lattice.direction_pairs, plaq_to_repo; simpl.
    destruct mu, nu; simpl; split; intro H;
      repeat match type of H with | _ \/ _ => destruct H as [H | H] end;
      try discriminate; try contradiction;
      try (left; reflexivity);
      try (right; left; reflexivity);
      try (right; right; left; reflexivity);
      try (right; right; right; left; reflexivity);
      try (right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; left; reflexivity).
  Qed.

  Lemma edges_to_repo : forall p,
    Lattice4DCoord.plaq_raw_edges (plaq_to_repo p) =
    map (fun e => (site_to_repo (fst e), site_to_repo (snd e))) (Challenge.plaq4D_edges p).
  Proof.
    intro p. unfold Lattice4DCoord.plaq_raw_edges, Challenge.plaq4D_edges, plaq_to_repo; simpl.
    rewrite !shift_to_repo. reflexivity.
  Qed.

  Lemma same_edge_iff : forall e1 e2,
    Challenge.same_undirected_edge e1 e2 <->
    Lattice4DCoord.same_undirected_edge
      (site_to_repo (fst e1), site_to_repo (snd e1))
      (site_to_repo (fst e2), site_to_repo (snd e2)).
  Proof.
    intros [a1 b1] [a2 b2].
    unfold Challenge.same_undirected_edge, Lattice4DCoord.same_undirected_edge; simpl.
    split; intros [[H1 H2] | [H1 H2]].
    - left; subst; auto.
    - right; subst; auto.
    - left; split; apply site_to_repo_inj; assumption.
    - right; split; apply site_to_repo_inj; assumption.
  Qed.

  Lemma shares_edge_iff : forall p1 p2,
    Challenge.plaq4D_shares_edge p1 p2 <->
    Lattice4DCoord.plaq_shares_edge (plaq_to_repo p1) (plaq_to_repo p2).
  Proof.
    intros p1 p2.
    unfold Challenge.plaq4D_shares_edge, Lattice4DCoord.plaq_shares_edge.
    rewrite !edges_to_repo.
    split.
    - intros [Hne [e1 [e2 [He1 [He2 Hsame]]]]].
      split.
      + intro Heq. apply Hne. exact (plaq_to_repo_inj p1 p2 Heq).
      + exists (site_to_repo (fst e1), site_to_repo (snd e1)),
               (site_to_repo (fst e2), site_to_repo (snd e2)).
        repeat split.
        * apply (in_map (fun e => (site_to_repo (fst e), site_to_repo (snd e)))). exact He1.
        * apply (in_map (fun e => (site_to_repo (fst e), site_to_repo (snd e)))). exact He2.
        * apply same_edge_iff. exact Hsame.
    - intros [Hne [e1' [e2' [He1' [He2' Hsame]]]]].
      apply in_map_iff in He1'. destruct He1' as [e1 [Heq1 He1]].
      apply in_map_iff in He2'. destruct He2' as [e2 [Heq2 He2]].
      subst e1' e2'. apply same_edge_iff in Hsame.
      split.
      + intro Heq. apply Hne. subst. reflexivity.
      + exists e1, e2. repeat split; assumption.
  Qed.

  Lemma overlap_4D_iff : forall p1 p2,
    Challenge.plaq4D_overlap p1 p2 <->
    Lattice4DCoord.plaq_overlap (plaq_to_repo p1) (plaq_to_repo p2).
  Proof.
    intros p1 p2.
    unfold Challenge.plaq4D_overlap, Lattice4DCoord.plaq_overlap.
    rewrite shares_edge_iff.
    split; intros [H | H].
    - left; subst; reflexivity.
    - right; exact H.
    - left; exact (plaq_to_repo_inj p1 p2 H).
    - right; exact H.
  Qed.

  Definition neighbors_4D (p : Challenge.Plaq4D) : list Challenge.Plaq4D :=
    map plaq_from_repo (Lattice4DCoord.plaq_neighbors (plaq_to_repo p)).

  Theorem verified_lattice4D_exact21 : Challenge.Challenge_Lattice4D_Exact21.
  Proof.
    unfold Challenge.Challenge_Lattice4D_Exact21.
    exists neighbors_4D.
    split; [| split; [| split]].
    - intros p _. unfold neighbors_4D.
      apply Lattice4DCoord.NoDup_map_inj; [exact plaq_from_repo_inj |].
      exact (Lattice4DCoord.plaq_neighbors_NoDup (plaq_to_repo p)).
    - intros p q _ Hin. unfold neighbors_4D in Hin.
      apply in_map_iff in Hin. destruct Hin as [qr [Heq Hinr]].
      subst q. apply wf_plaq_iff. rewrite plaq_roundtrip_2.
      exact (Lattice4DCoord.plaq_neighbors_wf (plaq_to_repo p) qr Hinr).
    - intros p q _ Hwfq. split.
      + intro Hin. unfold neighbors_4D in Hin.
        apply in_map_iff in Hin. destruct Hin as [qr [Heq Hinr]].
        subst q. apply overlap_4D_iff. rewrite plaq_roundtrip_2.
        exact (Lattice4DCoord.plaq_neighbors_sound (plaq_to_repo p) qr Hinr).
      + intro Hov. unfold neighbors_4D.
        rewrite <- (plaq_roundtrip_1 q).
        apply in_map.
        apply Lattice4DCoord.plaq_neighbors_complete_wf.
        * apply wf_plaq_iff. exact Hwfq.
        * apply overlap_4D_iff. exact Hov.
    - intros p Hwfp. unfold neighbors_4D.
      rewrite map_length.
      apply Lattice4DCoord.plaq_neighbors_exact_21.
      apply wf_plaq_iff. exact Hwfp.
  Qed.

  Theorem verified_lattice4D_coordination24 : Challenge.Challenge_Lattice4D_Coordination24.
  Proof.
    unfold Challenge.Challenge_Lattice4D_Coordination24.
    destruct verified_lattice4D_exact21 as [nb [Hnd [Hwf [Hspec Hlen]]]].
    exists nb.
    split; [exact Hnd | split; [exact Hwf | split; [exact Hspec | split; [exact Hlen |]]]].
    intros p Hwfp.
    rewrite (Hlen p Hwfp).
    assert (H21 : INR 21 = 21) by (unfold INR; simpl; ring).
    rewrite H21. lra.
  Qed.

  (* =======================================================================
     5. Bridging & Verifying Genuine Kotecky-Preiss Targets (5a, 5b, 5c)
     ======================================================================= *)

  Lemma kp_tuples_eq : forall {P : Type} (Lambda : list P) n,
    Challenge.kp_tuples_of_length Lambda n = KoteckyPreiss.tuples_of_length Lambda n.
  Proof.
    intros P Lambda. induction n as [| n' IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma kp_sum_over_tuples_eq : forall {P : Type} (Lambda : list P) n f,
    Challenge.kp_sum_over_tuples Lambda n f = KoteckyPreiss.sum_over_tuples Lambda n f.
  Proof.
    intros P Lambda n f. unfold Challenge.kp_sum_over_tuples, KoteckyPreiss.sum_over_tuples.
    rewrite kp_tuples_eq. reflexivity.
  Qed.

  Lemma kp_prod_weight_eq : forall {P : Type} (wt : P -> R) X,
    Challenge.kp_prod_weight wt X = KoteckyPreiss.prod_weight wt X.
  Proof. reflexivity. Qed.

  Lemma kp_series_eq : forall {P : Type} (Lambda : list P) N_max term,
    Challenge.kp_series Lambda N_max term = KoteckyPreiss.kp_series Lambda N_max term.
  Proof.
    intros P Lambda N_max term. induction N_max as [| N' IH]; simpl; [reflexivity |].
    rewrite IH, kp_sum_over_tuples_eq. reflexivity.
  Qed.

  Lemma kp_root_series_eq : forall {P : Type} (Lambda : list P) N p0 term,
    Challenge.kp_root_series Lambda N p0 term = KoteckyPreiss.root_series Lambda N p0 term.
  Proof.
    intros P Lambda N p0 term. induction N as [| N' IH]; simpl.
    - rewrite kp_sum_over_tuples_eq. reflexivity.
    - rewrite IH, kp_sum_over_tuples_eq. reflexivity.
  Qed.

  Lemma kp_sublists_eq : forall {A : Type} (l : list A),
    Challenge.kp_sublists l = PenroseTreeBound.sublists l.
  Proof.
    intros A. induction l as [| a xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma kp_expand_iter_eq : forall k H S,
    Challenge.kp_expand_iter k H S = PenroseTreeBound.expand_iter k H S.
  Proof.
    induction k as [| k' IH]; intros H S; simpl; [reflexivity |].
    unfold Challenge.kp_expand_once, PenroseTreeBound.expand_once. apply IH.
  Qed.

  Lemma kp_is_connectedb_eq : forall n H,
    Challenge.kp_is_connectedb n H = PenroseTreeBound.is_connectedb n H.
  Proof.
    intros [| n'] H; [reflexivity |].
    unfold Challenge.kp_is_connectedb, PenroseTreeBound.is_connectedb.
    apply PenroseTreeBound.forallb_ext_in. intros v _.
    rewrite kp_expand_iter_eq. reflexivity.
  Qed.

  Lemma kp_pairs_with_head_eq : forall {P : Type} (ob : P -> P -> bool) i x j xs,
    Challenge.kp_pairs_with_head ob i x j xs = PenroseTreeBound.pairs_with_head ob i x j xs.
  Proof.
    intros P ob i x j xs. revert j.
    induction xs as [| y ys IH]; intro j; simpl; [reflexivity |].
    destruct (ob x y); [f_equal |]; apply IH.
  Qed.

  Lemma kp_graph_edges_from_eq : forall {P : Type} (ob : P -> P -> bool) i X,
    Challenge.kp_graph_edges_from ob i X = PenroseTreeBound.graph_edges_from ob i X.
  Proof.
    intros P ob i X. revert i.
    induction X as [| x xs IH]; intro i; simpl; [reflexivity |].
    rewrite kp_pairs_with_head_eq, IH. reflexivity.
  Qed.

  Lemma kp_ursell_fn_eq : forall {P : Type} (ob : P -> P -> bool) X,
    Challenge.kp_ursell_fn ob X = PenroseTreeBound.ursell_fn ob X.
  Proof.
    intros P ob X.
    unfold Challenge.kp_ursell_fn, PenroseTreeBound.ursell_fn, PenroseTreeBound.ursell_graph,
           Challenge.kp_graph_edges, PenroseTreeBound.graph_edges.
    rewrite kp_graph_edges_from_eq, kp_sublists_eq.
    apply PenroseTreeBound.fold_right_Rplus_ext. intros H _.
    rewrite kp_is_connectedb_eq. reflexivity.
  Qed.

  Lemma kp_ursell_correlator_eq : forall {P : Type} (ob : P -> P -> bool) Lambda N_max w p1 p2,
    Challenge.kp_ursell_correlator ob Lambda N_max w p1 p2 =
    KoteckyPreiss.ursell_correlator ob Lambda N_max w p1 p2.
  Proof.
    intros P ob Lambda N_max w p1 p2.
    unfold Challenge.kp_ursell_correlator, KoteckyPreiss.ursell_correlator.
    rewrite kp_series_eq.
    assert (Hf :
      (fun X => if existsb (ob p1) X && existsb (ob p2) X
                then Challenge.kp_ursell_fn ob X * Challenge.kp_prod_weight w X else 0) =
      (fun X => if existsb (ob p1) X && existsb (ob p2) X
                then PenroseTreeBound.ursell_fn ob X * KoteckyPreiss.prod_weight w X else 0)).
    { apply functional_extensionality. intro X. rewrite kp_ursell_fn_eq. reflexivity. }
    rewrite Hf. reflexivity.
  Qed.

  Theorem verified_kotecky_preiss_pinned_bound :
    Challenge.Challenge_KoteckyPreiss_PinnedBound.
  Proof.
    unfold Challenge.Challenge_KoteckyPreiss_PinnedBound.
    intros P ob Hsym Lambda w a d p0 Ha0 Ha_nn Hkp0 Hkp.
    split.
    - intro N. rewrite kp_root_series_eq.
      assert (Hf :
        (fun X => Rabs (Challenge.kp_ursell_fn ob X) *
                  Challenge.kp_prod_weight (fun q => Rabs (w q) * exp (d q)) (tl X)) =
        (fun X => Rabs (PenroseTreeBound.ursell_fn ob X) *
                  KoteckyPreiss.prod_weight (fun q => Rabs (w q) * exp (d q)) (tl X))).
      { apply functional_extensionality. intro X. rewrite kp_ursell_fn_eq. reflexivity. }
      rewrite Hf.
      exact (KoteckyPreiss.kp_root_pinned_bound ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N).
    - intro N_max. rewrite kp_series_eq.
      assert (Hf :
        (fun X => if existsb (ob p0) X
                  then Rabs (Challenge.kp_ursell_fn ob X) *
                       Challenge.kp_prod_weight (fun q => Rabs (w q) * exp (d q)) X
                  else 0) =
        (fun X => if existsb (ob p0) X
                  then Rabs (PenroseTreeBound.ursell_fn ob X) *
                       KoteckyPreiss.prod_weight (fun q => Rabs (w q) * exp (d q)) X
                  else 0)).
      { apply functional_extensionality. intro X. rewrite kp_ursell_fn_eq. reflexivity. }
      rewrite Hf.
      exact (KoteckyPreiss.kp_overlap_pinned_bound ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N_max).
  Qed.

  Theorem verified_kotecky_preiss_exponential_decay :
    Challenge.Challenge_KoteckyPreiss_ExponentialDecay.
  Proof.
    unfold Challenge.Challenge_KoteckyPreiss_ExponentialDecay.
    intros P ob Hsym Lambda w a size dist Hrefl Htri Hob_dist Hsize c p1 p2 Hc Ha1 Ha_nn Hkp1 Hkp N_max.
    rewrite kp_ursell_correlator_eq.
    exact (KoteckyPreiss.kp_correlator_exponential_decay
             ob Lambda w a size dist c p1 p2
             Hsym Hrefl Htri Hob_dist Hsize Hc Ha1 Ha_nn Hkp1 Hkp N_max).
  Qed.

  (* Transporting concrete Z^4 Ursell correlator across plaq_to_repo *)
  Lemma map_tuples_of_length : forall {A B : Type} (f : A -> B) (l : list A) n,
    KoteckyPreiss.tuples_of_length (map f l) n =
    map (map f) (KoteckyPreiss.tuples_of_length l n).
  Proof.
    intros A B f l. induction n as [| n' IH]; simpl; [reflexivity |].
    rewrite IH. clear IH.
    generalize (KoteckyPreiss.tuples_of_length l n') as T. intro T.
    induction l as [| a xs IHl]; simpl; [reflexivity |].
    rewrite map_app, map_map, map_map, IHl. reflexivity.
  Qed.

  Lemma pairs_with_head_map : forall {A B : Type} (f : A -> B) (obA : A -> A -> bool) (obB : B -> B -> bool),
    (forall x y, obB (f x) (f y) = obA x y) ->
    forall i x j xs,
      PenroseTreeBound.pairs_with_head obB i (f x) j (map f xs) =
      PenroseTreeBound.pairs_with_head obA i x j xs.
  Proof.
    intros A B f obA obB Hcompat i x j xs. revert j.
    induction xs as [| y ys IH]; intro j; simpl; [reflexivity |].
    rewrite Hcompat. destruct (obA x y); [f_equal |]; apply IH.
  Qed.

  Lemma graph_edges_from_map : forall {A B : Type} (f : A -> B) (obA : A -> A -> bool) (obB : B -> B -> bool),
    (forall x y, obB (f x) (f y) = obA x y) ->
    forall i X,
      PenroseTreeBound.graph_edges_from obB i (map f X) =
      PenroseTreeBound.graph_edges_from obA i X.
  Proof.
    intros A B f obA obB Hcompat i X. revert i.
    induction X as [| x xs IH]; intro i; simpl; [reflexivity |].
    rewrite (pairs_with_head_map f obA obB Hcompat), IH. reflexivity.
  Qed.

  Lemma ursell_fn_map : forall {A B : Type} (f : A -> B) (obA : A -> A -> bool) (obB : B -> B -> bool),
    (forall x y, obB (f x) (f y) = obA x y) ->
    forall X, PenroseTreeBound.ursell_fn obB (map f X) = PenroseTreeBound.ursell_fn obA X.
  Proof.
    intros A B f obA obB Hcompat X.
    unfold PenroseTreeBound.ursell_fn, PenroseTreeBound.graph_edges.
    rewrite map_length, (graph_edges_from_map f obA obB Hcompat). reflexivity.
  Qed.

  Lemma existsb_map_compat : forall {A B : Type} (f : A -> B) (gA : A -> bool) (gB : B -> bool),
    (forall x, gB (f x) = gA x) ->
    forall X, existsb gB (map f X) = existsb gA X.
  Proof.
    intros A B f gA gB Hcompat. induction X as [| x xs IH]; simpl; [reflexivity |].
    rewrite Hcompat, IH. reflexivity.
  Qed.

  Lemma prod_weight_const_map : forall {A B : Type} (f : A -> B) (c : R) X,
    KoteckyPreiss.prod_weight (fun _ => c) (map f X) =
    KoteckyPreiss.prod_weight (fun _ => c) X.
  Proof.
    intros A B f c. induction X as [| x xs IH]; unfold KoteckyPreiss.prod_weight, KoteckyPreiss.prod_list in *;
      simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma plaq4D_dist_to_repo : forall p1 p2,
    Challenge.plaq4D_dist p1 p2 = Lattice4DKP.plaq_dist (plaq_to_repo p1) (plaq_to_repo p2).
  Proof.
    intros [[t1 x1 y1 z1] mu1 nu1] [[t2 x2 y2 z2] mu2 nu2]. reflexivity.
  Qed.

  Theorem verified_lattice4D_kp_exponential_decay :
    Challenge.Challenge_Lattice4D_KP_ExponentialDecay.
  Proof.
    unfold Challenge.Challenge_Lattice4D_KP_ExponentialDecay.
    intros ob Hob_spec beta Lambda N_max p1 p2 Hbeta Hnd Hall Hwfp1.
    rewrite kp_ursell_correlator_eq, plaq4D_dist_to_repo.
    assert (Hcompat : forall x y,
      Lattice4DCoord.plaq_overlap_bool (plaq_to_repo x) (plaq_to_repo y) = ob x y).
    { intros x y. apply eq_true_iff_eq.
      rewrite Lattice4DCoord.plaq_overlap_bool_spec, Hob_spec, overlap_4D_iff. reflexivity. }
    assert (Hcorr_eq :
      KoteckyPreiss.ursell_correlator ob Lambda N_max (fun _ => exp (- beta / 10)) p1 p2 =
      KoteckyPreiss.ursell_correlator Lattice4DCoord.plaq_overlap_bool
        (map plaq_to_repo Lambda) N_max (fun _ => exp (- beta / 10))
        (plaq_to_repo p1) (plaq_to_repo p2)).
    { unfold KoteckyPreiss.ursell_correlator.
      induction N_max as [| N' IH]; simpl; [reflexivity |].
      rewrite IH. f_equal. f_equal.
      unfold KoteckyPreiss.sum_over_tuples.
      rewrite map_tuples_of_length, map_map.
      apply PenroseTreeBound.fold_right_Rplus_ext. intros X _.
      rewrite (existsb_map_compat plaq_to_repo (ob p1) (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p1)) (Hcompat p1)).
      rewrite (existsb_map_compat plaq_to_repo (ob p2) (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p2)) (Hcompat p2)).
      rewrite (ursell_fn_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool Hcompat).
      rewrite prod_weight_const_map. reflexivity. }
    rewrite Hcorr_eq.
    apply Lattice4DKP.lattice4D_kp_exponential_decay; try exact Hbeta.
    - apply Lattice4DCoord.NoDup_map_inj; [exact plaq_to_repo_inj | exact Hnd].
    - rewrite Forall_forall in *. intros qr Hin.
      apply in_map_iff in Hin. destruct Hin as [q [<- Hq]].
      apply wf_plaq_iff. exact (Hall q Hq).
    - apply wf_plaq_iff. exact Hwfp1.
  Qed.

  (* =======================================================================
     7. Verification of Targets 6a, 6b, 6c: Partition Function ln Z_Lambda
        Convergence & Exact Partition-Function Log-Ratio Decay
     ======================================================================= *)

  Lemma kp_pairwise_compat_eq : forall {P : Type} (ob : P -> P -> bool) X,
    Challenge.kp_pairwise_compat ob X = ClusterLogPartition.pairwise_compat ob X.
  Proof.
    intros P ob. induction X as [| x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma kp_partition_fn_eq : forall {P : Type} (ob : P -> P -> bool) Lambda w,
    Challenge.kp_partition_fn ob Lambda w = ClusterLogPartition.partition_fn ob Lambda w.
  Proof.
    intros P ob Lambda w.
    unfold Challenge.kp_partition_fn, ClusterLogPartition.partition_fn.
    rewrite kp_sublists_eq.
    apply PenroseTreeBound.fold_right_Rplus_ext. intros S _.
    rewrite kp_pairwise_compat_eq. reflexivity.
  Qed.

  Lemma kp_ursell_order_eq : forall {P : Type} (ob : P -> P -> bool) Lambda w n,
    Challenge.kp_ursell_order ob Lambda w n = ClusterLogPartition.ursell_order ob Lambda w n.
  Proof.
    intros P ob Lambda w [| n']; reflexivity.
  Qed.

  Theorem verified_kotecky_preiss_log_partition_fn :
    Challenge.Challenge_KoteckyPreiss_LogPartitionFn.
  Proof.
    unfold Challenge.Challenge_KoteckyPreiss_LogPartitionFn.
    intros P ob Hrefl Hsym Lambda w a Ha_nn Hkp.
    destruct (ClusterLogPartition.kp_log_partition_fn ob Lambda w a Hrefl Hsym Ha_nn Hkp)
      as [Hpos [Habs Hcv]].
    rewrite kp_partition_fn_eq. repeat split.
    - exact Hpos.
    - intro N.
      assert (Heq : sum_f_R0 (fun n => Rabs (Challenge.kp_ursell_order ob Lambda w n)) N =
                    sum_f_R0 (fun n => Rabs (ClusterLogPartition.ursell_order ob Lambda w n)) N).
      { apply PolyExpBound.sum_f_R0_ext. intros n _. rewrite kp_ursell_order_eq. reflexivity. }
      rewrite Heq. exact (Habs N).
    - intros eps Heps. destruct (Hcv eps Heps) as [N0 HN0].
      exists N0. intros N HN.
      rewrite kp_series_eq.
      assert (Hf :
        (fun X => Challenge.kp_ursell_fn ob X * Challenge.kp_prod_weight w X) =
        (fun X => PenroseTreeBound.ursell_fn ob X * KoteckyPreiss.prod_weight w X)).
      { apply functional_extensionality. intro X. rewrite kp_ursell_fn_eq. reflexivity. }
      rewrite Hf. exact (HN0 N HN).
  Qed.

  Theorem verified_kotecky_preiss_log_ratio_decay :
    Challenge.Challenge_KoteckyPreiss_LogRatioDecay.
  Proof.
    unfold Challenge.Challenge_KoteckyPreiss_LogRatioDecay.
    intros P ob Hrefl Hsym Lambda w a size dist Hdist_refl Htri Hob_dist Hsize c p1 p2
           Hc Ha1 Ha_nn Hkp1 Hkp.
    cbv zeta. rewrite !kp_partition_fn_eq.
    pose proof (ClusterLogPartition.kp_log_ratio_decay
                  ob Lambda w a size dist c p1 p2
                  Hrefl Hsym Hdist_refl Htri Hob_dist Hsize Hc Ha1 Ha_nn Hkp1 Hkp)
      as [HZ [HZ1 [HZ2 [HZ12 [Hcv Hdec]]]]].
    repeat split; assumption.
  Qed.

  (* Transporting partition_fn and kp_series across plaq_to_repo *)
  Lemma map_sublists : forall {A B : Type} (f : A -> B) (l : list A),
    PenroseTreeBound.sublists (map f l) = map (map f) (PenroseTreeBound.sublists l).
  Proof.
    intros A B f. induction l as [| a xs IH]; simpl; [reflexivity |].
    rewrite IH, map_app, !map_map. reflexivity.
  Qed.

  Lemma forallb_map_compat : forall {A B : Type} (f : A -> B) (gA : A -> bool) (gB : B -> bool),
    (forall x, gB (f x) = gA x) ->
    forall X, forallb gB (map f X) = forallb gA X.
  Proof.
    intros A B f gA gB Hcompat. induction X as [| x xs IH]; simpl; [reflexivity |].
    rewrite Hcompat, IH. reflexivity.
  Qed.

  Lemma pairwise_compat_map : forall {A B : Type} (f : A -> B) (obA : A -> A -> bool) (obB : B -> B -> bool),
    (forall x y, obB (f x) (f y) = obA x y) ->
    forall X, ClusterLogPartition.pairwise_compat obB (map f X) = ClusterLogPartition.pairwise_compat obA X.
  Proof.
    intros A B f obA obB Hcompat. induction X as [| x xs IH]; simpl; [reflexivity |].
    rewrite (forallb_map_compat f (fun y => negb (obA x y)) (fun y => negb (obB (f x) y))
               (fun y => f_equal negb (Hcompat x y))), IH. reflexivity.
  Qed.

  Lemma filter_map_compat : forall {A B : Type} (f : A -> B) (gA : A -> bool) (gB : B -> bool),
    (forall x, gB (f x) = gA x) ->
    forall l, filter gB (map f l) = map f (filter gA l).
  Proof.
    intros A B f gA gB Hcompat. induction l as [| a xs IH]; simpl; [reflexivity |].
    rewrite Hcompat. destruct (gA a); simpl; [f_equal |]; exact IH.
  Qed.

  Lemma partition_fn_const_map : forall {A B : Type} (f : A -> B)
    (obA : A -> A -> bool) (obB : B -> B -> bool) (c : R) (Lambda : list A),
    (forall x y, obB (f x) (f y) = obA x y) ->
    ClusterLogPartition.partition_fn obB (map f Lambda) (fun _ => c) =
    ClusterLogPartition.partition_fn obA Lambda (fun _ => c).
  Proof.
    intros A B f obA obB c Lambda Hcompat.
    unfold ClusterLogPartition.partition_fn.
    rewrite map_sublists, map_map.
    apply PenroseTreeBound.fold_right_Rplus_ext. intros S _.
    rewrite (pairwise_compat_map f obA obB Hcompat S), prod_weight_const_map. reflexivity.
  Qed.

  Theorem verified_lattice4D_partition_fn_decay :
    Challenge.Challenge_Lattice4D_PartitionFn_Decay.
  Proof.
    unfold Challenge.Challenge_Lattice4D_PartitionFn_Decay.
    intros ob Hob_spec beta Lambda p1 p2 Hbeta Hnd Hall Hwfp1.
    cbv zeta. rewrite !kp_partition_fn_eq, plaq4D_dist_to_repo.
    assert (Hcompat : forall x y,
      Lattice4DCoord.plaq_overlap_bool (plaq_to_repo x) (plaq_to_repo y) = ob x y).
    { intros x y. apply eq_true_iff_eq.
      rewrite Lattice4DCoord.plaq_overlap_bool_spec, Hob_spec, overlap_4D_iff. reflexivity. }
    pose proof (Lattice4DKP.lattice4D_partition_fn_decay
                  beta (map plaq_to_repo Lambda) (plaq_to_repo p1) (plaq_to_repo p2)
                  Hbeta
                  (@Lattice4DCoord.NoDup_map_inj _ _ plaq_to_repo plaq_to_repo_inj Lambda Hnd)
                  ltac:(rewrite Forall_forall in *; intros qr Hin;
                        apply in_map_iff in Hin; destruct Hin as [q [<- Hq]];
                        apply wf_plaq_iff; exact (Hall q Hq))
                  (proj1 (wf_plaq_iff p1) Hwfp1))
      as [HZ [HZ1 [HZ2 [HZ12 [HcvZ [HcvR Hdec]]]]]].
    assert (HF1 : filter (fun q => negb (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p1) q))
                    (map plaq_to_repo Lambda) =
                  map plaq_to_repo (filter (fun q => negb (ob p1 q)) Lambda)).
    { apply filter_map_compat. intro q. rewrite Hcompat. reflexivity. }
    assert (HF2 : filter (fun q => negb (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p2) q))
                    (map plaq_to_repo Lambda) =
                  map plaq_to_repo (filter (fun q => negb (ob p2 q)) Lambda)).
    { apply filter_map_compat. intro q. rewrite Hcompat. reflexivity. }
    assert (HF12 : filter (fun q => negb (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p1) q) &&
                                    negb (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p2) q))
                    (map plaq_to_repo Lambda) =
                  map plaq_to_repo (filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda)).
    { apply filter_map_compat. intro q. rewrite !Hcompat. reflexivity. }
    rewrite HF1 in HZ1, HcvR, Hdec.
    rewrite HF2 in HZ2, HcvR, Hdec.
    rewrite HF12 in HZ12, HcvR, Hdec.
    rewrite (partition_fn_const_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool (exp (- beta / 10)) Lambda Hcompat)
      in HZ, HcvZ, HcvR, Hdec.
    rewrite (partition_fn_const_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool (exp (- beta / 10))
               (filter (fun q => negb (ob p1 q)) Lambda) Hcompat)
      in HZ1, HcvR, Hdec.
    rewrite (partition_fn_const_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool (exp (- beta / 10))
               (filter (fun q => negb (ob p2 q)) Lambda) Hcompat)
      in HZ2, HcvR, Hdec.
    rewrite (partition_fn_const_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool (exp (- beta / 10))
               (filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda) Hcompat)
      in HZ12, HcvR, Hdec.
    repeat split; try assumption.
    - intros eps Heps. destruct (HcvZ eps Heps) as [N0 HN0].
      exists N0. intros N HN.
      assert (Hser :
        Challenge.kp_series Lambda N
          (fun X => Challenge.kp_ursell_fn ob X * Challenge.kp_prod_weight (fun _ => exp (- beta / 10)) X) =
        KoteckyPreiss.kp_series (map plaq_to_repo Lambda) N
          (fun X => PenroseTreeBound.ursell_fn Lattice4DCoord.plaq_overlap_bool X *
                    KoteckyPreiss.prod_weight (fun _ => exp (- beta / 10)) X)).
      { clear HN. rewrite kp_series_eq. induction N as [| N' IH]; simpl; [reflexivity |].
        rewrite IH. f_equal. f_equal.
        unfold KoteckyPreiss.sum_over_tuples.
        rewrite map_tuples_of_length, map_map.
        apply PenroseTreeBound.fold_right_Rplus_ext. intros X _.
        rewrite kp_ursell_fn_eq,
                (ursell_fn_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool Hcompat),
                prod_weight_const_map. reflexivity. }
      rewrite Hser. exact (HN0 N HN).
    - intros eps Heps. destruct (HcvR eps Heps) as [N0 HN0].
      exists N0. intros N HN.
      assert (Hcorr :
        Challenge.kp_ursell_correlator ob Lambda N (fun _ => exp (- beta / 10)) p1 p2 =
        KoteckyPreiss.ursell_correlator Lattice4DCoord.plaq_overlap_bool
          (map plaq_to_repo Lambda) N (fun _ => exp (- beta / 10))
          (plaq_to_repo p1) (plaq_to_repo p2)).
      { clear HN. rewrite kp_ursell_correlator_eq. unfold KoteckyPreiss.ursell_correlator.
        induction N as [| N' IH]; simpl; [reflexivity |].
        rewrite IH. f_equal. f_equal.
        unfold KoteckyPreiss.sum_over_tuples.
        rewrite map_tuples_of_length, map_map.
        apply PenroseTreeBound.fold_right_Rplus_ext. intros X _.
        rewrite (existsb_map_compat plaq_to_repo (ob p1) (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p1)) (Hcompat p1)),
                (existsb_map_compat plaq_to_repo (ob p2) (Lattice4DCoord.plaq_overlap_bool (plaq_to_repo p2)) (Hcompat p2)),
                (ursell_fn_map plaq_to_repo ob Lattice4DCoord.plaq_overlap_bool Hcompat),
                prod_weight_const_map. reflexivity. }
      rewrite Hcorr. exact (HN0 N HN).
  Qed.

End Verify.
