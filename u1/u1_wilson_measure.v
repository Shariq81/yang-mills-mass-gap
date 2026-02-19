(* =========================================================================
   u1_wilson_measure.v - U(1) Wilson Lattice Gauge Theory Measure

   This module defines the actual Wilson lattice gauge theory for U(1):
   - Gauge configuration: angle θ ∈ [0, 2π) per link
   - Wilson action: S = β Σ_P (1 - cos(θ_P))
   - Haar measure: uniform on [0, 2π)^{#links}
   - Partition function: Z = ∫ exp(-S) dθ
   - Expectation: E[F] = (1/Z) ∫ F exp(-S) dθ

   This is the REAL lattice gauge theory, not a toy model.

   Reference: Wilson 1974, Creutz "Quarks, Gluons, and Lattices"
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.
From Coq Require Import Lia.
From Coq Require Import Psatz.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.
From Coq Require Import Permutation.

Import ListNotations.
Open Scope R_scope.

(* =========================================================================
   Part 1: Lattice Structure (reuse from main file)
   ========================================================================= *)

Module U1WilsonMeasure.

(* Lattice site: 4D coordinates with explicit time *)
Record site := mk_site {
  s_t : nat;  (* time *)
  s_x : nat;  (* spatial x *)
  s_y : nat;  (* spatial y *)
  s_z : nat   (* spatial z *)
}.

(* Direction: 0 = time, 1,2,3 = space *)
Definition direction := nat.

(* Link: site + direction *)
Record link := mk_link {
  link_site : site;
  link_dir : direction
}.

(* Plaquette: site + two directions *)
Record plaquette := mk_plaq {
  plaq_site : site;
  plaq_mu : direction;
  plaq_nu : direction
}.

(* Decidable equality for sites and links *)
Definition site_eq_dec : forall (s1 s2 : site), {s1 = s2} + {s1 <> s2}.
Proof.
  intros [t1 x1 y1 z1] [t2 x2 y2 z2].
  destruct (Nat.eq_dec t1 t2); destruct (Nat.eq_dec x1 x2);
  destruct (Nat.eq_dec y1 y2); destruct (Nat.eq_dec z1 z2);
  try (left; congruence); right; congruence.
Defined.

Definition link_eq_dec : forall (l1 l2 : link), {l1 = l2} + {l1 <> l2}.
Proof.
  intros [s1 d1] [s2 d2].
  destruct (site_eq_dec s1 s2); destruct (Nat.eq_dec d1 d2);
  try (left; congruence); right; congruence.
Defined.

(* Lattice size L: sites are in [0, L-1]^4 *)
Definition lattice_size := nat.

(* Total number of links in L^4 lattice: 4 * L^4 *)
Definition num_links (L : lattice_size) : nat := 4 * L * L * L * L.

(* Total number of plaquettes: 6 * L^4 *)
Definition num_plaquettes (L : lattice_size) : nat := 6 * L * L * L * L.

(* =========================================================================
   Part 2: U(1) Gauge Configuration

   A gauge configuration assigns an angle θ ∈ [0, 2π) to each link.
   In U(1), the link variable is U = exp(i θ).
   ========================================================================= *)

(* U(1) element represented as angle in [0, 2π) *)
Definition U1 := R.

(* Gauge configuration: angle per link *)
Definition gauge_config (L : lattice_size) := link -> U1.

(* Shift site by 1 in direction mu (periodic BC) *)
Definition shift (x : site) (mu : direction) (L : lattice_size) : site :=
  match mu with
  | 0 => mk_site (Nat.modulo (s_t x + 1) L) (s_x x) (s_y x) (s_z x)
  | 1 => mk_site (s_t x) (Nat.modulo (s_x x + 1) L) (s_y x) (s_z x)
  | 2 => mk_site (s_t x) (s_x x) (Nat.modulo (s_y x + 1) L) (s_z x)
  | 3 => mk_site (s_t x) (s_x x) (s_y x) (Nat.modulo (s_z x + 1) L)
  | _ => x
  end.

(* =========================================================================
   Part 3: Wilson Action

   Plaquette angle: θ_P = θ(x,μ) + θ(x+μ,ν) - θ(x+ν,μ) - θ(x,ν)
   Single plaquette action: β(1 - cos θ_P)
   Total action: S = Σ_P β(1 - cos θ_P)
   ========================================================================= *)

(* Plaquette angle (curl of gauge field) *)
Definition plaquette_angle (L : lattice_size) (U : gauge_config L) (p : plaquette) : R :=
  let x := plaq_site p in
  let mu := plaq_mu p in
  let nu := plaq_nu p in
  let theta_1 := U (mk_link x mu) in
  let theta_2 := U (mk_link (shift x mu L) nu) in
  let theta_3 := U (mk_link (shift x nu L) mu) in
  let theta_4 := U (mk_link x nu) in
  theta_1 + theta_2 - theta_3 - theta_4.

(* Single plaquette action *)
Definition plaq_action (beta : R) (theta_P : R) : R :=
  beta * (1 - cos theta_P).

(* Plaquette action is non-negative for β > 0 *)
Lemma plaq_action_nonneg : forall beta theta_P,
  beta > 0 -> plaq_action beta theta_P >= 0.
Proof.
  intros beta theta_P Hbeta.
  unfold plaq_action.
  assert (Hcos : -1 <= cos theta_P <= 1) by apply COS_bound.
  assert (H1cos : 0 <= 1 - cos theta_P) by lra.
  apply Rle_ge.
  apply Rmult_le_pos; lra.
Qed.

(* =========================================================================
   Part 4: Path Integral Measure

   The Wilson measure on gauge configurations is:
     dμ(U) = (1/Z) exp(-S[U]) Π_ℓ (dθ_ℓ / 2π)

   where:
   - S[U] = Σ_P β(1 - cos θ_P) is the Wilson action
   - dθ_ℓ / 2π is normalized Haar measure on U(1) ≅ S¹
   - Z = ∫ exp(-S[U]) Π_ℓ (dθ_ℓ / 2π) is the partition function

   For formalization, we axiomatize the existence of this integral.
   ========================================================================= *)

(* Haar measure on U(1): uniform measure on [0, 2π) *)
(* The measure is (1/2π) dθ, normalized so ∫ dμ = 1 *)
Definition haar_U1_density : R := / (2 * PI).

Lemma haar_U1_density_pos : haar_U1_density > 0.
Proof.
  unfold haar_U1_density.
  apply Rinv_0_lt_compat.
  apply Rmult_lt_0_compat; [lra | exact PI_RGT_0].
Qed.

(* Observable: function from gauge configurations to R *)
Definition Observable (L : lattice_size) := gauge_config L -> R.

(* =========================================================================
   Part 5: Wilson Partition Function and Expectation

   These are the REAL objects from which S2 should be derived.
   Tier-0: finite-dimensional product integral interface (iterated U(1) Haar).
   ========================================================================= *)

(* Sum of a list of reals *)
Fixpoint sum_R (l : list R) : R :=
  match l with
  | nil => 0
  | h :: t => h + sum_R t
  end.

Lemma sum_R_nonneg : forall l, (forall x, In x l -> x >= 0) -> sum_R l >= 0.
Proof.
  induction l; intros H; simpl.
  - lra.
  - assert (Ha: a >= 0) by (apply H; left; reflexivity).
    assert (Hl: sum_R l >= 0) by (apply IHl; intros; apply H; right; assumption).
    lra.
Qed.

Lemma sum_R_permutation : forall l1 l2, Permutation l1 l2 -> sum_R l1 = sum_R l2.
Proof.
  intros l1 l2 H. induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. ring.
  - rewrite IHPermutation1. exact IHPermutation2.
Qed.

Section WilsonMeasure.

Variable L : lattice_size.
Variable beta : R.
Hypothesis L_pos : (L > 0)%nat.
Hypothesis beta_pos : beta > 0.

(* List of all plaquettes in the lattice *)
Parameter all_plaquettes : list plaquette.

(* Wilson action for a configuration *)
(* S[U] = Σ_P β(1 - cos θ_P) *)
Definition wilson_action (U : gauge_config L) : R :=
  sum_R (map (fun p => plaq_action beta (plaquette_angle L U p)) all_plaquettes).

(* Wilson action is non-negative *)
Lemma wilson_action_nonneg : forall U, wilson_action U >= 0.
Proof.
  intro U. unfold wilson_action.
  apply sum_R_nonneg.
  intros x Hin.
  apply in_map_iff in Hin. destruct Hin as [p [Heq Hin]]. subst x.
  apply plaq_action_nonneg.
  apply beta_pos.
Qed.

(* Boltzmann weight *)
Definition boltzmann_weight (U : gauge_config L) : R := exp (- wilson_action U).

(* Boltzmann weight is positive *)
Lemma boltzmann_weight_pos : forall U, boltzmann_weight U > 0.
Proof.
  intros U. unfold boltzmann_weight. apply exp_pos.
Qed.

(* --- Tier-0 integration interface --- *)
Parameter all_links : list link.

Definition two_pi : R := 2 * PI.

Parameter RInt : (R -> R) -> R -> R -> R.

Definition haar_u1_integral (f : R -> R) : R :=
  (/ two_pi) * RInt f 0 two_pi.

(* Axioms for Haar integral needed for Phase C *)
Axiom haar_u1_integral_ext : forall f g, 
  (forall x, f x = g x) -> haar_u1_integral f = haar_u1_integral g.

Axiom haar_u1_integral_neg : forall f, 
  haar_u1_integral (fun x => f (-x)) = haar_u1_integral f.

Axiom haar_u1_integral_swap : forall f : R -> R -> R,
  haar_u1_integral (fun x => haar_u1_integral (fun y => f x y)) =
  haar_u1_integral (fun y => haar_u1_integral (fun x => f x y)).

Definition cfg_update (U : gauge_config L) (l : link) (theta : R) : gauge_config L :=
  fun l' => if link_eq_dec l' l then theta else U l'.

Fixpoint haar_prod_integral (ls : list link) (F : gauge_config L -> R) (U : gauge_config L) : R :=
  match ls with
  | nil => F U
  | l :: ls' =>
      haar_u1_integral (fun theta =>
        haar_prod_integral ls' F (cfg_update U l theta))
  end.

Definition integral_over_cfg (F : gauge_config L -> R) : R :=
  haar_prod_integral all_links F (fun _ => 0).

Axiom integral_linear_add : forall F G,
  integral_over_cfg (fun U => F U + G U) =
  integral_over_cfg F + integral_over_cfg G.

Axiom integral_linear_scale : forall c F,
  integral_over_cfg (fun U => c * F U) = c * integral_over_cfg F.

Axiom integral_nonneg : forall F,
  (forall U, F U >= 0) ->
  integral_over_cfg F >= 0.

Axiom integral_pos : forall F,
  (forall U, F U > 0) ->
  integral_over_cfg F > 0.

(* Partition function from the actual (finite-dimensional) integral *)
Definition partition_function : R :=
  integral_over_cfg boltzmann_weight.

Lemma partition_function_pos : partition_function > 0.
Proof.
  unfold partition_function.
  apply integral_pos.
  intro U.
  apply boltzmann_weight_pos.
Qed.

Lemma partition_function_neq_0 : partition_function <> 0.
Proof.
  apply Rgt_not_eq.
  apply partition_function_pos.
Qed.

(* Expectation functional *)
Definition Expect (F : Observable L) : R :=
  (/ partition_function) *
  integral_over_cfg (fun U => F U * boltzmann_weight U).

Lemma Expect_exists : forall (F : Observable L), exists v : R, True.
Proof.
  intros F.
  exists (Expect F).
  exact I.
Qed.

Lemma Expect_linear_add : forall F G,
  Expect (fun U => F U + G U) = Expect F + Expect G.
Proof.
  intros F G.
  unfold Expect.
  replace (fun U : gauge_config L => (F U + G U) * boltzmann_weight U)
    with (fun U : gauge_config L =>
      F U * boltzmann_weight U + G U * boltzmann_weight U).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite integral_linear_add.
  ring.
Qed.

Lemma Expect_linear_scale : forall c F,
  Expect (fun U => c * F U) = c * Expect F.
Proof.
  intros c F.
  unfold Expect.
  replace (fun U : gauge_config L => (c * F U) * boltzmann_weight U)
    with (fun U : gauge_config L => c * (F U * boltzmann_weight U)).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite integral_linear_scale.
  ring.
Qed.

Lemma Expect_normalized : Expect (fun _ => 1) = 1.
Proof.
  unfold Expect, partition_function.
  replace (fun U : gauge_config L => 1 * boltzmann_weight U) with boltzmann_weight.
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  field.
  apply partition_function_neq_0.
Qed.

Lemma Expect_nonneg : forall F,
  (forall U, F U >= 0) -> Expect F >= 0.
Proof.
  intros F HF.
  unfold Expect.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    exact partition_function_pos.
  - apply Rge_le.
    apply integral_nonneg.
    intro U.
    apply Rle_ge.
    apply Rmult_le_pos.
    + apply Rge_le.
      apply HF.
    + apply Rlt_le.
      apply boltzmann_weight_pos.
Qed.

Lemma Expect_square_nonneg : forall F : Observable L,
  0 <= Expect (fun U => F U * F U).
Proof.
  intro F.
  apply Rge_le.
  apply Expect_nonneg.
  intro U.
  apply Rle_ge.
  apply Rle_0_sqr.
Qed.

(* =========================================================================
   Part 6: Time Reflection Operator

   Time reflection: t ↦ L - 1 - t (for lattice with L sites in time direction)
   For gauge configs: (Θ U)(x, μ) depends on whether μ = 0 (time) or not.

   SCOPE FIREWALL: reflection defs/lemmas use nat only. Close R_scope to avoid
   "lia cannot find witness" and rewrite mismatches from silent R coercion.
   ========================================================================= *)

Close Scope R_scope.
Open Scope nat_scope.

(* Reflect a site in time *)
Definition reflect_site (x : site) : site :=
  mk_site (L - 1 - s_t x)%nat (s_x x) (s_y x) (s_z x).

(* Valid lattice links have time coordinate < L *)
Definition valid_link (l : link) : Prop := (s_t (link_site l) < L)%nat.

Definition valid_linkb (l : link) : bool := (s_t (link_site l) <? L)%nat.

(* Raw reflection on valid links *)
Definition reflect_link_raw (l : link) : link :=
  let x := link_site l in
  let mu := link_dir l in
  if Nat.eqb mu 0%nat then
    mk_link (reflect_site (shift x 0%nat L)) 0%nat
  else
    mk_link (reflect_site x) mu.

(* Total reflection: identity outside the finite lattice domain *)
Definition reflect_link (l : link) : link :=
  if valid_linkb l then reflect_link_raw l else l.

Lemma link_dir_reflect : forall l, link_dir (reflect_link l) = link_dir l.
Proof.
  intros [x mu]. unfold reflect_link, valid_linkb, reflect_link_raw. simpl.
  destruct (Nat.ltb (s_t x) L) eqn:Hrange.
  - destruct (Nat.eqb_spec mu 0%nat) as [H|H]; [subst; reflexivity | reflexivity].
  - reflexivity.
Qed.

(* Helper: a - (a - b) = b when b <= a *)
Lemma sub_sub_add : forall a b : nat, b <= a -> a - (a - b) = b.
Proof.
  intros a b H.
  apply Nat.add_sub_eq_l.
  rewrite Nat.sub_add by exact H. reflexivity.
Qed.

Lemma reflect_site_involutive : forall x, (s_t x < L)%nat -> reflect_site (reflect_site x) = x.
Proof.
  intros [t x y z] Ht. unfold reflect_site. simpl in *.
  apply (f_equal (fun t0 => mk_site t0 x y z)).
  apply sub_sub_add.
  lia.
Qed.

Lemma shift_reflect_shift : forall x, (s_t x < L)%nat ->
  shift (reflect_site (shift x 0%nat L)) 0%nat L = reflect_site x.
Proof.
  intros [t x y z] Ht. unfold shift, reflect_site. simpl in *.
  apply (f_equal (fun t0 => mk_site t0 x y z)).
  destruct (Nat.eq_dec t (L - 1)) as [Heq|Hneq].
  - subst t.
    assert (Hmod1 : Nat.modulo (L - 1 + 1) L = 0%nat).
    { replace (L - 1 + 1)%nat with L by lia. apply Nat.mod_same. lia. }
    rewrite Hmod1.
    replace (L - 1 - (L - 1))%nat with 0%nat by lia.
    replace (L - 1 - 0 + 1)%nat with L by lia.
    rewrite Nat.mod_same by lia.
    reflexivity.
  - assert (Hmod1 : Nat.modulo (t + 1) L = t + 1).
    { apply Nat.mod_small. lia. }
    rewrite Hmod1.
    replace (L - 1 - (t + 1) + 1)%nat with (L - (t + 1))%nat by lia.
    rewrite Nat.mod_small.
    + lia.
    + lia.
Qed.

Lemma reflect_link_raw_valid : forall l, valid_link l -> valid_link (reflect_link_raw l).
Proof.
  intros [x mu] Ht.
  unfold valid_link, reflect_link_raw in *.
  simpl in *.
  destruct (Nat.eqb_spec mu 0%nat) as [->|Hmu].
  - unfold shift, reflect_site; simpl.
    assert (Hmod : ((s_t x + 1) mod L < L)%nat).
    { apply Nat.mod_upper_bound. lia. }
    lia.
  - unfold reflect_site; simpl.
    lia.
Qed.

Lemma reflect_link_raw_involutive : forall l, valid_link l -> reflect_link_raw (reflect_link_raw l) = l.
Proof.
  intros [x mu] Ht.
  unfold reflect_link_raw.
  destruct (Nat.eqb_spec mu 0%nat) as [->|Hmu].
  - repeat rewrite Nat.eqb_refl.
    f_equal.
    change (reflect_site (shift (reflect_site (shift x 0%nat L)) 0%nat L) = x).
    rewrite (shift_reflect_shift x Ht).
    apply reflect_site_involutive.
    exact Ht.
  - assert (Hmu_eqb : Nat.eqb mu 0%nat = false).
    { apply Nat.eqb_neq. exact Hmu. }
    cbn [link_dir link_site].
    repeat rewrite Hmu_eqb.
    cbn.
    rewrite Hmu_eqb.
    f_equal.
    apply reflect_site_involutive.
    exact Ht.
Qed.

Lemma reflect_link_involutive : forall l, valid_link l -> reflect_link (reflect_link l) = l.
Proof.
  intros l Hl.
  assert (Hvb : valid_linkb l = true).
  { unfold valid_linkb, valid_link in *. apply Nat.ltb_lt. exact Hl. }
  unfold reflect_link at 2.
  rewrite Hvb.
  assert (Hvb' : valid_linkb (reflect_link_raw l) = true).
  { unfold valid_linkb, valid_link.
    apply Nat.ltb_lt.
    apply reflect_link_raw_valid.
    exact Hl. }
  unfold reflect_link at 1.
  rewrite Hvb'.
  apply reflect_link_raw_involutive.
  exact Hl.
Qed.

Lemma reflect_link_involutive_total : forall l, reflect_link (reflect_link l) = l.
Proof.
  intros l.
  destruct (valid_linkb l) eqn:Hvb.
  - apply reflect_link_involutive.
    apply Nat.ltb_lt. exact Hvb.
  - unfold reflect_link at 2.
    rewrite Hvb.
    unfold reflect_link at 1.
    rewrite Hvb.
    reflexivity.
Qed.

Lemma reflect_link_inj : forall a b, reflect_link a = reflect_link b -> a = b.
Proof.
  intros a b H.
  apply (f_equal reflect_link) in H.
  rewrite !reflect_link_involutive_total in H.
  exact H.
Qed.

(* Option C: orientation-based negation for Θ² = id.
   Time-like links (dir=0) always get negated; space-like links don't.
   Crucially, orientation_flipped is PRESERVED under reflection
   (since link_dir is preserved), which is what gives Θ² = id. *)
Definition orientation_flipped (l : link) : bool :=
  Nat.eqb (link_dir l) 0%nat.

Lemma orientation_flipped_reflect : forall l,
  orientation_flipped (reflect_link l) = orientation_flipped l.
Proof.
  intros l. unfold orientation_flipped. rewrite link_dir_reflect. reflexivity.
Qed.

Lemma reflect_link_fixed_from_time_eq : forall l,
  link_dir l = 0%nat ->
  s_t (link_site l) = s_t (link_site (reflect_link l)) ->
  reflect_link l = l.
Proof.
  intros [x mu] Hdir Heq.
  simpl in Hdir.
  subst mu.
  unfold reflect_link, valid_linkb, reflect_link_raw in *.
  simpl in *.
  destruct (s_t x <? L) eqn:Hrange.
  - destruct x as [t sx sy sz].
    simpl in *.
    f_equal.
    unfold reflect_site. simpl.
    f_equal; try reflexivity.
    symmetry. exact Heq.
  - reflexivity.
Qed.

Definition links_wf : Prop := forall l, In l all_links -> valid_link l.
Hypothesis all_links_wf : links_wf.
Hypothesis all_links_reflect_closed : forall l, In l all_links -> In (reflect_link l) all_links.

Lemma reflect_link_closed : forall l, In l all_links -> In (reflect_link l) all_links.
Proof.
  intros l Hin.
  apply all_links_reflect_closed.
  exact Hin.
Qed.

Lemma reflect_link_valid_on_links : forall l, In l all_links -> valid_link (reflect_link l).
Proof.
  intros l Hin.
  apply all_links_wf.
  apply reflect_link_closed.
  exact Hin.
Qed.

Lemma ltb_true_of_lt : forall a b, (a < b)%nat -> (a <? b) = true.
Proof. intros. apply (proj2 (Nat.ltb_lt a b)); auto. Qed.

Lemma ltb_false_of_ge : forall a b, (b <= a)%nat -> (a <? b) = false.
Proof. intros. exact (proj2 (Nat.ltb_ge a b) H). Qed.

(* Reopen R_scope for config_reflect (uses R, Ropp) *)
Open Scope R_scope.

(* Option C: orientation-based config_reflect *)
Definition config_reflect (U : gauge_config L) : gauge_config L :=
  fun l =>
    let lr := reflect_link l in
    if orientation_flipped l then - (U lr) else U lr.

Lemma config_reflect_involutive : forall U l,
  In l all_links ->
  config_reflect (config_reflect U) l = U l.
Proof.
  intros U l Hin.
  unfold config_reflect.
  replace (reflect_link (reflect_link l)) with l
    by (symmetry; apply reflect_link_involutive; apply all_links_wf; exact Hin).
  rewrite orientation_flipped_reflect.
  destruct (orientation_flipped l) eqn:Hl.
  - simpl. rewrite Ropp_involutive. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma shift_comm : forall x mu nu,
  shift (shift x mu L) nu L = shift (shift x nu L) mu L.
Proof.
  intros [t x y z] mu nu.
  destruct mu as [|[|[|[|mu]]]];
  destruct nu as [|[|[|[|nu]]]];
  unfold shift; simpl; f_equal; lia.
Qed.

Lemma reflect_site_shift_spatial : forall x mu,
  mu <> 0%nat ->
  reflect_site (shift x mu L) = shift (reflect_site x) mu L.
Proof.
  intros [t sx sy sz] mu Hmu.
  destruct mu as [|[|[|[|mu]]]]; try congruence;
  unfold reflect_site, shift; simpl; reflexivity.
Qed.

Definition plaq_boundary (p : plaquette) : list (link * bool) :=
  let x := plaq_site p in
  let mu := plaq_mu p in
  let nu := plaq_nu p in
  [ (mk_link x mu, true);
    (mk_link (shift x mu L) nu, true);
    (mk_link (shift x nu L) mu, false);
    (mk_link x nu, false) ].

Definition reflect_edge (e : link * bool) : link * bool :=
  let (l, sgn) := e in (reflect_link l, sgn).

(* Reflect a plaquette: shift base point if time-like *)
Definition reflect_plaq (p : plaquette) : plaquette :=
  if orb (Nat.eqb (plaq_mu p) 0%nat) (Nat.eqb (plaq_nu p) 0%nat) then
    mk_plaq (reflect_site (shift (plaq_site p) 0%nat L)) (plaq_mu p) (plaq_nu p)
  else
    mk_plaq (reflect_site (plaq_site p)) (plaq_mu p) (plaq_nu p).

Lemma reflect_plaq_involutive : forall p,
  valid_link (mk_link (plaq_site p) 0%nat) ->
  reflect_plaq (reflect_plaq p) = p.
Proof.
  intros [x mu nu] Hval.
  destruct mu as [| [| [| [| mu ]]]];
  destruct nu as [| [| [| [| nu ]]]];
  unfold reflect_plaq; simpl;
  f_equal;
  try (apply reflect_site_involutive; exact Hval);
  try (change (reflect_site (shift (reflect_site (shift x 0%nat L)) 0%nat L) = x);
       rewrite (shift_reflect_shift x); [| exact Hval];
       apply reflect_site_involutive; exact Hval).
Qed.

Lemma perm_rotate4 {A} (a b c d : A) :
  Permutation [a;b;c;d] [b;c;d;a].
Proof.
  apply Permutation_cons_append.
Qed.

Lemma perm_swap_23 {A} (a b c d : A) :
  Permutation [a;b;c;d] [a;c;b;d].
Proof.
  apply perm_skip. apply perm_swap.
Qed.

(* Geometry transport for purely spatial plaquettes.
   This statement is correct for sign-preserving reflect_edge only when both
   plaquette directions are spatial. Time-involving plaquettes require the
   Theta-aware boundary transport handled in u1_reflection.v
   (theta_plaq_reflect_boundary / plaq_action_reflect_boundary). *)
Lemma plaq_boundary_reflect_spatial : forall p,
  valid_link (mk_link (plaq_site p) 0%nat) ->
  plaq_mu p <> 0%nat ->
  plaq_nu p <> 0%nat ->
  Permutation (plaq_boundary (reflect_plaq p)) (map reflect_edge (plaq_boundary p)).
Proof.
  intros [x mu nu] Hx Hmu Hnu.
  unfold plaq_boundary, reflect_plaq, reflect_edge.
  simpl.
  assert (Hmu_eqb : Nat.eqb mu 0%nat = false) by (apply Nat.eqb_neq; exact Hmu).
  assert (Hnu_eqb : Nat.eqb nu 0%nat = false) by (apply Nat.eqb_neq; exact Hnu).
  rewrite Hmu_eqb, Hnu_eqb.
  unfold reflect_link, valid_linkb, reflect_link_raw.
  simpl.
  assert (Hx_b : s_t x <? L = true) by (apply Nat.ltb_lt; exact Hx).
  assert (HLpos : (L > 0)%nat) by lia.
  rewrite Hx_b.
  rewrite Hmu_eqb.
  rewrite Hnu_eqb.
  assert (Hshift_mu : (s_t (shift x mu L) < L)%nat).
  { destruct x as [t sx sy sz]; simpl in *.
    destruct mu as [|[|[|[|mu']]]]; simpl.
    - apply Nat.mod_upper_bound. lia.
    - exact Hx.
    - exact Hx.
    - exact Hx.
    - exact Hx. }
  assert (Hshift_nu : (s_t (shift x nu L) < L)%nat).
  { destruct x as [t sx sy sz]; simpl in *.
    destruct nu as [|[|[|[|nu']]]]; simpl.
    - apply Nat.mod_upper_bound. lia.
    - exact Hx.
    - exact Hx.
    - exact Hx.
    - exact Hx. }
  assert (Hshift_mu_b : s_t (shift x mu L) <? L = true) by (apply Nat.ltb_lt; exact Hshift_mu).
  assert (Hshift_nu_b : s_t (shift x nu L) <? L = true) by (apply Nat.ltb_lt; exact Hshift_nu).
  rewrite Hshift_mu_b, Hshift_nu_b.
  rewrite reflect_site_shift_spatial by exact Hmu.
  rewrite reflect_site_shift_spatial by exact Hnu.
  apply Permutation_refl.
Qed.

(* Compatibility wrapper: keeps the original lemma name while forcing the
   spatial-domain precondition explicitly. *)
Lemma plaq_boundary_reflect : forall p,
  valid_link (mk_link (plaq_site p) 0%nat) ->
  (plaq_mu p <> 0%nat /\ plaq_nu p <> 0%nat) ->
  Permutation (plaq_boundary (reflect_plaq p)) (map reflect_edge (plaq_boundary p)).
Proof.
  intros p Hvalid [Hmu Hnu].
  eapply plaq_boundary_reflect_spatial; eauto.
Qed.

Lemma fold_right_map {A B C} (f : B -> C -> C) (g : A -> B) z xs :
  fold_right f z (map g xs) = fold_right (fun x acc => f (g x) acc) z xs.
Proof.
  induction xs; simpl; try reflexivity.
  rewrite IHxs. reflexivity.
Qed.

Lemma Theta_on_reflected : forall U l,
  valid_link l ->
  config_reflect U (reflect_link l) =
  if orientation_flipped l then - (U l) else U l.
Proof.
  intros U l Hval.
  unfold config_reflect.
  rewrite reflect_link_involutive by exact Hval.
  rewrite orientation_flipped_reflect.
  reflexivity.
Qed.

Hypothesis all_plaquettes_reflect_closed : forall p, In p all_plaquettes -> In (reflect_plaq p) all_plaquettes.

(* Plaquette angle reflection symmetry. *)
Hypothesis plaquette_angle_reflect : forall U p,
  valid_link (mk_link (plaq_site p) 0%nat) ->
  cos (plaquette_angle L (config_reflect U) p) =
  cos (plaquette_angle L U (reflect_plaq p)).

(* Wilson action is invariant under reflection *)
Hypothesis all_plaquettes_nodup : NoDup all_plaquettes.
Hypothesis all_plaquettes_valid : forall p, In p all_plaquettes -> valid_link (mk_link (plaq_site p) 0%nat).

Lemma all_plaquettes_perm_reflected :
  Permutation all_plaquettes (map reflect_plaq all_plaquettes).
Proof.
  apply NoDup_Permutation_bis.
  - exact all_plaquettes_nodup.
  - rewrite map_length. lia.
  - unfold incl. intros p Hin.
    apply in_map_iff.
    exists (reflect_plaq p).
    split.
    + exact (reflect_plaq_involutive p (all_plaquettes_valid p Hin)).
    + apply all_plaquettes_reflect_closed.
      exact Hin.
Qed.

Lemma wilson_action_reflect : forall U,
  wilson_action (config_reflect U) = wilson_action U.
Proof.
  intro U. unfold wilson_action.
  transitivity (sum_R (map (fun p => plaq_action beta (plaquette_angle L (config_reflect U) p)) (map reflect_plaq all_plaquettes))).
  - apply sum_R_permutation. apply Permutation_map. exact all_plaquettes_perm_reflected.
  - rewrite map_map.
    f_equal. apply map_ext_in. intros p Hin.
    unfold plaq_action.
    f_equal. f_equal.
    rewrite plaquette_angle_reflect.
    + rewrite reflect_plaq_involutive.
      * reflexivity.
      * apply all_plaquettes_valid. exact Hin.
    + apply all_plaquettes_valid. apply all_plaquettes_reflect_closed. exact Hin.
Qed.

(* Time reflection on observables *)
Definition Theta (F : Observable L) : Observable L :=
  fun U => F (config_reflect U).

Definition supported_on_all_links (F : Observable L) : Prop :=
  forall U V, (forall l, In l all_links -> U l = V l) -> F U = F V.

Lemma Theta_Theta_on_links : forall F,
  supported_on_all_links F ->
  forall U, Theta (Theta F) U = F U.
Proof.
  intros F HF U.
  unfold Theta.
  apply HF.
  intros l Hin.
  apply config_reflect_involutive.
  exact Hin.
Qed.

(* Phase C: Change of Variables Invariance *)

(* 1. Geometric Lemma: config_reflect commutes with update *)
Lemma config_reflect_cfg_update :
  forall (U : gauge_config L) (l : link) (theta : R),
    valid_link l ->
    config_reflect (cfg_update U l theta) =
    cfg_update (config_reflect U) (reflect_link l)
      (if orientation_flipped l then - theta else theta).
Proof.
  intros U l theta Hval.
  apply functional_extensionality. intro l'.
  unfold config_reflect, cfg_update.
  destruct (link_eq_dec (reflect_link l') l) as [Hhit|Hmiss].
  - assert (Hl' : l' = reflect_link l).
    {
      apply (f_equal reflect_link) in Hhit.
      rewrite reflect_link_involutive_total in Hhit.
      exact Hhit.
    }
    assert (Hof : orientation_flipped l' = orientation_flipped l).
    {
      rewrite <- orientation_flipped_reflect.
      now rewrite Hhit.
    }
    destruct (link_eq_dec l' (reflect_link l)) as [Heq|Hneq].
    + rewrite Hof. reflexivity.
    + contradiction.
  - destruct (link_eq_dec l' (reflect_link l)) as [Heq|Hneq].
    + exfalso.
      apply Hmiss.
      subst l'.
      apply reflect_link_involutive.
      exact Hval.
    + reflexivity.
Qed.

Lemma cfg_update_comm_distinct :
  forall (U : gauge_config L) (l1 l2 : link) (theta1 theta2 : R),
    l1 <> l2 ->
    cfg_update (cfg_update U l1 theta1) l2 theta2 =
    cfg_update (cfg_update U l2 theta2) l1 theta1.
Proof.
  intros U l1 l2 theta1 theta2 Hneq.
  apply functional_extensionality; intro l.
  unfold cfg_update.
  destruct (link_eq_dec l l1) as [Hl1|Hl1];
  destruct (link_eq_dec l l2) as [Hl2|Hl2]; subst; simpl.
  - exfalso. apply Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* 2. Product Integral Permutation Invariance (Fubini) *)
Lemma haar_prod_integral_perm :
  forall (ls1 ls2 : list link) (F : gauge_config L -> R) (U : gauge_config L),
    Permutation ls1 ls2 ->
    NoDup ls1 ->
    haar_prod_integral ls1 F U = haar_prod_integral ls2 F U.
Proof.
  intros ls1 ls2 F U Hperm.
  revert F U.
  induction Hperm; intros F U Hnodup.
  - reflexivity.
  - inversion Hnodup as [|a l0 Ha_notin Hnd]; subst.
    simpl.
    apply haar_u1_integral_ext.
    intro theta.
    apply IHHperm.
    exact Hnd.
  - inversion Hnodup as [|y0 l0 Hy_notin Hnd0]; subst.
    inversion Hnd0 as [|x0 l1 Hx_notin Hnd1]; subst.
    simpl.
    eapply eq_trans.
    + apply haar_u1_integral_swap.
    + apply haar_u1_integral_ext; intro theta_x.
      apply haar_u1_integral_ext; intro theta_y.
      rewrite (cfg_update_comm_distinct U y x theta_y theta_x).
      * reflexivity.
      * intro Heq. subst y.
        apply Hy_notin. left. reflexivity.
  - rewrite (IHHperm1 F U Hnodup).
    apply IHHperm2.
    eapply Permutation_NoDup.
    + exact Hperm1.
    + exact Hnodup.
Qed.

Hypothesis all_links_nodup : NoDup all_links.

(* 3. Link Permutation Lemma *)
Lemma all_links_perm_reflect :
  Permutation all_links (map reflect_link all_links).
Proof.
  apply NoDup_Permutation_bis.
  - exact all_links_nodup.
  - rewrite map_length. lia.
  - unfold incl. intros l Hin.
    apply in_map_iff.
    exists (reflect_link l).
    split.
    + exact (reflect_link_involutive l (all_links_wf l Hin)).
    + apply all_links_reflect_closed.
      exact Hin.
Qed.

(* 4. Main Inductive Step: Change of Variables *)
Lemma haar_prod_integral_change_var :
  forall (ls : list link) (F : gauge_config L -> R) (U : gauge_config L),
    (forall l, In l ls -> valid_link l) ->
    haar_prod_integral ls (fun U0 => F (config_reflect U0)) U
    =
    haar_prod_integral (map reflect_link ls) F (config_reflect U).
Proof.
  induction ls as [| l ls' IH]; intros F U Hval.
  - simpl. reflexivity.
  - simpl.
    eapply eq_trans.
    + apply haar_u1_integral_ext. intro theta.
      apply IH.
      intros l0 Hin.
      apply Hval. right. exact Hin.
    + eapply eq_trans.
      * apply haar_u1_integral_ext. intro theta.
        rewrite config_reflect_cfg_update.
        -- reflexivity.
        -- apply Hval. left. reflexivity.
      * destruct (orientation_flipped l) eqn:Hflip.
        -- simpl.
           set (f := fun theta : R =>
             haar_prod_integral (map reflect_link ls') F
               (cfg_update (config_reflect U) (reflect_link l) theta)).
           change (haar_u1_integral (fun theta : R => f (- theta)) = haar_u1_integral f).
           apply haar_u1_integral_neg.
        -- reflexivity.
Qed.

(* 5. Phase C Main Theorem *)
Lemma integral_change_var : forall F : Observable L,
  integral_over_cfg (Theta F) = integral_over_cfg F.
Proof.
  intro F.
  unfold integral_over_cfg, Theta.
  set (U0 := fun _ : link => 0).
  rewrite (haar_prod_integral_change_var all_links F U0).
  2: { intros l Hin. apply all_links_wf. exact Hin. }
  assert (Hzero : config_reflect U0 = U0).
  {
    apply functional_extensionality. intro l.
    unfold config_reflect, U0.
    destruct (orientation_flipped l); lra.
  }
  rewrite Hzero.
  symmetry.
  apply haar_prod_integral_perm.
  - exact all_links_perm_reflect.
  - exact all_links_nodup.
Qed.

(* Site is in positive time (t > L/2 in lattice terms, or t > 0 in continuous) *)
Definition positive_time (x : site) : Prop :=
  (2 * s_t x > L)%nat.

(* Observable support as an extensional dependency condition on positive-time links. *)
Definition agrees_on_positive (U V : gauge_config L) : Prop :=
  forall l, positive_time (link_site l) -> U l = V l.

Definition supported_positive (F : Observable L) : Prop :=
  forall U V, agrees_on_positive U V -> F U = F V.

(* =========================================================================
   Part 7: The Key Theorem Target: Reflection Positivity

   THIS IS THE WALL.

   We need to prove:
     ∀ F supported in t > 0, E[Θ(F) · F] ≥ 0

   This requires analyzing the structure of the Wilson action
   under time reflection.
   ========================================================================= *)

(* Inner product from time reflection *)
Definition os_inner (F G : Observable L) : R :=
  Expect (fun U => (Theta F) U * G U).

Lemma os_inner_linear_right : forall F G H : Observable L,
  os_inner F (fun U => G U + H U) = os_inner F G + os_inner F H.
Proof.
  intros F G H.
  unfold os_inner.
  replace (fun U : gauge_config L => Theta F U * (G U + H U))
    with (fun U : gauge_config L => Theta F U * G U + Theta F U * H U).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite Expect_linear_add.
  reflexivity.
Qed.

Lemma os_inner_scale_right : forall (a : R) (F G : Observable L),
  os_inner F (fun U => a * G U) = a * os_inner F G.
Proof.
  intros a F G.
  unfold os_inner.
  replace (fun U : gauge_config L => Theta F U * (a * G U))
    with (fun U : gauge_config L => a * (Theta F U * G U)).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite Expect_linear_scale.
  reflexivity.
Qed.

Lemma os_inner_linear_left : forall F G H : Observable L,
  os_inner (fun U => F U + G U) H = os_inner F H + os_inner G H.
Proof.
  intros F G H.
  unfold os_inner, Theta.
  replace (fun U : gauge_config L =>
    (F (config_reflect U) + G (config_reflect U)) * H U)
    with (fun U : gauge_config L =>
      F (config_reflect U) * H U + G (config_reflect U) * H U).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite Expect_linear_add.
  reflexivity.
Qed.

Lemma os_inner_scale_left : forall (a : R) (F G : Observable L),
  os_inner (fun U => a * F U) G = a * os_inner F G.
Proof.
  intros a F G.
  unfold os_inner, Theta.
  replace (fun U : gauge_config L => (a * F (config_reflect U)) * G U)
    with (fun U : gauge_config L => a * (F (config_reflect U) * G U)).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite Expect_linear_scale.
  reflexivity.
Qed.

(* The reflection positivity theorem we need to prove *)
(* Phase D: Reflection Positivity Structure *)

(* 1. Kernel Positivity Axiom *)
(* The kernel K(x,y) = exp(beta * cos(x - y)) is positive definite *)
Axiom kernel_u1_posdef :
  forall (beta : R) (N : nat) (thetas : nat -> R) (cs : nat -> R),
    beta >= 0 ->
    sum_R (map (fun i => 
      sum_R (map (fun j => 
        cs i * cs j * exp (beta * cos (thetas i - thetas j))
      ) (seq 0 N))
    ) (seq 0 N)) >= 0.

(* 2. Boltzmann Decomposition frontier *)
(* We assume the weight factors into Positive, Negative (reflected), and Crossing parts. *)
(* This is the remaining analytic bridge from Wilson measure to kernel form. *)
Hypothesis os_inner_kernel_form :
  forall F, supported_positive F ->
  exists (N : nat) (G : nat -> gauge_config L -> R) (angles : nat -> gauge_config L -> R),
    os_inner F F = 
    integral_over_cfg (fun U =>
      sum_R (map (fun i => 
        sum_R (map (fun j => 
           (G i U) * (G j U) * exp (beta * cos ((angles i U) - (angles j U)))
        ) (seq 0 N))
      ) (seq 0 N))
    ).

(* 3. The Wall: Reflection Positivity *)
Theorem reflection_positivity_U1 :
  forall F : Observable L,
    supported_positive F ->
    os_inner F F >= 0.
Proof.
  intros F Hsupp.
  destruct (os_inner_kernel_form F Hsupp) as [N [G [angles Heq]]].
  rewrite Heq.
  apply integral_nonneg.
  intro U.
  apply kernel_u1_posdef.
  lra.
Qed.

(* Full Gram positivity for finite linear combinations *)
Fixpoint linear_combo (coeffs : list R) (obs : list (Observable L)) : Observable L :=
  match coeffs, obs with
  | c :: cs, F :: Fs => fun U => c * F U + linear_combo cs Fs U
  | _, _ => fun _ => 0
  end.

Definition all_positive_support (obs : list (Observable L)) : Prop :=
  Forall supported_positive obs.

Lemma supported_positive_zero : supported_positive (fun _ => 0).
Proof.
  intros U V Hagree.
  reflexivity.
Qed.

Lemma supported_positive_scale : forall (a : R) (F : Observable L),
  supported_positive F -> supported_positive (fun U => a * F U).
Proof.
  intros a F HF U V Hagree.
  rewrite (HF U V Hagree).
  reflexivity.
Qed.

Lemma supported_positive_add : forall (F G : Observable L),
  supported_positive F -> supported_positive G ->
  supported_positive (fun U => F U + G U).
Proof.
  intros F G HF HG U V Hagree.
  rewrite (HF U V Hagree).
  rewrite (HG U V Hagree).
  reflexivity.
Qed.

Lemma linear_combo_supported_positive : forall coeffs obs,
  all_positive_support obs ->
  length coeffs = length obs ->
  supported_positive (linear_combo coeffs obs).
Proof.
  induction coeffs as [| c cs IH]; intros obs Hsupp Hlen.
  - destruct obs as [| F Fs].
    + simpl. exact supported_positive_zero.
    + simpl in Hlen. discriminate Hlen.
  - destruct obs as [| F Fs].
    + simpl in Hlen. discriminate Hlen.
    + simpl in Hlen.
      inversion Hsupp as [| F' Fs' HF HFs Heq]; subst.
      simpl.
      apply supported_positive_add.
      * apply supported_positive_scale. exact HF.
      * apply IH.
        -- exact HFs.
        -- inversion Hlen. reflexivity.
Qed.

Theorem reflection_positivity_gram :
  forall coeffs obs,
    all_positive_support obs ->
    length coeffs = length obs ->
    os_inner (linear_combo coeffs obs) (linear_combo coeffs obs) >= 0.
Proof.
  intros coeffs obs Hsupp Hlen.
  apply reflection_positivity_U1.
  apply linear_combo_supported_positive; assumption.
Qed.

End WilsonMeasure.

(* =========================================================================
   Part 8: The REAL Two-Point Function

   This is what S2 SHOULD be: an actual correlator from the Wilson measure.
   ========================================================================= *)

Section RealCorrelators.

Variable L : lattice_size.
Variable beta : R.
Hypothesis L_pos : (L > 0)%nat.
Hypothesis beta_pos : beta > 0.

(* Local observable: plaquette energy at site x *)
Definition plaq_energy (x : site) (mu nu : direction) : Observable L :=
  fun U =>
    let p := mk_plaq x mu nu in
    (* Need plaquette_angle here - simplified for now *)
    0. (* placeholder *)

(* Two-point function: ⟨O(x) O(y)⟩ - ⟨O(x)⟩⟨O(y)⟩ *)
(* In full implementation, this would use the Wilson expectation:
   S2_real Ox Oy := E[Ox · Oy] - E[Ox] · E[Oy]
   For now, axiomatize the existence of such a function. *)
Parameter S2_real : Observable L -> Observable L -> R.

(* The axiom relating S2_real to Expect would go here once
   the cross-section signature issues are resolved. *)

(* THIS is the real Schwinger function, not exp(-σr) *)

End RealCorrelators.

End U1WilsonMeasure.
