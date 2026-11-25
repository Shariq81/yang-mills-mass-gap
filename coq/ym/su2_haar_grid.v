(* =========================================================================
   ym/su2_haar_grid.v

   The dyadic Hopf grids `su2_grid n` of `verification/ChallengeSU2Gauge.v`
   (the finite a-priori distributions whose weak limit is the Haar measure
   of SU(2)):

     - `grid_nonempty`, `grid_unit`: every grid is a non-empty list of unit
       quaternions (8^n of them, `grid_length`);
     - `grid_center`: for n >= 1 the grid is invariant, as a multiset, under
       the central element -1 (the half-period shift of both Hopf angles);
     - `grid_average_converges`: for every finite list of links E and every
       bounded uniformly continuous observable Phi the normalized grid sums
         |G_n|^{-|E|} * su2_sum G_n E Phi 1
       converge as n -> infinity.  They form a Cauchy sequence: the grid
       G_{n+m} refines G_n, every point of a cell of G_n being uniformly
       close to the corner of the cell, so the two averages differ by at
       most the modulus of continuity of Phi, with no accumulation of the
       error over the links;
     - `grid_average_bounds`: the normalized grid sums lie between any two
       bounds of Phi on the SU(2)-valued configurations.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + ym.z2_gauge_expansion + ym.su2_algebra.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.su2_algebra.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering Z2GaugeExpansion SU2Algebra.
Open Scope R_scope.

Module SU2HaarGrid.

  (* =======================================================================
     1. The Hopf grid with an arbitrary number N of subdivisions
     ======================================================================= *)

  (* the grid point with indices (i, j, k) of the grid with N subdivisions *)
  Definition gpt (N i j k : nat) : Quat :=
    su2_hopf (INR i / INR N) (INR j / INR N) (INR k / INR N).

  Definition gridN (N : nat) : list Quat :=
    flat_map (fun i =>
      flat_map (fun j => map (fun k => gpt N i j k) (seq 0 N)) (seq 0 N))
      (seq 0 N).

  Lemma grid_gridN : forall n, su2_grid n = gridN (2 ^ n).
  Proof. reflexivity. Qed.

  Lemma pow2_pos : forall n, (0 < 2 ^ n)%nat.
  Proof. intro n. pose proof (Nat.pow_nonzero 2 n). lia. Qed.

  Lemma flat_map_length_const :
    forall {A B : Type} (f : A -> list B) (c : nat) (l : list A),
      (forall x, In x l -> length (f x) = c) ->
      length (flat_map f l) = (length l * c)%nat.
  Proof.
    intros A B f c l H. induction l as [| a l IH]; [reflexivity |].
    cbn [flat_map length]. rewrite app_length, (H a (or_introl eq_refl)), IH.
    - reflexivity.
    - intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma gridN_length : forall N, length (gridN N) = (N * (N * N))%nat.
  Proof.
    intro N. unfold gridN.
    rewrite (flat_map_length_const _ (N * N)%nat).
    - rewrite seq_length. reflexivity.
    - intros i _. rewrite (flat_map_length_const _ N).
      + rewrite seq_length. reflexivity.
      + intros j _. rewrite map_length, seq_length. reflexivity.
  Qed.

  Lemma grid_length : forall n,
    length (su2_grid n) = (2 ^ n * (2 ^ n * 2 ^ n))%nat.
  Proof. intro n. rewrite grid_gridN. apply gridN_length. Qed.

  Lemma gridN_length_pos : forall N, (0 < N)%nat -> 0 < INR (length (gridN N)).
  Proof.
    intros N HN. rewrite gridN_length, !mult_INR.
    assert (H : 0 < INR N) by (apply lt_0_INR; exact HN).
    repeat apply Rmult_lt_0_compat; exact H.
  Qed.

  Lemma grid_length_pos : forall n, 0 < INR (length (su2_grid n)).
  Proof. intro n. rewrite grid_gridN. apply gridN_length_pos. apply pow2_pos. Qed.

  Lemma grid_nonempty : forall n, su2_grid n <> [].
  Proof.
    intros n H. pose proof (grid_length_pos n) as HL.
    rewrite H in HL. cbn [length INR] in HL. lra.
  Qed.

  Lemma gridN_In : forall N q, In q (gridN N) ->
    exists i j k, (i < N)%nat /\ (j < N)%nat /\ (k < N)%nat /\ q = gpt N i j k.
  Proof.
    intros N q H. unfold gridN in H.
    apply in_flat_map in H. destruct H as [i [Hi H]].
    apply in_flat_map in H. destruct H as [j [Hj H]].
    apply in_map_iff in H. destruct H as [k [Hq Hk]].
    apply in_seq in Hi. apply in_seq in Hj. apply in_seq in Hk.
    exists i, j, k. repeat split; try lia. symmetry. exact Hq.
  Qed.

  (* =======================================================================
     2. The grid points are unit quaternions
     ======================================================================= *)

  Lemma hopf_unit : forall s x y, 0 <= s <= 1 -> su2_unit (su2_hopf s x y).
  Proof.
    intros s x y [Hs0 Hs1]. unfold su2_unit, qnorm2, su2_hopf. cbn [qr qi qj qk].
    assert (H1 : sqrt (1 - s) * sqrt (1 - s) = 1 - s) by (apply sqrt_sqrt; lra).
    assert (H2 : sqrt s * sqrt s = s) by (apply sqrt_sqrt; lra).
    pose proof (sin2_cos2 (2 * PI * x)) as Hx.
    pose proof (sin2_cos2 (2 * PI * y)) as Hy.
    unfold Rsqr in Hx, Hy.
    transitivity
      ((sqrt (1 - s) * sqrt (1 - s))
       * (sin (2 * PI * x) * sin (2 * PI * x) + cos (2 * PI * x) * cos (2 * PI * x))
       + (sqrt s * sqrt s)
         * (sin (2 * PI * y) * sin (2 * PI * y) + cos (2 * PI * y) * cos (2 * PI * y)));
      [ring |].
    rewrite H1, H2, Hx, Hy. ring.
  Qed.

  Lemma frac_range : forall N i, (i < N)%nat -> 0 <= INR i / INR N <= 1.
  Proof.
    intros N i H.
    assert (HN : 0 < INR N) by (apply lt_0_INR; lia).
    assert (Hi : 0 <= INR i) by apply pos_INR.
    assert (HiN : INR i <= INR N) by (apply le_INR; lia).
    assert (Hinv : 0 < / INR N) by (apply Rinv_0_lt_compat; exact HN).
    unfold Rdiv. split.
    - apply Rmult_le_pos; [exact Hi | left; exact Hinv].
    - apply Rmult_le_reg_r with (INR N); [exact HN |].
      rewrite Rmult_assoc, Rinv_l by lra. lra.
  Qed.

  Lemma gpt_unit : forall N i j k, (i < N)%nat -> su2_unit (gpt N i j k).
  Proof. intros N i j k H. unfold gpt. apply hopf_unit. apply frac_range. exact H. Qed.

  Lemma grid_unit : forall n, Forall su2_unit (su2_grid n).
  Proof.
    intro n. rewrite grid_gridN. apply Forall_forall. intros q Hq.
    destruct (gridN_In _ _ Hq) as [i [j [k [Hi [_ [_ ->]]]]]].
    apply gpt_unit. exact Hi.
  Qed.

  (* =======================================================================
     3. Invariance under the center
     ======================================================================= *)

  Lemma trig_half_shift : forall x x', (x' = x + 1 / 2 \/ x' = x - 1 / 2) ->
    cos (2 * PI * x') = - cos (2 * PI * x) /\ sin (2 * PI * x') = - sin (2 * PI * x).
  Proof.
    intros x x' [-> | ->].
    - replace (2 * PI * (x + 1 / 2)) with (2 * PI * x + PI) by field.
      split; [apply neg_cos | apply neg_sin].
    - replace (2 * PI * (x - 1 / 2)) with (2 * PI * x - PI) by field.
      rewrite cos_minus, sin_minus, cos_PI, sin_PI. split; ring.
  Qed.

  (* shifting both Hopf angles by half a period multiplies by -1 *)
  Lemma hopf_neg : forall s x y x' y',
    (x' = x + 1 / 2 \/ x' = x - 1 / 2) -> (y' = y + 1 / 2 \/ y' = y - 1 / 2) ->
    qneg (su2_hopf s x y) = su2_hopf s x' y'.
  Proof.
    intros s x y x' y' Hx Hy.
    destruct (trig_half_shift x x' Hx) as [Hc1 Hs1].
    destruct (trig_half_shift y y' Hy) as [Hc2 Hs2].
    apply quat_eq; unfold qneg, su2_hopf; cbn [qr qi qj qk];
      rewrite ?Hc1, ?Hs1, ?Hc2, ?Hs2; ring.
  Qed.

  (* the half-period shift of an index of the grid with H + H subdivisions *)
  Definition hshift (H j : nat) : nat :=
    if (j <? H)%nat then (j + H)%nat else (j - H)%nat.

  Lemma hshift_frac : forall H j, (0 < H)%nat ->
    INR (hshift H j) / INR (H + H) = INR j / INR (H + H) + 1 / 2 \/
    INR (hshift H j) / INR (H + H) = INR j / INR (H + H) - 1 / 2.
  Proof.
    intros H j HH. unfold hshift.
    assert (HH' : 0 < INR H) by (apply lt_0_INR; exact HH).
    destruct (Nat.ltb_spec j H) as [Hlt | Hge].
    - left. rewrite !plus_INR. field. lra.
    - right. rewrite (minus_INR j H Hge), !plus_INR. field. lra.
  Qed.

  Lemma map_add_seq : forall H n a,
    map (fun j => (j + H)%nat) (seq a n) = seq (a + H) n.
  Proof.
    intros H n. induction n as [| n IH]; intro a; [reflexivity |].
    cbn [seq map]. f_equal. exact (IH (S a)).
  Qed.

  Lemma map_sub_seq : forall H n a,
    map (fun j => (j - H)%nat) (seq (a + H) n) = seq a n.
  Proof.
    intros H n. induction n as [| n IH]; intro a; [reflexivity |].
    cbn [seq map]. f_equal; [lia |]. exact (IH (S a)).
  Qed.

  (* the half-period shift permutes the index range *)
  Lemma hshift_perm : forall H,
    Permutation (map (hshift H) (seq 0 (H + H))) (seq 0 (H + H)).
  Proof.
    intro H. rewrite seq_app, map_app.
    change (0 + H)%nat with H.
    rewrite (map_ext_in (hshift H) (fun j => (j + H)%nat) (seq 0 H)).
    2: { intros j Hj. apply in_seq in Hj. unfold hshift.
         destruct (Nat.ltb_spec j H); [reflexivity | lia]. }
    rewrite (map_ext_in (hshift H) (fun j => (j - H)%nat) (seq H H)).
    2: { intros j Hj. apply in_seq in Hj. unfold hshift.
         destruct (Nat.ltb_spec j H); [lia | reflexivity]. }
    rewrite (map_add_seq H H 0).
    pose proof (map_sub_seq H H 0) as Hsub.
    change (0 + H)%nat with H in *. rewrite Hsub.
    apply Permutation_app_comm.
  Qed.

  Lemma map_flat_map_comm :
    forall {A B C : Type} (g : B -> C) (f : A -> list B) (l : list A),
      map g (flat_map f l) = flat_map (fun x => map g (f x)) l.
  Proof.
    intros A B C g f l. induction l as [| a l IH]; [reflexivity |].
    cbn [flat_map]. rewrite map_app, IH. reflexivity.
  Qed.

  Lemma flat_map_map_comm :
    forall {A B C : Type} (g : A -> B) (f : B -> list C) (l : list A),
      flat_map f (map g l) = flat_map (fun x => f (g x)) l.
  Proof.
    intros A B C g f l. induction l as [| a l IH]; [reflexivity |].
    cbn [flat_map map]. rewrite IH. reflexivity.
  Qed.

  Lemma Permutation_flat_map_pointwise :
    forall {A B : Type} (f g : A -> list B) (l : list A),
      (forall x, In x l -> Permutation (f x) (g x)) ->
      Permutation (flat_map f l) (flat_map g l).
  Proof.
    intros A B f g l H. induction l as [| a l IH]; [constructor |].
    cbn [flat_map]. apply Permutation_app.
    - apply H. left. reflexivity.
    - apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma gpt_neg : forall H i j k, (0 < H)%nat ->
    qneg (gpt (H + H) i j k) = gpt (H + H) i (hshift H j) (hshift H k).
  Proof.
    intros H i j k HH. unfold gpt. apply hopf_neg; apply hshift_frac; exact HH.
  Qed.

  Lemma gridN_center : forall H, (0 < H)%nat ->
    Permutation (map qneg (gridN (H + H))) (gridN (H + H)).
  Proof.
    intros H HH. unfold gridN. rewrite map_flat_map_comm.
    apply Permutation_flat_map_pointwise. intros i _.
    rewrite map_flat_map_comm.
    transitivity
      (flat_map (fun j => map (fun k => gpt (H + H) i j k) (seq 0 (H + H)))
                (map (hshift H) (seq 0 (H + H)))).
    - rewrite flat_map_map_comm.
      apply Permutation_flat_map_pointwise. intros j _.
      rewrite map_map.
      transitivity
        (map (fun k => gpt (H + H) i (hshift H j) k)
             (map (hshift H) (seq 0 (H + H)))).
      + rewrite map_map.
        rewrite (map_ext (fun k => qneg (gpt (H + H) i j k))
                         (fun k => gpt (H + H) i (hshift H j) (hshift H k))).
        * reflexivity.
        * intro k. apply gpt_neg. exact HH.
      + apply Permutation_map. apply hshift_perm.
    - apply Permutation_flat_map. apply hshift_perm.
  Qed.

  Lemma grid_center : forall n, (1 <= n)%nat ->
    Permutation (map qneg (su2_grid n)) (su2_grid n).
  Proof.
    intros n Hn. rewrite grid_gridN.
    destruct n as [| n]; [lia |].
    replace (2 ^ S n)%nat with (2 ^ n + 2 ^ n)%nat
      by (rewrite Nat.pow_succ_r'; lia).
    apply gridN_center. apply pow2_pos.
  Qed.

  (* =======================================================================
     4. Means over an index range, and their dyadic refinement
     ======================================================================= *)

  Definition mean (N : nat) (f : nat -> R) : R := rsum (seq 0 N) f / INR N.

  Lemma rsum_const_length : forall {A : Type} (l : list A) (c : R),
    rsum l (fun _ => c) = INR (length l) * c.
  Proof.
    intros A l c. induction l as [| a l IH].
    - rewrite rsum_nil. cbn [length INR]. ring.
    - rewrite rsum_cons, IH. cbn [length]. rewrite S_INR. ring.
  Qed.

  Lemma rsum_minus : forall {A : Type} (l : list A) (f g : A -> R),
    rsum l (fun x => f x - g x) = rsum l f - rsum l g.
  Proof.
    intros A l f g. induction l as [| a l IH].
    - rewrite !rsum_nil. ring.
    - rewrite !rsum_cons, IH. ring.
  Qed.

  Lemma mean_ext : forall N f g,
    (forall i, (i < N)%nat -> f i = g i) -> mean N f = mean N g.
  Proof.
    intros N f g H. unfold mean. f_equal. apply rsum_ext.
    intros i Hi. apply in_seq in Hi. apply H. lia.
  Qed.

  Lemma mean_const : forall N c, (0 < N)%nat -> mean N (fun _ => c) = c.
  Proof.
    intros N c HN. unfold mean. rewrite rsum_const_length, seq_length.
    field. apply not_0_INR. lia.
  Qed.

  Lemma mean_bounds : forall N f a b, (0 < N)%nat ->
    (forall i, (i < N)%nat -> a <= f i <= b) -> a <= mean N f <= b.
  Proof.
    intros N f a b HN H. unfold mean.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    pose proof (rsum_const_length (seq 0 N) a) as Ha. rewrite seq_length in Ha.
    pose proof (rsum_const_length (seq 0 N) b) as Hb. rewrite seq_length in Hb.
    assert (Hlo : rsum (seq 0 N) (fun _ => a) <= rsum (seq 0 N) f).
    { apply rsum_le. intros i Hi. apply in_seq in Hi. apply H. lia. }
    assert (Hhi : rsum (seq 0 N) f <= rsum (seq 0 N) (fun _ => b)).
    { apply rsum_le. intros i Hi. apply in_seq in Hi. apply H. lia. }
    rewrite Ha in Hlo. rewrite Hb in Hhi.
    unfold Rdiv. split.
    - apply Rmult_le_reg_r with (INR N); [exact HN' |].
      rewrite Rmult_assoc, Rinv_l by lra. lra.
    - apply Rmult_le_reg_r with (INR N); [exact HN' |].
      rewrite Rmult_assoc, Rinv_l by lra. lra.
  Qed.

  Lemma mean_close : forall N f g eps, (0 < N)%nat ->
    (forall i, (i < N)%nat -> Rabs (f i - g i) <= eps) ->
    Rabs (mean N f - mean N g) <= eps.
  Proof.
    intros N f g eps HN H. unfold mean.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    assert (Hinv : 0 < / INR N) by (apply Rinv_0_lt_compat; exact HN').
    replace (rsum (seq 0 N) f / INR N - rsum (seq 0 N) g / INR N)
      with (rsum (seq 0 N) (fun i => f i - g i) * / INR N)
      by (rewrite rsum_minus; field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq (/ INR N)) by lra.
    assert (Hs : Rabs (rsum (seq 0 N) (fun i => f i - g i)) <= INR N * eps).
    { eapply Rle_trans; [apply rsum_abs |].
      eapply Rle_trans; [apply (rsum_le _ _ (fun _ => eps)) |].
      - intros i Hi. apply in_seq in Hi. apply H. lia.
      - rewrite rsum_const_length, seq_length. lra. }
    apply Rmult_le_reg_r with (INR N); [exact HN' |].
    rewrite Rmult_assoc, Rinv_l by lra. lra.
  Qed.

  Lemma mean_close_const : forall N f c eps, (0 < N)%nat ->
    (forall i, (i < N)%nat -> Rabs (f i - c) <= eps) ->
    Rabs (mean N f - c) <= eps.
  Proof.
    intros N f c eps HN H.
    pose proof (mean_close N f (fun _ => c) eps HN H) as H1.
    rewrite (mean_const N c HN) in H1. exact H1.
  Qed.

  Lemma rsum_seq_shift : forall n a (f : nat -> R),
    rsum (seq a n) f = rsum (seq 0 n) (fun r => f (a + r)%nat).
  Proof.
    induction n as [| n IH]; intros a f; [reflexivity |].
    cbn [seq]. rewrite !rsum_cons.
    rewrite (IH (S a) f), (IH 1%nat (fun r => f (a + r)%nat)).
    f_equal; [f_equal; lia |].
    apply rsum_ext. intros r _. f_equal. lia.
  Qed.

  (* a sum over the index range N * M, cut into N blocks of length M *)
  Lemma rsum_seq_split : forall M N (f : nat -> R),
    rsum (seq 0 (N * M)) f =
    rsum (seq 0 N) (fun i => rsum (seq 0 M) (fun r => f (i * M + r)%nat)).
  Proof.
    intros M N f. induction N as [| N IH]; [reflexivity |].
    replace (S N * M)%nat with (N * M + M)%nat by lia.
    rewrite seq_app, rsum_app, IH, seq_S, rsum_app, rsum_cons, rsum_nil.
    change (0 + N * M)%nat with (N * M)%nat. change (0 + N)%nat with N.
    rewrite (rsum_seq_shift M (N * M)). ring.
  Qed.

  Lemma mean_split : forall N M f, (0 < N)%nat -> (0 < M)%nat ->
    mean (N * M) f = mean N (fun i => mean M (fun r => f (i * M + r)%nat)).
  Proof.
    intros N M f HN HM. unfold mean.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    assert (HM' : 0 < INR M) by (apply lt_0_INR; exact HM).
    rewrite rsum_seq_split, mult_INR. unfold Rdiv.
    rewrite (rsum_scal_r (seq 0 N) (/ INR M)). field. lra.
  Qed.

  (* a mean over the fine index range N * M is close to a mean over the
     coarse range N as soon as every fine term is close to its coarse term *)
  Lemma mean_refine : forall N M f f' eps, (0 < N)%nat -> (0 < M)%nat ->
    (forall i r, (i < N)%nat -> (r < M)%nat ->
       Rabs (f' (i * M + r)%nat - f i) <= eps) ->
    Rabs (mean (N * M) f' - mean N f) <= eps.
  Proof.
    intros N M f f' eps HN HM H. rewrite (mean_split N M f' HN HM).
    apply mean_close; [exact HN |]. intros i Hi.
    apply mean_close_const; [exact HM |]. intros r Hr. apply H; assumption.
  Qed.

  (* =======================================================================
     5. The normalized grid sums as iterated means
     ======================================================================= *)

  Lemma rsum_gridN : forall N (f : Quat -> R),
    rsum (gridN N) f =
    rsum (seq 0 N) (fun i => rsum (seq 0 N) (fun j =>
      rsum (seq 0 N) (fun k => f (gpt N i j k)))).
  Proof.
    intros N f. unfold gridN. rewrite rsum_flat_map.
    apply rsum_ext. intros i _. rewrite rsum_flat_map.
    apply rsum_ext. intros j _. rewrite rsum_map. reflexivity.
  Qed.

  Lemma gridN_mean : forall N (f : Quat -> R), (0 < N)%nat ->
    rsum (gridN N) f / INR (length (gridN N)) =
    mean N (fun i => mean N (fun j => mean N (fun k => f (gpt N i j k)))).
  Proof.
    intros N f HN. assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    rewrite rsum_gridN, gridN_length, !mult_INR. unfold mean, Rdiv.
    rewrite (rsum_ext (seq 0 N)
               (fun i => rsum (seq 0 N) (fun j =>
                  rsum (seq 0 N) (fun k => f (gpt N i j k)) * / INR N) * / INR N)
               (fun i => rsum (seq 0 N) (fun j =>
                  rsum (seq 0 N) (fun k => f (gpt N i j k))) * (/ INR N * / INR N))).
    2: { intros i _. rewrite rsum_scal_r. ring. }
    rewrite rsum_scal_r. field. lra.
  Qed.

  (* the normalized sum over all assignments of grid points to the links of
     E, as an iterated mean *)
  Fixpoint avgR (N : nat) (E : list Link4D) (Phi : SU2Config -> R)
      (U : SU2Config) : R :=
    match E with
    | [] => Phi U
    | l :: E' =>
        mean N (fun i => mean N (fun j => mean N (fun k =>
          avgR N E' Phi (su2_update U l (gpt N i j k)))))
    end.

  Lemma avgR_eq : forall N E Phi U, (0 < N)%nat ->
    su2_sum (gridN N) E Phi U / INR (length (gridN N)) ^ length E =
    avgR N E Phi U.
  Proof.
    intros N E Phi U HN.
    pose proof (gridN_length_pos N HN) as HL.
    revert U. induction E as [| l E IH]; intro U.
    - cbn [su2_sum length pow avgR]. field.
    - cbn [su2_sum length pow avgR].
      change (fold_right Rplus 0
                (map (fun g => su2_sum (gridN N) E Phi (su2_update U l g)) (gridN N)))
        with (rsum (gridN N) (fun g => su2_sum (gridN N) E Phi (su2_update U l g))).
      assert (HD : INR (length (gridN N)) ^ length E <> 0)
        by (apply pow_nonzero; lra).
      transitivity
        (rsum (gridN N)
           (fun g => su2_sum (gridN N) E Phi (su2_update U l g)
                     / INR (length (gridN N)) ^ length E)
         / INR (length (gridN N))).
      + unfold Rdiv. rewrite rsum_scal_r. field. split; solve [exact HD | lra].
      + rewrite gridN_mean by exact HN.
        apply mean_ext; intros i _. apply mean_ext; intros j _.
        apply mean_ext; intros k _. apply IH.
  Qed.

  Lemma avgR_bounds : forall N E Phi a b, (0 < N)%nat ->
    (forall U, su2_unit_config U -> a <= Phi U <= b) ->
    forall U, su2_unit_config U -> a <= avgR N E Phi U <= b.
  Proof.
    intros N E Phi a b HN HPhi. induction E as [| l E IH]; intros U HU.
    - cbn [avgR]. apply HPhi. exact HU.
    - cbn [avgR].
      apply mean_bounds; [exact HN |]. intros i Hi.
      apply mean_bounds; [exact HN |]. intros j Hj.
      apply mean_bounds; [exact HN |]. intros k Hk.
      apply IH. apply unit_config_update; [exact HU |]. apply gpt_unit. exact Hi.
  Qed.

  (* the normalized grid sums lie between any two bounds of the observable *)
  Lemma grid_average_bounds :
    forall (E : list Link4D) (Phi : SU2Config -> R) (a b : R),
      (forall U, su2_unit_config U -> a <= Phi U <= b) ->
      forall n,
        a <= su2_sum (su2_grid n) E Phi (fun _ => qone)
             / INR (length (su2_grid n)) ^ length E <= b.
  Proof.
    intros E Phi a b H n.
    rewrite grid_gridN, (avgR_eq (2 ^ n) E Phi _ (pow2_pos n)).
    apply avgR_bounds; [apply pow2_pos | exact H | apply unit_config_one].
  Qed.

  (* refinement: no error accumulates over the links *)
  Lemma avgR_refine : forall (Phi : SU2Config -> R) (delta eps : R) (N M : nat),
    (0 < N)%nat -> (0 < M)%nat ->
    (forall U U', su2_unit_config U -> su2_unit_config U' ->
       (forall l, su2_close delta (U l) (U' l)) -> Rabs (Phi U' - Phi U) <= eps) ->
    (forall i j k r1 r2 r3,
       (i < N)%nat -> (j < N)%nat -> (k < N)%nat ->
       (r1 < M)%nat -> (r2 < M)%nat -> (r3 < M)%nat ->
       su2_close delta (gpt N i j k)
         (gpt (N * M) (i * M + r1) (j * M + r2) (k * M + r3))) ->
    forall E U U', su2_unit_config U -> su2_unit_config U' ->
      (forall l, su2_close delta (U l) (U' l)) ->
      Rabs (avgR (N * M) E Phi U' - avgR N E Phi U) <= eps.
  Proof.
    intros Phi delta eps N M HN HM HPhi Hgrid.
    induction E as [| l E IH]; intros U U' HU HU' Hclose.
    - cbn [avgR]. apply HPhi; assumption.
    - cbn [avgR].
      apply mean_refine; [exact HN | exact HM |]. intros i r1 Hi Hr1. cbv beta.
      apply mean_refine; [exact HN | exact HM |]. intros j r2 Hj Hr2. cbv beta.
      apply mean_refine; [exact HN | exact HM |]. intros k r3 Hk Hr3. cbv beta.
      apply IH.
      + apply unit_config_update; [exact HU |]. apply gpt_unit. exact Hi.
      + apply unit_config_update; [exact HU' |]. apply gpt_unit. nia.
      + intro l0. unfold su2_update. destruct (link4D_eqb l0 l).
        * apply Hgrid; assumption.
        * apply Hclose.
  Qed.

  (* =======================================================================
     6. The modulus of continuity of the Hopf coordinates
     ======================================================================= *)

  Lemma sqrt_close : forall a b eta, 0 <= a -> 0 <= b -> 0 < eta ->
    Rabs (a - b) < eta * eta -> Rabs (sqrt a - sqrt b) < eta.
  Proof.
    intros a b eta Ha Hb Heta H.
    pose proof (sqrt_pos a) as Hu. pose proof (sqrt_pos b) as Hv.
    pose proof (sqrt_sqrt a Ha) as Hu2. pose proof (sqrt_sqrt b Hb) as Hv2.
    rewrite <- Hu2, <- Hv2 in H.
    apply Rabs_def2 in H. destruct H as [H1 H2].
    apply Rabs_def1; nra.
  Qed.

  Lemma cos_lip : forall u v, Rabs (cos u - cos v) <= Rabs (u - v).
  Proof.
    assert (H : forall a b, a < b -> Rabs (cos b - cos a) <= Rabs (b - a)).
    { intros a b Hab.
      destruct (MVT_cor2 cos (fun x => - sin x) a b Hab) as [c [Hc _]].
      - intros c _. apply derivable_pt_lim_cos.
      - rewrite Hc, Rabs_mult.
        assert (Hs : Rabs (- sin c) <= 1).
        { rewrite Rabs_Ropp. apply Rabs_le. apply SIN_bound. }
        pose proof (Rabs_pos (b - a)). pose proof (Rabs_pos (- sin c)). nra. }
    intros u v. destruct (Rtotal_order u v) as [Hlt | [Heq | Hgt]].
    - rewrite (Rabs_minus_sym (cos u)), (Rabs_minus_sym u). apply H. exact Hlt.
    - subst v. unfold Rminus. rewrite !Rplus_opp_r, Rabs_R0. lra.
    - apply H. exact Hgt.
  Qed.

  Lemma sin_lip : forall u v, Rabs (sin u - sin v) <= Rabs (u - v).
  Proof.
    assert (H : forall a b, a < b -> Rabs (sin b - sin a) <= Rabs (b - a)).
    { intros a b Hab.
      destruct (MVT_cor2 sin cos a b Hab) as [c [Hc _]].
      - intros c _. apply derivable_pt_lim_sin.
      - rewrite Hc, Rabs_mult.
        assert (Hs : Rabs (cos c) <= 1).
        { apply Rabs_le. apply COS_bound. }
        pose proof (Rabs_pos (b - a)). pose proof (Rabs_pos (cos c)). nra. }
    intros u v. destruct (Rtotal_order u v) as [Hlt | [Heq | Hgt]].
    - rewrite (Rabs_minus_sym (sin u)), (Rabs_minus_sym u). apply H. exact Hlt.
    - subst v. unfold Rminus. rewrite !Rplus_opp_r, Rabs_R0. lra.
    - apply H. exact Hgt.
  Qed.

  Lemma angle_close : forall x x' eta, Rabs (x - x') < eta ->
    Rabs (2 * PI * x - 2 * PI * x') <= 8 * eta.
  Proof.
    intros x x' eta H.
    replace (2 * PI * x - 2 * PI * x') with (2 * PI * (x - x')) by ring.
    pose proof PI_4 as H4. pose proof PI_RGT_0 as H0.
    rewrite Rabs_mult, (Rabs_pos_eq (2 * PI)) by lra.
    pose proof (Rabs_pos (x - x')). nra.
  Qed.

  Lemma prod_close : forall a c a' c' e1 e2,
    Rabs a' <= 1 -> Rabs c <= 1 ->
    Rabs (a - a') < e1 -> Rabs (c - c') <= e2 ->
    Rabs (a * c - a' * c') < e1 + e2.
  Proof.
    intros a c a' c' e1 e2 Ha' Hc H1 H2.
    replace (a * c - a' * c') with ((a - a') * c + a' * (c - c')) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
    pose proof (Rabs_pos (a - a')). pose proof (Rabs_pos (c - c')).
    pose proof (Rabs_pos c). pose proof (Rabs_pos a').
    nra.
  Qed.

  Lemma sqrt_abs_le_1 : forall t, 0 <= t <= 1 -> Rabs (sqrt t) <= 1.
  Proof.
    intros t [H0 H1]. rewrite Rabs_pos_eq by apply sqrt_pos.
    rewrite <- sqrt_1. apply sqrt_le_1; lra.
  Qed.

  (* the Hopf coordinates are uniformly continuous on [0,1] x R x R *)
  Lemma hopf_close : forall eta s s' x x' y y',
    0 < eta -> 0 <= s <= 1 -> 0 <= s' <= 1 ->
    Rabs (s - s') < eta * eta -> Rabs (x - x') < eta -> Rabs (y - y') < eta ->
    su2_close (9 * eta) (su2_hopf s x y) (su2_hopf s' x' y').
  Proof.
    intros eta s s' x x' y y' Heta Hs Hs' Hss Hxx Hyy.
    assert (Hq1 : Rabs (sqrt (1 - s) - sqrt (1 - s')) < eta).
    { apply sqrt_close; [lra | lra | exact Heta |].
      replace (1 - s - (1 - s')) with (- (s - s')) by ring.
      rewrite Rabs_Ropp. exact Hss. }
    assert (Hq2 : Rabs (sqrt s - sqrt s') < eta).
    { apply sqrt_close; [lra | lra | exact Heta | exact Hss]. }
    assert (Hb1 : Rabs (sqrt (1 - s')) <= 1) by (apply sqrt_abs_le_1; lra).
    assert (Hb2 : Rabs (sqrt s') <= 1) by (apply sqrt_abs_le_1; lra).
    assert (Hcx : Rabs (cos (2 * PI * x) - cos (2 * PI * x')) <= 8 * eta).
    { eapply Rle_trans; [apply cos_lip | apply angle_close; exact Hxx]. }
    assert (Hsx : Rabs (sin (2 * PI * x) - sin (2 * PI * x')) <= 8 * eta).
    { eapply Rle_trans; [apply sin_lip | apply angle_close; exact Hxx]. }
    assert (Hcy : Rabs (cos (2 * PI * y) - cos (2 * PI * y')) <= 8 * eta).
    { eapply Rle_trans; [apply cos_lip | apply angle_close; exact Hyy]. }
    assert (Hsy : Rabs (sin (2 * PI * y) - sin (2 * PI * y')) <= 8 * eta).
    { eapply Rle_trans; [apply sin_lip | apply angle_close; exact Hyy]. }
    assert (Hc1 : forall t, Rabs (cos t) <= 1)
      by (intro t; apply Rabs_le; apply COS_bound).
    assert (Hs1 : forall t, Rabs (sin t) <= 1)
      by (intro t; apply Rabs_le; apply SIN_bound).
    replace (9 * eta) with (eta + 8 * eta) by ring.
    unfold su2_close, su2_hopf. cbn [qr qi qj qk].
    split; [| split; [| split]].
    - apply prod_close; [exact Hb1 | apply Hc1 | exact Hq1 | exact Hcx].
    - apply prod_close; [exact Hb1 | apply Hs1 | exact Hq1 | exact Hsx].
    - apply prod_close; [exact Hb2 | apply Hc1 | exact Hq2 | exact Hcy].
    - apply prod_close; [exact Hb2 | apply Hs1 | exact Hq2 | exact Hsy].
  Qed.

  (* a point of the cell number i of the coarse subdivision is within the
     mesh 1 / N of the corner of the cell *)
  Lemma frac_close : forall N M i r, (0 < N)%nat -> (0 < M)%nat -> (r < M)%nat ->
    Rabs (INR i / INR N - INR (i * M + r) / INR (N * M)) < / INR N.
  Proof.
    intros N M i r HN HM Hr.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    assert (HM' : 0 < INR M) by (apply lt_0_INR; exact HM).
    assert (Hr0 : 0 <= INR r) by apply pos_INR.
    assert (Hr1 : INR r < INR M) by (apply lt_INR; exact Hr).
    assert (HiN : 0 < / INR N) by (apply Rinv_0_lt_compat; exact HN').
    assert (HiM : 0 < / INR M) by (apply Rinv_0_lt_compat; exact HM').
    assert (Ht0 : 0 <= INR r * / INR M) by (apply Rmult_le_pos; lra).
    assert (Ht1 : INR r * / INR M < 1).
    { apply Rmult_lt_reg_r with (INR M); [exact HM' |].
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    rewrite plus_INR, !mult_INR.
    replace (INR i / INR N - (INR i * INR M + INR r) / (INR N * INR M))
      with (- (INR r * / INR M * / INR N)) by (field; lra).
    rewrite Rabs_Ropp, Rabs_pos_eq by (apply Rmult_le_pos; lra).
    nra.
  Qed.

  Lemma gpt_close : forall eta N M i j k r1 r2 r3,
    0 < eta -> (0 < N)%nat -> (0 < M)%nat ->
    / INR N <= eta * eta -> / INR N <= eta ->
    (i < N)%nat -> (j < N)%nat -> (k < N)%nat ->
    (r1 < M)%nat -> (r2 < M)%nat -> (r3 < M)%nat ->
    su2_close (9 * eta) (gpt N i j k)
      (gpt (N * M) (i * M + r1) (j * M + r2) (k * M + r3)).
  Proof.
    intros eta N M i j k r1 r2 r3 Heta HN HM Hh2 Hh1 Hi Hj Hk Hr1 Hr2 Hr3.
    unfold gpt. apply hopf_close.
    - exact Heta.
    - apply frac_range. exact Hi.
    - apply frac_range. nia.
    - eapply Rlt_le_trans; [apply frac_close; assumption | exact Hh2].
    - eapply Rlt_le_trans; [apply frac_close; assumption | exact Hh1].
    - eapply Rlt_le_trans; [apply frac_close; assumption | exact Hh1].
  Qed.

  Lemma pow2_inv_small : forall h, 0 < h ->
    exists n0, forall n, (n0 <= n)%nat -> / INR (2 ^ n) < h.
  Proof.
    intros h Hh.
    destruct (pow_lt_1_zero (/ 2)) with (y := h) as [n0 Hn0].
    - rewrite Rabs_pos_eq; lra.
    - exact Hh.
    - exists n0. intros n Hn.
      assert (Hn' : (n >= n0)%nat) by lia.
      specialize (Hn0 n Hn').
      rewrite pow_INR. replace (INR 2) with 2 by (cbn [INR]; lra).
      rewrite <- pow_inv.
      eapply Rle_lt_trans; [apply Rle_abs | exact Hn0].
  Qed.

  (* every point of the grid with 2^(n+m) subdivisions is delta-close to the
     corner of its cell of the grid with 2^n subdivisions, for all n >= n0 *)
  Lemma hopf_modulus : forall delta, 0 < delta ->
    exists n0, forall n m i j k r1 r2 r3, (n0 <= n)%nat ->
      (i < 2 ^ n)%nat -> (j < 2 ^ n)%nat -> (k < 2 ^ n)%nat ->
      (r1 < 2 ^ m)%nat -> (r2 < 2 ^ m)%nat -> (r3 < 2 ^ m)%nat ->
      su2_close delta (gpt (2 ^ n) i j k)
        (gpt (2 ^ n * 2 ^ m) (i * 2 ^ m + r1) (j * 2 ^ m + r2) (k * 2 ^ m + r3)).
  Proof.
    intros delta Hdelta.
    assert (Heta : 0 < delta / 9) by lra.
    assert (Hh : 0 < Rmin (delta / 9 * (delta / 9)) (delta / 9)).
    { apply Rmin_glb_lt; [apply Rmult_lt_0_compat; exact Heta | exact Heta]. }
    destruct (pow2_inv_small _ Hh) as [n0 Hn0].
    exists n0. intros n m i j k r1 r2 r3 Hn Hi Hj Hk Hr1 Hr2 Hr3.
    specialize (Hn0 n Hn).
    replace delta with (9 * (delta / 9)) at 1 by field.
    apply gpt_close; try assumption.
    - apply pow2_pos.
    - apply pow2_pos.
    - left. eapply Rlt_le_trans; [exact Hn0 | apply Rmin_l].
    - left. eapply Rlt_le_trans; [exact Hn0 | apply Rmin_r].
  Qed.

  (* =======================================================================
     7. Convergence of the normalized grid sums
     ======================================================================= *)

  Lemma su2_close_same : forall delta q, 0 < delta -> su2_close delta q q.
  Proof.
    intros delta q Hd.
    assert (H : forall x, Rabs (x - x) < delta).
    { intro x. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. exact Hd. }
    unfold su2_close. repeat split; apply H.
  Qed.

  Theorem grid_average_converges :
    forall (E : list Link4D) (Phi : SU2Config -> R),
      su2_bounded_continuous Phi ->
      exists v : R,
        Un_cv (fun n => su2_sum (su2_grid n) E Phi (fun _ => qone)
                        / INR (length (su2_grid n)) ^ length E) v.
  Proof.
    intros E Phi [_ Hcont].
    set (u := fun n => su2_sum (su2_grid n) E Phi (fun _ => qone)
                       / INR (length (su2_grid n)) ^ length E).
    assert (Hu : forall n, u n = avgR (2 ^ n) E Phi (fun _ => qone)).
    { intro n. unfold u. rewrite grid_gridN. apply avgR_eq. apply pow2_pos. }
    (* the sequence is Cauchy: from n0 on it moves by at most eps *)
    assert (Hstep : forall eps, 0 < eps ->
              exists n0, forall m, Rabs (u (n0 + m)%nat - u n0) <= eps).
    { intros eps Heps. destruct (Hcont eps Heps) as [delta [Hdelta Hd]].
      destruct (hopf_modulus delta Hdelta) as [n0 Hn0].
      exists n0. intro m. rewrite !Hu, Nat.pow_add_r.
      apply (avgR_refine Phi delta eps).
      - apply pow2_pos.
      - apply pow2_pos.
      - intros U U' HU HU' Hc. left. rewrite Rabs_minus_sym. apply Hd; assumption.
      - intros i j k r1 r2 r3 Hi Hj Hk Hr1 Hr2 Hr3.
        apply Hn0; [apply le_n | assumption ..].
      - apply unit_config_one.
      - apply unit_config_one.
      - intro l. apply su2_close_same. exact Hdelta. }
    assert (HC : Cauchy_crit u).
    { intros eps Heps. destruct (Hstep (eps / 3)) as [n0 Hn0]; [lra |].
      assert (Hfar : forall n, (n >= n0)%nat -> Rabs (u n - u n0) <= eps / 3).
      { intros n Hn. pose proof (Hn0 (n - n0)%nat) as H1.
        replace (n0 + (n - n0))%nat with n in H1 by lia. exact H1. }
      exists n0. intros n m Hn Hm. unfold Rdist.
      replace (u n - u m) with ((u n - u n0) + - (u m - u n0)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
      pose proof (Hfar n Hn). pose proof (Hfar m Hm). lra. }
    destruct (R_complete u HC) as [v Hv]. exists v. exact Hv.
  Qed.

End SU2HaarGrid.
