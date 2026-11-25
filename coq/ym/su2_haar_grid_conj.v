(* =========================================================================
   ym/su2_haar_grid_conj.v

   Inversion invariance of the dyadic Hopf grids `su2_grid n` of
   `verification/ChallengeSU2Gauge.v`:

     - `grid_conj`: for n >= 1 the grid is invariant, as a multiset, under
       the inversion q |-> q^{-1} = qconj q of SU(2).

   In the Hopf coordinates the conjugation negates the first angle and
   shifts the second angle by half a period:
       qconj (su2_hopf s x y) = su2_hopf s (- x) (y + 1/2).
   On the grid with N = H + H subdivisions the first index j is sent to
   `rho N j` (0 for j = 0, N - j otherwise: the angle 1 - j/N, equal to
   - j/N modulo a full period) and the second index k to the half-period
   shift `hshift H k` of ym/su2_haar_grid.v.  Both index maps permute the
   index range, and the two permutations are lifted through the
   flat_map / flat_map / map structure of the grid exactly as in the proof
   of `SU2HaarGrid.grid_center`.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + ym.z2_gauge_expansion + ym.su2_algebra
   + ym.su2_haar_grid.
   No axioms, no parameters, no unfinished proofs are declared here.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.su2_algebra.
Require Import ym.su2_haar_grid.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import SU2Algebra.
Open Scope R_scope.

Module SU2HaarGridConj.

  Import SU2HaarGrid.

  (* =======================================================================
     1. Conjugation in the Hopf coordinates
     ======================================================================= *)

  (* negating an angle, possibly up to a full period *)
  Lemma trig_reflect : forall x x', (x' = - x \/ x' = 1 - x) ->
    cos (2 * PI * x') = cos (2 * PI * x) /\ sin (2 * PI * x') = - sin (2 * PI * x).
  Proof.
    intros x x' [-> | ->].
    - replace (2 * PI * - x) with (- (2 * PI * x)) by ring.
      split; [apply cos_neg | apply sin_neg].
    - replace (2 * PI * (1 - x)) with (2 * PI - 2 * PI * x) by ring.
      rewrite cos_minus, sin_minus, cos_2PI, sin_2PI. split; ring.
  Qed.

  (* negating the first Hopf angle and shifting the second one by half a
     period is the conjugation *)
  Lemma hopf_conj : forall s x y x' y',
    (x' = - x \/ x' = 1 - x) -> (y' = y + 1 / 2 \/ y' = y - 1 / 2) ->
    qconj (su2_hopf s x y) = su2_hopf s x' y'.
  Proof.
    intros s x y x' y' Hx Hy.
    destruct (trig_reflect x x' Hx) as [Hc1 Hs1].
    destruct (trig_half_shift y y' Hy) as [Hc2 Hs2].
    apply quat_eq; unfold qconj, su2_hopf; cbn [qr qi qj qk];
      rewrite ?Hc1, ?Hs1, ?Hc2, ?Hs2; ring.
  Qed.

  (* =======================================================================
     2. The reflection of an index of the grid with N subdivisions
     ======================================================================= *)

  Definition rho (N j : nat) : nat :=
    if (j =? 0)%nat then 0%nat else (N - j)%nat.

  Lemma rho_lt : forall N j, (j < N)%nat -> (rho N j < N)%nat.
  Proof.
    intros N j Hj. unfold rho. destruct (Nat.eqb_spec j 0); lia.
  Qed.

  Lemma rho_invol : forall N j, (j < N)%nat -> rho N (rho N j) = j.
  Proof.
    intros N j Hj. unfold rho.
    destruct (Nat.eqb_spec j 0) as [-> | Hne]; [reflexivity |].
    destruct (Nat.eqb_spec (N - j) 0); lia.
  Qed.

  Lemma rho_frac : forall N j, (j < N)%nat ->
    INR (rho N j) / INR N = - (INR j / INR N) \/
    INR (rho N j) / INR N = 1 - INR j / INR N.
  Proof.
    intros N j Hj. unfold rho.
    assert (HN : 0 < INR N) by (apply lt_0_INR; lia).
    destruct (Nat.eqb_spec j 0) as [-> | Hne].
    - left. cbn [INR]. field. lra.
    - right. rewrite minus_INR by lia. field. lra.
  Qed.

  (* the reflection permutes the index range *)
  Lemma rho_perm : forall N,
    Permutation (map (rho N) (seq 0 N)) (seq 0 N).
  Proof.
    intro N. symmetry. apply NoDup_Permutation_bis.
    - apply seq_NoDup.
    - rewrite map_length. apply le_n.
    - intros j Hj. apply in_seq in Hj.
      rewrite <- (rho_invol N j) by lia.
      apply in_map. apply in_seq.
      pose proof (rho_lt N j). lia.
  Qed.

  (* =======================================================================
     3. Invariance of the grid under the inversion
     ======================================================================= *)

  Lemma gpt_conj : forall H i j k, (0 < H)%nat -> (j < H + H)%nat ->
    qconj (gpt (H + H) i j k) = gpt (H + H) i (rho (H + H) j) (hshift H k).
  Proof.
    intros H i j k HH Hj. unfold gpt. apply hopf_conj.
    - apply rho_frac. exact Hj.
    - apply hshift_frac. exact HH.
  Qed.

  Lemma gridN_conj : forall H, (0 < H)%nat ->
    Permutation (map qconj (gridN (H + H))) (gridN (H + H)).
  Proof.
    intros H HH. unfold gridN. rewrite map_flat_map_comm.
    apply Permutation_flat_map_pointwise. intros i _.
    rewrite map_flat_map_comm.
    transitivity
      (flat_map (fun j => map (fun k => gpt (H + H) i j k) (seq 0 (H + H)))
                (map (rho (H + H)) (seq 0 (H + H)))).
    - rewrite flat_map_map_comm.
      apply Permutation_flat_map_pointwise. intros j Hj.
      apply in_seq in Hj.
      rewrite map_map.
      transitivity
        (map (fun k => gpt (H + H) i (rho (H + H) j) k)
             (map (hshift H) (seq 0 (H + H)))).
      + rewrite map_map.
        rewrite (map_ext (fun k => qconj (gpt (H + H) i j k))
                         (fun k => gpt (H + H) i (rho (H + H) j) (hshift H k))).
        * reflexivity.
        * intro k. apply gpt_conj; [exact HH | lia].
      + apply Permutation_map. apply hshift_perm.
    - apply Permutation_flat_map. apply rho_perm.
  Qed.

  (* for n >= 1 the Hopf grid is invariant, as a multiset, under inversion
     q |-> q^{-1} = qconj q *)
  Lemma grid_conj : forall n, (1 <= n)%nat ->
    Permutation (map qconj (su2_grid n)) (su2_grid n).
  Proof.
    intros n Hn. rewrite grid_gridN.
    destruct n as [| n]; [lia |].
    replace (2 ^ S n)%nat with (2 ^ n + 2 ^ n)%nat
      by (rewrite Nat.pow_succ_r'; lia).
    apply gridN_conj. apply pow2_pos.
  Qed.

End SU2HaarGridConj.
