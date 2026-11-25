(* =========================================================================
   verification/ChallengeSU2GaugeInvariance.v

   FROZEN CHALLENGE FILE FOR TARGET 11 (bi-invariance of the Haar measure of
   SU(2) realized by the Hopf grids, and gauge invariance of the Gibbs
   states of the 4D SU(2) Wilson lattice gauge theory).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`
   and `verification/ChallengeSU2InfiniteVolume.v`.  None of the earlier
   frozen files is modified by Target 11.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   Targets 8 to 10 realize the Haar measure of SU(2) = S^3 as the limit of
   the uniform distributions on the dyadic grids of the Hopf coordinates
   (`ChallengeSU2Gauge.su2_grid`), and use of that limit only its symmetry
   under the center and under inversion.  Target 11 proves that the limit
   is the Haar measure:

     11a  the grid averages of every bounded uniformly continuous function
          on SU(2) converge, and the limit is invariant under left and
          right translations and under inversion;
     11b  the Haar-measure Gibbs expectation in a finite volume is
          invariant under gauge transformations of the observable;
     11c  so is the infinite-volume Gibbs expectation.

   Scope disclaimer:
     11a is a statement about the compact group SU(2) and involves no
     lattice.  11b and 11c are statements about the LATTICE gauge theory;
     11c inherits the strong-coupling regime only through the existence of
     the infinite-volume expectation (Target 9b), which it takes as a
     hypothesis.  Nothing here formalizes a continuum limit, weak coupling,
     or the Clay Millennium Prize Problem.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import List.

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2GaugeInvariance.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.

  (* =======================================================================
     1. The Haar integral of a function on SU(2)
     ======================================================================= *)

  (* Bounded uniformly continuous functions on SU(2) (the unit quaternions),
     for the componentwise distance `su2_close`. *)
  Definition su2_fn_bounded_continuous (h : Quat -> R) : Prop :=
    (exists M : R, forall u, su2_unit u -> Rabs (h u) <= M) /\
    (forall eps : R, 0 < eps ->
       exists delta : R, 0 < delta /\
         forall u v, su2_unit u -> su2_unit v ->
           su2_close delta u v -> Rabs (h u - h v) < eps).

  (* The average of h over the n-th dyadic Hopf grid (8^n points): a
     Riemann sum of the Haar integral of h. *)
  Definition su2_grid_mean (n : nat) (h : Quat -> R) : R :=
    fold_right Rplus 0 (map h (su2_grid n)) / INR (length (su2_grid n)).

  (* v is the Haar integral of h: the limit of the grid averages. *)
  Definition su2_haar_integral_is (h : Quat -> R) (v : R) : Prop :=
    Un_cv (fun n => su2_grid_mean n h) v.

  (* =======================================================================
     2. TARGET 11a: bi-invariance of the Haar integral
     ======================================================================= *)

  (* TARGET 11a (Existence, Bi-Invariance and Inversion Invariance of the
     Haar Integral of SU(2)):
     For every bounded uniformly continuous function h on SU(2) the grid
     averages converge to a number v, and for all a, b in SU(2) the grid
     averages of the translated function u |-> h(a u b) converge to the
     same number v, as do those of u |-> h(u^{-1}). *)
  Definition Challenge_SU2_HaarBiInvariance : Prop :=
    forall h : Quat -> R,
      su2_fn_bounded_continuous h ->
      exists v : R,
        su2_haar_integral_is h v /\
        (forall a b : Quat, su2_unit a -> su2_unit b ->
           su2_haar_integral_is (fun u => h (qmul a (qmul u b))) v) /\
        su2_haar_integral_is (fun u => h (qconj u)) v.

  (* =======================================================================
     3. Gauge transformations
     ======================================================================= *)

  (* The gauge transformation of the gauge field U by the SU(2)-valued
     function g on the sites:  U(x, mu)  |->  g(x) U(x, mu) g(x + mu)^{-1}. *)
  Definition su2_gauge (g : Site4D -> Quat) (U : SU2Config) : SU2Config :=
    fun l => qmul (g (fst l)) (qmul (U l) (qconj (g (shift4D (fst l) (snd l))))).

  (* =======================================================================
     4. TARGET 11b: gauge invariance of the finite-volume Gibbs state
     ======================================================================= *)

  (* TARGET 11b (Gauge Invariance of the Haar-Measure Gibbs State):
     For every coupling beta, every finite volume Lambda, every bounded
     uniformly continuous observable F that depends only on the link
     variables of the plaquettes of a list P of plaquettes of Lambda, and
     every SU(2)-valued gauge transformation g: if v is the Haar-measure
     Gibbs expectation of F in Lambda, then v is also the Haar-measure
     Gibbs expectation of the gauge-transformed observable
     U |-> F(g . U). *)
  Definition Challenge_SU2Gauge4D_HaarGaugeInvariance : Prop :=
    forall (beta : R) (Lambda P : list Plaq4D) (F : SU2Config -> R)
           (g : Site4D -> Quat) (v : R),
      incl P Lambda ->
      su2_local_on F P ->
      su2_bounded_continuous F ->
      (forall x, su2_unit (g x)) ->
      su2_haar_expect_is beta Lambda F v ->
      su2_haar_expect_is beta Lambda (fun U => F (su2_gauge g U)) v.

  (* =======================================================================
     5. TARGET 11c: gauge invariance of the infinite-volume Gibbs state
     ======================================================================= *)

  (* TARGET 11c (Gauge Invariance of the Infinite-Volume Gibbs State):
     For every coupling beta, every bounded uniformly continuous observable
     F localized on a finite list of canonical plaquettes and every
     SU(2)-valued gauge transformation g: if v is the infinite-volume Gibbs
     expectation of F (Target 9b), then v is also the infinite-volume Gibbs
     expectation of U |-> F(g . U). *)
  Definition Challenge_SU2Gauge4D_InfiniteVolumeGaugeInvariance : Prop :=
    forall (beta : R) (P : list Plaq4D) (F : SU2Config -> R)
           (g : Site4D -> Quat) (v : R),
      Forall wf_plaq_4D P ->
      su2_local_on F P ->
      su2_bounded_continuous F ->
      (forall x, su2_unit (g x)) ->
      su2_infinite_volume_expect_is beta F v ->
      su2_infinite_volume_expect_is beta (fun U => F (su2_gauge g U)) v.

End ChallengeSU2GaugeInvariance.
