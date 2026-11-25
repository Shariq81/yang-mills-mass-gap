(* =========================================================================
   verification/ChallengeSU2TransferPositivity.v

   FROZEN CHALLENGE FILE FOR TARGET 12 (positivity of the transfer operator
   of the 4D SU(2) Wilson lattice gauge theory: reflection positivity with
   respect to a hyperplane through the midpoints of the time-like links).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`,
   `verification/ChallengeSU2InfiniteVolume.v` and
   `verification/ChallengeSU2MassGap.v`.  None of the earlier frozen files
   is modified by Target 12.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   Notation of Target 10: (F, G) = <(Theta F) G> is the Osterwalder-Schrader
   form of the infinite-volume Gibbs state on observables localized at
   non-negative times, Theta the reflection t -> -t, and T the translation
   by one unit of time.  Target 10 proved (F, F) >= 0 (reflection in the
   hyperplane t = 0 through lattice sites) and the gap estimate
   |(psi, T^k psi)| <= exp(- m k) (psi, psi) on the orthogonal complement of
   the vacuum.  Target 12 adds, for beta >= 0:

     12a  (F, T F) >= 0 for every observable F localized at non-negative
          times: the transfer operator is positive.  Equivalently, the
          state is reflection positive with respect to the hyperplane
          t = 1/2, which cuts the time-like links between t = 0 and t = 1;
     12b  hence, for psi = F - <F>:   0 <= (psi, T psi) <= exp(- m) (psi, psi);
     12c  the form and the transfer operator are symmetric:
          (F, G) = (G, F)  and  (F, T G) = (T F, G);
     12d  T is a contraction:  |(F, T^k F)| <= (F, F)  for every k.
   (12c and 12d hold for both signs of beta.)

   Scope disclaimer:
     These are statements about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling and for beta >= 0 only, on the
     pre-Hilbert space of local observables at non-negative times; the
     Hilbert-space completion, the self-adjoint operator T on it and the
     Hamiltonian - ln T are NOT constructed here.  Nothing here formalizes a
     continuum limit, weak coupling, or the Clay Millennium Prize Problem.
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
Require Import verification.ChallengeSU2MassGap.

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2TransferPositivity.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.
  Import ChallengeSU2MassGap.

  (* =======================================================================
     1. TARGET 12a: positivity of the transfer operator
     ======================================================================= *)

  (* TARGET 12a (Positivity of the Transfer Operator / Link-Reflection
     Positivity):
     For every coupling beta with 0 <= beta and 43008 * beta <= 1 and every
     bounded uniformly continuous observable f localized on a finite list of
     canonical plaquettes at non-negative times, the infinite-volume Gibbs
     expectation of (Theta f) * (tau f), tau = translation by one unit of
     time, exists and is non-negative:

       (f, T f) = <(Theta f) (tau f)> >= 0. *)
  Definition Challenge_SU2Gauge4D_TransferMatrixPositivity : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R),
      0 <= beta ->
      43008 * beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v1 : R,
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U) v1 /\
        0 <= v1.

  (* =======================================================================
     2. TARGET 12b: two-sided bound for the transfer operator on the
        orthogonal complement of the vacuum
     ======================================================================= *)

  (* TARGET 12b (Spectral Bounds for the Transfer Operator):
     For every mu >= 0, every coupling beta with 0 <= beta,
     168 * beta <= exp(- mu) and 43008 * beta <= 1, and every bounded
     uniformly continuous observable f localized on a finite list of
     canonical plaquettes at non-negative times: the infinite-volume Gibbs
     expectations
       v0 = <(Theta f) f>,   v1 = <(Theta f) (tau f)>,   vf = <f>
     exist and

       0 <= v1 - vf^2 <= exp(- mu / 2) * (v0 - vf^2).

     With psi = f - <f>:   0 <= (psi, T psi) <= exp(- m) (psi, psi),
     m = mu / 2. *)
  Definition Challenge_SU2Gauge4D_TransferMatrixSpectralBounds : Prop :=
    forall (beta mu : R) (P : list Plaq4D) (f : SU2Config -> R),
      0 <= mu ->
      0 <= beta ->
      168 * beta <= exp (- mu) ->
      43008 * beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v0 v1 vf : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * f U) v0 /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U) v1 /\
        su2_infinite_volume_expect_is beta f vf /\
        0 <= v1 - vf * vf /\
        v1 - vf * vf <= exp (- (mu / 2)) * (v0 - vf * vf).

  (* =======================================================================
     3. TARGET 12c: symmetry of the form and of the transfer operator
     ======================================================================= *)

  (* TARGET 12c (Symmetry):
     For every coupling beta with 43008 * |beta| <= 1 and all bounded
     uniformly continuous observables f, g localized on finite lists of
     canonical plaquettes at non-negative times:

       (f, g) = (g, f)     and     (f, T g) = (T f, g),

     i.e. the expectations of (Theta f) g and (Theta g) f exist and are
     equal, and so are those of (Theta f) (tau g) and (Theta (tau f)) g. *)
  Definition Challenge_SU2Gauge4D_TransferMatrixSymmetry : Prop :=
    forall (beta : R) (P Q : list Plaq4D) (f g : SU2Config -> R),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      Forall wf_plaq_4D Q ->
      Forall pos_time_plaq Q ->
      su2_local_on f P ->
      su2_local_on g Q ->
      su2_bounded_continuous f ->
      su2_bounded_continuous g ->
      exists v v' : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * g U) v /\
        su2_infinite_volume_expect_is beta (fun U => obs_reflect g U * f U) v /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t 1 g U) v' /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect (obs_translate_n D4_t 1 f) U * g U) v'.

  (* =======================================================================
     4. TARGET 12d: the transfer operator is a contraction
     ======================================================================= *)

  (* TARGET 12d (Contraction):
     For every coupling beta with 43008 * |beta| <= 1, every bounded
     uniformly continuous observable f localized on a finite list of
     canonical plaquettes at non-negative times, and every k:

       |(f, T^k f)| <= (f, f).

     With k = 2 and 12c:  (T f, T f) = (f, T^2 f) <= (f, f). *)
  Definition Challenge_SU2Gauge4D_TransferMatrixContraction : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R) (k : nat),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v0 vk : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * f U) v0 /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t k f U) vk /\
        Rabs vk <= v0.

End ChallengeSU2TransferPositivity.
