(* =========================================================================
   verification/ChallengeSU2InfiniteVolume.v

   FROZEN CHALLENGE FILE FOR TARGET 9 (infinite-volume limit of the 4D SU(2)
   Wilson lattice gauge theory at strong coupling).

   Imports ONLY the Coq 8.18.0 Standard Library and the four frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v` and `verification/ChallengeSU2Gauge.v`,
   from which it reuses the lattice objects and the SU(2) gauge-theory
   objects (`Quat`, `su2_unit`, `SU2Config`, `su2_expect_on`,
   `su2_haar_expect_is`, `su2_bounded_continuous`, `su2_local_at`,
   `su2_wilson_loop`).  None of those four files is modified by Target 9.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   What is formalized here:
     - the increasing sequence of volumes Lambda_n = `su2_box n`: all
       canonical plaquettes of Z^4 anchored at a site of the cube [-n, n]^4
       (every canonical plaquette of Z^4 belongs to Lambda_n for n large);
     - the infinite-volume Gibbs expectation of an observable with respect
       to the Haar measure: the limit, as n -> infinity, of the Haar-measure
       Gibbs expectations in the volumes Lambda_n (themselves limits of
       finite Riemann sums, see `ChallengeSU2Gauge.su2_haar_expect_is`).

   Targets:
     9a  at strong coupling, enlarging the finite volume by a set Q of
         plaquettes changes the expectation of an observable localized on a
         set P of plaquettes by at most a sum of terms that decay
         exponentially in the distance between P and Q, uniformly in the
         finite a-priori link distribution;
     9b  the infinite-volume Haar-measure Gibbs expectation of every bounded
         uniformly continuous observable localized on finitely many
         plaquettes exists (thermodynamic limit);
     9c  exponential clustering of the infinite-volume Gibbs state;
     9d  the Wilson-loop area law for the infinite-volume Gibbs state.

   Scope disclaimer:
     These are statements about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling (small beta) only.  The thermodynamic
     limit is taken along the cubes [-n, n]^4 with free boundary conditions
     and for observables localized on finitely many plaquettes; 9c bounds
     truncated correlations of plaquette-local observables and 9d is an
     UPPER bound for rectangular Wilson loops.  They do NOT formalize a
     continuum limit, weak coupling, independence of the limit from the
     boundary conditions or from the exhausting sequence, translation
     invariance, reflection positivity, Osterwalder-Schrader reconstruction,
     a transfer-matrix spectral gap, a string tension as a limit, or the
     Clay Millennium Prize Problem.  As in Target 8, that the Hopf-coordinate
     measure is the Haar measure of SU(2) is the classical volume formula of
     S^3 and its bi-invariance is not proved here.
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

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2InfiniteVolume.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.

  (* =======================================================================
     1. The exhausting sequence of volumes
     ======================================================================= *)

  (* The integers -n, ..., n. *)
  Definition z_range (n : nat) : list Z :=
    map (fun k => (Z.of_nat k - Z.of_nat n)%Z) (seq 0 (2 * n + 1)%nat).

  (* The sites of the cube [-n, n]^4. *)
  Definition cube_sites (n : nat) : list Site4D :=
    flat_map (fun t =>
      flat_map (fun x =>
        flat_map (fun y =>
          map (fun z => mkSite4D t x y z) (z_range n))
          (z_range n))
        (z_range n))
      (z_range n).

  (* The volume Lambda_n: all canonical plaquettes (the 6 planes mu < nu)
     anchored at a site of the cube [-n, n]^4. *)
  Definition su2_box (n : nat) : list Plaq4D :=
    flat_map (fun s => map (fun pl => mkPlaq4D s (fst pl) (snd pl)) canonical_planes_4D)
             (cube_sites n).

  (* =======================================================================
     2. Local observables and the infinite-volume Gibbs expectation
     ======================================================================= *)

  (* F depends only on the link variables of the plaquettes of the list P. *)
  Definition su2_local_on (F : SU2Config -> R) (P : list Plaq4D) : Prop :=
    forall U U',
      (forall p l, In p P -> In l (plaq4D_links p) -> U l = U' l) -> F U = F U'.

  (* v is the infinite-volume Gibbs expectation of F with respect to the
     Haar measure: the limit along the volumes Lambda_n of the Haar-measure
     Gibbs expectations vn n of F in Lambda_n. *)
  Definition su2_infinite_volume_expect_is (beta : R) (F : SU2Config -> R) (v : R) : Prop :=
    exists vn : nat -> R,
      (forall n, su2_haar_expect_is beta (su2_box n) F (vn n)) /\ Un_cv vn v.

  (* =======================================================================
     3. TARGET 9a: exponentially small dependence on the volume
     ======================================================================= *)

  (* TARGET 9a (Volume Dependence at Strong Coupling — ZERO analytic or
     combinatorial hypotheses):
     For every non-empty finite list G of elements of SU(2) (the a-priori
     link distribution), every mu >= 0, every coupling beta (of either sign)
     with 168 * |beta| <= exp(- mu), every finite duplicate-free volume
     Q ++ Lambda of canonical plaquettes of Z^4, every list P of plaquettes
     of Lambda and every observable f with |f| <= 1 that depends only on
     the link variables of the plaquettes of P:

       |<f>_{Q ++ Lambda} - <f>_Lambda|
         <= 2 exp(2 |beta|) * sum_{q in Q} sum_{p in P} exp(- mu (dist(p, q) - 1)).

     Adding the plaquettes of Q to the volume changes the expectation of f
     by an amount that is exponentially small in the distance between P and
     Q, uniformly in Lambda, Q and G. *)
  Definition Challenge_SU2Gauge4D_VolumeDependence : Prop :=
    forall (G : list Quat) (beta mu : R) (Lambda Q P : list Plaq4D)
           (f : SU2Config -> R),
      G <> [] ->
      Forall su2_unit G ->
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      NoDup (Q ++ Lambda) ->
      Forall wf_plaq_4D (Q ++ Lambda) ->
      incl P Lambda ->
      su2_local_on f P ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      Rabs (su2_expect_on G beta (Q ++ Lambda) f - su2_expect_on G beta Lambda f)
      <= 2 * exp (2 * Rabs beta) *
         fold_right Rplus 0
           (map (fun q =>
                   fold_right Rplus 0
                     (map (fun p => exp (- mu * (plaq4D_dist p q - 1))) P))
                Q).

  (* =======================================================================
     4. TARGET 9b: the thermodynamic limit exists
     ======================================================================= *)

  (* TARGET 9b (Existence of the Infinite-Volume Gibbs State at Strong
     Coupling):
     For every coupling beta (of either sign) with 43008 * |beta| <= 1,
     every finite list P of canonical plaquettes of Z^4 and every bounded
     uniformly continuous observable f that depends only on the link
     variables of the plaquettes of P, the Haar-measure Gibbs expectations
     of f in the volumes Lambda_n converge as n -> infinity: the
     infinite-volume Gibbs expectation of f exists. *)
  Definition Challenge_SU2Gauge4D_ThermodynamicLimit : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v : R, su2_infinite_volume_expect_is beta f v.

  (* =======================================================================
     5. TARGET 9c: exponential clustering of the infinite-volume state
     ======================================================================= *)

  (* TARGET 9c (Exponential Clustering in Infinite Volume):
     For every mu >= 0, every coupling beta with 168 * |beta| <= exp(- mu)
     and 43008 * |beta| <= 1, all canonical plaquettes p1, p2 and all
     bounded uniformly continuous observables f, g with |f|, |g| <= 1
     depending only on the link variables of p1 and of p2 respectively, the
     infinite-volume Gibbs expectations <f g>, <f>, <g> exist and
       |<f g> - <f> <g>| <= 4 * exp(- mu * (dist(p1, p2) - 1)). *)
  Definition Challenge_SU2Gauge4D_InfiniteVolumeClustering : Prop :=
    forall (beta mu : R) (p1 p2 : Plaq4D) (f g : SU2Config -> R),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      43008 * Rabs beta <= 1 ->
      wf_plaq_4D p1 ->
      wf_plaq_4D p2 ->
      su2_local_at f p1 ->
      su2_local_at g p2 ->
      su2_bounded_continuous f ->
      su2_bounded_continuous g ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      exists vfg vf vg : R,
        su2_infinite_volume_expect_is beta (fun U => f U * g U) vfg /\
        su2_infinite_volume_expect_is beta f vf /\
        su2_infinite_volume_expect_is beta g vg /\
        Rabs (vfg - vf * vg) <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).

  (* =======================================================================
     6. TARGET 9d: Wilson-loop area law of the infinite-volume state
     ======================================================================= *)

  (* TARGET 9d (Area Law in Infinite Volume):
     For every coupling beta with 43008 * |beta| <= 1, every corner s, every
     pair of distinct directions mu, nu and all side lengths a, b, the
     infinite-volume Gibbs expectation w of the Wilson loop around the
     a x b rectangle exists and
       |w| <= (63 * (exp(2 |beta|) - 1))^(a * b) * exp(2 * (a + b)).
     (In infinite volume every loop lies inside the dynamical volume, so the
     hypothesis of Targets 7e/8b/8e on the loop links disappears.) *)
  Definition Challenge_SU2Gauge4D_InfiniteVolumeAreaLaw : Prop :=
    forall (beta : R) (s : Site4D) (mu nu : Dir4D) (a b : nat),
      43008 * Rabs beta <= 1 ->
      mu <> nu ->
      exists w : R,
        su2_infinite_volume_expect_is beta
          (fun U => su2_wilson_loop U s mu nu a b) w /\
        Rabs w
        <= (63 * (exp (2 * Rabs beta) - 1)) ^ (a * b) * exp (2 * INR (a + b)).

End ChallengeSU2InfiniteVolume.
