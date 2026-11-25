(* =========================================================================
   verification/ChallengeSU2MassGap.v

   FROZEN CHALLENGE FILE FOR TARGET 10 (uniqueness and symmetries of the
   infinite-volume state, reflection positivity, and the transfer-matrix
   mass gap of the 4D SU(2) Wilson lattice gauge theory at strong coupling).

   Imports ONLY the Coq 8.18.0 Standard Library and the five frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`
   and `verification/ChallengeSU2InfiniteVolume.v`.  None of those five
   files is modified by Target 10.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`/`Fixpoint`.

   What is formalized here:
     - the action of the lattice translations and of the time reflection
       t -> -t on gauge fields and on observables;
     - the Osterwalder-Schrader form (F, G) = <(Theta F) G> on observables
       localized at non-negative times, and the transfer operator
       T = translation by one unit of time, in the infinite-volume Gibbs
       state of Target 9.

   Targets:
     10a  the infinite-volume Gibbs expectation of a local observable does
          not depend on the exhausting sequence of finite volumes (free
          boundary conditions);
     10b  it is invariant under the lattice translations and under the time
          reflection;
     10c  reflection positivity: (F, F) = <(Theta F) F> >= 0 for every
          observable localized at non-negative times;
     10d  exponential clustering for observables localized on arbitrary
          finite sets of plaquettes;
     10e  mass gap: for psi = F - <F> (the component of F orthogonal to the
          vacuum in the Osterwalder-Schrader form),
            |(psi, T^k psi)| <= exp(- m k) (psi, psi),  m = mu / 2 > 0,
          for every observable F localized at non-negative times;
     10f  the same for two observables: with phi = F - <F>, psi = G - <G>,
            (phi, T^k psi)^2 <= exp(- 2 m k) (phi, phi) (psi, psi),
          i.e. T^k restricted to the orthogonal complement of the vacuum
          has norm at most exp(- m k) in the Osterwalder-Schrader form.

   Scope disclaimer:
     These are statements about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling (small beta) only.  10e and 10f are
     the quadratic-form and bilinear-form statements of a spectral gap of
     the transfer operator on the pre-Hilbert space of local observables at
     non-negative times (which contains the gauge-invariant ones): the
     Hilbert-space completion (quotient by the null vectors and closure),
     the self-adjoint operator T on it and the Hamiltonian - ln T are NOT
     constructed here, and positivity of T is not proved.  Nothing here formalizes a
     continuum limit, weak coupling, boundary conditions other than free
     ones, gauge invariance of the state, Osterwalder-Schrader
     reconstruction of a continuum theory, or the Clay Millennium Prize
     Problem.  As in Targets 8 and 9, that the Hopf-coordinate measure is
     the Haar measure of SU(2) is the classical volume formula of S^3 and
     its bi-invariance is not proved here.
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

Module ChallengeSU2MassGap.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.

  (* =======================================================================
     1. Lattice translations
     ======================================================================= *)

  (* The link l moved by one lattice unit in direction d. *)
  Definition link_shift (d : Dir4D) (l : Link4D) : Link4D :=
    (shift4D (fst l) d, snd l).

  (* The gauge field read through the shift:  (U o shift_d)(l) = U(l + d). *)
  Definition su2_translate (d : Dir4D) (U : SU2Config) : SU2Config :=
    fun l => U (link_shift d l).

  (* The observable F moved by one lattice unit in direction d: if F depends
     on the link variables of a set of links, `obs_translate d F` depends in
     the same way on those of the shifted links. *)
  Definition obs_translate (d : Dir4D) (F : SU2Config -> R) : SU2Config -> R :=
    fun U => F (su2_translate d U).

  (* F moved by k lattice units in direction d. *)
  Fixpoint obs_translate_n (d : Dir4D) (k : nat) (F : SU2Config -> R)
      : SU2Config -> R :=
    match k with
    | O => F
    | S k' => obs_translate d (obs_translate_n d k' F)
    end.

  (* =======================================================================
     2. Time reflection
     ======================================================================= *)

  (* The reflection t -> -t of the sites (the hyperplane t = 0 is fixed). *)
  Definition site_reflect (s : Site4D) : Site4D :=
    mkSite4D (- s4_t s) (s4_x s) (s4_y s) (s4_z s).

  (* The image of a link.  A spatial link is moved with its initial site.
     The time-like link from (t, x) to (t + 1, x) is mapped to the link
     between (- t, x) and (- t - 1, x), i.e. to the positively oriented
     link starting at (- t - 1, x), traversed backwards. *)
  Definition link_reflect (l : Link4D) : Link4D :=
    match snd l with
    | D4_t =>
        (mkSite4D (- s4_t (fst l) - 1) (s4_x (fst l)) (s4_y (fst l)) (s4_z (fst l)),
         D4_t)
    | D4_x => (site_reflect (fst l), D4_x)
    | D4_y => (site_reflect (fst l), D4_y)
    | D4_z => (site_reflect (fst l), D4_z)
    end.

  (* The reflected gauge field: the variable of the image link, inverted on
     the time-like links (which are traversed backwards). *)
  Definition su2_reflect (U : SU2Config) : SU2Config :=
    fun l =>
      match snd l with
      | D4_t => qconj (U (link_reflect l))
      | D4_x => U (link_reflect l)
      | D4_y => U (link_reflect l)
      | D4_z => U (link_reflect l)
      end.

  (* The time-reflected observable Theta F. *)
  Definition obs_reflect (F : SU2Config -> R) : SU2Config -> R :=
    fun U => F (su2_reflect U).

  (* A plaquette at non-negative times: all its links join sites with
     t >= 0. *)
  Definition pos_time_plaq (p : Plaq4D) : Prop := (0 <= s4_t (p4_site p))%Z.

  (* =======================================================================
     3. TARGET 10a: the infinite-volume state does not depend on the
        exhausting sequence
     ======================================================================= *)

  (* TARGET 10a (Uniqueness of the Thermodynamic Limit, free boundary
     conditions):
     For every coupling beta with 43008 * |beta| <= 1, every bounded
     uniformly continuous observable f localized on a finite list P of
     canonical plaquettes, and EVERY sequence Lam k of finite duplicate-free
     volumes of canonical plaquettes that eventually contains each cube
     Lambda_m = `su2_box m`:  if w k is the Haar-measure Gibbs expectation
     of f in Lam k, then w k converges to the infinite-volume Gibbs
     expectation of f of Target 9b. *)
  Definition Challenge_SU2Gauge4D_InfiniteVolumeUniqueness : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R)
           (Lam : nat -> list Plaq4D) (w : nat -> R) (v : R),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      (forall k, NoDup (Lam k)) ->
      (forall k, Forall wf_plaq_4D (Lam k)) ->
      (forall m, exists K : nat, forall k, (K <= k)%nat -> incl (su2_box m) (Lam k)) ->
      (forall k, su2_haar_expect_is beta (Lam k) f (w k)) ->
      su2_infinite_volume_expect_is beta f v ->
      Un_cv w v.

  (* =======================================================================
     4. TARGET 10b: translation and reflection invariance
     ======================================================================= *)

  (* TARGET 10b (Symmetries of the Infinite-Volume State):
     For every coupling beta with 43008 * |beta| <= 1 and every bounded
     uniformly continuous observable f localized on a finite list of
     canonical plaquettes, with infinite-volume Gibbs expectation v:
     the translate of f by one lattice unit in each of the four directions,
     and the time-reflected observable Theta f, have the same
     infinite-volume Gibbs expectation v. *)
  Definition Challenge_SU2Gauge4D_InfiniteVolumeSymmetry : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R) (v : R),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      su2_infinite_volume_expect_is beta f v ->
      (forall d : Dir4D, su2_infinite_volume_expect_is beta (obs_translate d f) v) /\
      su2_infinite_volume_expect_is beta (obs_reflect f) v.

  (* =======================================================================
     5. TARGET 10c: reflection positivity
     ======================================================================= *)

  (* TARGET 10c (Reflection Positivity of the Infinite-Volume State):
     For every coupling beta with 43008 * |beta| <= 1 and every bounded
     uniformly continuous observable f localized on a finite list of
     canonical plaquettes at non-negative times, the infinite-volume Gibbs
     expectation of (Theta f) * f exists and is non-negative. *)
  Definition Challenge_SU2Gauge4D_ReflectionPositivity : Prop :=
    forall (beta : R) (P : list Plaq4D) (f : SU2Config -> R),
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * f U) v /\
        0 <= v.

  (* =======================================================================
     6. TARGET 10d: clustering for observables on finite sets of plaquettes
     ======================================================================= *)

  (* TARGET 10d (Exponential Clustering of Multi-Plaquette Observables):
     For every mu >= 0, every coupling beta with 168 * |beta| <= exp(- mu)
     and 43008 * |beta| <= 1, all finite lists P1, P2 of canonical
     plaquettes and all bounded uniformly continuous observables f, g with
     |f|, |g| <= 1 depending only on the link variables of the plaquettes of
     P1 and of P2 respectively, the infinite-volume Gibbs expectations
     <f g>, <f>, <g> exist and
       |<f g> - <f> <g>|
         <= 4 * sum_{p in P1} sum_{q in P2} exp(- mu * (dist(p, q) - 1)). *)
  Definition Challenge_SU2Gauge4D_MultiPlaquetteClustering : Prop :=
    forall (beta mu : R) (P1 P2 : list Plaq4D) (f g : SU2Config -> R),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P1 ->
      Forall wf_plaq_4D P2 ->
      su2_local_on f P1 ->
      su2_local_on g P2 ->
      su2_bounded_continuous f ->
      su2_bounded_continuous g ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      exists vfg vf vg : R,
        su2_infinite_volume_expect_is beta (fun U => f U * g U) vfg /\
        su2_infinite_volume_expect_is beta f vf /\
        su2_infinite_volume_expect_is beta g vg /\
        Rabs (vfg - vf * vg)
        <= 4 * fold_right Rplus 0
                 (map (fun p =>
                         fold_right Rplus 0
                           (map (fun q => exp (- mu * (plaq4D_dist p q - 1))) P2))
                      P1).

  (* =======================================================================
     7. TARGET 10e: the mass gap of the transfer operator
     ======================================================================= *)

  (* TARGET 10e (Transfer-Matrix Mass Gap at Strong Coupling):
     For every mu >= 0, every coupling beta with 168 * |beta| <= exp(- mu)
     and 43008 * |beta| <= 1, every bounded uniformly continuous observable
     f localized on a finite list of canonical plaquettes at non-negative
     times, and every k: the infinite-volume Gibbs expectations
       v0 = <(Theta f) f>,   vk = <(Theta f) (tau^k f)>,   vf = <f>
     exist (tau = translation by one unit of time) and

       0 <= v0 - vf^2,
       |vk - vf^2| <= exp(- (mu / 2) * k) * (v0 - vf^2).

     In terms of the Osterwalder-Schrader form (F, G) = <(Theta F) G> and
     of the transfer operator T = tau, with psi = f - <f> the component of
     f orthogonal to the vacuum (the constant observable 1):
       (psi, psi) = v0 - vf^2   and   (psi, T^k psi) = vk - vf^2,
     so the statement is  |(psi, T^k psi)| <= exp(- m k) (psi, psi)  with
     the mass gap m = mu / 2, which is positive for mu > 0 and diverges as
     beta -> 0. *)
  Definition Challenge_SU2Gauge4D_TransferMatrixMassGap : Prop :=
    forall (beta mu : R) (P : list Plaq4D) (f : SU2Config -> R) (k : nat),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      su2_local_on f P ->
      su2_bounded_continuous f ->
      exists v0 vk vf : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * f U) v0 /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t k f U) vk /\
        su2_infinite_volume_expect_is beta f vf /\
        0 <= v0 - vf * vf /\
        Rabs (vk - vf * vf) <= exp (- (mu / 2) * INR k) * (v0 - vf * vf).

  (* =======================================================================
     8. TARGET 10f: the norm of the transfer operator on the orthogonal
        complement of the vacuum
     ======================================================================= *)

  (* TARGET 10f (Norm Bound for the Transfer Operator on the Orthogonal
     Complement of the Vacuum):
     For every mu >= 0, every coupling beta with 168 * |beta| <= exp(- mu)
     and 43008 * |beta| <= 1, all bounded uniformly continuous observables
     f, g localized on finite lists of canonical plaquettes at non-negative
     times, and every k: the infinite-volume Gibbs expectations
       vff = <(Theta f) f>,   vgg = <(Theta g) g>,
       vk = <(Theta f) (tau^k g)>,   vf = <f>,   vg = <g>
     exist and

       (vk - vf vg)^2 <= exp(- mu * k) * (vff - vf^2) * (vgg - vg^2).

     With phi = f - <f> and psi = g - <g>:
       (phi, T^k psi)^2 <= exp(- 2 m k) (phi, phi) (psi, psi),  m = mu / 2,
     for all vectors phi, psi of the orthogonal complement of the vacuum in
     the pre-Hilbert space of local observables at non-negative times. *)
  Definition Challenge_SU2Gauge4D_TransferMatrixNormBound : Prop :=
    forall (beta mu : R) (P Q : list Plaq4D) (f g : SU2Config -> R) (k : nat),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      43008 * Rabs beta <= 1 ->
      Forall wf_plaq_4D P ->
      Forall pos_time_plaq P ->
      Forall wf_plaq_4D Q ->
      Forall pos_time_plaq Q ->
      su2_local_on f P ->
      su2_local_on g Q ->
      su2_bounded_continuous f ->
      su2_bounded_continuous g ->
      exists vff vgg vk vf vg : R,
        su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * f U) vff /\
        su2_infinite_volume_expect_is beta (fun U => obs_reflect g U * g U) vgg /\
        su2_infinite_volume_expect_is beta
          (fun U => obs_reflect f U * obs_translate_n D4_t k g U) vk /\
        su2_infinite_volume_expect_is beta f vf /\
        su2_infinite_volume_expect_is beta g vg /\
        (vk - vf * vg) * (vk - vf * vg)
        <= exp (- mu * INR k) * ((vff - vf * vf) * (vgg - vg * vg)).

End ChallengeSU2MassGap.
