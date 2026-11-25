(* =========================================================================
   verification/ChallengeSU2Gauge.v

   FROZEN CHALLENGE FILE FOR TARGET 8 (4D SU(2) Wilson lattice gauge theory,
   i.e. lattice Yang-Mills theory with the non-abelian compact simple gauge
   group SU(2), at strong coupling).

   Imports ONLY the Coq 8.18.0 Standard Library and the three frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v` and
   `verification/ChallengeZ2AreaLaw.v`, from which it reuses the lattice
   objects `Site4D`, `Dir4D`, `shift4D`, `Plaq4D`, `wf_plaq_4D`,
   `plaq4D_dist`, `Link4D`, `link4D_eqb`, `plaq4D_links`, `z2_links`,
   `shift4D_n`, `z2_segment` and `z2_rect_loop`.  None of those three files
   is modified by Target 8.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`/`Fixpoint`
   /`Record`.

   What is formalized here (genuine non-abelian lattice gauge theory, finite
   volume):
     - the gauge group SU(2), realized as the unit quaternions with the
       Hamilton product (the unit quaternion w + x i + y j + z k is the
       matrix [[w + i x, y + i z], [- y + i z, w - i x]] of SU(2); the
       Hamilton product is the matrix product, quaternion conjugation is the
       matrix inverse and the real part w is (1/2) tr),
     - link variables U : Link4D -> SU(2), path-ordered products, the
       holonomy of a rectangular loop and the Wilson loop (1/2) tr of it,
     - the plaquette variable (1/2) tr U_p and the Wilson action
       S(U) = - beta * sum_{p in Lambda} (1/2) tr U_p,
     - the Gibbs expectation for an a-priori link distribution that is
       uniform on a finite list G of group elements (a finite sum),
     - the Haar measure of SU(2) as the limit of the uniform distributions
       on the dyadic grids of the Hopf coordinates of S^3 (Riemann sums),
       and the Gibbs expectation with respect to it as the limit of the
       corresponding finite expectations.

   Targets:
     8a  exponential clustering of the truncated correlation of any two
         plaquette-local observables at strong coupling, uniformly in the
         finite volume AND in the finite a-priori distribution G;
     8b  Wilson-loop area law (an upper bound) at strong coupling for every
         rectangular loop inside the dynamical volume, uniformly in the
         finite volume and in the finite a-priori distribution G invariant
         under the center {+1, -1} of SU(2);
     8c  existence of the Haar-measure Gibbs expectation of every bounded
         uniformly continuous observable (convergence of the Riemann sums);
     8d  the clustering bound of 8a for the Haar-measure Gibbs state;
     8e  the area-law bound of 8b for the Haar-measure Gibbs state.

   Scope disclaimer:
     These are finite-volume statements about the LATTICE gauge theory with
     gauge group SU(2) on Z^4 with free boundary conditions, at STRONG
     coupling (small beta) only, with bounds that are uniform in the volume.
     8a/8d bound truncated correlations of plaquette-local observables and
     8b/8e are UPPER bounds for rectangular Wilson loops.  They do NOT
     formalize an infinite-volume limit, a continuum limit, weak coupling,
     reflection positivity, Osterwalder-Schrader reconstruction, a
     transfer-matrix spectral gap, a string tension as a limit, or the Clay
     Millennium Prize Problem.  That the image of Lebesgue measure on
     [0,1)^3 under the Hopf coordinates `su2_hopf` is the Haar measure of
     SU(2) is the classical volume formula of S^3; its bi-invariance is NOT
     proved here (8a and 8b do not depend on it: they hold for every finite
     a-priori distribution of the stated kind, hence for every weak limit
     of such distributions).
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Permutation.

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2Gauge.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.

  (* =======================================================================
     1. The gauge group SU(2) as the unit quaternions
     ======================================================================= *)

  (* The quaternion qr + qi i + qj j + qk k. *)
  Record Quat : Type := mkQuat {
    qr : R;
    qi : R;
    qj : R;
    qk : R
  }.

  (* Hamilton product (i j = k, j k = i, k i = j, i^2 = j^2 = k^2 = -1). *)
  Definition qmul (p q : Quat) : Quat :=
    mkQuat
      (qr p * qr q - qi p * qi q - qj p * qj q - qk p * qk q)
      (qr p * qi q + qi p * qr q + qj p * qk q - qk p * qj q)
      (qr p * qj q - qi p * qk q + qj p * qr q + qk p * qi q)
      (qr p * qk q + qi p * qj q - qj p * qi q + qk p * qr q).

  (* Conjugate (the inverse of a unit quaternion). *)
  Definition qconj (q : Quat) : Quat :=
    mkQuat (qr q) (- qi q) (- qj q) (- qk q).

  (* The identity 1 and the central element -1 acting by q |-> - q. *)
  Definition qone : Quat := mkQuat 1 0 0 0.

  Definition qneg (q : Quat) : Quat :=
    mkQuat (- qr q) (- qi q) (- qj q) (- qk q).

  Definition qnorm2 (q : Quat) : R :=
    qr q * qr q + qi q * qi q + qj q * qj q + qk q * qk q.

  (* SU(2) = the quaternions of norm 1. *)
  Definition su2_unit (q : Quat) : Prop := qnorm2 q = 1.

  (* =======================================================================
     2. SU(2) gauge fields, Wilson loops, and the Wilson action
     ======================================================================= *)

  Definition SU2Config : Type := Link4D -> Quat.

  Definition su2_unit_config (U : SU2Config) : Prop :=
    forall l, su2_unit (U l).

  Definition su2_update (U : SU2Config) (l : Link4D) (g : Quat) : SU2Config :=
    fun l' => if link4D_eqb l' l then g else U l'.

  (* Path-ordered product of the link variables along a list of consecutive
     links, each traversed in its positive direction. *)
  Definition su2_path (U : SU2Config) (C : list Link4D) : Quat :=
    fold_right (fun l acc => qmul (U l) acc) qone C.

  (* Holonomy around the boundary of the lattice rectangle with corner s
     spanned by a steps in direction mu and b steps in direction nu (the
     loop `ChallengeZ2AreaLaw.z2_rect_loop s mu nu a b`): bottom side
     forwards, right side forwards, top side backwards, left side
     backwards. *)
  Definition su2_rect_holonomy (U : SU2Config)
      (s : Site4D) (mu nu : Dir4D) (a b : nat) : Quat :=
    qmul (su2_path U (z2_segment s mu a))
      (qmul (su2_path U (z2_segment (shift4D_n s mu a) nu b))
        (qmul (qconj (su2_path U (z2_segment (shift4D_n s nu b) mu a)))
              (qconj (su2_path U (z2_segment s nu b))))).

  (* Wilson loop in the fundamental representation, normalized:
     (1/2) tr of the holonomy (gauge invariant). *)
  Definition su2_wilson_loop (U : SU2Config)
      (s : Site4D) (mu nu : Dir4D) (a b : nat) : R :=
    qr (su2_rect_holonomy U s mu nu a b).

  (* Plaquette variable (1/2) tr U_p, where
       U_p = U(s,mu) U(s+mu,nu) U(s+nu,mu)^{-1} U(s,nu)^{-1}
     is the holonomy around the unit plaquette p (the 1 x 1 Wilson loop). *)
  Definition su2_plaq (U : SU2Config) (p : Plaq4D) : R :=
    su2_wilson_loop U (p4_site p) (p4_mu p) (p4_nu p) 1 1.

  (* Wilson action  S(U) = - beta * sum_{p in Lambda} (1/2) tr U_p  (it
     differs from beta * sum_p (1 - (1/2) tr U_p) by a constant, which
     cancels in every expectation). *)
  Definition su2_wilson_action (beta : R) (Lambda : list Plaq4D) (U : SU2Config) : R :=
    - beta * fold_right Rplus 0 (map (su2_plaq U) Lambda).

  (* =======================================================================
     3. Gibbs expectation for a finite a-priori link distribution
     ======================================================================= *)

  (* Sum of F over all configurations obtained from U by assigning every
     element of the finite list G to every link of E in turn. *)
  Fixpoint su2_sum (G : list Quat) (E : list Link4D)
      (F : SU2Config -> R) (U : SU2Config) : R :=
    match E with
    | [] => F U
    | l :: E' =>
        fold_right Rplus 0 (map (fun g => su2_sum G E' F (su2_update U l g)) G)
    end.

  (* Gibbs expectation  <F> = Z^{-1} * int F(U) exp(- S(U)) dU  when every
     link of the volume is distributed uniformly on the finite list G of
     group elements (independently) and the links outside the volume are
     frozen to the identity.  The normalization |G|^{-|E|} of the a-priori
     measure cancels between numerator and denominator. *)
  Definition su2_expect_on (G : list Quat) (beta : R) (Lambda : list Plaq4D)
      (F : SU2Config -> R) : R :=
    su2_sum G (z2_links Lambda)
      (fun U => F U * exp (- su2_wilson_action beta Lambda U)) (fun _ => qone)
    / su2_sum G (z2_links Lambda)
        (fun U => exp (- su2_wilson_action beta Lambda U)) (fun _ => qone).

  (* =======================================================================
     4. The Haar measure of SU(2) by Riemann sums in Hopf coordinates
     ======================================================================= *)

  (* Hopf coordinates of S^3 = SU(2):
       a = sqrt(1 - s) e^{2 pi i x},  b = sqrt(s) e^{2 pi i y},
     the unit quaternion (Re a) + (Im a) i + (Re b) j + (Im b) k.  The
     normalized Haar measure of SU(2) (the uniform probability measure of
     S^3) is the image of Lebesgue measure on [0,1)^3 under this map. *)
  Definition su2_hopf (s x y : R) : Quat :=
    mkQuat (sqrt (1 - s) * cos (2 * PI * x))
           (sqrt (1 - s) * sin (2 * PI * x))
           (sqrt s * cos (2 * PI * y))
           (sqrt s * sin (2 * PI * y)).

  (* The image of the dyadic grid of mesh 2^{-n} of [0,1)^3: 8^n points. *)
  Definition su2_grid (n : nat) : list Quat :=
    let N := (2 ^ n)%nat in
    flat_map (fun i =>
      flat_map (fun j =>
        map (fun k => su2_hopf (INR i / INR N) (INR j / INR N) (INR k / INR N))
            (seq 0 N))
        (seq 0 N))
      (seq 0 N).

  (* v is the Gibbs expectation of F with respect to the Haar measure: the
     limit of the expectations for the uniform distributions on the grids
     (Riemann sums of the Haar integrals). *)
  Definition su2_haar_expect_is (beta : R) (Lambda : list Plaq4D)
      (F : SU2Config -> R) (v : R) : Prop :=
    Un_cv (fun n => su2_expect_on (su2_grid n) beta Lambda F) v.

  (* Bounded uniformly continuous observables on SU(2)-valued
     configurations (sup-distance over the links, componentwise). *)
  Definition su2_close (delta : R) (p q : Quat) : Prop :=
    Rabs (qr p - qr q) < delta /\ Rabs (qi p - qi q) < delta /\
    Rabs (qj p - qj q) < delta /\ Rabs (qk p - qk q) < delta.

  Definition su2_bounded_continuous (F : SU2Config -> R) : Prop :=
    (exists M : R, forall U, su2_unit_config U -> Rabs (F U) <= M) /\
    (forall eps : R, 0 < eps ->
       exists delta : R, 0 < delta /\
         forall U U', su2_unit_config U -> su2_unit_config U' ->
           (forall l, su2_close delta (U l) (U' l)) ->
           Rabs (F U - F U') < eps).

  (* =======================================================================
     5. TARGET 8a: exponential clustering at strong coupling
     ======================================================================= *)

  (* F depends only on the 4 link variables of the plaquette p. *)
  Definition su2_local_at (F : SU2Config -> R) (p : Plaq4D) : Prop :=
    forall U U', (forall l, In l (plaq4D_links p) -> U l = U' l) -> F U = F U'.

  (* Truncated (connected) correlation  <f ; g> = <f g> - <f> <g>. *)
  Definition su2_truncated_on (G : list Quat) (beta : R) (Lambda : list Plaq4D)
      (f g : SU2Config -> R) : R :=
    su2_expect_on G beta Lambda (fun U => f U * g U)
    - su2_expect_on G beta Lambda f * su2_expect_on G beta Lambda g.

  (* TARGET 8a (Strong-Coupling Exponential Clustering — ZERO analytic or
     combinatorial hypotheses):
     For every non-empty finite list G of elements of SU(2) (the a-priori
     link distribution), every decay rate mu >= 0, every coupling beta (of
     either sign) with
       168 * |beta| <= exp(- mu),
     every finite duplicate-free volume Lambda of canonical plaquettes of
     Z^4, every canonical plaquette p1, every plaquette p2 and all
     observables f, g with |f|, |g| <= 1 depending only on the link
     variables of p1 and of p2 respectively (for instance the plaquette
     variables (1/2) tr U_p1 and (1/2) tr U_p2):
       |<f ; g>_Lambda| <= 4 * exp(- mu * (dist(p1, p2) - 1)),
     where dist = plaq4D_dist is the scaled anchor distance of Targets
     5c/6c/7b.  The bound is uniform in Lambda and in G, and the admissible
     rate mu = ln(1 / (168 |beta|)) diverges as beta -> 0. *)
  Definition Challenge_SU2Gauge4D_StrongCouplingClustering : Prop :=
    forall (G : list Quat) (beta mu : R) (Lambda : list Plaq4D)
           (p1 p2 : Plaq4D) (f g : SU2Config -> R),
      G <> [] ->
      Forall su2_unit G ->
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      wf_plaq_4D p1 ->
      su2_local_at f p1 ->
      su2_local_at g p2 ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      Rabs (su2_truncated_on G beta Lambda f g)
      <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).

  (* =======================================================================
     6. TARGET 8b: Wilson-loop area law at strong coupling
     ======================================================================= *)

  (* TARGET 8b (Strong-Coupling Area Law — ZERO analytic or combinatorial
     hypotheses):
     For every non-empty finite list G of elements of SU(2) that is
     invariant, as a multiset, under multiplication by the central element
     -1, every coupling beta (of either sign) with
       63 * (exp(2 |beta|) - 1) <= 1,
     every finite duplicate-free volume Lambda of canonical plaquettes of
     Z^4, every corner s, every pair of distinct directions mu, nu and all
     side lengths a, b such that EVERY link of the rectangular loop belongs
     to the link set of Lambda (the loop lies inside the dynamical volume):

       |< (1/2) tr U(loop) >_Lambda|
         <= (63 * (exp(2 |beta|) - 1))^(a * b) * exp(2 * (a + b)).

     The first factor decays exponentially in the area a * b of the
     rectangle, the second grows only exponentially in its perimeter
     2 (a + b), and the bound is uniform in Lambda and in G.  As in Target
     7e the hypothesis on the loop links cannot be dropped: links outside
     `z2_links Lambda` are frozen to the identity. *)
  Definition Challenge_SU2Gauge4D_WilsonLoopAreaLaw : Prop :=
    forall (G : list Quat) (beta : R) (Lambda : list Plaq4D)
           (s : Site4D) (mu nu : Dir4D) (a b : nat),
      G <> [] ->
      Forall su2_unit G ->
      Permutation (map qneg G) G ->
      63 * (exp (2 * Rabs beta) - 1) <= 1 ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      mu <> nu ->
      (forall l, In l (z2_rect_loop s mu nu a b) -> In l (z2_links Lambda)) ->
      Rabs (su2_expect_on G beta Lambda
              (fun U => su2_wilson_loop U s mu nu a b))
      <= (63 * (exp (2 * Rabs beta) - 1)) ^ (a * b) * exp (2 * INR (a + b)).

  (* =======================================================================
     7. TARGET 8c: the Haar-measure Gibbs state exists
     ======================================================================= *)

  (* TARGET 8c (Existence of the Haar-Measure Gibbs Expectation — every
     beta):
     For every real beta, every finite list Lambda of plaquettes of Z^4 and
     every bounded uniformly continuous observable F, the Gibbs
     expectations of F for the uniform distributions on the Hopf grids
     converge as the mesh 2^{-n} tends to 0: the Gibbs expectation of F
     with respect to the Haar measure exists. *)
  Definition Challenge_SU2Gauge4D_HaarStateExists : Prop :=
    forall (beta : R) (Lambda : list Plaq4D) (F : SU2Config -> R),
      su2_bounded_continuous F ->
      exists v : R, su2_haar_expect_is beta Lambda F v.

  (* =======================================================================
     8. TARGET 8d: exponential clustering for the Haar-measure Gibbs state
     ======================================================================= *)

  (* TARGET 8d (Strong-Coupling Exponential Clustering, Haar Measure):
     Under the hypotheses of Target 8a on beta, mu, Lambda, p1, p2 and for
     bounded uniformly continuous observables f, g with |f|, |g| <= 1
     depending only on the link variables of p1 and of p2 respectively,
     the Haar-measure Gibbs expectations <f g>, <f>, <g> exist and
       |<f g> - <f> <g>| <= 4 * exp(- mu * (dist(p1, p2) - 1)),
     uniformly in the finite volume Lambda. *)
  Definition Challenge_SU2Gauge4D_HaarClustering : Prop :=
    forall (beta mu : R) (Lambda : list Plaq4D)
           (p1 p2 : Plaq4D) (f g : SU2Config -> R),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      wf_plaq_4D p1 ->
      su2_local_at f p1 ->
      su2_local_at g p2 ->
      su2_bounded_continuous f ->
      su2_bounded_continuous g ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      exists vfg vf vg : R,
        su2_haar_expect_is beta Lambda (fun U => f U * g U) vfg /\
        su2_haar_expect_is beta Lambda f vf /\
        su2_haar_expect_is beta Lambda g vg /\
        Rabs (vfg - vf * vg) <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).

  (* =======================================================================
     9. TARGET 8e: Wilson-loop area law for the Haar-measure Gibbs state
     ======================================================================= *)

  (* TARGET 8e (Strong-Coupling Area Law, Haar Measure):
     Under the hypotheses of Target 8b on beta, Lambda and the rectangular
     loop, the Haar-measure Gibbs expectation w of the Wilson loop exists
     and
       |w| <= (63 * (exp(2 |beta|) - 1))^(a * b) * exp(2 * (a + b)),
     uniformly in the finite volume Lambda. *)
  Definition Challenge_SU2Gauge4D_HaarWilsonLoopAreaLaw : Prop :=
    forall (beta : R) (Lambda : list Plaq4D)
           (s : Site4D) (mu nu : Dir4D) (a b : nat),
      63 * (exp (2 * Rabs beta) - 1) <= 1 ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      mu <> nu ->
      (forall l, In l (z2_rect_loop s mu nu a b) -> In l (z2_links Lambda)) ->
      exists w : R,
        su2_haar_expect_is beta Lambda
          (fun U => su2_wilson_loop U s mu nu a b) w /\
        Rabs w
        <= (63 * (exp (2 * Rabs beta) - 1)) ^ (a * b) * exp (2 * INR (a + b)).

End ChallengeSU2Gauge.
