(* =========================================================================
   verification/ChallengeSU2HilbertSpace.v

   FROZEN CHALLENGE FILE FOR TARGET 13 (the Osterwalder-Schrader Hilbert
   space of the 4D SU(2) Wilson lattice gauge theory at strong coupling,
   with the transfer operator as a positive self-adjoint contraction on it
   and a spectral gap above a unique vacuum).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`,
   `verification/ChallengeSU2InfiniteVolume.v` and
   `verification/ChallengeSU2MassGap.v`.  None of the earlier frozen files
   is modified by Target 13.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   Targets 10 and 12 were statements about the Osterwalder-Schrader form
   (F, G) = <(Theta F) G> on the local observables at non-negative times
   (a pre-Hilbert space).  Target 13 asserts the existence of the completed
   space:

     - a type H with an addition, a scalar multiplication and a symmetric
       bilinear positive semidefinite form `ip`, complete with respect to
       the seminorm ip(x, x);
     - a linear map `emb` from the local observables at non-negative times
       into H, with dense range, such that
           ip (emb F) (emb G) = (F, G) = <(Theta F) G>;
     - a linear operator T on H which is symmetric and everywhere defined
       (hence bounded and self-adjoint), satisfies 0 <= T <= 1, and extends
       the translation by one unit of time:  T (emb F) = emb (tau F);
     - the vacuum Omega = emb 1 with (Omega, Omega) = 1 and T Omega = Omega,
       and on its orthogonal complement the spectral gap
           (x, T x) <= exp(- m) (x, x),
           || T^k x ||^2 <= exp(- 2 m k) || x ||^2      for every k,
       so that, for m > 0, every T-invariant vector is a multiple of Omega.

   Null vectors.  No quotient type is used.  The form `ip` is positive
   SEMIdefinite on H, and the Hilbert space proper is H modulo the vectors
   of norm zero: two elements x, y of H represent the same vector when
   `hs_null x y`, i.e. ip(x - y, x - y) = 0.  Every identity between vectors
   below is stated in this sense.  Because `ip` is symmetric and bilinear
   with respect to the two operations, H modulo null vectors is a real
   inner-product space (all vector-space axioms hold modulo null vectors),
   and `emb` and T are compatible with the identification.

   Scope disclaimer:
     This is a statement about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling (0 <= beta <= 1/43008), in lattice
     units.  The Hamiltonian - ln T is NOT constructed (no spectral theorem
     or functional calculus is formalized); the statement is about T.
     Nothing here formalizes a continuum limit, weak coupling, or the Clay
     Millennium Prize Problem.
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

Module ChallengeSU2HilbertSpace.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.
  Import ChallengeSU2MassGap.

  (* =======================================================================
     1. The pre-Hilbert space: local observables at non-negative times
     ======================================================================= *)

  (* f is a bounded uniformly continuous observable localized on a finite
     list of canonical plaquettes at non-negative times. *)
  Definition su2_pos_time_observable (f : SU2Config -> R) : Prop :=
    exists P : list Plaq4D,
      Forall wf_plaq_4D P /\ Forall pos_time_plaq P /\
      su2_local_on f P /\ su2_bounded_continuous f.

  (* =======================================================================
     2. Complete inner-product spaces, without quotients
     ======================================================================= *)

  (* x - y *)
  Definition hs_sub {H : Type} (hadd : H -> H -> H) (hscal : R -> H -> H)
      (x y : H) : H :=
    hadd x (hscal (-1) y).

  (* x and y represent the same vector:  || x - y ||^2 = 0 *)
  Definition hs_null {H : Type} (hadd : H -> H -> H) (hscal : R -> H -> H)
      (ip : H -> H -> R) (x y : H) : Prop :=
    ip (hs_sub hadd hscal x y) (hs_sub hadd hscal x y) = 0.

  (* (H, hadd, hscal, ip) is a real Hilbert space modulo its null vectors:
     ip is symmetric, bilinear and positive semidefinite, and every Cauchy
     sequence converges. *)
  Definition hs_hilbert_space (H : Type) (hadd : H -> H -> H) (hscal : R -> H -> H)
      (ip : H -> H -> R) : Prop :=
    (forall x y : H, ip x y = ip y x) /\
    (forall x y z : H, ip (hadd x y) z = ip x z + ip y z) /\
    (forall (c : R) (x z : H), ip (hscal c x) z = c * ip x z) /\
    (forall x : H, 0 <= ip x x) /\
    (forall X : nat -> H,
       (forall eps : R, 0 < eps -> exists N : nat, forall p q : nat,
          (N <= p)%nat -> (N <= q)%nat ->
          ip (hs_sub hadd hscal (X p) (X q)) (hs_sub hadd hscal (X p) (X q)) < eps) ->
       exists y : H, forall eps : R, 0 < eps -> exists N : nat, forall n : nat,
         (N <= n)%nat ->
         ip (hs_sub hadd hscal (X n) y) (hs_sub hadd hscal (X n) y) < eps).

  (* =======================================================================
     3. The Osterwalder-Schrader embedding
     ======================================================================= *)

  (* emb maps the local observables at non-negative times linearly onto a
     dense subspace of H, and the inner product of the images is the
     Osterwalder-Schrader form of the infinite-volume Gibbs state:
       ip (emb f) (emb g) = <(Theta f) g>. *)
  Definition su2_os_embedding (beta : R) (H : Type) (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R)
      (emb : (SU2Config -> R) -> H) : Prop :=
    (forall f g : SU2Config -> R,
       su2_pos_time_observable f -> su2_pos_time_observable g ->
       su2_infinite_volume_expect_is beta (fun U => obs_reflect f U * g U)
         (ip (emb f) (emb g))) /\
    (forall f g : SU2Config -> R,
       su2_pos_time_observable f -> su2_pos_time_observable g ->
       hs_null hadd hscal ip (emb (fun U => f U + g U)) (hadd (emb f) (emb g))) /\
    (forall (c : R) (f : SU2Config -> R),
       su2_pos_time_observable f ->
       hs_null hadd hscal ip (emb (fun U => c * f U)) (hscal c (emb f))) /\
    (forall (x : H) (eps : R), 0 < eps ->
       exists f : SU2Config -> R,
         su2_pos_time_observable f /\
         ip (hs_sub hadd hscal x (emb f)) (hs_sub hadd hscal x (emb f)) < eps).

  (* =======================================================================
     4. The transfer operator
     ======================================================================= *)

  (* T is linear, symmetric (hence, being everywhere defined on a complete
     space, bounded and self-adjoint), positive, a contraction, and extends
     the translation by one unit of time. *)
  Definition su2_os_transfer_operator (H : Type) (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R)
      (emb : (SU2Config -> R) -> H) (T : H -> H) : Prop :=
    (forall x y : H, hs_null hadd hscal ip (T (hadd x y)) (hadd (T x) (T y))) /\
    (forall (c : R) (x : H), hs_null hadd hscal ip (T (hscal c x)) (hscal c (T x))) /\
    (forall x y : H, ip (T x) y = ip x (T y)) /\
    (forall x : H, 0 <= ip x (T x)) /\
    (forall x : H, ip (T x) (T x) <= ip x x) /\
    (forall f : SU2Config -> R,
       su2_pos_time_observable f ->
       hs_null hadd hscal ip (T (emb f)) (emb (obs_translate_n D4_t 1 f))).

  (* =======================================================================
     5. Vacuum and spectral gap
     ======================================================================= *)

  (* Omega is a normalized T-invariant vector, T is at most exp(- m) on its
     orthogonal complement, in the sense of quadratic forms and in norm for
     all powers, and for m > 0 the invariant vectors are the multiples of
     Omega. *)
  Definition su2_os_vacuum_gap (H : Type) (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R) (T : H -> H) (Omega : H)
      (m : R) : Prop :=
    ip Omega Omega = 1 /\
    hs_null hadd hscal ip (T Omega) Omega /\
    (forall x : H, ip x Omega = 0 -> ip x (T x) <= exp (- m) * ip x x) /\
    (forall (k : nat) (x : H), ip x Omega = 0 ->
       ip (Nat.iter k T x) (Nat.iter k T x) <= exp (- (2 * m * INR k)) * ip x x) /\
    (0 < m -> forall x : H,
       hs_null hadd hscal ip (T x) x ->
       hs_null hadd hscal ip x (hscal (ip x Omega) Omega)).

  (* =======================================================================
     6. TARGET 13
     ======================================================================= *)

  (* TARGET 13 (Osterwalder-Schrader Hilbert Space, Transfer Operator and
     Spectral Gap):
     For every mu >= 0 and every coupling beta with 0 <= beta,
     168 * beta <= exp(- mu) and 43008 * beta <= 1, there are a complete
     inner-product space H, an embedding emb of the local observables at
     non-negative times with dense range and
       ip (emb f) (emb g) = <(Theta f) g>,
     and a positive self-adjoint contraction T on H extending the
     translation by one unit of time, such that Omega = emb 1 is a
     normalized invariant vector and T has the spectral gap exp(- mu / 2) on
     the orthogonal complement of Omega.

     In particular (mu = ln 256, admissible for all 0 <= beta <= 1/43008):
     the spectrum of T is contained in [0, 1/16] together with the simple
     eigenvalue 1. *)
  Definition Challenge_SU2Gauge4D_OSHilbertSpace : Prop :=
    forall beta mu : R,
      0 <= mu ->
      0 <= beta ->
      168 * beta <= exp (- mu) ->
      43008 * beta <= 1 ->
      exists (H : Type) (hadd : H -> H -> H) (hscal : R -> H -> H)
             (ip : H -> H -> R) (emb : (SU2Config -> R) -> H) (T : H -> H),
        hs_hilbert_space H hadd hscal ip /\
        su2_os_embedding beta H hadd hscal ip emb /\
        su2_os_transfer_operator H hadd hscal ip emb T /\
        su2_os_vacuum_gap H hadd hscal ip T (emb (fun _ => 1)) (mu / 2).

End ChallengeSU2HilbertSpace.
