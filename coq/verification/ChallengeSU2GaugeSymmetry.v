(* =========================================================================
   verification/ChallengeSU2GaugeSymmetry.v

   FROZEN CHALLENGE FILE FOR TARGET 15 (the action of the gauge group on
   the Osterwalder-Schrader Hilbert space of the 4D SU(2) Wilson lattice
   gauge theory at strong coupling).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`,
   `verification/ChallengeSU2InfiniteVolume.v`,
   `verification/ChallengeSU2MassGap.v`,
   `verification/ChallengeSU2GaugeInvariance.v`,
   `verification/ChallengeSU2HilbertSpace.v` and
   `verification/ChallengeSU2TransferSpectrum.v`.  None of the earlier
   frozen files is modified by Target 15.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   Targets 13 and 14 constructed the Osterwalder-Schrader Hilbert space H,
   the transfer operator T on it and its spectrum.  H is the completion of
   ALL local observables at non-negative times, gauge invariant or not.
   Target 15 describes how the gauge transformations of Target 11,
       U(x, mu)  |->  g(x) U(x, mu) g(x + mu)^{-1},
   act on H.  It asserts, for the space and the operator of Targets 13 and
   14 (all their clauses are repeated, so that the statement is about the
   same H and T), the existence of a family of maps W g : H -> H, one for
   every SU(2)-valued function g on the sites, such that

     - W g implements the gauge transformation of the observables:
           W g (emb f) = emb (f o g);
     - W g is linear and preserves the inner product;
     - W 1 = identity and  W h (W g x) = W (g h) x  (pointwise product), so
       that every W g is invertible, i.e. unitary;
     - ONLY TIME ZERO MATTERS: if g and h coincide on the sites of the
       hyperplane t = 0, then W g = W h.  In particular a gauge
       transformation that is trivial on the hyperplane t = 0 acts as the
       identity of H;
     - W g commutes with the transfer operator T;
     - the vacuum is invariant: W g Omega = Omega.

   Hence the group of gauge transformations acts on H through its
   restriction to the time-zero hyperplane (the time-zero gauge group), by
   unitary operators that commute with T and fix the vacuum.  The vectors
   fixed by every W g therefore form a closed T-invariant subspace
   containing the vacuum (the gauge-invariant sector), and the spectral gap
   of Targets 13 and 14, which holds on the whole orthogonal complement of
   the vacuum, holds in particular on that sector.

   Null vectors.  As in `ChallengeSU2HilbertSpace.v`, no quotient type is
   used: the Hilbert space proper is H modulo the vectors of norm zero, and
   every identity between vectors is `hs_null`.

   Scope disclaimer:
     This is a statement about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling (0 <= beta <= 1/43008), in lattice
     units.  The gauge-invariant sector is NOT further analysed: it is not
     shown to be the closure of the gauge-invariant observables, no
     projection onto it is constructed, and nothing is asserted about the
     existence or absence of vectors that are not gauge invariant.  No
     continuity of g |-> W g is asserted.  The Hamiltonian - ln T is NOT
     constructed.  Nothing here formalizes a continuum limit, weak coupling,
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
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.ChallengeSU2TransferSpectrum.

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2GaugeSymmetry.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.
  Import ChallengeSU2MassGap.
  Import ChallengeSU2GaugeInvariance.
  Import ChallengeSU2HilbertSpace.
  Import ChallengeSU2TransferSpectrum.

  (* =======================================================================
     1. Gauge transformations of observables
     ======================================================================= *)

  (* g is an SU(2)-valued function on the sites. *)
  Definition su2_gauge_fn (g : Site4D -> Quat) : Prop :=
    forall x : Site4D, su2_unit (g x).

  (* The gauge-transformed observable  U |-> f(g . U),  with `su2_gauge` the
     gauge transformation of Target 11. *)
  Definition obs_gauge (g : Site4D -> Quat) (f : SU2Config -> R) : SU2Config -> R :=
    fun U => f (su2_gauge g U).

  (* =======================================================================
     2. The action of the gauge group on the Hilbert space
     ======================================================================= *)

  (* W g, for g an SU(2)-valued function on the sites, is a linear map of H
     that preserves the inner product and implements the gauge
     transformation of the observables; W is compatible with the pointwise
     product of gauge transformations, depends only on the restriction of g
     to the hyperplane t = 0, commutes with the transfer operator and fixes
     Omega. *)
  Definition su2_os_gauge_action (H : Type) (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R)
      (emb : (SU2Config -> R) -> H) (T : H -> H) (Omega : H)
      (W : (Site4D -> Quat) -> H -> H) : Prop :=
    (* implements the gauge transformations of the observables *)
    (forall (g : Site4D -> Quat) (f : SU2Config -> R),
       su2_gauge_fn g -> su2_pos_time_observable f ->
       hs_null hadd hscal ip (W g (emb f)) (emb (obs_gauge g f))) /\
    (* linear *)
    (forall (g : Site4D -> Quat) (x y : H), su2_gauge_fn g ->
       hs_null hadd hscal ip (W g (hadd x y)) (hadd (W g x) (W g y))) /\
    (forall (g : Site4D -> Quat) (c : R) (x : H), su2_gauge_fn g ->
       hs_null hadd hscal ip (W g (hscal c x)) (hscal c (W g x))) /\
    (* preserves the inner product *)
    (forall (g : Site4D -> Quat) (x y : H), su2_gauge_fn g ->
       ip (W g x) (W g y) = ip x y) /\
    (* identity and composition *)
    (forall x : H, hs_null hadd hscal ip (W (fun _ => qone) x) x) /\
    (forall (g h : Site4D -> Quat) (x : H), su2_gauge_fn g -> su2_gauge_fn h ->
       hs_null hadd hscal ip (W h (W g x)) (W (fun s => qmul (g s) (h s)) x)) /\
    (* only the restriction to the hyperplane t = 0 matters *)
    (forall (g h : Site4D -> Quat) (x : H), su2_gauge_fn g -> su2_gauge_fn h ->
       (forall s : Site4D, s4_t s = 0%Z -> g s = h s) ->
       hs_null hadd hscal ip (W g x) (W h x)) /\
    (* commutes with the transfer operator *)
    (forall (g : Site4D -> Quat) (x : H), su2_gauge_fn g ->
       hs_null hadd hscal ip (W g (T x)) (T (W g x))) /\
    (* the vacuum is invariant *)
    (forall g : Site4D -> Quat, su2_gauge_fn g ->
       hs_null hadd hscal ip (W g Omega) Omega).

  (* =======================================================================
     3. TARGET 15
     ======================================================================= *)

  (* TARGET 15 (Gauge Symmetry of the Osterwalder-Schrader Hilbert Space):
     For every mu >= 0 and every coupling beta with 0 <= beta,
     168 * beta <= exp(- mu) and 43008 * beta <= 1, there are a complete
     inner-product space H, an embedding emb of the local observables at
     non-negative times, a transfer operator T with vacuum Omega = emb 1,
     spectral gap and spectrum exactly as in Targets 13 and 14, and a
     family W of inner-product-preserving linear maps of H, indexed by the
     SU(2)-valued functions g on the sites, with
       W g (emb f) = emb (f o g),   W 1 = 1,   W h W g = W (g h),
       W g = W h  whenever g = h on the hyperplane t = 0,
       W g T = T W g,   W g Omega = Omega. *)
  Definition Challenge_SU2Gauge4D_GaugeSymmetry : Prop :=
    forall beta mu : R,
      0 <= mu ->
      0 <= beta ->
      168 * beta <= exp (- mu) ->
      43008 * beta <= 1 ->
      exists (H : Type) (hadd : H -> H -> H) (hscal : R -> H -> H)
             (ip : H -> H -> R) (emb : (SU2Config -> R) -> H) (T : H -> H)
             (W : (Site4D -> Quat) -> H -> H),
        hs_hilbert_space H hadd hscal ip /\
        su2_os_embedding beta H hadd hscal ip emb /\
        su2_os_transfer_operator H hadd hscal ip emb T /\
        su2_os_vacuum_gap H hadd hscal ip T (emb (fun _ => 1)) (mu / 2) /\
        su2_os_transfer_spectrum H hadd hscal ip T (mu / 2) /\
        su2_os_gauge_action H hadd hscal ip emb T (emb (fun _ => 1)) W.

End ChallengeSU2GaugeSymmetry.
