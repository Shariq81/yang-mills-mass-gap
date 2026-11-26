(* =========================================================================
   verification/ChallengeSU2TransferSpectrum.v

   FROZEN CHALLENGE FILE FOR TARGET 14 (the spectrum of the transfer
   operator of the 4D SU(2) Wilson lattice gauge theory at strong coupling
   on its Osterwalder-Schrader Hilbert space).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen files
   `verification/Challenge.v`, `verification/ChallengeZ2Gauge.v`,
   `verification/ChallengeZ2AreaLaw.v`, `verification/ChallengeSU2Gauge.v`,
   `verification/ChallengeSU2InfiniteVolume.v`,
   `verification/ChallengeSU2MassGap.v` and
   `verification/ChallengeSU2HilbertSpace.v`.  None of the earlier frozen
   files is modified by Target 14.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`.

   Target 13 constructed the Osterwalder-Schrader Hilbert space H and the
   transfer operator T on it, and proved the gap as inequalities for T on
   the orthogonal complement of the vacuum.  Target 14 turns these
   inequalities into a statement about the SPECTRUM of T, without a
   spectral theorem: a real number lam belongs to the resolvent set of T
   when T - lam has a bounded, everywhere defined, linear two-sided
   inverse, and the spectrum is the complement of the resolvent set.
   Target 14 asserts, for the space and the operator of Target 13 (all the
   clauses of Target 13 are repeated, so that the statement is about the
   same H and T):

     - every lam < 0 is in the resolvent set;
     - every lam > exp(- m) different from 1 is in the resolvent set;
     - 1 is NOT in the resolvent set (it is an eigenvalue, with eigenvector
       the vacuum, and by Target 13 a simple one when m > 0).

   Hence   spec(T)  is contained in  [0, exp(- m)]  together with  {1},
   and 1 belongs to spec(T).  (T is symmetric on a real Hilbert space, so
   only real lam are relevant.)

   Null vectors.  As in `ChallengeSU2HilbertSpace.v`, no quotient type is
   used: the Hilbert space proper is H modulo the vectors of norm zero, and
   every identity between vectors is `hs_null`.  An inverse G in the sense
   below is linear and bounded modulo null vectors, hence compatible with
   the identification.

   Scope disclaimer:
     This is a statement about the LATTICE gauge theory with gauge group
     SU(2) on Z^4 at STRONG coupling (0 <= beta <= 1/43008), in lattice
     units.  The Hamiltonian - ln T is NOT constructed, and no spectral
     theorem, spectral measure or functional calculus is formalized; the
     statement is about the resolvent set of T.  Nothing here formalizes a
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
Require Import verification.ChallengeSU2HilbertSpace.

Import ListNotations.
Open Scope R_scope.

Module ChallengeSU2TransferSpectrum.

  Import Challenge.
  Import ChallengeZ2Gauge.
  Import ChallengeZ2AreaLaw.
  Import ChallengeSU2Gauge.
  Import ChallengeSU2InfiniteVolume.
  Import ChallengeSU2MassGap.
  Import ChallengeSU2HilbertSpace.

  (* =======================================================================
     1. Bounded inverses and the resolvent set
     ======================================================================= *)

  (* The operator A has a bounded, everywhere defined, linear two-sided
     inverse G (all identities modulo null vectors):
       G (x + y) = G x + G y,   G (c x) = c G x,
       || G x ||^2 <= C || x ||^2,
       A (G x) = x,   G (A x) = x. *)
  Definition hs_bounded_inverse {H : Type} (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R) (A : H -> H) : Prop :=
    exists (G : H -> H) (C : R),
      (forall x y : H, hs_null hadd hscal ip (G (hadd x y)) (hadd (G x) (G y))) /\
      (forall (c : R) (x : H), hs_null hadd hscal ip (G (hscal c x)) (hscal c (G x))) /\
      (forall x : H, ip (G x) (G x) <= C * ip x x) /\
      (forall x : H, hs_null hadd hscal ip (A (G x)) x) /\
      (forall x : H, hs_null hadd hscal ip (G (A x)) x).

  (* lam is in the resolvent set of T:  T - lam  has a bounded inverse. *)
  Definition hs_in_resolvent_set {H : Type} (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R) (T : H -> H) (lam : R) : Prop :=
    hs_bounded_inverse hadd hscal ip
      (fun x : H => hs_sub hadd hscal (T x) (hscal lam x)).

  (* =======================================================================
     2. The spectrum of the transfer operator
     ======================================================================= *)

  (* The spectrum of T is contained in [0, exp(- m)] together with {1}, and
     1 belongs to the spectrum. *)
  Definition su2_os_transfer_spectrum (H : Type) (hadd : H -> H -> H)
      (hscal : R -> H -> H) (ip : H -> H -> R) (T : H -> H) (m : R) : Prop :=
    (forall lam : R, lam < 0 -> hs_in_resolvent_set hadd hscal ip T lam) /\
    (forall lam : R, exp (- m) < lam -> lam <> 1 ->
       hs_in_resolvent_set hadd hscal ip T lam) /\
    ~ hs_in_resolvent_set hadd hscal ip T 1.

  (* =======================================================================
     3. TARGET 14
     ======================================================================= *)

  (* TARGET 14 (Spectrum of the Transfer Operator):
     For every mu >= 0 and every coupling beta with 0 <= beta,
     168 * beta <= exp(- mu) and 43008 * beta <= 1, there are a complete
     inner-product space H, an embedding of the local observables at
     non-negative times and a transfer operator T on H exactly as in
     Target 13 (Hilbert space, Osterwalder-Schrader embedding, positive
     self-adjoint contraction extending the translation by one unit of
     time, normalized invariant vacuum Omega = emb 1 and gap exp(- mu / 2)
     on its orthogonal complement), such that in addition

       T - lam  has a bounded inverse for every  lam < 0  and for every
       lam > exp(- mu / 2)  different from 1,   and   T - 1  has none.

     In particular (mu = ln 256, admissible for all 0 <= beta <= 1/43008):
     the spectrum of T is contained in [0, 1/16] together with {1}, the
     open interval (1/16, 1) is a spectral gap, and 1 is a simple
     eigenvalue. *)
  Definition Challenge_SU2Gauge4D_TransferSpectrum : Prop :=
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
        su2_os_vacuum_gap H hadd hscal ip T (emb (fun _ => 1)) (mu / 2) /\
        su2_os_transfer_spectrum H hadd hscal ip T (mu / 2).

End ChallengeSU2TransferSpectrum.
