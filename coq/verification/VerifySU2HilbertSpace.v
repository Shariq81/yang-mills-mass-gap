(* =========================================================================
   verification/VerifySU2HilbertSpace.v

   SOLUTION VERIFICATION MODULE FOR TARGET 13 (the Osterwalder-Schrader
   Hilbert space of the 4D SU(2) Wilson lattice gauge theory at strong
   coupling, its transfer operator and spectral gap).

   Assigns the repository's submitted Coq proof
     - ym.su2_os_hilbert_space.SU2OSHilbertSpace.su2_os_hilbert_space
   to the exact frozen proposition declared in
   `verification/ChallengeSU2HilbertSpace.v`.

   The submitted proof is stated directly on the frozen definitions, so no
   bridging lemma is needed: the assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import ym.su2_os_hilbert_space.

Module VerifySU2HilbertSpace.

  (* TARGET 13: the Osterwalder-Schrader Hilbert space, the transfer operator
     as a positive self-adjoint contraction, and its spectral gap. *)
  Theorem verified_su2gauge4D_os_hilbert_space :
    ChallengeSU2HilbertSpace.Challenge_SU2Gauge4D_OSHilbertSpace.
  Proof. exact SU2OSHilbertSpace.su2_os_hilbert_space. Qed.

End VerifySU2HilbertSpace.
