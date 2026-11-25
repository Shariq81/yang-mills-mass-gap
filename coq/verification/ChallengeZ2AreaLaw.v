(* =========================================================================
   verification/ChallengeZ2AreaLaw.v

   FROZEN CHALLENGE FILE FOR TARGET 7e (Wilson-loop area law of the 4D Z_2
   Wilson lattice gauge theory at strong coupling).

   Imports ONLY the Coq 8.18.0 Standard Library and the two frozen files
   `verification/Challenge.v` (Standard-Library-only) and
   `verification/ChallengeZ2Gauge.v` (Standard Library + Challenge.v), from
   which it reuses `Site4D`, `Dir4D`, `shift4D`, `Plaq4D`, `wf_plaq_4D` and
   the gauge-theory objects `Link4D`, `z2_links`, `z2_holonomy`, `z2_expect`.
   Neither of those two files is modified by Target 7e.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`/`Fixpoint`.

   Target:
     7e  for a rectangular Wilson loop all of whose links belong to the
         dynamical volume, the Wilson-loop expectation decays at least
         exponentially in the AREA of the rectangle at strong coupling, with
         a correction that is exponential only in its perimeter, uniformly
         in the finite volume.

   Scope disclaimer:
     This is a finite-volume, strong-coupling UPPER bound for the lattice
     gauge theory with the ABELIAN FINITE gauge group Z_2 on Z^4 with free
     boundary conditions. It is the classical strong-coupling confinement
     criterion; it does NOT formalize an infinite-volume or continuum limit,
     a non-abelian or continuous gauge group, a lower bound on the Wilson
     loop, a string tension as a limit, reflection positivity,
     Osterwalder-Schrader reconstruction, a transfer-matrix spectral gap, or
     the Clay Millennium Prize Problem.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import List.

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.

Import ListNotations.
Open Scope R_scope.

Module ChallengeZ2AreaLaw.

  Import Challenge.
  Import ChallengeZ2Gauge.

  (* =======================================================================
     1. Rectangular Wilson loops
     ======================================================================= *)

  (* The site reached from s by k unit steps in direction d. *)
  Fixpoint shift4D_n (s : Site4D) (d : Dir4D) (k : nat) : Site4D :=
    match k with
    | O => s
    | S k' => shift4D (shift4D_n s d k') d
    end.

  (* The k consecutive links of the straight segment that starts at s and
     runs in direction d. *)
  Definition z2_segment (s : Site4D) (d : Dir4D) (k : nat) : list Link4D :=
    map (fun i => (shift4D_n s d i, d)) (seq 0 k).

  (* The boundary of the lattice rectangle with corner s spanned by a steps
     in direction mu and b steps in direction nu: its four sides, listed as
     bottom, right, top, left.  It consists of 2 (a + b) links.  (For the
     gauge group Z_2 the orientation of the links is immaterial.) *)
  Definition z2_rect_loop (s : Site4D) (mu nu : Dir4D) (a b : nat) : list Link4D :=
    z2_segment s mu a ++
    z2_segment (shift4D_n s mu a) nu b ++
    z2_segment (shift4D_n s nu b) mu a ++
    z2_segment s nu b.

  (* =======================================================================
     2. TARGET 7e: Wilson-loop area law at strong coupling
     ======================================================================= *)

  (* TARGET 7e (Strong-Coupling Area Law — ZERO analytic or combinatorial
     hypotheses):
     For every coupling beta (of either sign) with 63 * |tanh(beta)| <= 1,
     every finite duplicate-free volume Lambda of canonical plaquettes of
     Z^4, every corner s, every pair of distinct directions mu, nu and all
     side lengths a, b such that EVERY link of the rectangular loop belongs
     to the link set of Lambda (the loop lies inside the dynamical volume):

       |< prod_{l in loop} U_l >_Lambda|
         <= (63 * |tanh(beta)|)^(a * b) * exp(2 * (a + b)).

     The first factor decays exponentially in the area a * b of the
     rectangle, the second grows only exponentially in its perimeter
     2 (a + b), and the bound is uniform in Lambda.

     The hypothesis on the loop links cannot be dropped: in
     `ChallengeZ2Gauge.z2_expect` the links outside `z2_links Lambda` are
     frozen to +1, so a loop lying entirely outside the volume has
     expectation exactly 1 whatever its area. *)
  Definition Challenge_Z2Gauge4D_WilsonLoopAreaLaw : Prop :=
    forall (beta : R) (Lambda : list Plaq4D)
           (s : Site4D) (mu nu : Dir4D) (a b : nat),
      63 * Rabs (tanh beta) <= 1 ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      mu <> nu ->
      (forall l, In l (z2_rect_loop s mu nu a b) -> In l (z2_links Lambda)) ->
      Rabs (z2_expect beta Lambda
              (fun U => z2_holonomy U (z2_rect_loop s mu nu a b)))
      <= (63 * Rabs (tanh beta)) ^ (a * b) * exp (2 * INR (a + b)).

End ChallengeZ2AreaLaw.
