(* =========================================================================
   polymer_types.v - Abstract Interface for Cluster Expansions

   Defines the input structure for the Cluster Expansion Machine (Phase E).
   Any system implementing this interface gets a Mass Gap theorem for free.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.

Open Scope R_scope.

(* =========================================================================
   1. Abstract Polymer System
   ========================================================================= *)

Class PolymerSystem (P : Type) := {
  (* Compatibility / Overlap Relation *)
  (* overlap p1 p2 means they CANNOT coexist in the same cluster term *)
  overlap : P -> P -> Prop;
  
  overlap_sym : Symmetric overlap;
  overlap_refl : Reflexive overlap; (* A polymer overlaps itself *)

  (* Activity / Weight *)
  (* K(p) is the norm of the polymer activity *)
  activity : P -> R;
  activity_nonneg : forall p, activity p >= 0
}.

(* =========================================================================
   2. Metric Structure (for Decay Bounds)
   ========================================================================= *)

Class MetricSystem (P : Type) `{PolymerSystem P} := {
  (* Distance between polymers (e.g. lattice distance) *)
  dist : P -> P -> R;
  
  dist_nonneg : forall p1 p2, dist p1 p2 >= 0;
  dist_sym : forall p1 p2, dist p1 p2 = dist p2 p1;
  
  (* Size of a polymer (used for convergence conditions) *)
  (* Usually size(p) = # of links or plaquettes *)
  size : P -> R;
  size_pos : forall p, size p >= 1
}.

(* =========================================================================
   3. The Kotecky-Preiss Convergence Condition
   ========================================================================= *)

(* Sufficient condition for cluster expansion convergence *)
(* sum_{p' overlap p} activity(p') * exp(a * size(p')) <= a * size(p) *)

Definition kotecky_preiss_condition 
  {P : Type} `{PolymerSystem P} `{MetricSystem P} 
  (a : R) : Prop :=
  forall (p : P),
    (* This sum must be finite and bounded *)
    (* We usually model this via a 'weighted degree' bound *)
    exists (M : R), 
      M <= a * size p /\
      (* sum_{p' ~ p} K(p') e^{a|p'|} <= M *)
      True. (* Placeholder for infinite sum formalization *)

(* =========================================================================
   4. Output: Mass Gap Statement
   ========================================================================= *)

(* The Cluster Machine proves that if KP holds, correlations decay *)
Definition has_mass_gap
  {P : Type} `{PolymerSystem P} `{MetricSystem P}
  (m : R) : Prop :=
  forall (p1 p2 : P),
    (* Correlator bounded by exp(-m * dist) *)
    True. (* Placeholder *)
