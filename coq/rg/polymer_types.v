(* =========================================================================
   polymer_types.v - Abstract Interface for Cluster Expansions

   Defines the input structure for the Cluster Expansion Machine (Phase E).
   Any system implementing this interface gets a Mass Gap theorem for free.

   Author: APEX
   Date: 2026-02-19
   Updated: 2026-02-19 - Real has_mass_gap definition (no placeholders)
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
   3. Connectivity Structure (for Cluster Definitions)

   Adjacency relation for defining "connecting clusters". This is SEPARATE
   from overlap (incompatibility). Two polymers can be adjacent (share a
   boundary) without overlapping (being incompatible).

   In lattice gauge theory:
   - overlap = share a vertex/link (incompatibility for Mayer expansion)
   - adj = share a link (connectivity for cluster paths)
   These may or may not be the same depending on the model.
   ========================================================================= *)

Class ConnectivitySystem (P : Type) := {
  (* Adjacency: polymers that can be consecutive in a cluster path *)
  adj : P -> P -> Prop;

  adj_dec : forall p1 p2, {adj p1 p2} + {~ adj p1 p2};
  adj_sym : forall p1 p2, adj p1 p2 -> adj p2 p1
}.

(* =========================================================================
   4. Summation Structure (Abstract Integration)
   ========================================================================= *)

Class SummationSystem (P : Type) := {
  (* Abstract summation over polymers p' that overlap with p *)
  (* sum_overlap p f = sum_{p' : p' ~ p} f(p') *)
  sum_overlap : P -> (P -> R) -> R;

  (* Properties of the sum *)
  sum_overlap_nonneg : forall p f,
    (forall p', 0 <= f p') -> 0 <= sum_overlap p f;

  sum_overlap_linear : forall p c f,
    sum_overlap p (fun p' => c * f p') = c * sum_overlap p f
}.

(* =========================================================================
   5. The Kotecky-Preiss Convergence Condition
   ========================================================================= *)

(* Real KP Condition:
   sum_{p' ~ p} |K(p')| * exp(a * size(p')) <= a * size(p) *)

Definition kotecky_preiss_condition 
  {P : Type} `{PolymerSystem P} `{MetricSystem P} `{SummationSystem P}
  (a : R) : Prop :=
  forall (p : P),
    sum_overlap p (fun p' => activity p' * exp (a * size p')) <= a * size p.

(* =========================================================================
   6. Output: Mass Gap Statement (REAL - NOT PLACEHOLDER)
   ========================================================================= *)

(* The mass gap is defined as exponential decay of the connected correlator.

   correlator(p1, p2) := sum over clusters connecting p1 to p2 of cluster_weight(X)

   has_mass_gap correlator m means:
     exists C > 0 such that |correlator(p1, p2)| <= C * exp(-m * dist(p1, p2))

   This is the standard definition from constructive quantum field theory. *)

Definition has_mass_gap
  {P : Type} `{PolymerSystem P} `{MetricSystem P}
  (correlator : P -> P -> R) (m : R) : Prop :=
  exists C, C > 0 /\
  forall p1 p2,
    Rabs (correlator p1 p2) <= C * exp (- m * dist p1 p2).
