(* =========================================================================
   polymer_norms.v - Abstract Polymer Activity Norms for RG

   Defines the Banach space structure for polymer activities K.
   Used to formulate rigorous RG contraction bounds.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.

Open Scope R_scope.

(* Abstract Type for Polymer Activities *)
(* Ideally this is (Polymer -> (Field -> R)) *)
Parameter Activity : Type.

(* Norm on Activities *)
(* We assume a family of norms indexed by scale k *)
Parameter activity_norm : nat -> Activity -> R.

(* Properties of the norm *)
Axiom activity_norm_nonneg : forall k K, activity_norm k K >= 0.
Axiom activity_norm_zero : forall k, activity_norm k (fun _ => 0) = 0. (* conceptual *)

(* The RG Operator *)
Parameter RG_map : nat -> Activity -> Activity.

(* The Critical Bounds (To be proven in gaussian_integration_bounds.v etc) *)

(* 1. Rescaling / Renormalization Bound *)
(* || R(K) || <= L^-eps || K || *)
Parameter contraction_factor : R.
Axiom contraction_factor_bound : 0 < contraction_factor < 1.

(* 2. Nonlinear Feedback Bound *)
(* || T(K) || <= ||K|| + C ||K||^2 *)
Parameter nonlinear_const : R.
Axiom nonlinear_const_pos : nonlinear_const > 0.

(* Combined One-Step Bound *)
(* || K_{k+1} || <= rho * || K_k || + C * || K_k ||^2 + error *)
Parameter error_term : nat -> R -> R. (* scale -> beta -> error *)

Axiom rg_step_bound :
  forall k beta (K : Activity),
    activity_norm (S k) (RG_map k K) <=
    contraction_factor * activity_norm k K +
    nonlinear_const * (activity_norm k K)^2 +
    error_term k beta.
