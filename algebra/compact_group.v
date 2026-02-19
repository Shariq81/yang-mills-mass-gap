(* =========================================================================
   compact_group.v - Abstract Interface for Compact Lie Groups
   
   This module defines the typeclasses required to formulate Wilson lattice 
   gauge theory for a general compact group G (e.g. U(1), SU(2), SU(3)).

   Layers:
   1. Algebraic Group Structure
   2. Haar Integration (Single Group)
   3. Class Functions & Kernels (Wilson Action Support)
   
   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.
Open Scope R_scope.

(* =========================================================================
   1. Algebraic Group Structure
   ========================================================================= *)

Class Group (G : Type) := {
  gmul : G -> G -> G;
  gone : G;
  ginv : G -> G;

  (* Group axioms *)
  gmul_assoc : forall a b c, gmul a (gmul b c) = gmul (gmul a b) c;
  gmul_one_l : forall a, gmul gone a = a;
  gmul_one_r : forall a, gmul a gone = a;
  gmul_left_inv : forall a, gmul (ginv a) a = gone;
  gmul_right_inv : forall a, gmul a (ginv a) = gone;
  
  (* Optional: Involutive inverse (usually provable from axioms but nice to have) *)
  ginv_involutive : forall a, ginv (ginv a) = a
}.

(* Helper notation *)
Declare Scope group_scope.
Infix "*" := gmul : group_scope.
Notation "1" := gone : group_scope.
Notation "/ x" := (ginv x) : group_scope.
Open Scope group_scope.

(* =========================================================================
   2. Haar Integration (Single Group)
   ========================================================================= *)

(* Abstract integration functional on G -> R *)
Class HaarIntegral (G : Type) `{Group G} := {
  haar : (G -> R) -> R;

  (* Linearity *)
  haar_linear_add   : forall f g, haar (fun x => f x + g x) = haar f + haar g;
  haar_linear_scale : forall c f, haar (fun x => c * f x) = c * haar f;

  (* Positivity *)
  haar_nonneg : forall f, (forall x, f x >= 0) -> haar f >= 0;
  
  (* Normalization *)
  haar_normalized : haar (fun _ => 1) = 1;

  (* Invariance *)
  haar_left_invariant  : forall a f, haar (fun x => f (a * x)) = haar f;
  haar_right_invariant : forall a f, haar (fun x => f (x * a)) = haar f;
  haar_inv_invariant   : forall f, haar (fun x => f (/ x)) = haar f;
  
  (* Extensionality (usually needed for functional manipulation) *)
  haar_ext : forall f g, (forall x, f x = g x) -> haar f = haar g
}.

(* =========================================================================
   3. Class Functions & Kernels (Wilson Action Support)
   ========================================================================= *)

(* Real-valued class function (trace-like) used in Wilson action *)
(* For SU(N), usually Re(Tr(U)) / N *)
Class WilsonClassFunction (G : Type) `{Group G} := {
  phi : G -> R;

  (* Symmetry properties *)
  phi_inv : forall g, phi (/ g) = phi g;
  phi_conj : forall g h, phi (h * g * / h) = phi g;
  
  (* Boundedness (useful for convergence) *)
  phi_bound : exists M, forall g, Rabs (phi g) <= M
}.

(* Positive Definite Kernel Definition *)
(* A kernel K(x,y) is positive definite if the Gram matrix is PSD *)
Definition posdef_kernel {X : Type} (K : X -> X -> R) : Prop :=
  forall (n : nat) (xs : nat -> X) (cs : nat -> R),
    let S := seq 0 n in
    (* Custom sum helper to avoid dependency on complex list libs *)
    let sum_list l := fold_right Rplus 0 l in
    sum_list (map (fun i => 
      sum_list (map (fun j => 
        cs i * cs j * K (xs i) (xs j)
      ) S)
    ) S) >= 0.

(* Heat Kernel Positivity Axiom Package *)
(* The heat kernel exp(beta * phi(g h^-1)) must be positive definite *)
Class HeatKernelPosDef (G : Type) `{Group G} `{WilsonClassFunction G} := {
  heat_kernel : R -> G -> G -> R := 
    fun beta g h => exp (beta * phi (g * / h));

  heat_kernel_posdef :
    forall beta, beta >= 0 -> posdef_kernel (heat_kernel beta)
}.
