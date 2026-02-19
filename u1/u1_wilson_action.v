(* =========================================================================
   u1_wilson_action.v - Wilson Action, Partition Function, Expectation

   Tier 0 minimal stack: explicit Wilson action for U(1).
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.
From Coq Require Import FunctionalExtensionality.

Require Import U1.u1_lattice.
Require Import U1.u1_integral.
Import U1Lattice.
Import U1Integral.

Import ListNotations.
Open Scope R_scope.

Module U1WilsonAction.

(* =========================================================================
   Part 1: Plaquette Angle (Lattice Curl)

   For U(1), the plaquette variable is the sum of oriented link angles:
     θ_P = θ(x,μ) + θ(x+μ,ν) - θ(x+ν,μ) - θ(x,ν)

   This is the discrete curl of the gauge field.
   ========================================================================= *)

(* Compute plaquette angle from boundary *)
Definition theta_plaq (U : cfg) (p : plaquette) : R :=
  fold_right (fun (x : link * bool) acc =>
    let (l, sgn) := x in
    acc + (if sgn then U l else - U l))
    0 (plaq_boundary p).

(* Plaquette angle is gauge-invariant under U(1) gauge transformations *)
(* (This is a key property but we won't need it for OS positivity) *)

(* =========================================================================
   Part 2: Wilson Action

   S[U] = β Σ_P (1 - cos θ_P)

   This is non-negative and achieves minimum 0 when all θ_P = 0 (mod 2π).
   ========================================================================= *)

(* Single plaquette contribution *)
Definition plaq_action (beta : R) (theta_P : R) : R :=
  beta * (1 - cos theta_P).

(* Plaquette action is non-negative for β ≥ 0 *)
Lemma plaq_action_nonneg : forall beta theta_P,
  beta >= 0 -> plaq_action beta theta_P >= 0.
Proof.
  intros beta theta_P Hbeta.
  unfold plaq_action.
  assert (Hcos : -1 <= cos theta_P <= 1) by apply COS_bound.
  assert (H1cos : 0 <= 1 - cos theta_P) by lra.
  apply Rle_ge.
  apply Rmult_le_pos; lra.
Qed.

(* Full Wilson action: sum over all plaquettes *)
Definition wilson_action (L : lattice_size) (beta : R) (U : cfg) : R :=
  fold_right (fun p acc => plaq_action beta (theta_plaq U p) + acc)
    0 (all_plaquettes L).

(* Wilson action is non-negative *)
Lemma wilson_action_nonneg : forall L beta U,
  beta >= 0 -> wilson_action L beta U >= 0.
Proof.
  intros L beta U Hbeta.
  unfold wilson_action.
  induction (all_plaquettes L) as [| p ps IH].
  - simpl. lra.
  - simpl.
    assert (Hp : plaq_action beta (theta_plaq U p) >= 0)
      by (apply plaq_action_nonneg; exact Hbeta).
    lra.
Qed.

(* =========================================================================
   Part 3: Boltzmann Weight

   w[U] = exp(-S[U])

   This is strictly positive for any configuration.
   ========================================================================= *)

Definition weight (L : lattice_size) (beta : R) (U : cfg) : R :=
  exp (- wilson_action L beta U).

Lemma weight_pos : forall L beta U,
  weight L beta U > 0.
Proof.
  intros. unfold weight. apply exp_pos.
Qed.

Lemma weight_bounded : forall L beta U,
  beta >= 0 -> weight L beta U <= 1.
Proof.
  intros L beta U Hbeta.
  unfold weight.
  assert (H : wilson_action L beta U >= 0)
    by (apply wilson_action_nonneg; exact Hbeta).
  (* exp(-S) <= exp(0) = 1 when S >= 0 *)
  replace 1 with (exp 0) by apply exp_0.
  destruct (Rtotal_order (- wilson_action L beta U) 0) as [Hlt | [Heq | Hgt]].
  - apply Rlt_le. apply exp_increasing. exact Hlt.
  - rewrite Heq. right. reflexivity.
  - (* This case is impossible since S >= 0 means -S <= 0 *)
    exfalso. lra.
Qed.

(* =========================================================================
   Part 4: Partition Function

   Z = ∫ exp(-S[U]) dU

   where the integral is over all link angles with Haar measure.
   ========================================================================= *)

Definition Z (L : lattice_size) (beta : R) : R :=
  integral_over_cfg L (weight L beta).

(* Partition function is strictly positive *)
Lemma Z_pos : forall L beta,
  Z L beta > 0.
Proof.
  intros L beta. unfold Z.
  apply integral_pos.
  intros U. apply weight_pos.
Qed.

Lemma Z_neq_0 : forall L beta,
  Z L beta <> 0.
Proof.
  intros L beta.
  apply Rgt_not_eq. apply Z_pos.
Qed.

(* =========================================================================
   Part 5: Expectation Value

   E[F] = (1/Z) ∫ F[U] exp(-S[U]) dU

   This is the fundamental object for correlators.
   ========================================================================= *)

Definition expect (L : lattice_size) (beta : R) (F : cfg -> R) : R :=
  (/ Z L beta) * integral_over_cfg L (fun U => F U * weight L beta U).

(* Observable type *)
Definition Obs := cfg -> R.

(* Expectation of constant 1 is 1 *)
Lemma expect_normalized : forall L beta,
  expect L beta (fun _ => 1) = 1.
Proof.
  intros L beta.
  unfold expect.
  replace (fun U => 1 * weight L beta U) with (weight L beta)
    by (apply functional_extensionality; intros; ring).
  unfold Z.
  field.
  apply Z_neq_0.
Qed.

(* Expectation is linear in F *)
Lemma expect_linear_add : forall L beta F G,
  expect L beta (fun U => F U + G U) =
  expect L beta F + expect L beta G.
Proof.
  intros L beta F G.
  unfold expect.
  replace (fun U : cfg => (F U + G U) * weight L beta U)
    with (fun U : cfg => F U * weight L beta U + G U * weight L beta U).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite integral_linear_add.
  ring.
Qed.

Lemma expect_linear_scale : forall L beta c F,
  expect L beta (fun U => c * F U) = c * expect L beta F.
Proof.
  intros L beta c F.
  unfold expect.
  replace (fun U : cfg => (c * F U) * weight L beta U)
    with (fun U : cfg => c * (F U * weight L beta U)).
  2:{
    apply functional_extensionality.
    intro U.
    ring.
  }
  rewrite integral_linear_scale.
  ring.
Qed.

(* Non-negative observables have non-negative expectation *)
Lemma expect_nonneg : forall L beta F,
  (forall U, F U >= 0) ->
  expect L beta F >= 0.
Proof.
  intros L beta F Hpos.
  unfold expect.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply Z_pos.
  - apply Rge_le. apply integral_nonneg.
    intros U. apply Rle_ge. apply Rmult_le_pos.
    + apply Rge_le. apply Hpos.
    + apply Rlt_le. apply weight_pos.
Qed.

(* Strictly positive observables have positive expectation *)
Lemma expect_pos : forall L beta F,
  (forall U, F U > 0) ->
  expect L beta F > 0.
Proof.
  intros L beta F Hpos.
  unfold expect.
  apply Rmult_lt_0_compat.
  - apply Rinv_0_lt_compat. apply Z_pos.
  - apply integral_pos.
    intros U. apply Rmult_lt_0_compat.
    + apply Hpos.
    + apply weight_pos.
Qed.

(* =========================================================================
   Part 6: Two-Point Function (Real Schwinger Function)

   S2(x,y) = ⟨O(x) O(y)⟩ - ⟨O(x)⟩ ⟨O(y)⟩

   This is the connected correlator, the REAL object from Wilson theory.
   ========================================================================= *)

Definition S2_connected (L : lattice_size) (beta : R) (Ox Oy : Obs) : R :=
  expect L beta (fun U => Ox U * Oy U) -
  expect L beta Ox * expect L beta Oy.

End U1WilsonAction.
