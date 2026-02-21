(* ========================================================================= *)
(* transfer_matrix.v                                                         *)
(*                                                                           *)
(* Minimal transfer-matrix interface for replacing "spectral_gap_equals..."   *)
(* without spectral measures.                                                 *)
(*                                                                           *)
(* L1: Transfer matrix data + Tpow                                            *)
(* L3: Correlator = matrix element (as an interface hook)                     *)
(* L4: Decay -> contraction on vacuum-orthogonal subspace (hard analytic)     *)
(*                                                                           *)
(* Author: APEX                                                               *)
(* Date: 2026-02-21                                                           *)
(* ========================================================================= *)

From Coq Require Import Reals Lra List.
Import ListNotations.
Open Scope R_scope.

(* ------------------------------------------------------------------------- *)
(* Basic power operator                                                      *)
(* ------------------------------------------------------------------------- *)

Section Powers.

Context {H : Type}.
Variable T : H -> H.

Fixpoint Tpow (n : nat) (v : H) : H :=
  match n with
  | O => v
  | S k => T (Tpow k v)
  end.

Lemma Tpow_0 : forall v, Tpow 0 v = v.
Proof. reflexivity. Qed.

Lemma Tpow_S : forall n v, Tpow (S n) v = T (Tpow n v).
Proof. reflexivity. Qed.

(* Composition law: T^{n+m} = T^n . T^m *)
Lemma Tpow_add : forall n m v, Tpow (n + m) v = Tpow n (Tpow m v).
Proof.
  induction n as [|n' IH]; intros m v; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

End Powers.

(* ------------------------------------------------------------------------- *)
(* Transfer-matrix signature                                                 *)
(* ------------------------------------------------------------------------- *)

Module Type TransferMatrixSig.

  (* State space (can be functions on a slice, but abstract for now) *)
  Parameter H : Type.

  (* Inner product. We assume real inner product for now. *)
  Parameter inner : H -> H -> R.

  (* Vacuum vector *)
  Parameter vacuum : H.

  (* Transfer operator *)
  Parameter T : H -> H.

  (* Observable insertion: v |-> O v or a distinguished vector O|0> *)
  Parameter obs_insert : H -> H.

  (* --- Basic inner product laws (minimal pre-Hilbert-ish) --- *)

  Axiom inner_sym : forall u v, inner u v = inner v u.

  (* Positivity on diagonal (semi-definite is enough for now) *)
  Axiom inner_pos : forall v, inner v v >= 0.

  (* Vacuum normalized (optional but convenient) *)
  Axiom vacuum_norm1 : inner vacuum vacuum = 1.

  (* --- Transfer operator properties (L2 targets) --- *)

  (* Self-adjointness *)
  Axiom T_selfadjoint : forall u v, inner u (T v) = inner (T u) v.

  (* Positivity (quadratic form) *)
  Axiom T_positive : forall v, inner v (T v) >= 0.

  (* Contraction (often follows from reflection positivity + normalization) *)
  Axiom T_contractive :
    forall v, inner (T v) (T v) <= inner v v.

  (* --- L3: Correlator hook (to be proved from time-slice construction) --- *)
  (* Keep correlator abstract here; spectral_gap_bridge will instantiate it. *)
  Parameter Correlator : nat -> R.

  Axiom correlator_as_matrix_element :
    forall n : nat,
      Correlator n =
        inner (obs_insert vacuum) (Tpow T n (obs_insert vacuum)).

End TransferMatrixSig.

(* ------------------------------------------------------------------------- *)
(* Vacuum-orthogonal subspace + decay-to-gap statement shape (L4/L5 targets)  *)
(* ------------------------------------------------------------------------- *)

Module TransferMatrixTheory (TM : TransferMatrixSig).

  Import TM.

  Definition orthogonal_to_vacuum (v : H) : Prop :=
    inner v vacuum = 0.

  (* A very lightweight "norm" - enough to state contraction inequalities. *)
  Definition norm2 (v : H) : R := inner v v.

  (* "Exponential decay of the correlator" phrased on the Correlator sequence. *)
  Definition has_correlator_decay (m C : R) : Prop :=
    m > 0 /\ C > 0 /\
    forall n : nat,
      Rabs (Correlator n) <= C * exp (- m * INR n).

  (* A proxy notion of "gap m" in transfer-matrix terms:
     the vacuum-excited vector obs_insert vacuum decays at rate m. *)
  Definition has_transfer_gap_on_observable (m : R) : Prop :=
    exists C : R, C > 0 /\
      forall n : nat,
        Rabs (inner (obs_insert vacuum) (Tpow T n (obs_insert vacuum)))
        <= C * exp (- m * INR n).

  (* L4: Hard analytic lemma (placeholder statement).
     In your final system, you will likely replace this with a stronger statement
     about contraction on the entire vacuum-orthogonal subspace, but this is
     the minimal bridge you need to eliminate the old axiom.

     If you assume correlator_as_matrix_element, then correlator decay implies
     transfer-gap-on-observable immediately by rewriting.
  *)
  Lemma correlator_decay_implies_transfer_gap_on_observable :
    forall m C,
      has_correlator_decay m C ->
      has_transfer_gap_on_observable m.
  Proof.
    intros m C Hdec.
    unfold has_correlator_decay in Hdec.
    destruct Hdec as [Hm [HC Hbound]].
    exists C. split; [exact HC|].
    intro n.
    (* rewrite correlator into matrix element *)
    rewrite <- (correlator_as_matrix_element n).
    apply Hbound.
  Qed.

  (* If you later define a stronger "uniform gap" notion, it can live here too. *)
  Definition has_uniform_gap (m : R) : Prop :=
    (* placeholder: upgrade later to a statement about the restriction of T *)
    has_transfer_gap_on_observable m.

End TransferMatrixTheory.

(* ------------------------------------------------------------------------- *)
(* Slice-indexed correlator bridge                                           *)
(*                                                                           *)
(* Your current correlator is: correlator : Plaquette -> Plaquette -> R      *)
(* The transfer matrix formalism uses: Correlator : nat -> R                  *)
(*                                                                           *)
(* The connection: for plaquettes p1, p2 with time separation t,              *)
(*   correlator p1 p2 = Correlator t   (up to normalization)                  *)
(*                                                                           *)
(* This section provides the bridge definitions.                              *)
(* ------------------------------------------------------------------------- *)

Section SliceCorrelatorBridge.

  (* Time coordinate extraction *)
  Parameter time_of_plaq : Type -> Z.

  (* Your existing correlator *)
  Parameter plaq_correlator : Type -> Type -> R.

  (* Reference plaquette at time 0 (for defining Correlator(n)) *)
  Parameter reference_plaq_at_time : Z -> Type.

  (* The bridge: Correlator n = correlator of ref plaq at 0 and ref plaq at n *)
  Definition Correlator_from_plaq (n : nat) : R :=
    plaq_correlator (reference_plaq_at_time 0%Z)
                    (reference_plaq_at_time (Z.of_nat n)).

  (* Key property: correlator only depends on time separation
     (translation invariance in Euclidean time) *)
  (* This would be proved from your lattice structure *)

End SliceCorrelatorBridge.

(* ------------------------------------------------------------------------- *)
(* Notes on instantiation                                                    *)
(*                                                                           *)
(* To instantiate TransferMatrixSig from your lattice:                        *)
(*                                                                           *)
(* 1. H := SliceConfig L -> R   (functions on slice configurations)           *)
(*    where SliceConfig L is the type of link assignments on t=0 hyperplane   *)
(*                                                                           *)
(* 2. inner f g := fold_right Rplus 0                                         *)
(*                   (map (fun sigma => f sigma * g sigma) all_slice_configs)  *)
(*                                                                           *)
(* 3. vacuum := fun sigma => Z_0^{-1/2} * exp(-S_0(sigma)/2)                  *)
(*    where S_0 is the slice action and Z_0 normalizes                        *)
(*                                                                           *)
(* 4. T := defined via transfer_kernel from slab cluster weights              *)
(*    (T f)(sigma') = sum_sigma K(sigma, sigma') * f(sigma)                   *)
(*                                                                           *)
(* 5. obs_insert := multiplication by local observable O(sigma)               *)
(*                                                                           *)
(* The axioms T_selfadjoint, T_positive, T_contractive follow from            *)
(* reflection positivity (your plaq_is_crossing machinery in lattice.v).      *)
(* ------------------------------------------------------------------------- *)
