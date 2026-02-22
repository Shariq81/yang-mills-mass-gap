(* =========================================================================
   apex_harness.v - Standardized Import Harness for APEX Daemon

   PURPOSE: Provides a single, stable import environment for all APEX-generated
   proof attempts. This eliminates "missing import" failures and ensures
   consistent scope/notation setup.

   USAGE: All APEX test files should begin with:
     From algebra Require Import apex_harness.

   Then only the goal + Proof. <tactic>. Qed.

   Author: APEX
   Date: 2026-02-20
   ========================================================================= *)

(* =========================================================================
   Part 1: Core Coq Stdlib - Real Analysis
   ========================================================================= *)

From Coq Require Export Reals Rfunctions Rpower.
From Coq Require Export Rseries SeqProp Exp_prop.
From Coq Require Export R_sqrt Rtrigo_def.
From Coq Require Export Arith Lia Lra.
From Coq Require Export Psatz.  (* nra tactic *)

(* =========================================================================
   Part 2: Logic and Classical Reasoning
   ========================================================================= *)

From Coq Require Export Logic.ClassicalEpsilon.
From Coq Require Export Logic.FunctionalExtensionality.
From Coq Require Export Logic.Classical_Prop.
From Coq Require Export Logic.Decidable.

(* =========================================================================
   Part 3: Data Structures
   ========================================================================= *)

From Coq Require Export List.
Import ListNotations.
From Coq Require Export Bool.

(* =========================================================================
   Part 4: Open Scopes
   ========================================================================= *)

Open Scope R_scope.

(* =========================================================================
   Part 5: APEX Hint Database

   All proven lemmas should be added here via:
     Hint Resolve lemma_name : apex.

   Then daemon uses: eauto with apex.
   ========================================================================= *)

Create HintDb apex discriminated.

(* Add standard real analysis lemmas *)
Hint Resolve Rle_refl Rle_trans Rlt_le : apex.
Hint Resolve Rplus_le_compat Rmult_le_pos : apex.
Hint Resolve pow_le exp_pos : apex.
Hint Resolve Rinv_0_lt_compat : apex.

(* =========================================================================
   Part 6: Common Tactic Notations
   ========================================================================= *)

(* Safe version of lra that doesn't loop *)
Ltac safe_lra := timeout 5 lra.
Ltac safe_nra := timeout 10 nra.

(* Try multiple tactics, return first success *)
Ltac apex_auto :=
  first [ assumption
        | reflexivity
        | safe_lra
        | safe_nra
        | eauto with apex
        | trivial ].

(* Destruct with cleanup *)
Ltac apex_destruct H :=
  destruct H; try apex_auto.

(* =========================================================================
   Part 7: Re-export Algebra Modules (when compiled)

   NOTE: These are commented out initially. Uncomment as files are sealed.
   ========================================================================= *)

(* From algebra Require Export bessel_positivity. *)
(* From algebra Require Export peter_weyl. *)
(* From algebra Require Export schur_orthogonality. *)

(* =========================================================================
   Part 8: Common Helper Lemmas
   ========================================================================= *)

(* Factorial helpers *)
Lemma fact_R_pos : forall n, INR (fact n) > 0.
Proof.
  intros n. apply lt_0_INR.
  induction n; simpl; lia.
Qed.

Lemma fact_ge_1_nat : forall n, (fact n >= 1)%nat.
Proof.
  induction n; simpl; lia.
Qed.

Lemma fact_R_ge_1 : forall n, INR (fact n) >= 1.
Proof.
  intros n.
  apply Rle_ge.
  replace 1 with (INR 1) by reflexivity.
  apply le_INR.
  apply fact_ge_1_nat.
Qed.

Hint Resolve fact_R_pos fact_R_ge_1 : apex.

(* Sum helpers *)
Lemma sum_f_R0_nonneg : forall f n,
  (forall k, (k <= n)%nat -> f k >= 0) ->
  sum_f_R0 f n >= 0.
Proof.
  intros f n Hf.
  induction n as [|n IH].
  - simpl. apply Hf. lia.
  - simpl.
    assert (H1 : sum_f_R0 f n >= 0).
    { apply IH. intros k Hk. apply Hf. lia. }
    assert (H2 : f (S n) >= 0) by (apply Hf; lia).
    lra.
Qed.

Hint Resolve sum_f_R0_nonneg : apex.

(* =========================================================================
   Part 9: Canonical Solve Tactics for Common Goal Shapes
   ========================================================================= *)

(* For goals of form: P \/ Q *)
Ltac apex_or :=
  first [ left; apex_auto | right; apex_auto ].

(* For goals with decidable equality *)
Ltac apex_eq_dec dec :=
  destruct dec as [?Heq | ?Hneq];
  [ subst; try apex_auto | try apex_auto ].

(* For induction on nat *)
Ltac apex_nat_induction n :=
  induction n as [|n IH]; simpl; try apex_auto.

(* For induction on list *)
Ltac apex_list_induction l :=
  induction l as [|x xs IH]; simpl; try apex_auto.

(* =========================================================================
   HARNESS VERIFICATION

   This lemma should always compile. If it fails, the harness is broken.
   ========================================================================= *)

Lemma apex_harness_ok : True.
Proof. exact I. Qed.

