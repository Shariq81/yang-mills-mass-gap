(* Test file for ursell factor bound proofs *)

From Coq Require Import Reals.
From Coq Require Import Lra.
From Coq Require Import List.
Import ListNotations.

Open Scope R_scope.

(* Simplified ursell bound proof structure *)

Section UrsellBoundTest.

  Variable P : Type.
  Variable overlap : P -> P -> Prop.
  Variable overlap_dec : forall p q, {overlap p q} + {~ overlap p q}.

  (* Hard-core Mayer function *)
  Definition zeta_hc (u v : P) : R :=
    if overlap_dec u v then (-1) else 0.

  Lemma zeta_hc_abs_le_1 : forall u v, Rabs (zeta_hc u v) <= 1.
  Proof.
    intros u v. unfold zeta_hc.
    destruct (overlap_dec u v).
    - unfold Rabs. destruct (Rcase_abs (-1)); lra.
    - rewrite Rabs_R0. lra.
  Qed.

  Lemma one_plus_zeta_hc_is_0_or_1 :
    forall u v, (1 + zeta_hc u v = 0) \/ (1 + zeta_hc u v = 1).
  Proof.
    intros u v. unfold zeta_hc.
    destruct (overlap_dec u v); [left | right]; lra.
  Qed.

  (* Closure factor: product of (1 + zeta_hc) *)
  Fixpoint closure_factor (edges : list (P * P)) : R :=
    match edges with
    | [] => 1
    | e :: es => (1 + zeta_hc (fst e) (snd e)) * closure_factor es
    end.

  (* KEY: closure_factor is 0 or 1 *)
  Lemma closure_factor_is_0_or_1 :
    forall edges, closure_factor edges = 0 \/ closure_factor edges = 1.
  Proof.
    induction edges as [| e es IH].
    - right. reflexivity.
    - simpl.
      destruct (one_plus_zeta_hc_is_0_or_1 (fst e) (snd e)) as [Hz | Hz].
      + left. rewrite Hz. lra.
      + destruct IH as [IH0 | IH1].
        * left. rewrite IH0. lra.
        * right. rewrite Hz, IH1. lra.
  Qed.

  Lemma closure_factor_le_1 : forall edges, closure_factor edges <= 1.
  Proof.
    intro edges.
    destruct (closure_factor_is_0_or_1 edges) as [H0 | H1]; lra.
  Qed.

  Lemma closure_factor_nonneg : forall edges, 0 <= closure_factor edges.
  Proof.
    intro edges.
    destruct (closure_factor_is_0_or_1 edges) as [H0 | H1]; lra.
  Qed.

  (* Graph weight: product of zeta_hc *)
  Fixpoint graph_weight (edges : list (P * P)) : R :=
    match edges with
    | [] => 1
    | e :: es => zeta_hc (fst e) (snd e) * graph_weight es
    end.

  (* Graph abs weight: product of |zeta_hc| *)
  Fixpoint graph_abs_weight (edges : list (P * P)) : R :=
    match edges with
    | [] => 1
    | e :: es => Rabs (zeta_hc (fst e) (snd e)) * graph_abs_weight es
    end.

  Lemma graph_abs_weight_nonneg : forall edges, 0 <= graph_abs_weight edges.
  Proof.
    induction edges as [| e es IH]; simpl.
    - lra.
    - apply Rmult_le_pos; [apply Rabs_pos | exact IH].
  Qed.

  Lemma graph_abs_weight_le_1 : forall edges, graph_abs_weight edges <= 1.
  Proof.
    induction edges as [| e es IH]; simpl.
    - lra.
    - pose proof (zeta_hc_abs_le_1 (fst e) (snd e)) as Hz.
      pose proof (graph_abs_weight_nonneg es) as Hnn.
      nra.
  Qed.

  (* For each tree T, its contribution is bounded by 1 *)
  Lemma tree_contribution_bound :
    forall T_edges A_edges,
      graph_abs_weight T_edges * closure_factor A_edges <= 1.
  Proof.
    intros T_edges A_edges.
    pose proof (graph_abs_weight_le_1 T_edges) as HT.
    pose proof (graph_abs_weight_nonneg T_edges) as HTnn.
    pose proof (closure_factor_le_1 A_edges) as HA.
    pose proof (closure_factor_nonneg A_edges) as HAnn.
    nra.
  Qed.

End UrsellBoundTest.

(* Qed count: 10 *)
