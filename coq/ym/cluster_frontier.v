(* =========================================================================
   cluster_frontier.v - YM Cluster Analysis Frontier Interface

   Collects the analytic cluster-expansion frontiers:
   - neighbor enumeration with coordination bound (makes KP explicit)
   - correlator triangle bound
   - pinned-cluster bound (hard Brydges-style frontier)

   CONTRACT:
   These are the only cluster-analysis assumptions consumed by Phase F
   (`coq/ym/small_field.v`) for the lattice mass-gap pillar.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.
Require Import rg.polymer_types.
Require Import rg.cluster_expansion.

Import ListNotations.
Open Scope R_scope.

Section ClusterFrontier.
  Context {P : Type} `{PolymerSystem P} `{MetricSystem P} `{ConnectivitySystem P} `{SummationSystem P}.

  (* =========================================================================
     Neighbor Enumeration Frontier

     This makes kp_sum EXPLICIT as a finite sum over neighbors.
     The key assumption is coordination_bound: each polymer overlaps
     at most 24 others. For 4D plaquettes, this is exact.
     ========================================================================= *)

  Class YMNeighborEnumerationFrontier : Type := {
    (* Enumerate neighbors (polymers that overlap with p) *)
    neighbors : P -> list P;

    (* Spec: neighbors lists exactly the overlapping polymers *)
    neighbors_spec : forall p q, In q (neighbors p) <-> overlap p q;

    (* Coordination bound: at most 24 neighbors per polymer *)
    (* For 4D plaquettes: 4 links * 6 plaquettes per link = 24 *)
    coordination_bound : forall p, INR (length (neighbors p)) <= 24
  }.

  Context `{YMNeighborEnumerationFrontier}.

  (* Explicit KP sum: actual sum over neighbors *)
  Definition kp_sum_explicit (a : R) (p : P) : R :=
    fold_right Rplus 0
      (map (fun q => Rabs (activity q) * exp (a * size q)) (neighbors p)).

  (* Helper: fold_right Rplus over nonneg terms is nonneg *)
  Lemma fold_right_Rplus_nonneg : forall (l : list R),
    (forall x, In x l -> x >= 0) ->
    fold_right Rplus 0 l >= 0.
  Proof.
    intros l Hnonneg.
    induction l as [|h t IH].
    - simpl. lra.
    - simpl. assert (Hh : h >= 0) by (apply Hnonneg; left; reflexivity).
      assert (Ht : fold_right Rplus 0 t >= 0).
      { apply IH. intros x Hx. apply Hnonneg. right. exact Hx. }
      lra.
  Qed.

  (* Helper: fold_right Rplus bound by length * max *)
  Lemma fold_right_Rplus_bound : forall (l : list R) (M : R),
    (forall x, In x l -> x <= M) ->
    M >= 0 ->
    fold_right Rplus 0 l <= INR (length l) * M.
  Proof.
    intros l M Hbound HM.
    induction l as [|h t IH].
    - simpl. lra.
    - simpl fold_right. simpl length.
      assert (Hh : h <= M) by (apply Hbound; left; reflexivity).
      assert (Ht : fold_right Rplus 0 t <= INR (length t) * M).
      { apply IH. intros x Hx. apply Hbound. right. exact Hx. }
      rewrite S_INR. lra.
  Qed.

  (* KP sum is bounded by coordination * max activity term *)
  Lemma kp_sum_explicit_bound : forall (a : R) (p : P) (K_max : R),
    a > 0 ->
    (forall q, In q (neighbors p) -> Rabs (activity q) * exp (a * size q) <= K_max) ->
    K_max >= 0 ->
    kp_sum_explicit a p <= 24 * K_max.
  Proof.
    intros a p K_max Ha Hterm HKmax.
    unfold kp_sum_explicit.
    set (l := map (fun q => Rabs (activity q) * exp (a * size q)) (neighbors p)).
    apply Rle_trans with (INR (length l) * K_max).
    - apply fold_right_Rplus_bound.
      + intros x Hx. unfold l in Hx.
        apply in_map_iff in Hx.
        destruct Hx as [q [Heq Hin]].
        rewrite <- Heq. apply Hterm. exact Hin.
      + exact HKmax.
    - unfold l. rewrite map_length.
      apply Rmult_le_compat_r.
      + lra.
      + apply coordination_bound.
  Qed.

  (* NOTE: YMKPSumFrontier removed - kp_sum is now kp_sum_explicit *)

  (* =========================================================================
     Cluster Analysis Frontier (Reduced)

     NOTE: The 3 sum algebra properties (monotone, triangle, scale) are now
     LEMMAS in cluster_expansion.v, not hypotheses! They're proved from the
     concrete finite sum implementation.

     Only the tree-graph bound remains as a frontier.
     ========================================================================= *)

  (* Finite volume parameters needed for sum_connecting *)
  Variable polymers_Λ : list P.
  Variable N_max : nat.
  Variable connects_dec : forall (X : Cluster P) (p1 p2 : P),
    {connects X p1 p2} + {~ connects X p1 p2}.

  Class YMClusterAnalysisFrontier : Prop := {
    (* The ONLY remaining frontier: tree-graph bound (Brydges inequality) *)
    ym_connecting_bounded_by_pinned_frontier :
      forall (a : R) (p1 p2 : P),
        a > 0 ->
        kp_sum_condition a ->
        sum_connecting polymers_Λ N_max connects_dec p1 p2
          (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X)) <=
        exp (a * size p1) * exp (a * size p2)
  }.
End ClusterFrontier.
