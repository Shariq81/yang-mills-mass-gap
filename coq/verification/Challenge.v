(* =========================================================================
   verification/Challenge.v

   FROZEN CHALLENGE FILE (Coq Standard Library ONLY — zero project imports).

   Purpose:
     Defines the exact mathematical objects and target propositions for the
     conditional finite-lattice polymer exponential-decay formalization,
     with ZERO global `Axiom`, `Parameter`, or `Admitted` declarations.
     Every mathematical hypothesis is explicitly visible in the proposition
     signatures below so a mathematician can judge their exact strength
     without inspecting any proof file.

   Trusted Definition Base of this file:
     ONLY Coq 8.18.0 Standard Library modules:
       - Coq.Reals.Reals
       - Coq.ZArith.ZArith
       - Coq.Bool.Bool
       - Coq.Arith.Arith
       - Coq.Lists.List
       - Coq.Classes.RelationClasses

   Scope disclaimer:
     These frozen propositions formalize finite-volume abstract polymer
     cluster-expansion implications (constructive path-distance bounds,
     conditional exponential correlator decay, and the genuine ordered-tuple
     1/n! Ursell Kotecky-Preiss tree-graph theorem) and concrete 4D
     hypercubic lattice plaquette edge-sharing combinatorics and polymer
     exponential decay. They do NOT formalize 4D continuum Yang-Mills
     theory, Wilson action / Haar measure, Osterwalder-Schrader
     reconstruction, or the Clay Millennium Prize Problem.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Classes.RelationClasses.

Import ListNotations.
Open Scope R_scope.

Module Challenge.

  (* =======================================================================
     1. Core Polymer & Cluster Definitions (Stdlib-only)
     ======================================================================= *)

  Definition Cluster (P : Type) : Type := list P.

  (* Path inside a finite cluster X with consecutive adjacent steps. *)
  Inductive path_in_cluster {P : Type} (adj : P -> P -> Prop)
    : Cluster P -> P -> P -> Prop :=
  | path_refl : forall X p, In p X -> path_in_cluster adj X p p
  | path_step : forall X p q r,
      In p X -> adj p q -> path_in_cluster adj X q r ->
      path_in_cluster adj X p r.

  (* A cluster X connects p1 to p2 iff both lie in X and are joined by an
     adj-path inside X. *)
  Definition connects {P : Type} (adj : P -> P -> Prop)
    (X : Cluster P) (p1 p2 : P) : Prop :=
    In p1 X /\ In p2 X /\ path_in_cluster adj X p1 p2.

  (* Finite NoDup-preserving enumeration of ordered clusters of length <= N_max
     drawn from a finite polymer pool `polymers_Λ`. *)
  Fixpoint lists_of_length {P : Type}
    (eq_dec : forall x y : P, {x = y} + {x <> y})
    (k : nat) (pool : list P) : list (list P) :=
    match k with
    | O => [[]]
    | S k' =>
        flat_map
          (fun p =>
             map (cons p) (lists_of_length eq_dec k' (remove eq_dec p pool)))
          pool
    end.

  Fixpoint lists_up_to_length {P : Type}
    (eq_dec : forall x y : P, {x = y} + {x <> y})
    (n : nat) (pool : list P) : list (list P) :=
    match n with
    | O => [[]]
    | S n' =>
        lists_up_to_length eq_dec n' pool ++ lists_of_length eq_dec (S n') pool
    end.

  Definition clusters_Λ_N {P : Type}
    (eq_dec : forall x y : P, {x = y} + {x <> y})
    (polymers_Λ : list P) (N_max : nat) : list (Cluster P) :=
    lists_up_to_length eq_dec N_max polymers_Λ.

  (* Finite sum over all clusters in clusters_Λ_N connecting p1 and p2. *)
  Definition sum_connecting {P : Type} (adj : P -> P -> Prop)
    (eq_dec : forall x y : P, {x = y} + {x <> y})
    (polymers_Λ : list P) (N_max : nat)
    (connects_dec : forall (X : Cluster P) (p1 p2 : P),
        {connects adj X p1 p2} + {~ connects adj X p1 p2})
    (p1 p2 : P) (f : Cluster P -> R) : R :=
    fold_right Rplus 0
      (map (fun X => if connects_dec X p1 p2 then f X else 0)
           (clusters_Λ_N eq_dec polymers_Λ N_max)).

  (* Product of activities along a cluster. *)
  Fixpoint prod_activity {P : Type} (activity : P -> R) (c : Cluster P) : R :=
    match c with
    | [] => 1
    | p :: rest => activity p * prod_activity activity rest
    end.

  (* Cluster weight = Ursell factor * product of polymer activities. *)
  Definition cluster_weight {P : Type}
    (ursell_factor : list P -> R) (activity : P -> R) (c : Cluster P) : R :=
    ursell_factor c * prod_activity activity c.

  (* Total size of a cluster. *)
  Fixpoint cluster_size {P : Type} (size : P -> R) (c : Cluster P) : R :=
    match c with
    | [] => 0
    | p :: rest => size p + cluster_size size rest
    end.

  (* Finite-volume connected polymer two-point correlator. *)
  Definition correlator {P : Type} (adj : P -> P -> Prop)
    (eq_dec : forall x y : P, {x = y} + {x <> y})
    (polymers_Λ : list P) (N_max : nat)
    (connects_dec : forall (X : Cluster P) (p1 p2 : P),
        {connects adj X p1 p2} + {~ connects adj X p1 p2})
    (ursell_factor : list P -> R) (activity : P -> R)
    (p1 p2 : P) : R :=
    sum_connecting adj eq_dec polymers_Λ N_max connects_dec p1 p2
      (cluster_weight ursell_factor activity).

  (* Kotecky-Preiss overlap sum condition at parameter a. *)
  Definition kotecky_preiss_condition {P : Type}
    (activity : P -> R) (size : P -> R)
    (sum_overlap : P -> (P -> R) -> R) (a : R) : Prop :=
    forall p : P,
      sum_overlap p (fun p' => activity p' * exp (a * size p')) <= a * size p.

  (* Exponential decay of a two-point correlator at rate m with respect to dist. *)
  Definition has_mass_gap {P : Type} (dist : P -> P -> R)
    (corr : P -> P -> R) (m : R) : Prop :=
    exists C : R, C > 0 /\
      forall p1 p2 : P, Rabs (corr p1 p2) <= C * exp (- m * dist p1 p2).

  (* =======================================================================
     2. Frozen Target Propositions (Zero Global Parameters or Axioms)
     ======================================================================= *)

  (* TARGET 1 (Pure Graph/Metric Theorem — ZERO analytic hypotheses):
     Any cluster X connecting p1 to p2 in a polymer graph with unit-step
     metric distance and polymer size >= 1 satisfies dist(p1, p2) <= size(X).
     (Backed by constructive BFS / simple-path loop erasure.) *)
  Definition Challenge_ConnectsImpliesDistBound : Prop :=
    forall (P : Type)
      (eq_dec : forall x y : P, {x = y} + {x <> y})
      (adj : P -> P -> Prop)
      (adj_dec : forall p1 p2, {adj p1 p2} + {~ adj p1 p2})
      (adj_sym : forall p1 p2, adj p1 p2 -> adj p2 p1)
      (dist : P -> P -> R)
      (dist_nonneg : forall p1 p2, dist p1 p2 >= 0)
      (dist_sym : forall p1 p2, dist p1 p2 = dist p2 p1)
      (dist_refl : forall p, dist p p = 0)
      (dist_triangle : forall p q r, dist p r <= dist p q + dist q r)
      (adj_dist_bound : forall p q, adj p q -> dist p q <= 1)
      (size : P -> R)
      (size_pos : forall p, size p >= 1)
      (X : Cluster P) (p1 p2 : P),
      connects adj X p1 p2 ->
      dist p1 p2 <= cluster_size size X.

  (* TARGET 2 (Clean Conditional Exponential Decay Implication):
     Given the polymer/metric/adjacency structure above, finite-volume cluster
     enumeration (polymers_Λ, N_max), uniform polymer size bound S_max >= 1,
     decay rate a > 0, and the EXPLICIT pinned-cluster exponential-moment
     bound below, the connected correlator satisfies exponential decay with
     explicit prefactor exp(2 * a * S_max) and rate a. *)
  Definition Challenge_ConditionalExponentialDecay : Prop :=
    forall (P : Type)
      (eq_dec : forall x y : P, {x = y} + {x <> y})
      (overlap : P -> P -> Prop)
      (overlap_sym : Symmetric overlap)
      (overlap_refl : Reflexive overlap)
      (activity : P -> R)
      (activity_nonneg : forall p, activity p >= 0)
      (adj : P -> P -> Prop)
      (adj_dec : forall p1 p2, {adj p1 p2} + {~ adj p1 p2})
      (adj_sym : forall p1 p2, adj p1 p2 -> adj p2 p1)
      (dist : P -> P -> R)
      (dist_nonneg : forall p1 p2, dist p1 p2 >= 0)
      (dist_sym : forall p1 p2, dist p1 p2 = dist p2 p1)
      (dist_refl : forall p, dist p p = 0)
      (dist_triangle : forall p q r, dist p r <= dist p q + dist q r)
      (adj_dist_bound : forall p q, adj p q -> dist p q <= 1)
      (size : P -> R)
      (size_pos : forall p, size p >= 1)
      (ursell_factor : list P -> R)
      (ursell_bounded : forall c, Rabs (ursell_factor c) <= 1)
      (polymers_Λ : list P)
      (N_max : nat)
      (connects_dec : forall (X : Cluster P) (p1 p2 : P),
          {connects adj X p1 p2} + {~ connects adj X p1 p2})
      (a S_max : R),
      a > 0 ->
      S_max >= 1 ->
      (forall p : P, size p <= S_max) ->
      (* Explicit analytic hypothesis (Brydges / pinned-cluster moment bound): *)
      (forall p1 p2 : P,
         sum_connecting adj eq_dec polymers_Λ N_max connects_dec p1 p2
           (fun X => Rabs (cluster_weight ursell_factor activity X) *
                     exp (a * cluster_size size X))
         <= exp (a * size p1) * exp (a * size p2)) ->
      forall p1 p2 : P,
        Rabs (correlator adj eq_dec polymers_Λ N_max connects_dec
                ursell_factor activity p1 p2)
        <= exp (2 * a * S_max) * exp (- a * dist p1 p2).

  (* TARGET 3 (Exact Hoisted Form of wightman_mass_gap_master_corollary):
     Matches the specialization used in ym/wightman_mass_gap_master.v
     (unit-size polymers, activity = exp(-beta/10), ursell = 1, beta > 85,
     a <= beta/20, KP at a and 2a, neighbor enumeration with coordination <= 24,
     and the Brydges pinned-cluster bound), with ALL 8 former global parameters
     of ym/small_field.v hoisted into explicit forall quantifiers. *)
  Definition Challenge_MasterConditionalStatement : Prop :=
    forall (P : Type)
      (beta : R)
      (eq_dec : forall x y : P, {x = y} + {x <> y})
      (overlap : P -> P -> Prop)
      (overlap_sym : Symmetric overlap)
      (overlap_refl : Reflexive overlap)
      (adj : P -> P -> Prop)
      (adj_dec : forall p1 p2, {adj p1 p2} + {~ adj p1 p2})
      (adj_sym : forall p1 p2, adj p1 p2 -> adj p2 p1)
      (dist : P -> P -> R)
      (dist_nonneg : forall p1 p2, dist p1 p2 >= 0)
      (dist_sym : forall p1 p2, dist p1 p2 = dist p2 p1)
      (dist_refl : forall p, dist p p = 0)
      (dist_triangle : forall p q r, dist p r <= dist p q + dist q r)
      (adj_dist_bound : forall p q, adj p q -> dist p q <= 1)
      (neighbors : P -> list P)
      (neighbors_spec : forall p q, In q (neighbors p) <-> overlap p q)
      (coordination_bound : forall p, INR (length (neighbors p)) <= 24)
      (polymers_Λ : list P)
      (N_max : nat)
      (connects_dec : forall (X : Cluster P) (p1 p2 : P),
          {connects adj X p1 p2} + {~ connects adj X p1 p2}),
      let activity : P -> R := fun _ => exp (- beta / 10) in
      let size : P -> R := fun _ => 1 in
      let ursell : list P -> R := fun _ => 1 in
      let sum_overlap : P -> (P -> R) -> R :=
        fun p f => fold_right Rplus 0 (map f (neighbors p)) in
      (* Explicit Brydges / pinned-cluster frontier hypothesis: *)
      (forall (a' : R) (p1 p2 : P),
         a' > 0 ->
         beta > 85 ->
         kotecky_preiss_condition activity size sum_overlap a' ->
         (forall q : P,
            sum_overlap q (fun x => activity x * exp (2 * a' * size x)) <= a' * size q) ->
         a' <= beta / 20 ->
         sum_connecting adj eq_dec polymers_Λ N_max connects_dec p1 p2
           (fun X => Rabs (cluster_weight ursell activity X) *
                     exp (a' * cluster_size size X))
         <= exp (a' * size p1) * exp (a' * size p2)) ->
      forall a : R,
        a > 0 ->
        kotecky_preiss_condition activity size sum_overlap a ->
        (forall q : P,
           sum_overlap q (fun x => activity x * exp (2 * a * size x)) <= a * size q) ->
        a <= beta / 20 ->
        beta > 85 ->
        exists m : R, m > 0 /\
          has_mass_gap dist
            (correlator adj eq_dec polymers_Λ N_max connects_dec ursell activity) m.

  (* =======================================================================
     3. Concrete 4D Hypercubic Lattice Z^4 Definitions (Stdlib-only)
     ======================================================================= *)

  Record Site4D : Type := mkSite4D {
    s4_t : Z;
    s4_x : Z;
    s4_y : Z;
    s4_z : Z
  }.

  Inductive Dir4D : Type :=
  | D4_t : Dir4D
  | D4_x : Dir4D
  | D4_y : Dir4D
  | D4_z : Dir4D.

  Definition shift4D (s : Site4D) (d : Dir4D) : Site4D :=
    match d with
    | D4_t => mkSite4D (s4_t s + 1)%Z (s4_x s) (s4_y s) (s4_z s)
    | D4_x => mkSite4D (s4_t s) (s4_x s + 1)%Z (s4_y s) (s4_z s)
    | D4_y => mkSite4D (s4_t s) (s4_x s) (s4_y s + 1)%Z (s4_z s)
    | D4_z => mkSite4D (s4_t s) (s4_x s) (s4_y s) (s4_z s + 1)%Z
    end.

  Record Plaq4D : Type := mkPlaq4D {
    p4_site : Site4D;
    p4_mu   : Dir4D;
    p4_nu   : Dir4D
  }.

  (* The 6 canonical 2-plane orientations mu < nu in 4D. *)
  Definition canonical_planes_4D : list (Dir4D * Dir4D) :=
    [(D4_t, D4_x); (D4_t, D4_y); (D4_t, D4_z);
     (D4_x, D4_y); (D4_x, D4_z); (D4_y, D4_z)].

  (* Well-formedness predicate replacing the legacy `Axiom plaq_wellformed`. *)
  Definition wf_plaq_4D (p : Plaq4D) : Prop :=
    In (p4_mu p, p4_nu p) canonical_planes_4D.

  (* The 4 boundary edges of a unit plaquette (as vertex pairs). *)
  Definition plaq4D_edges (p : Plaq4D) : list (Site4D * Site4D) :=
    let v0 := p4_site p in
    let v1 := shift4D v0 (p4_mu p) in
    let v2 := shift4D v0 (p4_nu p) in
    let v3 := shift4D v1 (p4_nu p) in
    [(v0, v1); (v0, v2); (v1, v3); (v2, v3)].

  (* Unordered-edge equality: avoids any arbitrary tie-breaking order in the spec. *)
  Definition same_undirected_edge (e1 e2 : Site4D * Site4D) : Prop :=
    (fst e1 = fst e2 /\ snd e1 = snd e2) \/
    (fst e1 = snd e2 /\ snd e1 = fst e2).

  (* Two distinct plaquettes share a boundary edge. *)
  Definition plaq4D_shares_edge (p1 p2 : Plaq4D) : Prop :=
    p1 <> p2 /\
    exists e1 e2,
      In e1 (plaq4D_edges p1) /\
      In e2 (plaq4D_edges p2) /\
      same_undirected_edge e1 e2.

  (* Edge-based plaquette overlap (reflexive closure of edge sharing). *)
  Definition plaq4D_overlap (p1 p2 : Plaq4D) : Prop :=
    p1 = p2 \/ plaq4D_shares_edge p1 p2.

  (* TARGET 4a (Pure Constructive 4D Lattice Combinatorics — ZERO axioms total):
     Exact cardinality = 21 (1 self + 4 edges * 5 other plaquettes) with
     NoDup, well-formedness preservation, and sound+complete edge-sharing
     characterization across all of Z^4. *)
  Definition Challenge_Lattice4D_Exact21 : Prop :=
    exists (neighbors : Plaq4D -> list Plaq4D),
      (forall p, wf_plaq_4D p -> NoDup (neighbors p)) /\
      (forall p q, wf_plaq_4D p -> In q (neighbors p) -> wf_plaq_4D q) /\
      (forall p q, wf_plaq_4D p -> wf_plaq_4D q ->
         (In q (neighbors p) <-> plaq4D_overlap p q)) /\
      (forall p, wf_plaq_4D p -> (length (neighbors p) = 21)%nat).

  (* TARGET 4b (Real-valued 24-Coordination Bound matching YMNeighborEnumerationFrontier):
     Adds INR (length (neighbors p)) <= 24 on top of Target 4a.
     ZERO analytic hypotheses, ZERO project axioms. *)
  Definition Challenge_Lattice4D_Coordination24 : Prop :=
    exists (neighbors : Plaq4D -> list Plaq4D),
      (forall p, wf_plaq_4D p -> NoDup (neighbors p)) /\
      (forall p q, wf_plaq_4D p -> In q (neighbors p) -> wf_plaq_4D q) /\
      (forall p q, wf_plaq_4D p -> wf_plaq_4D q ->
         (In q (neighbors p) <-> plaq4D_overlap p q)) /\
      (forall p, wf_plaq_4D p -> (length (neighbors p) = 21)%nat) /\
      (forall p, wf_plaq_4D p -> INR (length (neighbors p)) <= 24).

  (* =======================================================================
     4. Genuine Ordered-Tuple 1/n! Ursell / Kotecky-Preiss Definitions
        (Fernandez-Procacci 2007 sec. 2 / Kotecky-Preiss 1986; Stdlib-only)
     ======================================================================= *)

  (* All ordered n-tuples over Lambda (polymers MAY repeat, as in standard
     Mayer / Kotecky-Preiss expansion of log Z_Lambda). *)
  Fixpoint kp_tuples_of_length {P : Type} (Lambda : list P) (n : nat) : list (list P) :=
    match n with
    | 0%nat => [[]]
    | S n' => flat_map (fun p => map (cons p) (kp_tuples_of_length Lambda n')) Lambda
    end.

  Definition kp_sum_over_tuples {P : Type} (Lambda : list P) (n : nat) (f : list P -> R) : R :=
    fold_right Rplus 0 (map f (kp_tuples_of_length Lambda n)).

  Definition kp_prod_weight {P : Type} (wt : P -> R) (X : list P) : R :=
    fold_right Rmult 1 (map wt X).

  (* Standard 1/n! weighted cluster series truncated at cluster size <= N_max. *)
  Fixpoint kp_series {P : Type} (Lambda : list P) (N_max : nat) (term : list P -> R) : R :=
    match N_max with
    | 0%nat => 0
    | S N' =>
        kp_series Lambda N' term +
        (/ INR (fact (S N'))) * kp_sum_over_tuples Lambda (S N') term
    end.

  (* Root-pinned 1/k! series for k = 0..N with p0 pinned at vertex 0. *)
  Fixpoint kp_root_series {P : Type} (Lambda : list P) (N : nat) (p0 : P) (term : list P -> R) : R :=
    match N with
    | 0%nat => (/ INR (fact 0%nat)) * kp_sum_over_tuples Lambda 0%nat (fun Y => term (p0 :: Y))
    | S N' =>
        kp_root_series Lambda N' p0 term +
        (/ INR (fact (S N'))) * kp_sum_over_tuples Lambda (S N') (fun Y => term (p0 :: Y))
    end.

  (* Single-polymer overlap sum over Lambda. *)
  Definition kp_sum_overlap {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (p : P) (f : P -> R) : R :=
    fold_right Rplus 0 (map (fun q => if ob p q then f q else 0) Lambda).

  (* Elementary single-polymer Kotecky-Preiss inequality at polymer p:
       sum_{q in Lambda, ob p q} |w(q)| * exp(a(q) + d(q)) <= a(p). *)
  Definition kp_condition_at {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p : P) : Prop :=
    kp_sum_overlap ob Lambda p (fun q => Rabs (w q) * exp (a q + d q)) <= a p.

  (* All sublists (spanning subgraphs) of an edge list. *)
  Fixpoint kp_sublists {A : Type} (l : list A) : list (list A) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let subs := kp_sublists xs in
        subs ++ map (cons x) subs
    end.

  (* BFS connectedness on vertices {0, ..., n - 1}. *)
  Definition kp_expand_once (H : list (nat * nat)) (S : list nat) : list nat :=
    S ++ flat_map (fun e =>
      (if existsb (Nat.eqb (fst e)) S then [snd e] else []) ++
      (if existsb (Nat.eqb (snd e)) S then [fst e] else [])) H.

  Fixpoint kp_expand_iter (k : nat) (H : list (nat * nat)) (S : list nat) : list nat :=
    match k with
    | 0%nat => S
    | S k' => kp_expand_iter k' H (kp_expand_once H S)
    end.

  Definition kp_is_connectedb (n : nat) (H : list (nat * nat)) : bool :=
    match n with
    | 0%nat => false
    | S _ => forallb (fun v => existsb (Nat.eqb v) (kp_expand_iter n H [0%nat])) (seq 0%nat n)
    end.

  (* Incompatibility graph edges {(i, j) | 0 <= i < j < |X|, ob X[i] X[j] = true}. *)
  Fixpoint kp_pairs_with_head {P : Type} (ob : P -> P -> bool)
    (i : nat) (x : P) (j : nat) (xs : list P) : list (nat * nat) :=
    match xs with
    | [] => []
    | y :: ys =>
        if ob x y
        then (i, j) :: kp_pairs_with_head ob i x (S j) ys
        else kp_pairs_with_head ob i x (S j) ys
    end.

  Fixpoint kp_graph_edges_from {P : Type} (ob : P -> P -> bool)
    (i : nat) (X : list P) : list (nat * nat) :=
    match X with
    | [] => []
    | x :: xs =>
        kp_pairs_with_head ob i x (S i) xs ++ kp_graph_edges_from ob (S i) xs
    end.

  Definition kp_graph_edges {P : Type} (ob : P -> P -> bool) (X : list P) : list (nat * nat) :=
    kp_graph_edges_from ob 0%nat X.

  (* Genuine Ursell / Mayer cluster coefficient:
       phi^T(X) = sum_{H <= G(X), H connected spanning} (-1)^{|E(H)|}. *)
  Definition kp_ursell_fn {P : Type} (ob : P -> P -> bool) (X : list P) : R :=
    let n := length X in
    let E := kp_graph_edges ob X in
    fold_right Rplus 0
      (map (fun H => if kp_is_connectedb n H then (-1) ^ (length H) else 0) (kp_sublists E)).

  (* Genuine finite-volume truncated Ursell two-point correlator (clusters overlapping
     both p1 and p2; converges as N_max -> infinity to the partition-function log ratio
     ln ((Z_Lambda * Z_{Lambda \ (N(p1) U N(p2))}) / (Z_{Lambda \ N(p1)} * Z_{Lambda \ N(p2)})),
     as proved in Targets 6a-6c below). *)
  Definition kp_ursell_correlator {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (N_max : nat) (w : P -> R) (p1 p2 : P) : R :=
    kp_series Lambda N_max (fun X =>
      if existsb (ob p1) X && existsb (ob p2) X
      then kp_ursell_fn ob X * kp_prod_weight w X
      else 0).

  (* Scaled L1 anchor distance on Z^4 plaquettes: (1/2) * ||s(p1) - s(p2)||_1
     (edge-sharing plaquettes satisfy ||s1 - s2||_1 <= 2, hence dist <= 1). *)
  Definition site4D_manhattan (s1 s2 : Site4D) : Z :=
    (Z.abs (s4_t s1 - s4_t s2) +
     Z.abs (s4_x s1 - s4_x s2) +
     Z.abs (s4_y s1 - s4_y s2) +
     Z.abs (s4_z s1 - s4_z s2))%Z.

  Definition plaq4D_dist (p1 p2 : Plaq4D) : R :=
    IZR (site4D_manhattan (p4_site p1) (p4_site p2)) / 2.

  (* TARGET 5a (Genuine Kotecky-Preiss Pinned Exponential-Moment Bounds — ZERO analytic assumptions):
     Proves BOTH the root-pinned bound (<= exp(a p0)) AND the 1-pinned overlap
     bound (<= a p0) for the genuine 1/n! ordered-tuple Ursell expansion directly
     from the elementary single-polymer KP inequality. *)
  Definition Challenge_KoteckyPreiss_PinnedBound : Prop :=
    forall (P : Type)
      (ob : P -> P -> bool)
      (ob_sym : forall x y, ob x y = ob y x)
      (Lambda : list P)
      (w a d : P -> R)
      (p0 : P),
      0 <= a p0 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_condition_at ob Lambda w a d p0 ->
      (forall p, In p Lambda -> kp_condition_at ob Lambda w a d p) ->
      (forall N : nat,
         kp_root_series Lambda N p0 (fun X =>
           Rabs (kp_ursell_fn ob X) *
           kp_prod_weight (fun q => Rabs (w q) * exp (d q)) (tl X))
         <= exp (a p0)) /\
      (forall N_max : nat,
         kp_series Lambda N_max (fun X =>
           if existsb (ob p0) X
           then Rabs (kp_ursell_fn ob X) *
                kp_prod_weight (fun q => Rabs (w q) * exp (d q)) X
           else 0)
         <= a p0).

  (* TARGET 5b (Unconditional Exponential Decay of the Genuine Ursell Correlator from KP Alone):
     ZERO analytic assumptions (no assumed pinned-cluster bound!). Given ONLY
     the single-polymer KP inequality and a unit-step metric, the genuine
     Ursell truncated two-point correlator decays exponentially uniformly in
     Lambda and N_max. *)
  Definition Challenge_KoteckyPreiss_ExponentialDecay : Prop :=
    forall (P : Type)
      (ob : P -> P -> bool)
      (ob_sym : forall x y, ob x y = ob y x)
      (Lambda : list P)
      (w a size : P -> R)
      (dist : P -> P -> R)
      (dist_refl : forall p, dist p p = 0)
      (dist_triangle : forall p q r, dist p r <= dist p q + dist q r)
      (ob_dist : forall p q, ob p q = true -> dist p q <= 1)
      (size_pos : forall p, 1 <= size p)
      (c : R)
      (p1 p2 : P),
      0 < c ->
      0 <= a p1 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_condition_at ob Lambda w a (fun q => c * size q) p1 ->
      (forall p, In p Lambda -> kp_condition_at ob Lambda w a (fun q => c * size q) p) ->
      forall N_max : nat,
        Rabs (kp_ursell_correlator ob Lambda N_max w p1 p2)
        <= a p1 * exp c * exp (- c * dist p1 p2).

  (* TARGET 5c (Concrete 4D Hypercubic Lattice Z^4 Plaquette Exponential Decay):
     Discharges the single-polymer KP inequality automatically from the exact
     21-neighbor coordination theorem for beta > 85, w(p) = exp(-beta/10).
     ZERO analytic hypotheses, ZERO combinatorial hypotheses, ZERO project axioms. *)
  Definition Challenge_Lattice4D_KP_ExponentialDecay : Prop :=
    forall (ob : Plaq4D -> Plaq4D -> bool),
      (forall p q, ob p q = true <-> plaq4D_overlap p q) ->
      forall (beta : R) (Lambda : list Plaq4D) (N_max : nat) (p1 p2 : Plaq4D),
        beta > 85 ->
        NoDup Lambda ->
        Forall wf_plaq_4D Lambda ->
        wf_plaq_4D p1 ->
        Rabs (kp_ursell_correlator ob Lambda N_max (fun _ => exp (- beta / 10)) p1 p2)
        <= exp 1 * exp (- plaq4D_dist p1 p2).

  (* =======================================================================
     6. Finite-Volume Partition Function Z_Lambda, ln Z_Lambda Convergence,
        and Exact Partition-Function Log-Ratio Decay (Targets 6a-6c)
     ======================================================================= *)

  (* Pairwise compatibility of a finite list of polymers under incompatibility ob *)
  Fixpoint kp_pairwise_compat {P : Type} (ob : P -> P -> bool) (X : list P) : bool :=
    match X with
    | [] => true
    | x :: xs => forallb (fun y => negb (ob x y)) xs && kp_pairwise_compat ob xs
    end.

  (* Exact finite-volume polymer partition function:
       Z_Lambda = sum_{S <= Lambda, S pairwise compatible} prod_{p in S} w(p). *)
  Definition kp_partition_fn {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) : R :=
    fold_right Rplus 0
      (map (fun S => if kp_pairwise_compat ob S then kp_prod_weight w S else 0) (kp_sublists Lambda)).

  (* Order-n term of the 1/n! Mayer / Ursell expansion (0 at n = 0) *)
  Definition kp_ursell_order {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) (n : nat) : R :=
    match n with
    | 0%nat => 0
    | S _ => (/ INR (fact n)) * kp_sum_over_tuples Lambda n (fun X => kp_ursell_fn ob X * kp_prod_weight w X)
    end.

  (* TARGET 6a (Partition Function Positivity, Absolute Convergence, and ln Z_Lambda Limit):
     Under the elementary single-polymer Kotecky-Preiss inequality on Lambda
     (with reflexive, symmetric incompatibility predicate ob), proves Z_Lambda > 0,
     absolute convergence of the 1/n! Mayer/Ursell series bounded by sum_{p in Lambda} a(p),
     and convergence of the partial sums to ln Z_Lambda as N -> infinity. *)
  Definition Challenge_KoteckyPreiss_LogPartitionFn : Prop :=
    forall (P : Type)
      (ob : P -> P -> bool)
      (ob_refl : forall p, ob p p = true)
      (ob_sym : forall x y, ob x y = ob y x)
      (Lambda : list P)
      (w a : P -> R),
      (forall p, In p Lambda -> 0 <= a p) ->
      (forall p, In p Lambda -> kp_condition_at ob Lambda w a (fun _ => 0) p) ->
      0 < kp_partition_fn ob Lambda w /\
      (forall N : nat,
         sum_f_R0 (fun n => Rabs (kp_ursell_order ob Lambda w n)) N
         <= fold_right Rplus 0 (map a Lambda)) /\
      Un_cv (fun N => kp_series Lambda N (fun X => kp_ursell_fn ob X * kp_prod_weight w X))
            (ln (kp_partition_fn ob Lambda w)).

  (* TARGET 6b (Exact Partition-Function Log-Ratio Convergence & Exponential Decay):
     Proves positivity of all four finite-volume partition functions Z_Lambda,
     Z_{Lambda \ N(p1)}, Z_{Lambda \ N(p2)}, Z_{Lambda \ (N(p1) U N(p2))},
     exact convergence of the truncated Ursell correlator to their log ratio
     as N -> infinity, and unconditional exponential decay of the exact log ratio. *)
  Definition Challenge_KoteckyPreiss_LogRatioDecay : Prop :=
    forall (P : Type)
      (ob : P -> P -> bool)
      (ob_refl : forall p, ob p p = true)
      (ob_sym : forall x y, ob x y = ob y x)
      (Lambda : list P)
      (w a size : P -> R)
      (dist : P -> P -> R)
      (dist_refl : forall p, dist p p = 0)
      (dist_triangle : forall p q r, dist p r <= dist p q + dist q r)
      (ob_dist : forall p q, ob p q = true -> dist p q <= 1)
      (size_pos : forall p, 1 <= size p)
      (c : R)
      (p1 p2 : P),
      0 < c ->
      0 <= a p1 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_condition_at ob Lambda w a (fun q => c * size q) p1 ->
      (forall p, In p Lambda -> kp_condition_at ob Lambda w a (fun q => c * size q) p) ->
      let Z := kp_partition_fn ob Lambda w in
      let Z1 := kp_partition_fn ob (filter (fun q => negb (ob p1 q)) Lambda) w in
      let Z2 := kp_partition_fn ob (filter (fun q => negb (ob p2 q)) Lambda) w in
      let Z12 := kp_partition_fn ob (filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda) w in
      0 < Z /\ 0 < Z1 /\ 0 < Z2 /\ 0 < Z12 /\
      Un_cv (fun N => kp_ursell_correlator ob Lambda N w p1 p2) (ln ((Z * Z12) / (Z1 * Z2))) /\
      Rabs (ln ((Z * Z12) / (Z1 * Z2))) <= a p1 * exp c * exp (- c * dist p1 p2).

  (* TARGET 6c (Concrete 4D Z^4 Partition Function ln Z_Lambda Convergence & Log-Ratio Decay):
     Discharges KP automatically from the exact 21-neighbor coordination theorem
     for beta > 85, w(p) = exp(-beta/10), proving positivity of all four finite-volume
     partition functions, convergence of the cluster series to ln Z_Lambda, convergence
     of the truncated correlator to the partition-function log ratio, and exponential
     decay of the exact partition-function log ratio with ZERO analytic or combinatorial
     hypotheses and ZERO project axioms. *)
  Definition Challenge_Lattice4D_PartitionFn_Decay : Prop :=
    forall (ob : Plaq4D -> Plaq4D -> bool),
      (forall p q, ob p q = true <-> plaq4D_overlap p q) ->
      forall (beta : R) (Lambda : list Plaq4D) (p1 p2 : Plaq4D),
        beta > 85 ->
        NoDup Lambda ->
        Forall wf_plaq_4D Lambda ->
        wf_plaq_4D p1 ->
        let w := fun _ : Plaq4D => exp (- beta / 10) in
        let Z := kp_partition_fn ob Lambda w in
        let Z1 := kp_partition_fn ob (filter (fun q => negb (ob p1 q)) Lambda) w in
        let Z2 := kp_partition_fn ob (filter (fun q => negb (ob p2 q)) Lambda) w in
        let Z12 := kp_partition_fn ob (filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda) w in
        0 < Z /\ 0 < Z1 /\ 0 < Z2 /\ 0 < Z12 /\
        Un_cv (fun N => kp_series Lambda N (fun X => kp_ursell_fn ob X * kp_prod_weight w X)) (ln Z) /\
        Un_cv (fun N => kp_ursell_correlator ob Lambda N w p1 p2) (ln ((Z * Z12) / (Z1 * Z2))) /\
        Rabs (ln ((Z * Z12) / (Z1 * Z2))) <= exp 1 * exp (- plaq4D_dist p1 p2).

End Challenge.
