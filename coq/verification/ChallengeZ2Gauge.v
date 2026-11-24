(* =========================================================================
   verification/ChallengeZ2Gauge.v

   FROZEN CHALLENGE FILE FOR TARGET 7 (4D Z_2 Wilson lattice gauge theory).

   Imports ONLY the Coq 8.18.0 Standard Library and the frozen
   `verification/Challenge.v` (itself Standard-Library-only), from which it
   reuses the concrete Z^4 objects `Site4D`, `Dir4D`, `shift4D`, `Plaq4D`,
   `wf_plaq_4D`, `plaq4D_dist` and the polymer-gas objects of Targets 5a-6c
   (`kp_sublists`, `kp_is_connectedb`, `kp_graph_edges`, `kp_partition_fn`,
   `kp_condition_at`, `kp_series`, `kp_ursell_fn`, `kp_prod_weight`).
   `verification/Challenge.v` is NOT modified by Target 7.

   This file contains ZERO `Axiom`, `Parameter`, `Admitted` declarations and
   ZERO proof scripts: every object below is a plain `Definition`/`Fixpoint`.

   What is formalized here (genuine lattice gauge theory, finite volume):
     - link variables U : Link4D -> Z_2 = {+1, -1} on the links of Z^4,
     - the plaquette holonomy U_p = product of U over the 4 boundary links,
     - the Wilson action S(U) = - beta * sum_{p in Lambda} U_p,
     - the exact normalized Haar integral over Z_2^E (a finite sum over all
       2^|E| link configurations, E = links of the plaquette volume Lambda),
     - the partition function Z and the Gibbs expectation <F>.

   Targets:
     7a  exact strong-coupling (high-temperature) expansion, every beta: link
         integration kills every plaquette set with open boundary, leaving
         the sum over mod-2 surfaces with prescribed boundary (closed
         surfaces for Z, surfaces spanning C for the Wilson line
         <prod_{l in C} U_l>).
     7b  exponential clustering of the gauge-invariant connected plaquette
         correlator <U_p1 ; U_p2> at strong coupling, uniformly in the
         finite volume Lambda, with a decay rate that diverges as beta -> 0.
     7c  exact representation of Z, for every beta, as cosh(beta)^{|Lambda|}
         times the hard-core polymer partition function
         `Challenge.kp_partition_fn` of the connected closed mod-2 surfaces.
     7d  at strong coupling: the Kotecky-Preiss inequality for that polymer
         gas, convergence of its cluster series to
         ln Z - |Lambda| ln cosh(beta), and a bound on this quantity that is
         uniform in the volume.

   Scope disclaimer:
     These are finite-volume statements about the lattice gauge theory with
     the ABELIAN FINITE gauge group Z_2 on Z^4 with free boundary conditions;
     7b and 7d hold at strong coupling only. They do NOT formalize an
     infinite-volume or continuum limit, a non-abelian or continuous gauge
     group, reflection positivity, Osterwalder-Schrader reconstruction, a
     transfer-matrix spectral gap, a Wilson-loop area law, or the Clay
     Millennium Prize Problem.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import List.

Require Import verification.Challenge.

Import ListNotations.
Open Scope R_scope.

Module ChallengeZ2Gauge.

  Import Challenge.

  (* =======================================================================
     1. Links of Z^4 and the boundary links of a plaquette
     ======================================================================= *)

  (* The link (s, d) joins the site s to its neighbour shift4D s d. *)
  Definition Link4D : Type := (Site4D * Dir4D)%type.

  Definition site4D_eqb (s1 s2 : Site4D) : bool :=
    (s4_t s1 =? s4_t s2)%Z && (s4_x s1 =? s4_x s2)%Z &&
    (s4_y s1 =? s4_y s2)%Z && (s4_z s1 =? s4_z s2)%Z.

  Definition dir4D_eqb (d1 d2 : Dir4D) : bool :=
    match d1, d2 with
    | D4_t, D4_t => true
    | D4_x, D4_x => true
    | D4_y, D4_y => true
    | D4_z, D4_z => true
    | _, _ => false
    end.

  Definition link4D_eqb (l1 l2 : Link4D) : bool :=
    site4D_eqb (fst l1) (fst l2) && dir4D_eqb (snd l1) (snd l2).

  (* The 4 boundary links of the unit plaquette anchored at s in the
     (mu, nu)-plane, listed in the same order as `Challenge.plaq4D_edges`:
     the link (s', d) is the vertex pair (s', shift4D s' d). *)
  Definition plaq4D_links (p : Plaq4D) : list Link4D :=
    let s := p4_site p in
    [ (s, p4_mu p);
      (s, p4_nu p);
      (shift4D s (p4_mu p), p4_nu p);
      (shift4D s (p4_nu p), p4_mu p) ].

  (* Number of occurrences of the link l in a list of links. *)
  Fixpoint link4D_count (l : Link4D) (M : list Link4D) : nat :=
    match M with
    | [] => 0%nat
    | x :: M' => ((if link4D_eqb x l then 1 else 0) + link4D_count l M')%nat
    end.

  (* Removal of repeated links (keeps the last occurrence of each link). *)
  Fixpoint link4D_dedup (M : list Link4D) : list Link4D :=
    match M with
    | [] => []
    | x :: M' =>
        if existsb (link4D_eqb x) M' then link4D_dedup M' else x :: link4D_dedup M'
    end.

  (* The set of links carried by a finite plaquette volume Lambda. *)
  Definition z2_links (Lambda : list Plaq4D) : list Link4D :=
    link4D_dedup (flat_map plaq4D_links Lambda).

  (* =======================================================================
     2. Z_2 gauge fields, holonomies, and the Wilson action
     ======================================================================= *)

  (* A Z_2 link configuration: `false` is the group element +1 and `true`
     is the group element -1. *)
  Definition Z2Config : Type := Link4D -> bool.

  Definition z2_sign (b : bool) : R := if b then -1 else 1.

  Definition z2_update (U : Z2Config) (l : Link4D) (b : bool) : Z2Config :=
    fun l' => if link4D_eqb l' l then b else U l'.

  (* Product of the link variables along a list of links C (a Wilson line;
     gauge invariant when C is a closed loop). *)
  Definition z2_holonomy (U : Z2Config) (C : list Link4D) : R :=
    fold_right Rmult 1 (map (fun l => z2_sign (U l)) C).

  (* Plaquette variable U_p: holonomy around the boundary of p. *)
  Definition z2_plaq (U : Z2Config) (p : Plaq4D) : R :=
    z2_holonomy U (plaq4D_links p).

  (* Wilson action  S(U) = - beta * sum_{p in Lambda} U_p. *)
  Definition z2_wilson_action (beta : R) (Lambda : list Plaq4D) (U : Z2Config) : R :=
    - beta * fold_right Rplus 0 (map (z2_plaq U) Lambda).

  (* =======================================================================
     3. Exact normalized Haar integral over Z_2^E, partition function,
        and Gibbs expectation
     ======================================================================= *)

  (* All configurations obtained from U by assigning both group elements
     to every link of E in turn: 2^|E| configurations (pairwise distinct
     when E has no repeated link), each equal to U outside E. *)
  Fixpoint z2_configs_from (E : list Link4D) (U : Z2Config) : list Z2Config :=
    match E with
    | [] => [U]
    | l :: E' =>
        z2_configs_from E' (z2_update U l false) ++
        z2_configs_from E' (z2_update U l true)
    end.

  (* All configurations supported on E (equal to +1 outside E). *)
  Definition z2_configs (E : list Link4D) : list Z2Config :=
    z2_configs_from E (fun _ => false).

  (* Normalized Haar integral over the compact group Z_2^E:
       int F dU = 2^{-|E|} * sum_{U in Z_2^E} F(U). *)
  Definition z2_haar (E : list Link4D) (F : Z2Config -> R) : R :=
    / (2 ^ length E) * fold_right Rplus 0 (map F (z2_configs E)).

  (* Partition function  Z_Lambda(beta) = int exp(- S(U)) dU. *)
  Definition z2_partition_fn (beta : R) (Lambda : list Plaq4D) : R :=
    z2_haar (z2_links Lambda) (fun U => exp (- z2_wilson_action beta Lambda U)).

  (* Gibbs expectation  <F> = Z^{-1} * int F(U) exp(- S(U)) dU. *)
  Definition z2_expect (beta : R) (Lambda : list Plaq4D) (F : Z2Config -> R) : R :=
    z2_haar (z2_links Lambda)
      (fun U => F U * exp (- z2_wilson_action beta Lambda U))
    / z2_partition_fn beta Lambda.

  (* =======================================================================
     4. TARGET 7a: exact strong-coupling (high-temperature) expansion
     ======================================================================= *)

  (* The plaquette set S has mod-2 boundary C on the link set E:
     every link of E occurs an even number of times in C together with the
     boundaries of the plaquettes of S.  For C = [] this says that S is a
     closed mod-2 surface.  (Links of C outside E carry the frozen value +1
     and impose no condition.) *)
  Definition z2_bdry_is (E C : list Link4D) (S : list Plaq4D) : bool :=
    forallb
      (fun l => Nat.even (link4D_count l (C ++ flat_map plaq4D_links S)))
      E.

  (* Sum over all plaquette subsets S of Lambda with mod-2 boundary C of
     t^{|S|}. *)
  Definition z2_surface_sum (Lambda : list Plaq4D) (C : list Link4D) (t : R) : R :=
    fold_right Rplus 0
      (map (fun S => if z2_bdry_is (z2_links Lambda) C S
                     then t ^ length S else 0)
           (kp_sublists Lambda)).

  (* TARGET 7a (Exact Strong-Coupling Expansion — ZERO hypotheses):
     For EVERY real beta and EVERY finite list Lambda of plaquettes of Z^4:
       (1) Z_Lambda(beta) > 0;
       (2) Z_Lambda(beta) = cosh(beta)^{|Lambda|}
                            * sum_{S <= Lambda, dS = 0} tanh(beta)^{|S|};
       (3) the closed-surface sum is strictly positive;
       (4) for every list of links C,
             <prod_{l in C} U_l>
               = (sum_{S <= Lambda, dS = C} tanh(beta)^{|S|})
                 / (sum_{S <= Lambda, dS = 0} tanh(beta)^{|S|}).
     Integration over the links annihilates every plaquette set whose
     boundary is not the prescribed one. *)
  Definition Challenge_Z2Gauge4D_StrongCouplingExpansion : Prop :=
    forall (beta : R) (Lambda : list Plaq4D),
      0 < z2_partition_fn beta Lambda /\
      z2_partition_fn beta Lambda =
        cosh beta ^ length Lambda * z2_surface_sum Lambda [] (tanh beta) /\
      0 < z2_surface_sum Lambda [] (tanh beta) /\
      forall C : list Link4D,
        z2_expect beta Lambda (fun U => z2_holonomy U C) =
        z2_surface_sum Lambda C (tanh beta) / z2_surface_sum Lambda [] (tanh beta).

  (* =======================================================================
     5. TARGET 7b: exponential clustering of the connected plaquette
        correlator at strong coupling
     ======================================================================= *)

  (* Connected (truncated) two-plaquette correlator
       <U_p1 ; U_p2> = <U_p1 U_p2> - <U_p1> <U_p2>. *)
  Definition z2_plaq_truncated (beta : R) (Lambda : list Plaq4D) (p1 p2 : Plaq4D) : R :=
    z2_expect beta Lambda (fun U => z2_plaq U p1 * z2_plaq U p2)
    - z2_expect beta Lambda (fun U => z2_plaq U p1)
      * z2_expect beta Lambda (fun U => z2_plaq U p2).

  (* TARGET 7b (Strong-Coupling Exponential Clustering — ZERO analytic or
     combinatorial hypotheses):
     For every decay rate mu >= 0, every coupling beta (of either sign) with
       168 * |beta| <= exp(- mu),
     every finite duplicate-free volume Lambda of canonical plaquettes of
     Z^4 and all p1, p2 in Lambda:
       |<U_p1 ; U_p2>_Lambda| <= 4 * exp(- mu * (dist(p1, p2) - 1)),
     where dist = plaq4D_dist is the scaled anchor distance of Targets 5c/6c.
     The bound is uniform in Lambda, and the admissible rate
     mu = ln(1 / (168 |beta|)) diverges as beta -> 0. *)
  Definition Challenge_Z2Gauge4D_StrongCouplingClustering : Prop :=
    forall (beta mu : R) (Lambda : list Plaq4D) (p1 p2 : Plaq4D),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      In p1 Lambda ->
      In p2 Lambda ->
      Rabs (z2_plaq_truncated beta Lambda p1 p2)
      <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).

  (* =======================================================================
     6. TARGET 7c: the gauge theory is a hard-core gas of closed mod-2
        surface polymers (the polymer system of Targets 5a-6c)
     ======================================================================= *)

  (* Two plaquettes touch when they share a boundary link. *)
  Definition plaq4D_touch (p q : Plaq4D) : bool :=
    existsb (fun l => existsb (link4D_eqb l) (plaq4D_links q)) (plaq4D_links p).

  (* Closed mod-2 surface: every link lies in an even number of plaquettes
     of S (boundary condition of Target 7a with C = [] on the links of S). *)
  Definition z2_closed (S : list Plaq4D) : bool :=
    z2_bdry_is (flat_map plaq4D_links S) [] S.

  (* Connected under link sharing: BFS connectivity (Challenge.v) of the
     graph on the positions of S whose edges join touching plaquettes.
     The empty list is not connected. *)
  Definition z2_connected (S : list Plaq4D) : bool :=
    kp_is_connectedb (length S) (kp_graph_edges plaq4D_touch S).

  (* The surface polymers of Lambda: connected closed surfaces in Lambda. *)
  Definition z2_polymers (Lambda : list Plaq4D) : list (list Plaq4D) :=
    filter (fun S => z2_closed S && z2_connected S) (kp_sublists Lambda).

  (* Hard-core incompatibility: some plaquette of g1 touches some plaquette
     of g2.  (The empty list is incompatible only with itself; it is never
     a polymer.) *)
  Definition z2_poly_incompat (g1 g2 : list Plaq4D) : bool :=
    match g1, g2 with
    | [], [] => true
    | _, _ => existsb (fun p => existsb (plaq4D_touch p) g2) g1
    end.

  (* Polymer activity tanh(beta)^{|gamma|}. *)
  Definition z2_poly_activity (beta : R) (g : list Plaq4D) : R :=
    tanh beta ^ length g.

  (* TARGET 7c (Exact Surface-Polymer-Gas Representation — every beta):
     For every real beta and every duplicate-free plaquette list Lambda,
       Z_Lambda(beta) = cosh(beta)^{|Lambda|} * Xi_Lambda(beta),
     where Xi_Lambda is EXACTLY the finite-volume hard-core polymer
     partition function `Challenge.kp_partition_fn` of Targets 6a-6c
     (sum over pairwise compatible families of polymers of the product of
     activities), for the polymer system
       polymers        = connected closed mod-2 surfaces inside Lambda,
       incompatibility = sharing a link,
       activity        = tanh(beta)^{number of plaquettes}. *)
  Definition Challenge_Z2Gauge4D_SurfacePolymerGas : Prop :=
    forall (beta : R) (Lambda : list Plaq4D),
      NoDup Lambda ->
      z2_partition_fn beta Lambda =
      cosh beta ^ length Lambda *
      kp_partition_fn z2_poly_incompat (z2_polymers Lambda) (z2_poly_activity beta).

  (* =======================================================================
     7. TARGET 7d: Kotecky-Preiss criterion and convergent cluster expansion
        of the free energy of the gauge theory at strong coupling
     ======================================================================= *)

  (* TARGET 7d (Free-Energy Cluster Expansion — ZERO analytic or
     combinatorial hypotheses):
     For every beta with 189 * |tanh(beta)| <= 1 and every finite
     duplicate-free volume Lambda of canonical plaquettes of Z^4, the
     surface-polymer gas of Target 7c satisfies:
       (1) the elementary single-polymer Kotecky-Preiss inequality
           `Challenge.kp_condition_at` (the hypothesis of Targets 5a-6b) at
           every polymer, with a(gamma) = 189 |tanh beta| |gamma| and d = 0;
       (2) the 1/n! Mayer / Ursell cluster series of Target 6a converges to
             ln Z_Lambda(beta) - |Lambda| * ln cosh(beta);
       (3) the free energy is within 189 |tanh beta| per plaquette of its
           single-plaquette value, uniformly in the volume:
             |ln Z_Lambda(beta) - |Lambda| ln cosh(beta)|
               <= 189 * |tanh(beta)| * |Lambda|.
     The entropy of the surface polymers (a lattice-animal bound) is derived
     from the Kotecky-Preiss tree-graph engine applied to the gas of single
     plaquettes and the exact 21-neighbour theorem (Target 4a). *)
  Definition Challenge_Z2Gauge4D_FreeEnergyClusterExpansion : Prop :=
    forall (beta : R) (Lambda : list Plaq4D),
      189 * Rabs (tanh beta) <= 1 ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      let Polys := z2_polymers Lambda in
      let w := z2_poly_activity beta in
      let a := fun g : list Plaq4D => 189 * Rabs (tanh beta) * INR (length g) in
      (forall g, In g Polys ->
         kp_condition_at z2_poly_incompat Polys w a (fun _ => 0) g) /\
      Un_cv (fun N => kp_series Polys N
                        (fun X => kp_ursell_fn z2_poly_incompat X * kp_prod_weight w X))
            (ln (z2_partition_fn beta Lambda) - INR (length Lambda) * ln (cosh beta)) /\
      Rabs (ln (z2_partition_fn beta Lambda) - INR (length Lambda) * ln (cosh beta))
      <= 189 * Rabs (tanh beta) * INR (length Lambda).

End ChallengeZ2Gauge.
