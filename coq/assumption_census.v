(* Assumption Census for Yang-Mills Mass Gap Formalization *)
(* Run: wsl -d Ubuntu-24.04 bash -c "cd /mnt/c/APEX/coq && coqc -Q rg rg -Q ym ym assumption_census.v" *)

Require Import rg.polymer_types.
Require Import rg.cluster_expansion.
Require Import rg.tree_graph.
Require Import rg.pinned_bound.
Require Import ym.geometry_frontier.
Require Import ym.cluster_frontier.
Require Import ym.numerics_frontier.
Require Import ym.small_field.
Require Import rg.continuum_limit.
Require Import rg.mass_gap_bridge.
Require Import ym.wilson_entry.

(* Print assumptions for main theorems *)

Print Assumptions lattice_mass_gap.
Print Assumptions continuum_mass_gap.
Print Assumptions WilsonEntry.yang_mills_mass_gap_unconditional.

(* Additional key theorems *)
Print Assumptions WilsonEntry.wilson_starts_small.
Print Assumptions ContinuumLimit.continuum_limit_exists.
Print Assumptions ym_satisfies_kp.
