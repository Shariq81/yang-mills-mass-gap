Require Import Coq.Reals.Reals.
Require Import Coq.List.List.
Require Import Coq.micromega.Lra.
Require Import rg.polymer_types.
Require Import rg.cluster_expansion.
Require Import ym.geometry_frontier.

Derive Dependent Inversion adj_path_list_inv with (forall X p q l, adj_path_list X p q l).

