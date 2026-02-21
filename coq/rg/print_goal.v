Require Import Reals Lra List.
Import ListNotations.
Require Import rg.polymer_types rg.rooted_tree rg.pinned_bound.

Open Scope R_scope.

Lemma sum_gen_trees_Sk_le_test :
  forall k p forb,
    sum_list (map tree_weight (gen_trees_Sk k p forb)) <=
    exp (a * size p) *
    sum_over_sublists (nbr_excluding p forb) (fun q => rooted_sum k q (p :: forb)).
Proof.
  intros k p forb.
  unfold gen_trees_Sk. simpl.
  rewrite tree_weight_leaf.
  set (L := nbr_excluding p forb).
  set (F := fun q => rooted_sum k q (p :: forb)).
  rewrite sum_list_flat_map.

  destruct (all_sublists_cons_nil L) as [rest Hrest].
  rewrite Hrest. simpl.

  rewrite tree_weight_node_nil.
