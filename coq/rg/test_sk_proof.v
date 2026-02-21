Require Import Reals Lra List.
Import ListNotations.
Require Import rg.polymer_types rg.rooted_tree rg.pinned_bound.

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

  (* Break all_sublists L into [] :: rest *)
  destruct (all_sublists_cons_nil L) as [rest Hrest].
  rewrite Hrest. simpl.

  (* First term of sum_list map is for [] *)
  (* all_choices (map ... []) = all_choices [] = [ [] ] *)
  (* map (rt_node p) [ [] ] = [ rt_node p [] ] *)
  (* map tree_weight [ rt_node p [] ] = [ tree_weight (rt_node p []) ] *)
  (* tree_weight (rt_node p []) = 0 *)
  rewrite tree_weight_node_nil.
  replace (sum_list [0]) with 0 by reflexivity.
  rewrite Rplus_0_l.

  (* Now we bound the rest of the node terms *)
  assert (Hnode_bound :
    sum_list (map (fun qs => sum_list (map tree_weight
      (map (rt_node p) (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)))))
      rest)
    <= exp (a * size p) *
      sum_list (map (fun qs => sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
        (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
        rest)).
  {
    assert (Hexp_pos : 0 < exp (a * size p)) by apply exp_pos.
    assert (Hinner_le : forall qs,
      sum_list (map tree_weight
        (map (rt_node p) (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
      <= exp (a * size p) *
        sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
          (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)))).
    { intro qs. rewrite map_map.
      eapply Rle_trans.
      - apply sum_list_map_monotone.
        intros children _. apply tree_weight_node_le.
      - induction (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)) as [|cs css IHcs];
          simpl; [lra|]. lra.
    }
    induction rest as [|qs0 rest' IHr]; simpl; [lra|].
    pose proof (Hinner_le qs0) as Hinner0.
    assert (Hprod_nonneg : 0 <= sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs0)))).
    { apply sum_list_nonneg. intros r Hr. apply in_map_iff in Hr. destruct Hr as [cs [Heq Hin]]. subst.
      apply fold_right_Rmult_nonneg_gen. intros t Ht. apply tree_weight_nonneg. }
    nra.
  }

  assert (Hfact :
    forall qs,
    sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))) =
    fold_right Rmult 1 (map F qs)).
  {
    intro qs.
    rewrite (all_choices_sum_prod_factorizes tree_weight
      (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)).
    - rewrite map_map. reflexivity.
    - intros l' Hl' x Hx. apply tree_weight_nonneg.
  }

  assert (Hrewrite :
    sum_list (map (fun qs => sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
      rest) =
    sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) rest)).
  { apply f_equal. apply map_ext. intro qs. apply Hfact. }

  rewrite Hrewrite in Hnode_bound.
  
  (* We know sum_over_sublists_tl relates tail sum to total subset sum *)
  pose proof (sum_over_sublists_tl L F) as Htl.
  (* tl (all_sublists L) = tl ([] :: rest) = rest *)
  rewrite Hrest in Htl. simpl in Htl.
  
  (* Htl: sum_list (map ... rest) = sum_over_sublists L F - 1 *)
  rewrite Htl in Hnode_bound.

  (* Now lra should work:
     Goal is exp + sum_list (map ... rest) <= exp * sum_over_sublists L F.
     We have exp + Hnode_bound <= exp + exp * (sum_over_sublists L F - 1)
     = exp + exp * sum... - exp = exp * sum... *)
  
  nra.
Qed.
