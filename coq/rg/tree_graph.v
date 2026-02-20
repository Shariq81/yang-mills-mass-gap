(* =========================================================================
   tree_graph.v - Stage 3/4: Penrose Tree-Graph Inequality Scaffold
   
   Generic graph combinatorics file for proving the tree-graph majorant.
   Parameterized by finite vertex sets, generic edges, and edge weights.
   
   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Section TreeGraph.

  (* =========================================================================
     1. Vertices and Total Order
     ========================================================================= *)

  Context {V : Type}.
  Variable X : list V.
  Hypothesis X_NoDup : NoDup X.
  
  (* Total order for deterministic lex-min path extraction *)
  Variable V_lt : V -> V -> Prop.
  Hypothesis V_lt_dec : forall u v, {V_lt u v} + {~ V_lt u v}.
  Hypothesis V_eq_dec : forall u v : V, {u = v} + {u <> v}.
  Hypothesis V_lt_asym : forall u v, V_lt u v -> ~ V_lt v u.
  Hypothesis V_lt_total : forall u v, u <> v -> V_lt u v \/ V_lt v u.
  
  (* =========================================================================
     2. Normalized Edges (avoids symmetric duplication and UIP issues)
     ========================================================================= *)
     
  Record Edge := { eu : V; ev : V }.

  Definition mkEdge (u v : V) : Edge :=
    if V_lt_dec u v then {| eu := u; ev := v |} else {| eu := v; ev := u |}.
    
  Lemma edge_eq_dec : forall e1 e2 : Edge, {e1 = e2} + {e1 <> e2}.
  Proof.
    intros [u1 v1] [u2 v2].
    destruct (V_eq_dec u1 u2) as [Hu | Hnu].
    - destruct (V_eq_dec v1 v2) as [Hv | Hnv].
      + subst. left. auto.
      + right. congruence.
    - right. congruence.
  Qed.

  Lemma mkEdge_comm :
    forall u v, mkEdge u v = mkEdge v u.
  Proof.
    intros u v.
    unfold mkEdge.
    destruct (V_lt_dec u v) as [Huv|Hnuv];
    destruct (V_lt_dec v u) as [Hvu|Hnvu].
    - exfalso. exact (V_lt_asym u v Huv Hvu).
    - reflexivity.
    - reflexivity.
    - (* neither u<v nor v<u and u<>v is impossible by totality *)
      destruct (V_eq_dec u v) as [Heq|Hne].
      + subst. reflexivity.
      + exfalso. destruct (V_lt_total u v Hne) as [H|H]; contradiction.
  Qed.

  (* =========================================================================
     3. Graphs and Connectivity
     ========================================================================= *)
     
  Definition Graph := list Edge.
  Definition is_wf_graph (G : Graph) : Prop := NoDup G.
  
  Definition edge_in_graph (G : Graph) (u v : V) : Prop :=
    In (mkEdge u v) G.

  Lemma edge_in_graph_comm :
    forall (G:Graph) u v,
      edge_in_graph G u v -> edge_in_graph G v u.
  Proof.
    intros G u v H.
    unfold edge_in_graph in *.
    rewrite <- mkEdge_comm.
    exact H.
  Qed.

  (* Connectivity via length-indexed paths *)
  Inductive path_len (G : Graph) : nat -> V -> V -> Prop :=
  | pl_refl : forall u, In u X -> path_len G 0 u u
  | pl_step : forall n u v w, 
      edge_in_graph G u v -> path_len G n v w -> path_len G (S n) u w.

  Definition is_connected (G : Graph) : Prop :=
    forall u v, In u X -> In v X -> exists n : nat, path_len G n u v.

  (* =========================================================================
     4. Deterministic Tree Extraction: Depth and Parent Specs
     ========================================================================= *)
     
  Variable root : V.
  Hypothesis root_in_X : In root X.
  
  (* Minimal depth definition *)
  Definition has_depth (G : Graph) (v : V) (n : nat) : Prop :=
    exists p : path_len G n root v, True.

  Definition is_min_depth (G : Graph) (v : V) (n : nat) : Prop :=
    has_depth G v n /\ forall m, has_depth G v m -> (n <= m)%nat.

  Parameter depth_G : Graph -> V -> nat.
  Hypothesis depth_G_spec :
    forall G v, In v X -> is_connected G -> is_min_depth G v (depth_G G v).

  (* Parent choice definition *)
  Definition is_parent_choice (G : Graph) (v u : V) : Prop :=
    In v X /\ In u X /\
    edge_in_graph G u v /\
    (depth_G G u + 1 = depth_G G v)%nat /\
    forall u', In u' X ->
      edge_in_graph G u' v ->
      (depth_G G u' + 1 = depth_G G v)%nat ->
      ~ V_lt u' u.

  Parameter parent_G : Graph -> V -> option V.
  Hypothesis parent_G_spec :
    forall G v,
      In v X -> is_connected G ->
      (v = root -> parent_G G v = None) /\
      (v <> root -> exists u, parent_G G v = Some u /\ is_parent_choice G v u).

  (* Extracted Tree *)
  Definition penrose_tree (G : Graph) : Graph :=
    fold_right (fun v acc =>
      match parent_G G v with
      | Some u => mkEdge u v :: acc
      | None => acc
      end) [] X.

  Lemma parent_edge_in_penrose_tree_generic :
    forall (L : list V) G u v,
      In v L -> parent_G G v = Some u ->
      In (mkEdge u v) (fold_right (fun v acc => match parent_G G v with Some u => mkEdge u v :: acc | None => acc end) [] L).
  Proof.
    intros L G u v Hv Hp.
    induction L as [|x xs IH]; simpl in *.
    - contradiction.
    - destruct Hv as [Hv|Hv].
      + subst x. rewrite Hp. simpl. left. reflexivity.
      + destruct (parent_G G x) as [px|] eqn:Hpx; simpl.
        * right. apply IH. exact Hv.
        * apply IH. exact Hv.
  Qed.

  (* =========================================================================
     5. Extracted Lemmas (L1: Extraction Property)
     ========================================================================= *)

  Lemma penrose_tree_subgraph :
    forall G v u,
      is_connected G -> In v X -> parent_G G v = Some u ->
      In (mkEdge u v) (penrose_tree G).
  Proof.
    intros G v u Hconn Hv Hpar.
    unfold penrose_tree.
    apply parent_edge_in_penrose_tree_generic; assumption.
  Qed.

  Lemma penrose_tree_edges_in_G :
    forall G v u,
      is_connected G -> In v X -> parent_G G v = Some u ->
      edge_in_graph G u v.
  Proof.
    intros G v u Hconn Hv Hpar.
    destruct (parent_G_spec G v Hv Hconn) as [_ Hcase].
    assert (v <> root) as Hneq.
    { intro Heq. subst v. destruct (parent_G_spec G root root_in_X Hconn) as [Hroot _].
      specialize (Hroot eq_refl). rewrite Hroot in Hpar. discriminate. }
    specialize (Hcase Hneq).
    destruct Hcase as [u' [Hu' Hchoice]].
    rewrite Hpar in Hu'. inversion Hu'. subst u'.
    unfold is_parent_choice in Hchoice.
    tauto.
  Qed.

  Lemma penrose_tree_reaches_root :
    forall G v,
      is_connected G -> In v X ->
      exists n, path_len (penrose_tree G) n v root.
  Proof.
    intros G v Hconn Hv.
    (* Strong induction on depth_G G v *)
    set (d := depth_G G v).
    assert (Hd : depth_G G v = d) by reflexivity.
    clearbody d.
    revert v Hv Hd.
    induction d as [d IH] using lt_wf_ind.
    intros v Hv Hd.
    destruct (V_eq_dec v root) as [->|Hne].
    - (* v = root: path of length 0 *)
      exists 0%nat. apply pl_refl. exact root_in_X.
    - (* v ≠ root: use parent *)
      destruct (parent_G_spec G v Hv Hconn) as [_ Hnr].
      specialize (Hnr Hne) as [u [Hpu Hchoice]].
      unfold is_parent_choice in Hchoice.
      destruct Hchoice as [_ [Hu [Hedge [Hdepth _]]]].
      (* depth(u) < depth(v) *)
      assert (Hlt : (depth_G G u < d)%nat).
      { rewrite <- Hd. lia. }
      (* IH gives path from u to root *)
      specialize (IH (depth_G G u) Hlt u Hu eq_refl) as [n Hpath_u].
      (* Edge (u,v) is in penrose_tree *)
      assert (Hin_edge : In (mkEdge u v) (penrose_tree G)).
      { apply penrose_tree_subgraph; assumption. }
      (* Extend path: v -> u -> ... -> root *)
      (* We need edge_in_graph (penrose_tree G) v u *)
      unfold edge_in_graph.
      rewrite mkEdge_comm in Hin_edge.
      exists (S n).
      apply (pl_step (penrose_tree G) n v u root).
      + unfold edge_in_graph. exact Hin_edge.
      + exact Hpath_u.
  Qed.

  (* Helper: filter with all-true predicate is identity *)
  Lemma filter_all_true :
    forall {A} (f : A -> bool) (l : list A),
      (forall x, In x l -> f x = true) ->
      filter f l = l.
  Proof.
    intros A f l Hall.
    induction l as [|x xs IH]; simpl.
    - reflexivity.
    - rewrite (Hall x (or_introl eq_refl)). f_equal. apply IH.
      intros y Hy. apply Hall. right. exact Hy.
  Qed.

  (* Helper: count edges contributed by a sublist *)
  Lemma penrose_tree_fold_length :
    forall G (L : list V),
      is_connected G ->
      (forall v, In v L -> In v X) ->
      NoDup L ->
      length (fold_right (fun v acc => match parent_G G v with Some u => mkEdge u v :: acc | None => acc end) [] L)
      = length (filter (fun v => match parent_G G v with Some _ => true | None => false end) L).
  Proof.
    intros G L Hconn HinX Hnd.
    induction L as [|x xs IH]; simpl.
    - reflexivity.
    - destruct (parent_G G x) as [px|] eqn:Hpx; simpl.
      + f_equal. apply IH.
        * intros v Hv. apply HinX. right. exact Hv.
        * inversion Hnd; assumption.
      + apply IH.
        * intros v Hv. apply HinX. right. exact Hv.
        * inversion Hnd; assumption.
  Qed.

  (* General version that works on any list, avoiding section variable induction *)
  Lemma penrose_tree_edge_count_general :
    forall G (L : list V) (r : V),
      is_connected G ->
      NoDup L ->
      In r L ->
      (forall v, In v L -> In v X) ->
      (* r is root-like: parent_G G r = None *)
      parent_G G r = None ->
      (* All other v in L have Some parent *)
      (forall v, In v L -> v <> r -> exists u, parent_G G v = Some u) ->
      length (fold_right (fun v acc => match parent_G G v with Some u => mkEdge u v :: acc | None => acc end) [] L)
      = pred (length L).
  Proof.
    intros G L r Hconn Hnd Hr HinX Hrpar Hother.
    induction L as [|x xs IH]; simpl.
    - reflexivity.
    - inversion Hnd as [|? ? Hnotinxs Hndxs]; subst.
      destruct (V_eq_dec x r) as [->|Hne].
      + (* x = r: root contributes no edge *)
        rewrite Hrpar.
        (* Since r = x, r is not in xs (by NoDup), so every v in xs has a parent *)
        assert (Hall_some : forall v, In v xs -> exists u, parent_G G v = Some u).
        { intros v Hv. apply Hother. right. exact Hv.
          intro Heq. subst. apply Hnotinxs in Hv. contradiction. }
        assert (Hlen_xs : length (fold_right (fun v acc => match parent_G G v with Some u => mkEdge u v :: acc | None => acc end) [] xs) = length xs).
        { clear - Hall_some. induction xs as [|z zs IHxs]; simpl.
          - reflexivity.
          - destruct (Hall_some z (or_introl eq_refl)) as [pz Hpz].
            rewrite Hpz. simpl. f_equal. apply IHxs.
            intros v Hv. apply Hall_some. right. exact Hv. }
        exact Hlen_xs.
      + (* x ≠ r: x has a parent *)
        destruct (Hother x (or_introl eq_refl) Hne) as [px Hpx].
        rewrite Hpx. simpl. f_equal.
        destruct xs as [|y ys].
        * simpl in Hr. destruct Hr as [Hr|[]]. contradiction.
        * simpl.
          assert (Hr_in_xs : In r (y::ys)).
          { destruct Hr as [Hr|Hr]; [contradiction|exact Hr]. }
          pose proof (IH Hndxs Hr_in_xs (fun v Hv => HinX v (or_intror Hv)) (fun v Hv Hvne => Hother v (or_intror Hv) Hvne)) as HIH.
          simpl in HIH.
          rewrite HIH. reflexivity.
  Qed.

  Lemma penrose_tree_edge_count :
    forall G,
      is_connected G -> NoDup X ->
      length (penrose_tree G) = pred (length X).
  Proof.
    intros G Hconn HndX.
    unfold penrose_tree.
    apply (penrose_tree_edge_count_general G X root Hconn HndX root_in_X).
    - (* forall v, In v X -> In v X *)
      intros; assumption.
    - (* parent_G G root = None *)
      destruct (parent_G_spec G root root_in_X Hconn) as [Hroot _].
      apply Hroot. reflexivity.
    - (* forall v ≠ root, parent exists *)
      intros v Hv Hne.
      destruct (parent_G_spec G v Hv Hconn) as [_ Hnr].
      specialize (Hnr Hne) as [u [Hu _]].
      exists u. exact Hu.
  Qed.

  (* =========================================================================
     6. Extracted Lemmas (L2: Closure Property)
     ========================================================================= *)

  (* The Penrose Closure Predicate A(T) expressed via the extraction functions.
     We INCLUDE same-depth edges to simplify P2. *)
  Definition edge_in_A_G (G : Graph) (u v : V) : Prop :=
    (depth_G G u = depth_G G v)%nat \/
    ((depth_G G u < depth_G G v)%nat /\
     match parent_G G v with
     | Some pv => (depth_G G u + 1 = depth_G G v)%nat /\ ~ V_lt u pv
     | None => False
     end) \/
    ((depth_G G v < depth_G G u)%nat /\
     match parent_G G u with
     | Some pu => (depth_G G v + 1 = depth_G G u)%nat /\ ~ V_lt v pu
     | None => False
     end).

  (* Helper: extend path by appending an edge at the end *)
  Lemma path_len_extend :
    forall G n u v w,
      path_len G n u v -> edge_in_graph G v w -> In w X -> path_len G (S n) u w.
  Proof.
    intros G n u v w Hpath.
    revert w.
    induction Hpath as [u' Hu' | n' u' v' w' Hedge' Hpath' IH]; intros w Hedge Hw.
    - (* pl_refl: path of length 0 from u' to u', extend by edge u'->w *)
      apply (pl_step G 0 u' w w Hedge).
      apply pl_refl. exact Hw.
    - (* pl_step: had edge u'->v' and path v'->w', now extend to w *)
      (* IH applied to subpath gives path_len G (S n') v' w *)
      specialize (IH w Hedge Hw).
      (* prepend edge u'->v' to get path_len G (S (S n')) u' w *)
      apply (pl_step G (S n') u' v' w Hedge' IH).
  Qed.

  (* Helper: edge implies depth difference at most 1 *)
  Lemma edge_depth_bound :
    forall G u v,
      is_connected G -> In u X -> In v X ->
      edge_in_graph G u v ->
      (depth_G G v <= depth_G G u + 1)%nat.
  Proof.
    intros G u v Hconn Hu Hv Hedge.
    (* From depth_G_spec, depth_G G v is minimal *)
    destruct (depth_G_spec G v Hv Hconn) as [[p _] Hmin].
    (* We can reach v from root in depth(u)+1 steps via u *)
    destruct (depth_G_spec G u Hu Hconn) as [[pu _] _].
    (* path from root to u of length depth(u), then edge u->v *)
    assert (Hreach : has_depth G v (S (depth_G G u))).
    { exists (path_len_extend G (depth_G G u) root u v pu Hedge Hv). trivial. }
    apply Hmin in Hreach. lia.
  Qed.

  Lemma closure_property_depth_oriented :
    forall G u v,
      is_connected G -> In u X -> In v X ->
      edge_in_graph G u v ->
      (depth_G G u < depth_G G v)%nat ->
      parent_G G v <> Some u ->
      edge_in_A_G G u v.
  Proof.
    intros G u v Hconn Hu Hv Hedge Hlt Hnotpar.
    (* Show depth difference is exactly 1 *)
    assert (Hdiff : (depth_G G u + 1 = depth_G G v)%nat).
    { pose proof (edge_depth_bound G u v Hconn Hu Hv Hedge). lia. }
    (* v is not root since depth(v) > 0 *)
    assert (Hne : v <> root).
    { intro Heq. subst v.
      destruct (depth_G_spec G root root_in_X Hconn) as [[p _] Hmin].
      (* root has depth 0 by pl_refl *)
      assert (H0 : has_depth G root 0).
      { exists (pl_refl G root root_in_X). trivial. }
      apply Hmin in H0. lia. }
    (* Get parent pv of v *)
    destruct (parent_G_spec G v Hv Hconn) as [_ Hnr].
    specialize (Hnr Hne) as [pv [Hpv Hchoice]].
    (* edge_in_A_G: second disjunct applies *)
    unfold edge_in_A_G. right. left.
    split; [exact Hlt|].
    rewrite Hpv. split; [exact Hdiff|].
    (* Use minimality: u satisfies parent conditions, so ~V_lt u pv *)
    unfold is_parent_choice in Hchoice.
    destruct Hchoice as [_ [_ [_ [_ Hminimal]]]].
    apply Hminimal; assumption.
  Qed.

  (* =========================================================================
     7. P2 Bucket Expansion
     ========================================================================= *)
     
  Lemma depth_trichotomy :
    forall (G : Graph) (u v : V),
      (depth_G G u < depth_G G v)%nat \/
      (depth_G G u = depth_G G v)%nat \/
      (depth_G G v < depth_G G u)%nat.
  Proof.
    intros G u v.
    destruct (lt_eq_lt_dec (depth_G G u) (depth_G G v)) as [[Hlt|Heq]|Hgt].
    - left; exact Hlt.
    - right; left; exact Heq.
    - right; right; exact Hgt.
  Qed.

  Lemma parent_edge_in_penrose_tree :
    forall G u v,
      In v X -> parent_G G v = Some u ->
      edge_in_graph (penrose_tree G) u v.
  Proof.
    intros G u v Hv Hp.
    unfold penrose_tree, edge_in_graph.
    apply parent_edge_in_penrose_tree_generic; auto.
  Qed.

  Lemma edge_in_A_G_comm :
    forall G u v, edge_in_A_G G u v -> edge_in_A_G G v u.
  Proof.
    intros G u v H. unfold edge_in_A_G in *.
    destruct H as [Heq | [[Hlt Hp1] | [Hgt Hp2]]].
    - left. auto.
    - right; right. split; assumption.
    - right; left. split; assumption.
  Qed.

  Lemma P2_bucket_expansion :
    forall (G : Graph) (u v : V),
      is_connected G -> In u X -> In v X ->
      edge_in_graph G u v ->
      edge_in_graph (penrose_tree G) u v \/ edge_in_A_G G u v.
  Proof.
    intros G u v Hconn Hu Hv He.
    destruct (in_dec edge_eq_dec (mkEdge u v) (penrose_tree G)) as [HinT|HnotinT].
    - left. exact HinT.
    - right.
      destruct (depth_trichotomy G u v) as [Hlt|[Heq|Hgt]].
      + apply closure_property_depth_oriented; try assumption.
        intro Hp. apply HnotinT. apply parent_edge_in_penrose_tree; assumption.
      + unfold edge_in_A_G. left. exact Heq.
      + apply edge_in_A_G_comm.
        apply closure_property_depth_oriented; try assumption.
        * apply edge_in_graph_comm. exact He.
        * intro Hp. apply HnotinT.
          assert (HinVU : edge_in_graph (penrose_tree G) v u).
          { apply (parent_edge_in_penrose_tree G v u Hu Hp). }
          unfold edge_in_graph in *. rewrite mkEdge_comm in HinVU. exact HinVU.
  Qed.

  (* =========================================================================
     8. Finite Graphs and the Summation Identity
     ========================================================================= *)

  (* We assume we can enumerate all valid edges on X *)
  Variable complete_edges : list Edge.
  Hypothesis complete_edges_NoDup : NoDup complete_edges.
  Hypothesis complete_edges_correct : 
    forall e, In e complete_edges <-> (In (eu e) X /\ In (ev e) X /\ eu e <> ev e).

  (* All graphs are sublists of complete_edges *)
  Fixpoint all_sublists {A} (l : list A) : list (list A) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let S := all_sublists xs in
        S ++ map (fun s => x :: s) S
    end.

  Definition all_graphs_X : list Graph := all_sublists complete_edges.

  (* Subset Sum: Σ_{S⊆L} Π_{x∈S} F(x) = Π_{x∈L} (1 + F(x)) *)
  Fixpoint sum_over_sublists (L : list Edge) (F : Edge -> R) : R :=
    match L with
    | [] => 1
    | x :: xs => sum_over_sublists xs F + F x * sum_over_sublists xs F
    end.

  Lemma sum_subsets_eq_prod_1plus_edges :
    forall (Aedges : list Edge) (w : Edge -> R),
      (forall e, In e Aedges -> 0 <= w e) ->
      sum_over_sublists Aedges w = fold_right Rmult 1 (map (fun e => 1 + w e) Aedges).
  Proof.
    intros Aedges w _.
    induction Aedges as [|e es IH]; simpl.
    - reflexivity.
    - rewrite IH. ring.
  Qed.

  (* =========================================================================
     9. Depth Trichotomy Helper
     ========================================================================= *)

  (* (Replaced depth_trichotomy here because it was moved above) *)

  (* =========================================================================
     10. Filtered Lists for Summation
     ========================================================================= *)

  (* We assume we can decide connectivity and tree properties *)
  Variable is_connected_dec : forall G, {is_connected G} + {~ is_connected G}.
  
  Definition connected_graphs_X : list Graph :=
    filter (fun G => if is_connected_dec G then true else false) all_graphs_X.

  Definition is_tree (T : Graph) : Prop :=
    is_connected T /\ length T = pred (length X).

  Variable is_tree_dec : forall G, {is_tree G} + {~ is_tree G}.

  Definition trees_X : list Graph :=
    filter (fun G => if is_tree_dec G then true else false) all_graphs_X.

  (* =========================================================================
     11. The Penrose Majorant Target Lemma
     ========================================================================= *)
     
  Variable zeta : V -> V -> R.

  Fixpoint graph_weight (G : Graph) : R :=
    match G with
    | [] => 1
    | e :: rest => zeta (eu e) (ev e) * graph_weight rest
    end.

  Definition w_edge (e : Edge) : R :=
    Rabs (zeta (eu e) (ev e)).

  Fixpoint graph_abs_weight (G : Graph) : R :=
    match G with
    | [] => 1
    | e :: rest => w_edge e * graph_abs_weight rest
    end.

  (* Concrete sum over a list using fold_right *)
  Definition sum_list (l : list Graph) (f : Graph -> R) : R :=
    fold_right Rplus 0 (map f l).

  Lemma sum_list_mono :
    forall l f g,
      (forall x, In x l -> f x <= g x) ->
      sum_list l f <= sum_list l g.
  Proof.
    intros l f g Hle.
    unfold sum_list.
    induction l as [|x xs IH]; simpl.
    - right. reflexivity.
    - assert (Hlex : f x <= g x). { apply Hle. left. reflexivity. }
      assert (HIH : fold_right Rplus 0 (map f xs) <= fold_right Rplus 0 (map g xs)).
      { apply IH. intros y Hy. apply Hle. right. exact Hy. }
      lra.
  Qed.

  Lemma Rabs_sum_list_le_sum_list_Rabs :
    forall (l : list Graph) (f : Graph -> R),
      Rabs (sum_list l f) <= sum_list l (fun x => Rabs (f x)).
  Proof.
    intros l f.
    induction l as [|x xs IH]; unfold sum_list; simpl.
    - rewrite Rabs_R0. lra.
    - eapply Rle_trans.
      + apply Rabs_triang.
      + apply Rplus_le_compat_l. exact IH.
  Qed.

  (* Define the filtered list of A(T) edges *)
  Variable edge_in_A_G_dec : forall G u v, {edge_in_A_G G u v} + {~ edge_in_A_G G u v}.

  Definition A_edges_G (G : Graph) : list Edge :=
    filter (fun e => if edge_in_A_G_dec G (eu e) (ev e) then true else false) complete_edges.

  Definition bucket_graphs (T : Graph) : list Graph :=
    map (fun S => T ++ S) (all_sublists (A_edges_G T)).

  (* Helper: graph_weight distributes over append *)
  Lemma graph_weight_app :
    forall G1 G2,
      graph_weight (G1 ++ G2) = graph_weight G1 * graph_weight G2.
  Proof.
    intros G1 G2.
    induction G1 as [|e es IH]; simpl.
    - ring.
    - rewrite IH. ring.
  Qed.

  (* Helper: graph_abs_weight distributes over append *)
  Lemma graph_abs_weight_app :
    forall G1 G2,
      graph_abs_weight (G1 ++ G2) = graph_abs_weight G1 * graph_abs_weight G2.
  Proof.
    intros G1 G2.
    induction G1 as [|e es IH]; simpl.
    - ring.
    - rewrite IH. ring.
  Qed.

  (* Helper: Rabs of graph_weight bounded by graph_abs_weight *)
  Lemma Rabs_graph_weight_le_abs_weight :
    forall G,
      Rabs (graph_weight G) <= graph_abs_weight G.
  Proof.
    intros G.
    induction G as [|e es IH]; simpl.
    - rewrite Rabs_R1. lra.
    - rewrite Rabs_mult. unfold w_edge.
      apply Rmult_le_compat; try apply Rabs_pos.
      + lra.
      + exact IH.
  Qed.

  (* Helper: graph_abs_weight is nonnegative *)
  Lemma graph_abs_weight_nonneg :
    forall G, 0 <= graph_abs_weight G.
  Proof.
    intros G.
    induction G as [|e es IH]; simpl.
    - lra.
    - unfold w_edge. apply Rmult_le_pos; [apply Rabs_pos | exact IH].
  Qed.

  (* Helper: sum over map (fun S => f (T ++ S)) *)
  Lemma sum_list_map_app :
    forall (Subs : list (list Edge)) T f,
      sum_list (map (fun S => T ++ S) Subs) f =
      fold_right Rplus 0 (map (fun S => f (T ++ S)) Subs).
  Proof.
    intros Subs T f.
    unfold sum_list.
    induction Subs as [|S Ss IH]; simpl.
    - reflexivity.
    - f_equal. exact IH.
  Qed.

  (* Helper: sum_over_sublists gives upper bound when all terms nonnegative *)
  Lemma sum_over_sublists_Rabs_bound :
    forall L w,
      (forall e, In e L -> 0 <= w e) ->
      (forall e, In e L -> Rabs (w e) <= w e) ->
      sum_over_sublists L (fun e => Rabs (w e)) <= sum_over_sublists L w.
  Proof.
    intros L w Hpos Habs.
    induction L as [|x xs IH]; simpl.
    - lra.
    - assert (Hx_pos : 0 <= w x). { apply Hpos. left. reflexivity. }
      assert (Hx_abs : Rabs (w x) <= w x). { apply Habs. left. reflexivity. }
      assert (IHxs : sum_over_sublists xs (fun e => Rabs (w e)) <= sum_over_sublists xs w).
      { apply IH.
        - intros e He. apply Hpos. right. exact He.
        - intros e He. apply Habs. right. exact He. }
      (* LHS: sum xs |w| + |w x| * sum xs |w| *)
      (* RHS: sum xs w + w x * sum xs w *)
      assert (Hsum_xs_nonneg : 0 <= sum_over_sublists xs w).
      { assert (Hpos_xs : forall e, In e xs -> 0 <= w e) by (intros e He; apply Hpos; right; exact He).
        clear - Hpos_xs.
        induction xs as [|y ys IHy]; simpl.
        - lra.
        - assert (Hy : 0 <= w y). { apply Hpos_xs. left. reflexivity. }
          assert (IHys' : 0 <= sum_over_sublists ys w).
          { apply IHy. intros e He. apply Hpos_xs. right. exact He. }
          nra. }
      assert (Hrx : Rabs (w x) = w x).
      { apply Rabs_right. apply Rle_ge. exact Hx_pos. }
      rewrite Hrx.
      nra.
  Qed.

  (* Key: sum over sublists of |graph_weight S| where S ⊆ A_edges *)
  (* For each sublist S, |graph_weight S| ≤ graph_abs_weight S = Π |zeta e| *)
  (* And Σ_{S⊆L} Π_{e∈S} |zeta e| ≤ Σ_{S⊆L} Π_{e∈S} (if |zeta e| ≤ 1+zeta e then 1+zeta else ...) *)

  (* Simpler approach: just bound each term *)
  Lemma sum_list_bucket_bound :
    forall T (Subs : list (list Edge)),
      (forall S, In S Subs -> forall e, In e S -> 0 <= zeta (eu e) (ev e)) ->
      fold_right Rplus 0 (map (fun S => Rabs (graph_weight (T ++ S))) Subs)
      <= graph_abs_weight T * fold_right Rplus 0 (map (fun S => graph_abs_weight S) Subs).
  Proof.
    intros T Subs Hpos.
    induction Subs as [|S Ss IH]; simpl.
    - ring_simplify. lra.
    - assert (IHSs : fold_right Rplus 0 (map (fun S0 => Rabs (graph_weight (T ++ S0))) Ss) <=
                     graph_abs_weight T * fold_right Rplus 0 (map (fun S0 => graph_abs_weight S0) Ss)).
      { apply IH. intros S' HS' e He. apply (Hpos S' (or_intror HS') e He). }
      rewrite graph_weight_app, Rabs_mult.
      assert (Hle1 : Rabs (graph_weight T) <= graph_abs_weight T).
      { apply Rabs_graph_weight_le_abs_weight. }
      assert (Hle2 : Rabs (graph_weight S) <= graph_abs_weight S).
      { apply Rabs_graph_weight_le_abs_weight. }
      assert (Hnn1 : 0 <= graph_abs_weight T). { apply graph_abs_weight_nonneg. }
      assert (Hnn2 : 0 <= graph_abs_weight S). { apply graph_abs_weight_nonneg. }
      assert (Hnn3 : 0 <= fold_right Rplus 0 (map (fun S0 => graph_abs_weight S0) Ss)).
      { clear Hpos IH IHSs. induction Ss as [|s ss IHss]; simpl; [lra|].
        apply Rplus_le_le_0_compat.
        - apply graph_abs_weight_nonneg.
        - exact IHss. }
      assert (Hpos_T : 0 <= Rabs (graph_weight T)) by apply Rabs_pos.
      assert (Hpos_S : 0 <= Rabs (graph_weight S)) by apply Rabs_pos.
      nra.
  Qed.

  (* Helper: elements of all_sublists are sublists of the original *)
  Lemma all_sublists_incl :
    forall {A} (L : list A) S,
      In S (all_sublists L) -> incl S L.
  Proof.
    intros A L.
    induction L as [|x xs IH]; intros S HS; simpl in *.
    - destruct HS as [HS|[]]. subst. intros y [].
    - rewrite in_app_iff in HS.
      destruct HS as [HS|HS].
      + (* S ∈ all_sublists xs, so S ⊆ xs ⊆ (x::xs) *)
        specialize (IH S HS).
        intros y Hy. right. apply IH. exact Hy.
      + (* S ∈ map (fun s => x::s) (all_sublists xs) *)
        rewrite in_map_iff in HS.
        destruct HS as [S' [Heq HS']].
        subst S.
        intros y Hy. simpl in Hy. destruct Hy as [->|Hy].
        * left. reflexivity.
        * right. apply (IH S' HS'). exact Hy.
  Qed.

  (* Convert sum_over_sublists to fold_right sum over all_sublists *)
  Lemma sum_over_sublists_eq_fold :
    forall L w,
      sum_over_sublists L w =
      fold_right Rplus 0 (map (fun S => fold_right Rmult 1 (map w S)) (all_sublists L)).
  Proof.
    intros L w.
    induction L as [|x xs IH]; simpl.
    - lra.
    - rewrite IH.
      rewrite map_app.
      rewrite map_map. simpl.
      (* Need: fold_right Rplus 0 (A ++ B) = fold_right Rplus 0 A + fold_right Rplus 0 B *)
      assert (Hfold : forall (A B : list R),
                fold_right Rplus 0 (A ++ B) = fold_right Rplus 0 A + fold_right Rplus 0 B).
      { clear. intros A B. induction A as [|a A' IHA]; simpl.
        - ring.
        - rewrite IHA. ring. }
      rewrite Hfold.
      assert (Hfactor2 : forall c (L' : list (list Edge)) (f : list Edge -> R),
                fold_right Rplus 0 (map (fun v => c * f v) L') = c * fold_right Rplus 0 (map f L')).
      { clear. intros c L' f. induction L' as [|v vs IHv]; simpl; [ring|rewrite IHv; ring]. }
      rewrite Hfactor2.
      rewrite <- IH.
      ring.
  Qed.

  (* graph_abs_weight S = fold_right Rmult 1 (map w_edge S) *)
  Lemma graph_abs_weight_eq_fold :
    forall S,
      graph_abs_weight S = fold_right Rmult 1 (map w_edge S).
  Proof.
    intros S.
    induction S as [|e es IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma penrose_bucket_sum_bound :
    forall T,
      In T trees_X ->
      (* For the bound to hold with 1+zeta (not 1+|zeta|), we need zeta >= 0 *)
      (forall e, In e (A_edges_G T) -> 0 <= zeta (eu e) (ev e)) ->
      sum_list (bucket_graphs T) (fun G => Rabs (graph_weight G))
      <= graph_abs_weight T *
         fold_right Rmult 1 (map (fun e => 1 + zeta (eu e) (ev e)) (A_edges_G T)).
  Proof.
    intros T HT Hzeta_pos.
    unfold bucket_graphs.
    rewrite sum_list_map_app.
    (* LHS = Σ_{S⊆A(T)} |w(T++S)| = Σ_{S⊆A(T)} |w(T)| * |w(S)| *)
    (* Since zeta >= 0, |w(S)| = w(S) = Π_{e∈S} zeta(e) *)
    (* And Σ_{S⊆A(T)} Π_{e∈S} zeta(e) = Π_{e∈A(T)} (1 + zeta(e)) *)
    set (A := A_edges_G T).
    set (Subs := all_sublists A).
    (* Key insight: when zeta >= 0, |graph_weight S| = graph_weight S for S ⊆ A *)
    assert (Habs_eq : forall S, (forall e, In e S -> In e A) ->
              Rabs (graph_weight S) = graph_weight S).
    { intros S HS.
      induction S as [|e es IH]; simpl.
      - rewrite Rabs_R1. reflexivity.
      - rewrite Rabs_mult.
        assert (He_in_A : In e A). { apply HS. left. reflexivity. }
        assert (Hze : 0 <= zeta (eu e) (ev e)). { apply Hzeta_pos. exact He_in_A. }
        rewrite Rabs_right by lra.
        rewrite IH by (intros e' He'; apply HS; right; exact He').
        reflexivity. }
    (* Similarly for T: |w(T)| <= w_abs(T) *)
    assert (HT_bound : Rabs (graph_weight T) <= graph_abs_weight T).
    { apply Rabs_graph_weight_le_abs_weight. }
    (* Now transform the sum *)
    assert (Hsum_bound : forall Subs',
      (forall S, In S Subs' -> incl S A) ->
      fold_right Rplus 0 (map (fun S => Rabs (graph_weight (T ++ S))) Subs')
      <= graph_abs_weight T * fold_right Rplus 0 (map (fun S => graph_weight S) Subs')).
    { intros Subs' Hsubs.
      induction Subs' as [|S Ss IH']; simpl.
      - ring_simplify. lra.
      - rewrite graph_weight_app, Rabs_mult.
        assert (HS_in_A : forall e, In e S -> In e A).
        { apply Hsubs. left. reflexivity. }
        rewrite (Habs_eq S HS_in_A).
        assert (Hnn1 : 0 <= graph_abs_weight T). { apply graph_abs_weight_nonneg. }
        assert (Hnn2 : 0 <= graph_weight S).
        { assert (Hpos_S : forall e, In e S -> 0 <= zeta (eu e) (ev e)) by (intros e He; apply Hzeta_pos; apply HS_in_A; exact He).
          clear - Hpos_S. induction S as [|e es IHs]; simpl; [lra|].
          assert (Hze : 0 <= zeta (eu e) (ev e)) by (apply Hpos_S; left; reflexivity).
          assert (Hes : 0 <= graph_weight es) by (apply IHs; intros e' He'; apply Hpos_S; right; exact He').
          nra. }
        assert (Hnn3 : 0 <= fold_right Rplus 0 (map (fun S0 => graph_weight S0) Ss)).
        { clear - Hsubs Hzeta_pos. induction Ss as [|s ss IHss]; simpl; [lra|].
          assert (Hws : 0 <= graph_weight s).
          { assert (Hs_in_A : forall e, In e s -> In e A) by (intros e0 He0; apply (Hsubs s); [right; left; reflexivity|exact He0]).
            clear - Hs_in_A Hzeta_pos.
            induction s as [|e es IHs]; simpl; [lra|].
            assert (Hze : 0 <= zeta (eu e) (ev e)) by (apply Hzeta_pos; apply Hs_in_A; left; reflexivity).
            assert (Hes : 0 <= graph_weight es) by (apply IHs; intros e' He'; apply Hs_in_A; right; exact He').
            nra. }
          assert (Hwss : 0 <= fold_right Rplus 0 (map (fun S0 => graph_weight S0) ss)).
          { apply IHss. intros S_inner [HSeq | HSin].
            - apply Hsubs. left. exact HSeq.
            - apply Hsubs. right. right. exact HSin. }
          nra. }
        assert (H_IH : fold_right Rplus 0 (map (fun S0 => Rabs (graph_weight (T ++ S0))) Ss) <=
                 graph_abs_weight T * fold_right Rplus 0 (map (fun S0 => graph_weight S0) Ss)).
        { apply IH'. intros S0 HS0. apply Hsubs. right. exact HS0. }
        nra. }
    eapply Rle_trans. { apply Hsum_bound. intros S HS. apply all_sublists_incl. exact HS. }
    apply Rmult_le_compat_l. { apply graph_abs_weight_nonneg. }
    (* Now show: Σ_{S⊆A} w(S) = Π_{e∈A} (1 + zeta(e)) *)
    assert (Hfactor :
      fold_right Rplus 0 (map (fun S => graph_weight S) Subs)
      = fold_right Rmult 1 (map (fun e => 1 + zeta (eu e) (ev e)) A)).
    { unfold Subs.
      clear HT HT_bound Habs_eq Hsum_bound.
      rewrite <- (sum_subsets_eq_prod_1plus_edges A (fun e => zeta (eu e) (ev e))).
      2: { intros e He. apply Hzeta_pos. exact He. }
      rewrite sum_over_sublists_eq_fold.
      assert (Hgw : forall S, graph_weight S = fold_right Rmult 1 (map (fun e => zeta (eu e) (ev e)) S)).
      { intros S0. induction S0 as [|e es IH]; simpl; [reflexivity|rewrite IH; reflexivity]. }
      apply f_equal. apply map_ext. intro S0. apply Hgw. }
    rewrite Hfactor. lra.
  Qed.

  (* Helper: fold_right Rplus distributes over app *)
  Lemma fold_right_Rplus_app :
    forall (A B : list R),
      fold_right Rplus 0 (A ++ B) = fold_right Rplus 0 A + fold_right Rplus 0 B.
  Proof.
    intros A B.
    induction A as [|a A' IH]; simpl.
    - ring.
    - rewrite IH. ring.
  Qed.

  (* Helper: sum_list over flat_map equals nested sum_list *)
  Lemma sum_list_flat_map :
    forall (L : list Graph) (f : Graph -> list Graph) (g : Graph -> R),
      sum_list (flat_map f L) g = sum_list L (fun T => sum_list (f T) g).
  Proof.
    intros L f g.
    induction L as [|T Ts IH].
    - reflexivity.
    - simpl. unfold sum_list in *. simpl.
      rewrite map_app, fold_right_Rplus_app, IH.
      reflexivity.
  Qed.

  (* Helper: nonneg terms give nonneg sum *)
  Lemma sum_list_nonneg :
    forall (L : list Graph) (f : Graph -> R),
      (forall G, In G L -> 0 <= f G) ->
      0 <= sum_list L f.
  Proof.
    intros L f Hpos. unfold sum_list.
    induction L as [|H Hs IH]; simpl.
    - lra.
    - assert (Hh : 0 <= f H). { apply Hpos. left. reflexivity. }
      assert (Hhs : 0 <= fold_right Rplus 0 (map f Hs)).
      { apply IH. intros G' HG'. apply Hpos. right. exact HG'. }
      lra.
  Qed.

  (* Helper: sum over superset bounds sum over subset when terms are nonneg *)
  (* We prove this by showing each element of L1 contributes to both sums *)
  Lemma sum_list_incl_nonneg :
    forall (L1 L2 : list Graph) (f : Graph -> R),
      incl L1 L2 ->
      NoDup L1 ->
      (forall G, In G L2 -> 0 <= f G) ->
      sum_list L1 f <= sum_list L2 f.
  Proof.
    intros L1. induction L1 as [|a L1' IH]; intros L2 f Hincl Hnd Hpos.
    - (* Base: sum [] = 0 <= sum L2 *)
      unfold sum_list. simpl.
      apply sum_list_nonneg. exact Hpos.
    - (* Step: a :: L1' *)
      inversion Hnd as [|? ? Hnotin Hnd']; subst.
      assert (Ha : In a L2) by (apply Hincl; left; reflexivity).
      destruct (In_split a L2 Ha) as [l1 [l2 Heq]].
      rewrite Heq in *. clear Ha Heq.
      (* L2 = l1 ++ a :: l2, goal: sum (a::L1') <= sum (l1 ++ a :: l2) *)
      unfold sum_list. simpl.
      rewrite map_app. simpl.
      rewrite fold_right_Rplus_app. simpl.
      (* Goal: f a + fold_right Rplus 0 (map f L1') <=
               fold_right Rplus 0 (map f l1) + (f a + fold_right Rplus 0 (map f l2)) *)
      (* Need: incl L1' (l1 ++ l2) *)
      assert (Hincl' : incl L1' (l1 ++ l2)).
      { intros z Hz.
        assert (Hz2 : In z (l1 ++ a :: l2)) by (apply Hincl; right; exact Hz).
        apply in_app_or in Hz2. destruct Hz2 as [Hzl1|Hzl2].
        - apply in_or_app. left. exact Hzl1.
        - destruct Hzl2 as [Heq|Hzl2].
          + subst z. contradiction.
          + apply in_or_app. right. exact Hzl2.
      }
      (* IH applied to L1' and (l1 ++ l2) *)
      assert (Hpos' : forall G, In G (l1 ++ l2) -> 0 <= f G).
      { intros G HG. apply Hpos.
        apply in_app_or in HG. destruct HG as [HG|HG].
        - apply in_or_app. left. exact HG.
        - apply in_or_app. right. right. exact HG.
      }
      specialize (IH (l1 ++ l2) f Hincl' Hnd' Hpos').
      unfold sum_list in IH.
      rewrite map_app, fold_right_Rplus_app in IH.
      (* Now: fold_right ... L1' <= fold_right ... l1 + fold_right ... l2 *)
      lra.
  Qed.

  (* Hypothesis: each connected graph is in the bucket of its penrose tree *)
  Variable connected_in_bucket :
    forall G, In G connected_graphs_X -> In G (bucket_graphs (penrose_tree G)).

  (* Hypothesis: penrose_tree of a connected graph is in trees_X *)
  Variable penrose_tree_in_trees :
    forall G, In G connected_graphs_X -> In (penrose_tree G) trees_X.

  (* Hypothesis: connected_graphs_X has no duplicates *)
  Variable connected_graphs_NoDup : NoDup connected_graphs_X.

  (* Hypothesis: zeta is nonnegative on all A-edges (for bucket bound) *)
  Variable zeta_nonneg_on_A :
    forall T e, In T trees_X -> In e (A_edges_G T) -> 0 <= zeta (eu e) (ev e).

  (* Every connected graph uniquely belongs to the bucket of its penrose_tree,
     hence the sum over connected graphs is bounded by the sum over trees of buckets. *)
  Lemma Rabs_sum_connected_bounded_by_buckets :
    Rabs (sum_list connected_graphs_X graph_weight)
    <= sum_list trees_X (fun T => sum_list (bucket_graphs T) (fun G => Rabs (graph_weight G))).
  Proof.
    eapply Rle_trans.
    - apply Rabs_sum_list_le_sum_list_Rabs.
    - rewrite <- sum_list_flat_map.
      apply sum_list_incl_nonneg.
      + intros G HG.
        apply in_flat_map.
        exists (penrose_tree G).
        split.
        * apply penrose_tree_in_trees. exact HG.
        * apply connected_in_bucket. exact HG.
      + exact connected_graphs_NoDup.
      + intros G _. apply Rabs_pos.
  Qed.

  (* The final assembly target *)
  Lemma tree_graph_majorant_penrose_proved :
    Rabs (sum_list connected_graphs_X graph_weight)
    <=
    sum_list trees_X (fun T =>
      graph_abs_weight T *
      fold_right Rmult 1 (map (fun e => 1 + zeta (eu e) (ev e)) (A_edges_G T))).
  Proof.
    eapply Rle_trans.
    - apply Rabs_sum_connected_bounded_by_buckets.
    - apply sum_list_mono.
      intros T HT.
      apply penrose_bucket_sum_bound.
      + exact HT.
      + intros e He. apply (zeta_nonneg_on_A T e HT He).
  Qed.

End TreeGraph.
