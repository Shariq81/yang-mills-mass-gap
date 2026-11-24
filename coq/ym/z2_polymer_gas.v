(* =========================================================================
   ym/z2_polymer_gas.v

   The 4D Z_2 Wilson lattice gauge theory IS a hard-core gas of closed
   mod-2 surface polymers (TARGET 7c), proved directly for the frozen
   objects of `verification/ChallengeZ2Gauge.v`:

     Z_Lambda(beta)
       = cosh(beta)^{|Lambda|}
         * kp_partition_fn z2_poly_incompat (z2_polymers Lambda)
                           (fun gamma => tanh(beta)^{|gamma|})

   for every real beta and every duplicate-free plaquette list Lambda.

   Ingredients:
     - Target 7a (`Z2GaugeExpansion.partition_fn_expand`): Z is
       cosh^{|Lambda|} times the sum over closed mod-2 surfaces;
     - the weight rho(S) = [S closed] * t^{|S|} factorizes over parts that
       share no link (boundaries add mod 2 on disjoint link sets);
     - the abstract theorem `PolymerRepresentation.polymer_representation`
       (rg/polymer_representation.v);
     - polymers of zero activity (connected but not closed) are discarded.

   Depends ONLY on Coq stdlib + verification.Challenge
   + verification.ChallengeZ2Gauge + verification.Verify (definition bridges)
   + rg.dup_clustering + rg.polymer_representation + the Kotecky-Preiss
   engine + ym.z2_gauge_expansion + ym.z2_gauge_clustering.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.penrose_tree_bound.
Require Import rg.kotecky_preiss.
Require Import rg.cluster_log_partition.
Require Import rg.polymer_representation.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.

Import ListNotations.
Import Challenge ChallengeZ2Gauge.
Import DupClustering Z2GaugeExpansion Z2GaugeClustering.
Open Scope R_scope.

Module Z2PolymerGas.

  (* =======================================================================
     1. Link counting and closed surfaces
     ======================================================================= *)

  Definition links_of (S : list Plaq4D) : list Link4D := flat_map plaq4D_links S.

  Lemma count_app : forall l M1 M2,
    link4D_count l (M1 ++ M2) = (link4D_count l M1 + link4D_count l M2)%nat.
  Proof.
    intros l M1 M2. induction M1 as [| x M1 IH]; [reflexivity |].
    cbn [app link4D_count]. rewrite IH. lia.
  Qed.

  Lemma count_zero : forall l M, ~ In l M -> link4D_count l M = 0%nat.
  Proof.
    intros l M. induction M as [| x M IH]; intro H; [reflexivity |].
    cbn [link4D_count].
    destruct (link4D_eqb x l) eqn:E.
    - apply link4D_eqb_spec in E. subst x. exfalso. apply H. left. reflexivity.
    - rewrite IH; [reflexivity |]. intro Hin. apply H. right. exact Hin.
  Qed.

  Lemma count_pos_In : forall l M, (0 < link4D_count l M)%nat -> In l M.
  Proof.
    intros l M. induction M as [| x M IH]; cbn [link4D_count]; intro H; [lia |].
    destruct (link4D_eqb x l) eqn:E.
    - apply link4D_eqb_spec in E. left. exact E.
    - right. apply IH. cbn in H. exact H.
  Qed.

  Lemma dedup_In : forall l M, In l (link4D_dedup M) <-> In l M.
  Proof.
    intros l M. induction M as [| x M IH]; [reflexivity |].
    cbn [link4D_dedup]. destruct (existsb (link4D_eqb x) M) eqn:E.
    - rewrite IH. split; [intro H; right; exact H |].
      intros [H | H]; [| exact H]. subst x.
      apply existsb_exists in E. destruct E as [y [Hy Heq]].
      apply link4D_eqb_spec in Heq. subst y. exact Hy.
    - cbn [In]. rewrite IH. reflexivity.
  Qed.

  Lemma closed_iff : forall S,
    z2_closed S = true <-> forall l, Nat.even (link4D_count l (links_of S)) = true.
  Proof.
    intro S. unfold z2_closed, z2_bdry_is. cbn [app]. fold (links_of S).
    rewrite forallb_forall. split.
    - intros H l. destruct (memb link4D_eqb l (links_of S)) eqn:Hm.
      + apply (memb_In link4D_eqb link4D_eqb_spec) in Hm. exact (H l Hm).
      + apply (memb_false link4D_eqb link4D_eqb_spec) in Hm.
        rewrite (count_zero l _ Hm). reflexivity.
    - intros H l _. exact (H l).
  Qed.

  (* On subsets of Lambda the boundary condition of Target 7a with C = []
     is intrinsic closedness. *)
  Lemma bdry_closed : forall Lambda S, incl S Lambda ->
    z2_bdry_is (z2_links Lambda) [] S = z2_closed S.
  Proof.
    intros Lambda S HS. apply eq_true_iff_eq. rewrite closed_iff.
    unfold z2_bdry_is. cbn [app]. fold (links_of S). rewrite forallb_forall. split.
    - intros H l. destruct (memb link4D_eqb l (links_of S)) eqn:Hm.
      + apply (memb_In link4D_eqb link4D_eqb_spec) in Hm. apply H.
        unfold z2_links. apply dedup_In.
        unfold links_of in Hm. apply in_flat_map in Hm. destruct Hm as [p [Hp Hl]].
        apply in_flat_map. exists p. split; [apply HS; exact Hp | exact Hl].
      + apply (memb_false link4D_eqb link4D_eqb_spec) in Hm.
        rewrite (count_zero l _ Hm). reflexivity.
    - intros H l _. exact (H l).
  Qed.

  Lemma count_filter_split : forall l (f : Plaq4D -> bool) S,
    link4D_count l (links_of S) =
    (link4D_count l (links_of (filter f S)) +
     link4D_count l (links_of (filter (fun b => negb (f b)) S)))%nat.
  Proof.
    intros l f S. induction S as [| a S IH]; [reflexivity |].
    unfold links_of in *. cbn [flat_map filter]. rewrite count_app, IH.
    destruct (f a); cbn [negb flat_map]; rewrite ?count_app; lia.
  Qed.

  Lemma length_filter_split : forall {A : Type} (f : A -> bool) (l : list A),
    length l = (length (filter f l) + length (filter (fun b => negb (f b)) l))%nat.
  Proof.
    intros A f l. induction l as [| a l IH]; [reflexivity |].
    cbn [filter length]. destruct (f a); cbn [negb length]; lia.
  Qed.

  Lemma filter_andb : forall {A : Type} (f g : A -> bool) (l : list A),
    filter (fun x => f x && g x) l = filter f (filter g l).
  Proof.
    intros A f g l. induction l as [| a l IH]; [reflexivity |].
    simpl. destruct (g a) eqn:Hg; destruct (f a) eqn:Hf; simpl; rewrite ?Hf, IH; reflexivity.
  Qed.

  (* Closedness splits over parts that do not touch each other *)
  Lemma closed_split : forall S (f : Plaq4D -> bool),
    (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                 plaq4D_touch p q = false) ->
    z2_closed S =
    z2_closed (filter f S) && z2_closed (filter (fun b => negb (f b)) S).
  Proof.
    intros S f Hnt. apply eq_true_iff_eq. rewrite andb_true_iff, !closed_iff.
    assert (Hdis : forall l,
      link4D_count l (links_of (filter f S)) = 0%nat \/
      link4D_count l (links_of (filter (fun b => negb (f b)) S)) = 0%nat).
    { intro l.
      destruct (Nat.eq_dec (link4D_count l (links_of (filter f S))) 0) as [H1 | H1];
        [left; exact H1 |].
      destruct (Nat.eq_dec
                  (link4D_count l (links_of (filter (fun b => negb (f b)) S))) 0)
        as [H2 | H2]; [right; exact H2 |].
      exfalso.
      assert (Hin1 : In l (links_of (filter f S))) by (apply count_pos_In; lia).
      assert (Hin2 : In l (links_of (filter (fun b => negb (f b)) S)))
        by (apply count_pos_In; lia).
      unfold links_of in Hin1, Hin2.
      apply in_flat_map in Hin1. destruct Hin1 as [p [Hp Hlp]].
      apply in_flat_map in Hin2. destruct Hin2 as [q [Hq Hlq]].
      apply filter_In in Hp. destruct Hp as [HpS Hfp].
      apply filter_In in Hq. destruct Hq as [HqS Hfq]. apply negb_true_iff in Hfq.
      pose proof (Hnt p q HpS HqS Hfp Hfq) as Hno.
      assert (Hyes : plaq4D_touch p q = true).
      { change (touchb Link4D link4D_eqb (plaq4D_links p) (plaq4D_links q) = true).
        apply (touchb_true Link4D link4D_eqb link4D_eqb_spec). exists l. split; assumption. }
      congruence. }
    split.
    - intro H. split; intro l; pose proof (H l) as Hl;
        rewrite (count_filter_split l f S) in Hl; destruct (Hdis l) as [H0 | H0].
      + rewrite H0. reflexivity.
      + rewrite H0, Nat.add_0_r in Hl. exact Hl.
      + rewrite H0 in Hl. cbn [Nat.add] in Hl. exact Hl.
      + rewrite H0. reflexivity.
    - intros [H1 H2] l. rewrite (count_filter_split l f S).
      destruct (Hdis l) as [H0 | H0]; rewrite H0.
      + cbn [Nat.add]. apply H2.
      + rewrite Nat.add_0_r. apply H1.
  Qed.

  (* =======================================================================
     2. The factorizing weight rho(S) = [S closed] * t^{|S|}
     ======================================================================= *)

  Definition rho (t : R) (S : list Plaq4D) : R :=
    if z2_closed S then t ^ length S else 0.

  Lemma rho_nil : forall t, rho t [] = 1.
  Proof. intro t. reflexivity. Qed.

  Lemma rho_factor : forall t (S : list Plaq4D) (f : Plaq4D -> bool),
    (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                 PolymerRepresentation.touch Link4D Plaq4D link4D_eqb plaq4D_links p q = false) ->
    rho t S = rho t (filter f S) * rho t (filter (fun b => negb (f b)) S).
  Proof.
    intros t S f Hnt. unfold rho.
    rewrite (closed_split S f Hnt), (length_filter_split f S).
    destruct (z2_closed (filter f S)),
             (z2_closed (filter (fun b => negb (f b)) S)); cbn [andb]; try ring.
    rewrite pow_add. ring.
  Qed.

  Lemma links_nonempty : forall p, plaq4D_links p <> [].
  Proof. intro p. unfold plaq4D_links. discriminate. Qed.

  (* =======================================================================
     3. Bridging the abstract polymer system to the frozen definitions
     ======================================================================= *)

  Local Notation absIncompat :=
    (PolymerRepresentation.incompat Link4D Plaq4D link4D_eqb plaq4D_links).
  Local Notation absConnb :=
    (PolymerRepresentation.connb Link4D Plaq4D link4D_eqb plaq4D_links).

  Lemma incompat_eq : forall g1 g2, absIncompat g1 g2 = z2_poly_incompat g1 g2.
  Proof. reflexivity. Qed.

  Lemma connb_eq : forall S, absConnb S = z2_connected S.
  Proof.
    intro S. unfold PolymerRepresentation.connb, z2_connected.
    transitivity
      (PenroseTreeBound.is_connectedb (length S) (kp_graph_edges plaq4D_touch S)).
    - reflexivity.
    - symmetry.
      exact (Verify.kp_is_connectedb_eq (length S) (kp_graph_edges plaq4D_touch S)).
  Qed.

  Lemma polymers_eq : forall Lambda,
    z2_polymers Lambda =
    filter z2_closed (filter absConnb (PenroseTreeBound.sublists Lambda)).
  Proof.
    intro Lambda. unfold z2_polymers. rewrite Verify.kp_sublists_eq.
    transitivity (filter (fun S => z2_closed S && absConnb S)
                    (PenroseTreeBound.sublists Lambda)).
    - apply filter_ext. intro S. reflexivity.
    - apply filter_andb.
  Qed.

  (* The closed-surface sum is the surface-polymer partition function *)
  Theorem surface_sum_polymer : forall t Lambda, NoDup Lambda ->
    z2_surface_sum Lambda [] t =
    kp_partition_fn z2_poly_incompat (z2_polymers Lambda) (fun g => t ^ length g).
  Proof.
    intros t Lambda Hnd.
    assert (H1 : z2_surface_sum Lambda [] t =
                 rsum (PenroseTreeBound.sublists Lambda) (rho t)).
    { unfold z2_surface_sum. rewrite Verify.kp_sublists_eq.
      change (rsum (PenroseTreeBound.sublists Lambda)
                (fun S => if z2_bdry_is (z2_links Lambda) [] S then t ^ length S else 0) =
              rsum (PenroseTreeBound.sublists Lambda) (rho t)).
      apply rsum_ext. intros S HS. unfold rho.
      rewrite (bdry_closed Lambda S (PenroseTreeBound.sublists_incl Lambda S HS)).
      reflexivity. }
    rewrite H1.
    rewrite (PolymerRepresentation.polymer_representation
               Link4D Plaq4D link4D_eqb link4D_eqb_spec plaq4D_eqb plaq4D_eqb_spec
               plaq4D_links links_nonempty (rho t) (rho_nil t) (rho_factor t) Lambda Hnd).
    rewrite polymers_eq.
    change (ClusterLogPartition.partition_fn absIncompat
              (filter absConnb (PenroseTreeBound.sublists Lambda)) (rho t) =
            ClusterLogPartition.partition_fn z2_poly_incompat
              (filter z2_closed (filter absConnb (PenroseTreeBound.sublists Lambda)))
              (fun g => t ^ length g)).
    transitivity
      (ClusterLogPartition.partition_fn absIncompat
         (filter z2_closed (filter absConnb (PenroseTreeBound.sublists Lambda))) (rho t)).
    - apply (PolymerRepresentation.pf_drop_zero absIncompat (rho t) z2_closed
               (length (filter absConnb (PenroseTreeBound.sublists Lambda))) _ (le_n _)).
      intros g Hg. unfold rho. rewrite Hg. reflexivity.
    - apply (PolymerRepresentation.pf_ext z2_poly_incompat).
      intros g Hg. apply filter_In in Hg. destruct Hg as [_ Hc].
      unfold rho. rewrite Hc. reflexivity.
  Qed.

  (* TARGET 7c *)
  Theorem z2_surface_polymer_gas : Challenge_Z2Gauge4D_SurfacePolymerGas.
  Proof.
    intros beta Lambda Hnd. rewrite partition_fn_expand. f_equal.
    exact (surface_sum_polymer (tanh beta) Lambda Hnd).
  Qed.

End Z2PolymerGas.
