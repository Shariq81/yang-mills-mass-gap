(* =========================================================================
   rg/polymer_representation.v

   Exact polymer-gas representation of sums over subsets with a factorizing
   weight (the combinatorial step behind every strong-coupling expansion of
   a lattice gauge theory).

   Setting.
     - "plaquettes" of type B, each carrying a nonempty list of "links"
       supp b : list L; two plaquettes TOUCH when they share a link;
     - a weight rho on lists of plaquettes with rho [] = 1 that FACTORIZES
       over non-touching parts:
         rho S = rho (filter f S) * rho (filter (negb o f) S)
       whenever no plaquette selected by f touches an unselected one.

   Theorem (`polymer_representation`).  For every duplicate-free list Lam,

       sum_{S <= Lam} rho S
         = partition_fn incompat (connected sublists of Lam) rho,

     the hard-core polymer partition function of
     `rg/cluster_log_partition.v`, where the polymers are the sublists of Lam
     that are connected under `touch` (in the index-graph sense of
     `rg/penrose_tree_bound.v`) and two polymers are incompatible when a
     plaquette of one touches a plaquette of the other.

   Proof.  Induction on Lam, peeling off the first plaquette p0.  A subset
   containing p0 splits uniquely into the touch-component of p0 and a rest
   that does not touch it; the weight factorizes over this splitting, and
   the polymer partition function obeys the same recursion.

   Depends ONLY on Coq stdlib + rg.dup_clustering (finite sums, chains)
   + the Kotecky-Preiss engine files of the verification cone.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra.
From rg Require Import dup_clustering.
From rg Require Import penrose_tree_bound poly_exp_bound tree_cut_bijection
                       kotecky_preiss exp_series_limit cluster_log_partition.
Import ListNotations.
Import DupClustering.
Import PenroseTreeBound PolyExpBound TreeCutBijection KoteckyPreiss ExpSeriesLimit
       ClusterLogPartition.
Open Scope R_scope.

Module PolymerRepresentation.

  (* =======================================================================
     1. Generic list lemmas
     ======================================================================= *)

  Lemma filter_comm : forall {A : Type} (f g : A -> bool) (l : list A),
    filter f (filter g l) = filter g (filter f l).
  Proof.
    intros A f g l. induction l as [| a l IH]; [reflexivity |].
    simpl. destruct (g a) eqn:Hg; destruct (f a) eqn:Hf; simpl;
      rewrite ?Hg, ?Hf, IH; reflexivity.
  Qed.

  Lemma filter_map_swap : forall {A C : Type} (h : A -> C) (g : C -> bool) (l : list A),
    filter g (map h l) = map h (filter (fun x => g (h x)) l).
  Proof.
    intros A C h g l. induction l as [| a l IH]; [reflexivity |].
    simpl. destruct (g (h a)); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma filter_all_false : forall {A : Type} (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = false) -> filter f l = [].
  Proof.
    intros A f l H. induction l as [| a l IH]; [reflexivity |].
    simpl. rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma existsb_swap : forall {A C : Type} (f : A -> C -> bool) (l1 : list A) (l2 : list C),
    existsb (fun a => existsb (f a) l2) l1 = existsb (fun b => existsb (fun a => f a b) l1) l2.
  Proof.
    intros A C f l1 l2. apply eq_true_iff_eq. rewrite !existsb_exists. split.
    - intros [x [Hx H]]. apply existsb_exists in H. destruct H as [y [Hy H]].
      exists y. split; [exact Hy |]. apply existsb_exists. exists x. split; assumption.
    - intros [y [Hy H]]. apply existsb_exists in H. destruct H as [x [Hx H]].
      exists x. split; [exact Hx |]. apply existsb_exists. exists y. split; assumption.
  Qed.

  Lemma existsb_false_In : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
    existsb f l = false -> In x l -> f x = false.
  Proof.
    intros A f l x Hf Hx. destruct (f x) eqn:E; [| reflexivity].
    assert (Hyes : existsb f l = true) by (apply existsb_exists; exists x; split; assumption).
    congruence.
  Qed.

  Lemma rsum_sublists_cons : forall {A : Type} (a : A) (l : list A) (F : list A -> R),
    rsum (sublists (a :: l)) F =
    rsum (sublists l) F + rsum (sublists l) (fun S => F (a :: S)).
  Proof. intros A a l F. cbn [sublists]. rewrite rsum_app, rsum_map. reflexivity. Qed.

  Lemma rsum_unique : forall {A : Type} (l : list A) (Pb : A -> bool) (x0 : A),
    NoDup l -> In x0 l -> Pb x0 = true ->
    (forall y, In y l -> Pb y = true -> y = x0) ->
    rsum l (fun y => if Pb y then 1 else 0) = 1.
  Proof.
    intros A l Pb x0 Hnd. induction Hnd as [| a l Hna Hnd IH]; intros Hin Hp Huniq;
      [contradiction |].
    rewrite rsum_cons. destruct Hin as [Heq | Hin].
    - subst a. rewrite Hp.
      rewrite (rsum_zero l (fun y => if Pb y then 1 else 0)); [ring |].
      intros y Hy. destruct (Pb y) eqn:Hy'; [| reflexivity].
      exfalso. apply Hna. rewrite <- (Huniq y (or_intror Hy) Hy'). exact Hy.
    - assert (Hpa : Pb a = false).
      { destruct (Pb a) eqn:Ha; [| reflexivity]. exfalso. apply Hna.
        rewrite (Huniq a (or_introl eq_refl) Ha). exact Hin. }
      rewrite Hpa, IH; [ring | exact Hin | exact Hp |].
      intros y Hy. apply Huniq. right. exact Hy.
  Qed.

  Lemma filter_forallb_sublists : forall {A : Type} (Pb : A -> bool) (l : list A),
    filter (forallb Pb) (sublists l) = sublists (filter Pb l).
  Proof.
    intros A Pb l. induction l as [| a l IH]; [reflexivity |].
    cbn [sublists filter]. rewrite filter_app, filter_map_swap, IH.
    destruct (Pb a) eqn:Ha.
    - cbn [sublists]. f_equal. f_equal.
      rewrite <- IH. apply filter_ext. intro S. cbn [forallb]. rewrite Ha. reflexivity.
    - rewrite (filter_all_false (fun x => forallb Pb (a :: x)) (sublists l)).
      + cbn [map]. apply app_nil_r.
      + intros S _. cbn [forallb]. rewrite Ha. reflexivity.
  Qed.

  (* =======================================================================
     2. Polymer partition function: cliques, extensionality, zero activities
     ======================================================================= *)

  Section PF.
    Context {P : Type} (ob : P -> P -> bool).
    Hypothesis ob_sym : forall x y, ob x y = ob y x.

    Lemma pf_clique : forall (w : P -> R) (Q : list P),
      (forall x y, In x Q -> In y Q -> ob x y = true) ->
      partition_fn ob Q w = 1 + rsum Q w.
    Proof.
      intros w Q. induction Q as [| x Q IH]; intro Hc.
      - rewrite partition_fn_nil, rsum_nil. ring.
      - rewrite partition_fn_cons, rsum_cons.
        rewrite (filter_all_false (fun q => negb (ob x q)) Q).
        + rewrite partition_fn_nil, IH; [ring |].
          intros a b Ha Hb. apply Hc; right; assumption.
        + intros q Hq. rewrite (Hc x q (or_introl eq_refl) (or_intror Hq)). reflexivity.
    Qed.

    (* Appending a family Q of pairwise incompatible polymers *)
    Lemma pf_app_clique : forall (w : P -> R) (n : nat) (Lp Q : list P),
      (length Lp <= n)%nat ->
      (forall x y, In x Q -> In y Q -> ob x y = true) ->
      partition_fn ob (Lp ++ Q) w =
      partition_fn ob Lp w +
      rsum Q (fun g => w g * partition_fn ob (filter (fun q => negb (ob g q)) Lp) w).
    Proof.
      intros w n. induction n as [| n IH]; intros Lp Q Hlen Hc.
      - destruct Lp as [| x Lp']; [| simpl in Hlen; lia].
        cbn [app]. rewrite (pf_clique w Q Hc), partition_fn_nil. f_equal.
        apply rsum_ext. intros g _. cbn [filter]. rewrite partition_fn_nil. ring.
      - destruct Lp as [| x Lp'].
        + cbn [app]. rewrite (pf_clique w Q Hc), partition_fn_nil. f_equal.
          apply rsum_ext. intros g _. cbn [filter]. rewrite partition_fn_nil. ring.
        + assert (Hlen' : (length Lp' <= n)%nat) by (simpl in Hlen; lia).
          assert (HcF : forall a b,
                    In a (filter (fun q => negb (ob x q)) Q) ->
                    In b (filter (fun q => negb (ob x q)) Q) -> ob a b = true).
          { intros a b Ha Hb. apply filter_In in Ha. apply filter_In in Hb.
            apply Hc; tauto. }
          assert (HlenF : (length (filter (fun q => negb (ob x q)) Lp') <= n)%nat).
          { pose proof (length_filter_le (fun q => negb (ob x q)) Lp'). lia. }
          cbn [app]. rewrite !partition_fn_cons, filter_app.
          rewrite (IH Lp' Q Hlen' Hc).
          rewrite (IH (filter (fun q => negb (ob x q)) Lp')
                      (filter (fun q => negb (ob x q)) Q) HlenF HcF).
          rewrite rsum_filter.
          transitivity
            (partition_fn ob Lp' w +
             w x * partition_fn ob (filter (fun q => negb (ob x q)) Lp') w +
             rsum Q (fun g =>
               w g * partition_fn ob (filter (fun q => negb (ob g q)) Lp') w +
               w x * (if negb (ob x g)
                      then w g * partition_fn ob
                                   (filter (fun q => negb (ob g q))
                                      (filter (fun q => negb (ob x q)) Lp')) w
                      else 0))).
          * rewrite rsum_plus, rsum_scal. ring.
          * f_equal. apply rsum_ext. intros g _. cbn [filter].
            rewrite (ob_sym x g).
            destruct (ob g x); cbn [negb].
            -- ring.
            -- rewrite partition_fn_cons.
               rewrite (filter_comm (fun q => negb (ob g q)) (fun q => negb (ob x q)) Lp').
               ring.
    Qed.

    Lemma pf_ext : forall (w w' : P -> R) (Lp : list P),
      (forall g, In g Lp -> w g = w' g) ->
      partition_fn ob Lp w = partition_fn ob Lp w'.
    Proof.
      intros w w' Lp H. unfold partition_fn. apply fold_right_Rplus_ext. intros S HS.
      destruct (pairwise_compat ob S); [| reflexivity].
      unfold prod_weight. f_equal. apply map_ext_in. intros g Hg. apply H.
      exact (sublists_incl Lp S HS g Hg).
    Qed.

    (* Polymers of zero activity can be discarded *)
    Lemma pf_drop_zero : forall (w : P -> R) (keep : P -> bool) (n : nat) (Lp : list P),
      (length Lp <= n)%nat ->
      (forall g, keep g = false -> w g = 0) ->
      partition_fn ob Lp w = partition_fn ob (filter keep Lp) w.
    Proof.
      intros w keep n. induction n as [| n IH]; intros Lp Hlen Hz.
      - destruct Lp; [reflexivity | simpl in Hlen; lia].
      - destruct Lp as [| x Lp']; [reflexivity |].
        assert (Hlen' : (length Lp' <= n)%nat) by (simpl in Hlen; lia).
        assert (HlenF : (length (filter (fun q => negb (ob x q)) Lp') <= n)%nat).
        { pose proof (length_filter_le (fun q => negb (ob x q)) Lp'). lia. }
        rewrite partition_fn_cons. cbn [filter]. destruct (keep x) eqn:Hk.
        + rewrite partition_fn_cons.
          rewrite (IH Lp' Hlen' Hz).
          rewrite (IH (filter (fun q => negb (ob x q)) Lp') HlenF Hz).
          rewrite (filter_comm keep (fun q => negb (ob x q)) Lp'). reflexivity.
        + rewrite (Hz x Hk), (IH Lp' Hlen' Hz). ring.
    Qed.
  End PF.

  (* =======================================================================
     3. Plaquettes with link supports: touching, connectivity, components
     ======================================================================= *)

  Section PolyRep.
    Variables (L B : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable eqbB : B -> B -> bool.
    Hypothesis eqbB_spec : forall x y, eqbB x y = true <-> x = y.
    Variable supp : B -> list L.
    Hypothesis supp_nonempty : forall b, supp b <> [].

    Definition touch (p q : B) : bool := touchb L eqbL (supp p) (supp q).

    Lemma touch_true : forall p q,
      touch p q = true <-> exists e, In e (supp p) /\ In e (supp q).
    Proof. intros p q. unfold touch. apply (touchb_true L eqbL eqbL_spec). Qed.

    Lemma touch_sym : forall p q, touch p q = touch q p.
    Proof.
      intros p q. apply eq_true_iff_eq. rewrite !touch_true.
      split; intros [e [H1 H2]]; exists e; split; assumption.
    Qed.

    Lemma touch_refl : forall p, touch p p = true.
    Proof.
      intro p. apply touch_true. pose proof (supp_nonempty p) as Hne.
      destruct (supp p) as [| e rest]; [congruence |]. exists e. split; left; reflexivity.
    Qed.

    (* q touches some plaquette of g *)
    Definition ptouch (g : list B) (q : B) : bool := existsb (fun p => touch p q) g.

    (* polymer incompatibility: some plaquette of g1 touches some plaquette of g2
       (the empty list is incompatible only with itself) *)
    Definition incompat (g1 g2 : list B) : bool :=
      match g1, g2 with
      | [], [] => true
      | _, _ => existsb (fun p => existsb (touch p) g2) g1
      end.

    Lemma incompat_cons : forall p g g2,
      incompat (p :: g) g2 = existsb (fun q => ptouch (p :: g) q) g2.
    Proof.
      intros p g g2. unfold ptouch.
      exact (existsb_swap (fun a b => touch a b) (p :: g) g2).
    Qed.

    Lemma incompat_sym : forall g1 g2, incompat g1 g2 = incompat g2 g1.
    Proof.
      intros g1 g2.
      assert (HE : existsb (fun p => existsb (touch p) g2) g1 =
                   existsb (fun p => existsb (touch p) g1) g2).
      { apply eq_true_iff_eq. rewrite !existsb_exists.
        split; intros [x [Hx H]]; apply existsb_exists in H; destruct H as [y [Hy H]];
          exists y; (split; [exact Hy |]); apply existsb_exists; exists x;
          (split; [exact Hx |]); rewrite touch_sym; exact H. }
      destruct g1, g2; first [reflexivity | exact HE].
    Qed.

    Lemma incompat_refl : forall g, incompat g g = true.
    Proof.
      intros [| p g]; [reflexivity |].
      unfold incompat. cbn [existsb]. rewrite touch_refl. reflexivity.
    Qed.

    Definition connb (S : list B) : bool :=
      is_connectedb (length S) (graph_edges touch S).

    (* complement of G inside S *)
    Definition cmpl (S G : list B) : list B :=
      filter (fun b => negb (memb eqbB b G)) S.

    Lemma cmpl_In : forall S G q, In q (cmpl S G) <-> (In q S /\ ~ In q G).
    Proof.
      intros S G q. unfold cmpl. rewrite filter_In, negb_true_iff.
      rewrite (memb_false eqbB eqbB_spec). reflexivity.
    Qed.

    Lemma cmpl_cons_out : forall a S G, ~ In a G -> cmpl (a :: S) G = a :: cmpl S G.
    Proof.
      intros a S G Hna. unfold cmpl. cbn [filter].
      rewrite (proj2 (memb_false eqbB eqbB_spec a G) Hna). reflexivity.
    Qed.

    Lemma cmpl_cons_in : forall a S G, ~ In a S -> cmpl (a :: S) (a :: G) = cmpl S G.
    Proof.
      intros a S G Hna. unfold cmpl. cbn [filter].
      rewrite (proj2 (memb_In eqbB eqbB_spec a (a :: G)) (or_introl eq_refl)). cbn [negb].
      apply filter_ext_in. intros b Hb.
      assert (Hne : eqbB b a = false).
      { destruct (eqbB b a) eqn:E; [| reflexivity]. apply eqbB_spec in E. subst b. contradiction. }
      unfold memb. cbn [existsb]. rewrite Hne. reflexivity.
    Qed.

    (* ---------- element-level paths versus index-graph connectivity ---------- *)

    Inductive epath (X : list B) : B -> B -> Prop :=
    | ep_refl : forall x, In x X -> epath X x x
    | ep_step : forall x y z,
        In x X -> In y X -> touch x y = true -> epath X y z -> epath X x z.

    Lemma index_edge : forall X i k x y,
      nth_error X i = Some x -> nth_error X k = Some y -> i <> k ->
      touch x y = true -> has_edge (graph_edges touch X) i k.
    Proof.
      intros X i k x y Hi Hk Hne Ht.
      assert (Hil : (i < length X)%nat) by (apply nth_error_Some; congruence).
      assert (Hkl : (k < length X)%nat) by (apply nth_error_Some; congruence).
      destruct (Nat.lt_ge_cases i k) as [Hlt | Hge].
      - left. apply graph_edges_in. split; [exact Hlt |]. split; [exact Hkl |].
        exists x, y. split; [exact Hi |]. split; [exact Hk | exact Ht].
      - right. apply graph_edges_in. split; [lia |]. split; [exact Hil |].
        exists y, x. split; [exact Hk |]. split; [exact Hi |]. rewrite touch_sym. exact Ht.
    Qed.

    Lemma epath_reachable : forall X, NoDup X -> forall x z, epath X x z ->
      forall i j, nth_error X i = Some x -> nth_error X j = Some z ->
      reachable (graph_edges touch X) i j.
    Proof.
      intros X Hnd x z Hp.
      induction Hp as [x Hx | x y z Hx Hy Ht Hp IH]; intros i j Hi Hj.
      - assert (Heq : i = j).
        { apply (proj1 (NoDup_nth_error X) Hnd).
          - apply nth_error_Some. congruence.
          - congruence. }
        subst j. apply reach_refl.
      - destruct (In_nth_error X y Hy) as [k Hk].
        destruct (Nat.eq_dec i k) as [Heq | Hne].
        + subst k. apply IH; assumption.
        + eapply reach_step; [exact (index_edge X i k x y Hi Hk Hne Ht) |].
          exact (IH k j Hk Hj).
    Qed.

    Lemma reachable_epath : forall X i j, reachable (graph_edges touch X) i j ->
      forall x, nth_error X i = Some x ->
      exists z, nth_error X j = Some z /\ epath X x z.
    Proof.
      intros X i j Hr. induction Hr as [u | u v w He Hr IH]; intros x Hx.
      - exists x. split; [exact Hx |]. apply ep_refl. eapply nth_error_In. exact Hx.
      - destruct He as [Hin | Hin]; apply graph_edges_in in Hin;
          destruct Hin as [_ [_ [a [b [Ha [Hb Hab]]]]]].
        + rewrite Hx in Ha. injection Ha as Ha. subst a.
          destruct (IH b Hb) as [z [Hz Hp]]. exists z. split; [exact Hz |].
          eapply ep_step; [eapply nth_error_In; exact Hx | eapply nth_error_In; exact Hb
                          | exact Hab | exact Hp].
        + rewrite Hx in Hb. injection Hb as Hb. subst b.
          destruct (IH a Ha) as [z [Hz Hp]]. exists z. split; [exact Hz |].
          eapply ep_step; [eapply nth_error_In; exact Hx | eapply nth_error_In; exact Ha
                          | rewrite touch_sym; exact Hab | exact Hp].
    Qed.

    Lemma connb_iff : forall x0 X, NoDup (x0 :: X) ->
      (connb (x0 :: X) = true <-> forall y, In y (x0 :: X) -> epath (x0 :: X) x0 y).
    Proof.
      intros x0 X Hnd. unfold connb.
      pose proof (is_connectedb_iff (length (x0 :: X)) (graph_edges touch (x0 :: X))
                    (proj2 (graph_edges_wf touch (x0 :: X)))) as Hiff.
      split.
      - intros Hc y Hy. apply Hiff in Hc. destruct Hc as [_ Hall].
        destruct (In_nth_error _ _ Hy) as [j Hj].
        assert (Hjlt : (j < length (x0 :: X))%nat) by (apply nth_error_Some; congruence).
        destruct (reachable_epath (x0 :: X) 0 j (Hall j Hjlt) x0 eq_refl) as [z [Hz Hp]].
        rewrite Hj in Hz. injection Hz as Hz. subst z. exact Hp.
      - intro Hall. apply Hiff. split; [cbn [length]; lia |]. intros v Hv.
        destruct (nth_error (x0 :: X) v) as [y |] eqn:Hy.
        + exact (epath_reachable (x0 :: X) Hnd x0 y (Hall y (nth_error_In _ _ Hy)) 0 v eq_refl Hy).
        + apply nth_error_None in Hy. lia.
    Qed.

    (* ---------- chains (from rg/dup_clustering.v) and the component of p0 ---------- *)

    Local Notation chain := (chainf L B eqbL supp).
    Local Notation cend := (endS L B supp).
    Local Notation inKs := (inK L B eqbL eqbB supp).

    Lemma chain_elems_inK : forall (Sf : list L) (Rs om : list B) (b : B),
      NoDup om -> incl om Rs -> chain Sf om = true -> In b om ->
      forall e, In e (supp b) -> inKs Sf Rs e = true.
    Proof.
      intros Sf Rs om b Hnd Hincl Hch Hb e He.
      apply in_split in Hb. destruct Hb as [o1 [o2 Heq]]. subst om.
      unfold inK. apply (has_chain_to_true L B eqbL eqbB eqbB_spec supp Sf Rs [e]).
      exists (o1 ++ [b]). split; [exact (NoDup_prefix_snoc o1 o2 b Hnd) |]. split.
      - intros x Hx. apply in_app_or in Hx. apply Hincl. apply in_or_app.
        destruct Hx as [Hx | [Hx | []]]; [left; exact Hx | right; left; exact Hx].
      - rewrite chainf_app in Hch. cbn [chainf] in Hch.
        apply andb_true_iff in Hch. destruct Hch as [Hc1 Hc2].
        apply andb_true_iff in Hc2. destruct Hc2 as [Ht _].
        split.
        + rewrite chainf_app. cbn [chainf]. rewrite Hc1, Ht. reflexivity.
        + rewrite endS_app. cbn [endS]. apply (touchb_single L eqbL eqbL_spec). exact He.
    Qed.

    Lemma chain_epath : forall X om x q,
      In x X -> incl om X -> In q X ->
      chain (supp x) om = true ->
      touchb L eqbL (cend (supp x) om) (supp q) = true ->
      epath X x q.
    Proof.
      intros X om. induction om as [| b rest IH]; intros x q Hx Hincl Hq Hch Ht.
      - cbn [endS] in Ht.
        eapply ep_step; [exact Hx | exact Hq | exact Ht | apply ep_refl; exact Hq].
      - cbn [chainf] in Hch. apply andb_true_iff in Hch. destruct Hch as [Hxb Hrest].
        cbn [endS] in Ht.
        assert (Hb : In b X) by (apply Hincl; left; reflexivity).
        eapply ep_step; [exact Hx | exact Hb | exact Hxb |].
        apply IH; [exact Hb | | exact Hq | exact Hrest | exact Ht].
        intros y Hy. apply Hincl. right. exact Hy.
    Qed.

    (* q has a link reachable from p0 through the plaquettes of S *)
    Definition inC (p0 : B) (S : list B) (q : B) : bool :=
      existsb (inKs (supp p0) S) (supp q).

    (* the touch-component of p0 inside S (without p0 itself) *)
    Definition comp (p0 : B) (S : list B) : list B := filter (inC p0 S) S.

    Lemma inC_all : forall p0 S q, In q S -> inC p0 S q = true ->
      forall e, In e (supp q) -> inKs (supp p0) S e = true.
    Proof.
      intros p0 S q Hq HC e He. unfold inC in HC. apply existsb_exists in HC.
      destruct HC as [e0 [He0 HK]].
      exact (inK_block L B eqbL eqbL_spec eqbB eqbB_spec supp (supp p0) S q e0 Hq He0 HK e He).
    Qed.

    Lemma all_inC : forall p0 S q,
      (forall e, In e (supp q) -> inKs (supp p0) S e = true) -> inC p0 S q = true.
    Proof.
      intros p0 S q H. unfold inC. pose proof (supp_nonempty q) as Hne.
      destruct (supp q) as [| e rest] eqn:Hs; [congruence |].
      cbn [existsb]. rewrite (H e); [reflexivity |]. left. reflexivity.
    Qed.

    Lemma comp_notouch : forall p0 S q, In q S -> inC p0 S q = false ->
      ptouch (p0 :: comp p0 S) q = false.
    Proof.
      intros p0 S q Hq HC. destruct (ptouch (p0 :: comp p0 S) q) eqn:Hpt; [| reflexivity].
      exfalso. unfold ptouch in Hpt. apply existsb_exists in Hpt. destruct Hpt as [p [Hp Ht]].
      apply touch_true in Ht. destruct Ht as [e [Hep Heq]].
      assert (HKe : inKs (supp p0) S e = true).
      { destruct Hp as [Hp | Hp].
        - subst p. apply (inK_seed L B eqbL eqbL_spec eqbB eqbB_spec). exact Hep.
        - unfold comp in Hp. apply filter_In in Hp. destruct Hp as [HpS HpC].
          exact (inC_all p0 S p HpS HpC e Hep). }
      assert (Hyes : inC p0 S q = true).
      { unfold inC. apply existsb_exists. exists e. split; assumption. }
      congruence.
    Qed.

    Lemma comp_epath : forall p0 S q,
      In q (p0 :: comp p0 S) -> epath (p0 :: comp p0 S) p0 q.
    Proof.
      intros p0 S q [Hq | Hq].
      - subst q. apply ep_refl. left. reflexivity.
      - pose proof Hq as Hq'. unfold comp in Hq'. apply filter_In in Hq'.
        destruct Hq' as [HqS HqC].
        unfold inC in HqC. apply existsb_exists in HqC. destruct HqC as [e [He HK]].
        unfold inK in HK. apply (has_chain_to_true L B eqbL eqbB eqbB_spec) in HK.
        destruct HK as [om [Hnd [Hincl [Hch Ht]]]].
        apply (touchb_single L eqbL eqbL_spec) in Ht.
        apply (chain_epath (p0 :: comp p0 S) om p0 q).
        + left. reflexivity.
        + intros b Hb. right. unfold comp. apply filter_In. split; [apply Hincl; exact Hb |].
          apply all_inC. intros e' He'.
          exact (chain_elems_inK (supp p0) S om b Hnd Hincl Hch Hb e' He').
        + right. exact Hq.
        + exact Hch.
        + apply (touchb_true L eqbL eqbL_spec). exists e. split; assumption.
    Qed.

    Lemma epath_inK : forall p0 S G, incl G S ->
      forall y z, epath (p0 :: G) y z ->
      (forall e, In e (supp y) -> inKs (supp p0) S e = true) ->
      (forall e, In e (supp z) -> inKs (supp p0) S e = true).
    Proof.
      intros p0 S G HGS y z Hp.
      induction Hp as [x Hx | x y z Hx Hy Ht Hp IH]; intro HKx; [exact HKx |].
      apply IH. destruct Hy as [Hy | Hy].
      - subst y. intros e He. apply (inK_seed L B eqbL eqbL_spec eqbB eqbB_spec). exact He.
      - apply touch_true in Ht. destruct Ht as [e0 [He0x He0y]].
        intros e He.
        exact (inK_block L B eqbL eqbL_spec eqbB eqbB_spec supp (supp p0) S y e0
                 (HGS y Hy) He0y (HKx e0 He0x) e He).
    Qed.

    Lemma valid_sub_comp : forall p0 S G, NoDup (p0 :: G) -> incl G S ->
      connb (p0 :: G) = true -> forall x, In x G -> In x (comp p0 S).
    Proof.
      intros p0 S G Hnd HGS Hconn x Hx.
      pose proof (proj1 (connb_iff p0 G Hnd) Hconn x (or_intror Hx)) as Hp.
      unfold comp. apply filter_In. split; [apply HGS; exact Hx |].
      apply all_inC. apply (epath_inK p0 S G HGS p0 x Hp).
      intros e He. apply (inK_seed L B eqbL eqbL_spec eqbB eqbB_spec). exact He.
    Qed.

    Lemma touch_in_G : forall p0 S G,
      (forall q, In q S -> ~ In q G -> ptouch (p0 :: G) q = false) ->
      forall y q, In y (p0 :: G) -> In q S -> touch y q = true -> In q G.
    Proof.
      intros p0 S G Hnt y q Hy Hq Ht.
      destruct (memb eqbB q G) eqn:Hm; [apply (memb_In eqbB eqbB_spec); exact Hm |].
      apply (memb_false eqbB eqbB_spec) in Hm. exfalso.
      pose proof (Hnt q Hq Hm) as Hpt. unfold ptouch in Hpt.
      pose proof (existsb_false_In (fun p => touch p q) (p0 :: G) y Hpt Hy) as Hno.
      cbv beta in Hno. congruence.
    Qed.

    Lemma chain_in_G : forall p0 S G,
      (forall q, In q S -> ~ In q G -> ptouch (p0 :: G) q = false) ->
      forall om y q, In y (p0 :: G) -> incl om S -> In q S ->
      chain (supp y) om = true ->
      touchb L eqbL (cend (supp y) om) (supp q) = true ->
      In q G.
    Proof.
      intros p0 S G Hnt om. induction om as [| b rest IH]; intros y q Hy Hincl Hq Hch Ht.
      - cbn [endS] in Ht. exact (touch_in_G p0 S G Hnt y q Hy Hq Ht).
      - cbn [chainf] in Hch. apply andb_true_iff in Hch. destruct Hch as [Hyb Hrest].
        cbn [endS] in Ht.
        assert (HbS : In b S) by (apply Hincl; left; reflexivity).
        assert (HbG : In b G) by exact (touch_in_G p0 S G Hnt y b Hy HbS Hyb).
        apply (IH b q); [right; exact HbG | | exact Hq | exact Hrest | exact Ht].
        intros z Hz. apply Hincl. right. exact Hz.
    Qed.

    Lemma valid_comp_sub : forall p0 S G,
      (forall q, In q S -> ~ In q G -> ptouch (p0 :: G) q = false) ->
      forall x, In x (comp p0 S) -> In x G.
    Proof.
      intros p0 S G Hnt x Hx. unfold comp in Hx. apply filter_In in Hx.
      destruct Hx as [HxS HxC].
      unfold inC in HxC. apply existsb_exists in HxC. destruct HxC as [e [He HK]].
      unfold inK in HK. apply (has_chain_to_true L B eqbL eqbB eqbB_spec) in HK.
      destruct HK as [om [Hnd [Hincl [Hch Ht]]]].
      apply (touchb_single L eqbL eqbL_spec) in Ht.
      apply (chain_in_G p0 S G Hnt om p0 x);
        [left; reflexivity | exact Hincl | exact HxS | exact Hch |].
      apply (touchb_true L eqbL eqbL_spec). exists e. split; assumption.
    Qed.

    (* ---------- valid splittings: (p0 :: G) connected and the rest does not touch it ---------- *)

    Definition validb (p0 : B) (S G : list B) : bool :=
      connb (p0 :: G) && forallb (fun b => negb (ptouch (p0 :: G) b)) (cmpl S G).

    Lemma validb_notouch : forall p0 S G, validb p0 S G = true ->
      forall q, In q S -> ~ In q G -> ptouch (p0 :: G) q = false.
    Proof.
      intros p0 S G Hv q Hq Hnq. unfold validb in Hv.
      apply andb_true_iff in Hv. destruct Hv as [_ Hf].
      rewrite forallb_forall in Hf.
      assert (Hin : In q (cmpl S G)) by (apply cmpl_In; split; assumption).
      specialize (Hf q Hin). apply negb_true_iff in Hf. exact Hf.
    Qed.

    Lemma comp_valid : forall p0 S, NoDup (p0 :: S) -> validb p0 S (comp p0 S) = true.
    Proof.
      intros p0 S Hnd. inversion Hnd as [| p0' S' Hp0 HndS]; subst.
      unfold validb. apply andb_true_iff. split.
      - apply connb_iff.
        + constructor.
          * intro Hin. unfold comp in Hin. apply filter_In in Hin. tauto.
          * unfold comp. apply NoDup_filter. exact HndS.
        + exact (comp_epath p0 S).
      - apply forallb_forall. intros q Hq. apply cmpl_In in Hq. destruct Hq as [HqS Hnq].
        assert (HC : inC p0 S q = false).
        { destruct (inC p0 S q) eqn:E; [| reflexivity]. exfalso. apply Hnq.
          unfold comp. apply filter_In. split; assumption. }
        rewrite (comp_notouch p0 S q HqS HC). reflexivity.
    Qed.

    Lemma valid_unique : forall p0 S G, NoDup (p0 :: S) -> In G (sublists S) ->
      validb p0 S G = true -> G = comp p0 S.
    Proof.
      intros p0 S G Hnd HG Hv. inversion Hnd as [| p0' S' Hp0 HndS]; subst.
      pose proof (sublists_incl S G HG) as HGS.
      apply (sublists_ext S G (comp p0 S) HndS HG (filter_in_sublists (inC p0 S) S)).
      intro x. split.
      - apply valid_sub_comp; [| exact HGS |].
        + constructor; [intro Hin; apply Hp0; apply HGS; exact Hin |].
          exact (sublists_NoDup_elem S G HndS HG).
        + unfold validb in Hv. apply andb_true_iff in Hv. tauto.
      - apply valid_comp_sub. exact (validb_notouch p0 S G Hv).
    Qed.

    Lemma filter_memb_sublist : forall S G, NoDup S -> In G (sublists S) ->
      filter (fun b => memb eqbB b G) S = G.
    Proof.
      induction S as [| a S IH]; intros G Hnd HG.
      - cbn [sublists] in HG. destruct HG as [HG | []]. subst G. reflexivity.
      - inversion Hnd as [| a' S' Hna HndS]; subst.
        cbn [sublists] in HG. apply in_app_or in HG. destruct HG as [HG | HG].
        + cbn [filter].
          assert (Hm : memb eqbB a G = false).
          { apply (memb_false eqbB eqbB_spec). intro Hin. apply Hna.
            exact (sublists_incl S G HG a Hin). }
          rewrite Hm. apply IH; assumption.
        + apply in_map_iff in HG. destruct HG as [G' [HG'eq HG']]. subst G.
          cbn [filter].
          rewrite (proj2 (memb_In eqbB eqbB_spec a (a :: G')) (or_introl eq_refl)).
          f_equal.
          transitivity (filter (fun b => memb eqbB b G') S); [| apply IH; assumption].
          apply filter_ext_in. intros b Hb.
          assert (Hne : eqbB b a = false).
          { destruct (eqbB b a) eqn:E; [| reflexivity].
            apply eqbB_spec in E. subst b. contradiction. }
          unfold memb. cbn [existsb]. rewrite Hne. reflexivity.
    Qed.

    (* ---------- the factorizing weight ---------- *)

    Variable rho : list B -> R.
    Hypothesis rho_nil : rho [] = 1.
    Hypothesis rho_factor : forall (S : list B) (f : B -> bool),
      (forall p q, In p S -> In q S -> f p = true -> f q = false -> touch p q = false) ->
      rho S = rho (filter f S) * rho (filter (fun b => negb (f b)) S).

    Lemma valid_factor : forall p0 S G, NoDup (p0 :: S) -> In G (sublists S) ->
      validb p0 S G = true -> rho (p0 :: G) * rho (cmpl S G) = rho (p0 :: S).
    Proof.
      intros p0 S G Hnd HG Hv. inversion Hnd as [| p0' S' Hp0 HndS]; subst.
      pose proof (sublists_incl S G HG) as HGS.
      assert (Hneq : forall b, In b S -> eqbB b p0 = false).
      { intros b Hb. destruct (eqbB b p0) eqn:E; [| reflexivity].
        apply eqbB_spec in E. subst b. contradiction. }
      set (f := fun b : B => memb eqbB b (p0 :: G)).
      assert (Hfp0 : f p0 = true).
      { unfold f. apply (memb_In eqbB eqbB_spec). left. reflexivity. }
      assert (HfS : forall b, In b S -> f b = memb eqbB b G).
      { intros b Hb. unfold f, memb. cbn [existsb]. rewrite (Hneq b Hb). reflexivity. }
      assert (Hf1 : filter f (p0 :: S) = p0 :: G).
      { cbn [filter]. rewrite Hfp0. f_equal.
        transitivity (filter (fun b => memb eqbB b G) S);
          [| apply filter_memb_sublist; assumption].
        apply filter_ext_in. exact HfS. }
      assert (Hf2 : filter (fun b => negb (f b)) (p0 :: S) = cmpl S G).
      { cbn [filter]. rewrite Hfp0. cbn [negb]. unfold cmpl.
        apply filter_ext_in. intros b Hb. rewrite (HfS b Hb). reflexivity. }
      rewrite <- Hf1 at 1. rewrite <- Hf2. symmetry. apply rho_factor.
      intros p q Hp Hq Hfp Hfq.
      assert (HpG : In p (p0 :: G)).
      { unfold f in Hfp. apply (memb_In eqbB eqbB_spec) in Hfp. exact Hfp. }
      assert (HqnG : ~ In q (p0 :: G)).
      { unfold f in Hfq. apply (memb_false eqbB eqbB_spec) in Hfq. exact Hfq. }
      assert (HqS : In q S).
      { destruct Hq as [Hq | Hq]; [| exact Hq]. exfalso. apply HqnG. left. exact Hq. }
      assert (HqG : ~ In q G) by (intro Hin; apply HqnG; right; exact Hin).
      pose proof (validb_notouch p0 S G Hv q HqS HqG) as Hpt. unfold ptouch in Hpt.
      exact (existsb_false_In (fun p' => touch p' q) (p0 :: G) p Hpt HpG).
    Qed.

    Lemma split_sum : forall p0 S, NoDup (p0 :: S) ->
      rsum (sublists S)
        (fun G => if validb p0 S G then rho (p0 :: G) * rho (cmpl S G) else 0)
      = rho (p0 :: S).
    Proof.
      intros p0 S Hnd. inversion Hnd as [| p0' S' Hp0 HndS]; subst.
      transitivity
        (rsum (sublists S) (fun G => rho (p0 :: S) * (if validb p0 S G then 1 else 0))).
      - apply rsum_ext. intros G HG. destruct (validb p0 S G) eqn:Hv; [| ring].
        rewrite (valid_factor p0 S G Hnd HG Hv). ring.
      - rewrite rsum_scal.
        rewrite (rsum_unique (sublists S) (validb p0 S) (comp p0 S)).
        + ring.
        + apply sublists_NoDup_list. exact HndS.
        + exact (filter_in_sublists (inC p0 S) S).
        + apply comp_valid. exact Hnd.
        + intros G HG Hv. exact (valid_unique p0 S G Hnd HG Hv).
    Qed.

    (* ---------- pairs of disjoint subsets versus subsets with a splitting ---------- *)

    Lemma merge_sum : forall (l : list B), NoDup l ->
      forall (F : list B -> list B -> R),
      (forall G T, In G (sublists l) -> In T (sublists l) ->
                   (exists x, In x G /\ In x T) -> F G T = 0) ->
      rsum (sublists l) (fun G => rsum (sublists l) (fun T => F G T)) =
      rsum (sublists l) (fun S => rsum (sublists S) (fun G => F G (cmpl S G))).
    Proof.
      intros l Hnd. induction Hnd as [| a l Hna Hnd IH]; intros F Hvan.
      - cbn [sublists]. rewrite !rsum_cons, !rsum_nil. cbn [sublists].
        rewrite !rsum_cons, !rsum_nil. unfold cmpl. cbn [filter]. ring.
      - assert (Hin0 : forall G, In G (sublists l) -> In G (sublists (a :: l))).
        { intros G HG. cbn [sublists]. apply in_or_app. left. exact HG. }
        assert (Hin1 : forall G, In G (sublists l) -> In (a :: G) (sublists (a :: l))).
        { intros G HG. cbn [sublists]. apply in_or_app. right. apply in_map. exact HG. }
        assert (HL :
          rsum (sublists (a :: l)) (fun G => rsum (sublists (a :: l)) (fun T => F G T)) =
          rsum (sublists l) (fun G => rsum (sublists l) (fun T => F G T)) +
          rsum (sublists l) (fun G => rsum (sublists l) (fun T => F G (a :: T))) +
          rsum (sublists l) (fun G => rsum (sublists l) (fun T => F (a :: G) T))).
        { rewrite rsum_sublists_cons. cbv beta. f_equal.
          - rewrite <- rsum_plus. apply rsum_ext. intros G _.
            exact (rsum_sublists_cons a l (fun T => F G T)).
          - apply rsum_ext. intros G HG.
            rewrite (rsum_sublists_cons a l (fun T => F (a :: G) T)). cbv beta.
            rewrite (rsum_zero (sublists l) (fun T => F (a :: G) (a :: T))); [ring |].
            intros T HT. apply Hvan; [exact (Hin1 G HG) | exact (Hin1 T HT) |].
            exists a. split; left; reflexivity. }
        assert (HR :
          rsum (sublists (a :: l)) (fun S => rsum (sublists S) (fun G => F G (cmpl S G))) =
          rsum (sublists l) (fun S => rsum (sublists S) (fun G => F G (cmpl S G))) +
          rsum (sublists l) (fun S => rsum (sublists S) (fun G => F G (a :: cmpl S G))) +
          rsum (sublists l) (fun S => rsum (sublists S) (fun G => F (a :: G) (cmpl S G)))).
        { rewrite rsum_sublists_cons. cbv beta. rewrite Rplus_assoc. f_equal.
          rewrite <- rsum_plus. apply rsum_ext. intros S HS.
          rewrite (rsum_sublists_cons a S (fun G => F G (cmpl (a :: S) G))). cbv beta.
          f_equal.
          - apply rsum_ext. intros G HG. f_equal. apply cmpl_cons_out.
            intro Hin. apply Hna. apply (sublists_incl l S HS). apply (sublists_incl S G HG).
            exact Hin.
          - apply rsum_ext. intros G HG. f_equal. apply cmpl_cons_in.
            intro Hin. apply Hna. exact (sublists_incl l S HS a Hin). }
        rewrite HL, HR. f_equal; [f_equal |].
        + apply IH. intros G T HG HT Hx. apply Hvan; [exact (Hin0 G HG) | exact (Hin0 T HT) | exact Hx].
        + refine (IH (fun G T => F G (a :: T)) _).
          intros G T HG HT [x [HxG HxT]].
          apply Hvan; [exact (Hin0 G HG) | exact (Hin1 T HT) |].
          exists x. split; [exact HxG | right; exact HxT].
        + refine (IH (fun G T => F (a :: G) T) _).
          intros G T HG HT [x [HxG HxT]].
          apply Hvan; [exact (Hin1 G HG) | exact (Hin0 T HT) |].
          exists x. split; [right; exact HxG | exact HxT].
    Qed.

    (* ---------- the polymers and the representation theorem ---------- *)

    Definition polys (l : list B) : list (list B) := filter connb (sublists l).

    Lemma polys_cons : forall p0 l,
      polys (p0 :: l) =
      polys l ++ map (cons p0) (filter (fun S => connb (p0 :: S)) (sublists l)).
    Proof.
      intros p0 l. unfold polys. cbn [sublists]. rewrite filter_app, filter_map_swap.
      reflexivity.
    Qed.

    Lemma polys_nil : polys [] = [].
    Proof. reflexivity. Qed.

    Lemma compat_filter_polys : forall p0 G l,
      filter (fun q => negb (incompat (p0 :: G) q)) (polys l) =
      polys (filter (fun b => negb (ptouch (p0 :: G) b)) l).
    Proof.
      intros p0 G l. unfold polys.
      rewrite <- filter_forallb_sublists, (filter_comm connb).
      apply filter_ext. intro q. rewrite incompat_cons.
      exact (eq_sym (forallb_negb_eq_negb_existsb (fun b => ptouch (p0 :: G) b) q)).
    Qed.

    Lemma polymer_representation_aux : forall n l, (length l <= n)%nat -> NoDup l ->
      rsum (sublists l) rho = partition_fn incompat (polys l) rho.
    Proof.
      induction n as [| n IH]; intros l Hlen Hnd.
      - destruct l as [| p0 l']; [| simpl in Hlen; lia].
        cbn [sublists]. rewrite rsum_cons, rsum_nil, rho_nil, polys_nil, partition_fn_nil. ring.
      - destruct l as [| p0 l'].
        + cbn [sublists]. rewrite rsum_cons, rsum_nil, rho_nil, polys_nil, partition_fn_nil. ring.
        + inversion Hnd as [| p0' l'' Hp0 Hnd']; subst.
          assert (Hlen' : (length l' <= n)%nat) by (simpl in Hlen; lia).
          rewrite rsum_sublists_cons, polys_cons.
          rewrite (pf_app_clique incompat incompat_sym rho (length (polys l')) (polys l')
                     (map (cons p0) (filter (fun S => connb (p0 :: S)) (sublists l')))
                     (le_n _)).
          2: { intros x y Hx Hy. apply in_map_iff in Hx. destruct Hx as [S1 [Hx _]].
               apply in_map_iff in Hy. destruct Hy as [S2 [Hy _]]. subst x y.
               unfold incompat. cbn [existsb]. rewrite touch_refl. reflexivity. }
          rewrite <- (IH l' Hlen' Hnd'). f_equal.
          rewrite rsum_map, rsum_filter.
          set (FF := fun G T : list B =>
                 if connb (p0 :: G) && forallb (fun b => negb (ptouch (p0 :: G) b)) T
                 then rho (p0 :: G) * rho T else 0).
          transitivity (rsum (sublists l') (fun G => rsum (sublists l') (fun T => FF G T))).
          * rewrite (merge_sum l' Hnd' FF).
            -- apply rsum_ext. intros S HS. symmetry.
               assert (HndS : NoDup (p0 :: S)).
               { constructor.
                 - intro Hin. apply Hp0. exact (sublists_incl l' S HS p0 Hin).
                 - exact (sublists_NoDup_elem l' S Hnd' HS). }
               exact (split_sum p0 S HndS).
            -- intros G T HG HT [x [HxG HxT]]. unfold FF.
               destruct (connb (p0 :: G)); cbn [andb]; [| reflexivity].
               destruct (forallb (fun b => negb (ptouch (p0 :: G) b)) T) eqn:Hf; [| reflexivity].
               exfalso. rewrite forallb_forall in Hf. specialize (Hf x HxT).
               apply negb_true_iff in Hf. unfold ptouch in Hf.
               pose proof (existsb_false_In (fun p => touch p x) (p0 :: G) x Hf (or_intror HxG)) as Hno.
               cbv beta in Hno. rewrite touch_refl in Hno. discriminate.
          * apply rsum_ext. intros G HG. unfold FF.
            destruct (connb (p0 :: G)) eqn:Hc; cbn [andb].
            -- rewrite compat_filter_polys.
               assert (HlenF : (length (filter (fun b => negb (ptouch (p0 :: G) b)) l') <= n)%nat).
               { pose proof (length_filter_le (fun b => negb (ptouch (p0 :: G) b)) l'). lia. }
               rewrite <- (IH (filter (fun b => negb (ptouch (p0 :: G) b)) l') HlenF
                              (NoDup_filter _ Hnd')).
               rewrite <- rsum_scal.
               exact (fold_right_Rplus_sublists_filter
                        (fun b => negb (ptouch (p0 :: G) b)) l'
                        (fun T => rho (p0 :: G) * rho T)).
            -- apply rsum_zero. intros T _. reflexivity.
    Qed.

    Theorem polymer_representation : forall Lam, NoDup Lam ->
      rsum (sublists Lam) rho =
      partition_fn incompat (filter connb (sublists Lam)) rho.
    Proof.
      intros Lam Hnd. exact (polymer_representation_aux (length Lam) Lam (le_n _) Hnd).
    Qed.

  End PolyRep.

End PolymerRepresentation.
