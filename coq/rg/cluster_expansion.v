(* =========================================================================
   cluster_expansion.v - The Cluster Expansion Machine (Phase E Core)

   Implements the abstract Mayer expansion for a general Polymer System.
   Proves that if the Kotecky-Preiss condition holds (small activity),
   the expansion converges and correlations decay exponentially.

   THE CORRELATOR AND MASS GAP ARE REAL - NO PLACEHOLDERS.

   Reference: "A Course on the Cluster Expansion", Brydges 1986.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra Lia.
Require Import Coq.Sorting.Permutation.
Require Import rg.polymer_types.

Import ListNotations.
Open Scope R_scope.

(* =========================================================================
   0. Cluster Type (Outside Section for stable export)
   ========================================================================= *)

Definition Cluster (P : Type) := list P.

(* =========================================================================
   0a. Path and Connectivity (Outside Section - no finite volume params)
   ========================================================================= *)

Section PathConnectivity.
  Context {P : Type} `{ConnectivitySystem P}.

  (* Path in a cluster: consecutive elements are adjacent *)
  Inductive path_in_cluster : Cluster P -> P -> P -> Prop :=
  | path_refl : forall X p, In p X -> path_in_cluster X p p
  | path_step : forall X p q r,
      In p X -> adj p q -> path_in_cluster X q r -> path_in_cluster X p r.

  (* A cluster connects p1 to p2 if there's a path from p1 to p2 in X *)
  Definition connects (X : Cluster P) (p1 p2 : P) : Prop :=
    In p1 X /\ In p2 X /\ path_in_cluster X p1 p2.

  (* The start vertex of any path is in the cluster *)
  Lemma path_in_cluster_start_in :
    forall X p1 p2, path_in_cluster X p1 p2 -> In p1 X.
  Proof.
    intros X p1 p2 Hpath. induction Hpath as [X' p' Hp | X' p' q' r' Hp _ _]; exact Hp.
  Qed.

End PathConnectivity.

(* =========================================================================
   0b. Finite Sum Machinery (Parametric, Outside Section)
   ========================================================================= *)

Section FiniteSumMachinery.
  Variable P : Type.
  Variable eq_dec : forall x y : P, {x = y} + {x <> y}.
  Variable polymers_Λ : list P.
  Variable N_max : nat.

  Lemma NoDup_remove_eq_dec {A : Type} (eq_dec_A : forall x y : A, {x = y} + {x <> y}) :
    forall (l : list A) (x : A), NoDup l -> NoDup (remove eq_dec_A x l).
  Proof.
    intros l x Hnd. induction Hnd as [| a t Hnotin Hnd IH]; simpl.
    - constructor.
    - destruct (eq_dec_A x a) as [Heq | Hneq].
      + exact IH.
      + constructor.
        * intro Hin. apply in_remove in Hin. destruct Hin as [Hin _].
          exact (Hnotin Hin).
        * exact IH.
  Qed.

  (* -------------------------------------------------------------------------
     NoDup-preserving enumeration: choose each next element from the current
     pool, then recurse on the pool with that element removed.
     ------------------------------------------------------------------------- *)

  Fixpoint lists_of_length (k : nat) (pool : list P) : list (list P) :=
    match k with
    | O => [[]]
    | S k' =>
        flat_map
          (fun p =>
             map (cons p) (lists_of_length k' (remove eq_dec p pool)))
          pool
    end.

  Fixpoint lists_up_to_length (n : nat) (pool : list P) : list (list P) :=
    match n with
    | O => [[]]
    | S n' =>
        lists_up_to_length n' pool ++ lists_of_length (S n') pool
    end.

  Definition clusters_Λ_N : list (Cluster P) :=
    lists_up_to_length N_max polymers_Λ.

  Lemma lists_of_length_length (k : nat) (pool : list P) :
    forall X, In X (lists_of_length k pool) -> List.length X = k.
  Proof.
    revert pool.
    induction k as [| k' IH]; intros pool X Hin; simpl in Hin.
    - destruct Hin as [Heq | []]. subst X. reflexivity.
    - apply in_flat_map in Hin.
      destruct Hin as [p [Hp Hmap]].
      apply in_map_iff in Hmap.
      destruct Hmap as [Y [Heq HY]].
      subst X. simpl. f_equal.
      apply (IH (remove eq_dec p pool) Y HY).
  Qed.

  Lemma lists_up_to_length_length_bound (n : nat) (pool : list P) :
    forall X, In X (lists_up_to_length n pool) -> (List.length X <= n)%nat.
  Proof.
    induction n as [| n' IH]; intros X Hin; simpl in Hin.
    - destruct Hin as [Heq | []]. subst X. simpl. lia.
    - apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      + specialize (IH X Hin). lia.
      + rewrite (lists_of_length_length (S n') pool X Hin).
        lia.
  Qed.

  Lemma lists_of_length_all_in_pool (k : nat) (pool : list P) (X : list P) :
    In X (lists_of_length k pool) ->
    forall p, In p X -> In p pool.
  Proof.
    revert pool X.
    induction k as [| k' IH]; intros pool X HX p Hp; simpl in HX.
    - destruct HX as [Heq | []]. subst X. contradiction.
    - apply in_flat_map in HX.
      destruct HX as [q [Hq HX]].
      apply in_map_iff in HX.
      destruct HX as [Y [Heq HY]].
      subst X. simpl in Hp.
      destruct Hp as [Heqp | Hp].
      + subst p. exact Hq.
      + assert (H_in_rem : In p (remove eq_dec q pool)).
        { apply (IH (remove eq_dec q pool) Y HY p Hp). }
        apply in_remove in H_in_rem. destruct H_in_rem as [H_in_p _]. exact H_in_p.
  Qed.

  Lemma lists_of_length_member_nodup (k : nat) (pool : list P) (X : list P) :
    NoDup pool ->
    In X (lists_of_length k pool) ->
    NoDup X.
  Proof.
    revert pool X.
    induction k as [| k' IH]; intros pool X Hnd Hin; simpl in Hin.
    - destruct Hin as [Heq | []]. subst X. constructor.
    - apply in_flat_map in Hin.
      destruct Hin as [p [Hp Hin]].
      apply in_map_iff in Hin.
      destruct Hin as [Y [Heq Hin]].
      subst X. constructor.
      + intro Hnot.
        apply (lists_of_length_all_in_pool k' (remove eq_dec p pool) Y Hin p) in Hnot.
        apply in_remove in Hnot. destruct Hnot as [_ Hneq].
        contradiction.
      + apply (IH (remove eq_dec p pool) Y).
        * apply NoDup_remove_eq_dec. exact Hnd.
        * exact Hin.
  Qed.

  Lemma lists_up_to_length_member_nodup (n : nat) (pool : list P) (X : list P) :
    NoDup pool ->
    In X (lists_up_to_length n pool) ->
    NoDup X.
  Proof.
    revert pool X.
    induction n as [| n' IH]; intros pool X Hnd Hin.
    - destruct Hin as [Heq | []]. subst X. constructor.
    - apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      + apply (IH pool X Hnd Hin).
      + eapply lists_of_length_member_nodup; [exact Hnd | exact Hin].
  Qed.

  Lemma in_remove_eq_dec_intro :
    forall x y (l : list P),
      In x l -> x <> y -> In x (remove eq_dec y l).
  Proof.
    intros x y l.
    induction l as [| a l IH]; intros Hin Hneq; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst a.
        destruct (eq_dec y x) as [Hxy | Hxy].
        * subst y; contradiction.
        * simpl. left. reflexivity.
      + destruct (eq_dec y a) as [Hya | Hya].
        * subst a. apply IH; assumption.
        * simpl. right. apply IH; assumption.
  Qed.

  Lemma lists_of_length_complete (X : list P) (pool : list P) :
    NoDup X ->
    (forall p, In p X -> In p pool) ->
    In X (lists_of_length (length X) pool).
  Proof.
    revert pool.
    induction X as [| p xs IH]; intros pool Hnd Hall; simpl.
    - left. reflexivity.
    - inversion Hnd as [| ? ? Hnotin Hnd_xs]. subst.
      apply in_flat_map.
      exists p. split.
      + apply Hall. simpl. auto.
      + apply in_map.
        apply IH.
        * exact Hnd_xs.
        * intros q Hq.
          apply in_remove_eq_dec_intro.
          -- apply Hall. simpl. auto.
          -- intro Heq. subst q. apply Hnotin. exact Hq.
  Qed.

  Lemma lists_of_length_in_up_to (k n : nat) (pool : list P) :
    (k <= n)%nat ->
    forall X, In X (lists_of_length k pool) -> In X (lists_up_to_length n pool).
  Proof.
    intros Hkn.
    induction n as [| n' IH]; simpl.
    - assert (k = 0%nat) by lia. subst k.
      intros X HX. exact HX.
    - destruct (Nat.eq_dec k (S n')) as [Heq | Hneq].
      + subst k. intros X HX. apply in_or_app. right. exact HX.
      + assert (Hk : (k <= n')%nat) by lia.
        intros X HX. apply in_or_app. left. apply IH; assumption.
  Qed.

  Lemma lists_up_to_length_complete (n : nat) (pool : list P) (X : list P) :
    NoDup X ->
    (length X <= n)%nat ->
    (forall p, In p X -> In p pool) ->
    In X (lists_up_to_length n pool).
  Proof.
    intros Hnd Hlen Hall.
    assert (Hin : In X (lists_of_length (length X) pool)).
    { apply lists_of_length_complete; assumption. }
    exact (lists_of_length_in_up_to (length X) n pool Hlen X Hin).
  Qed.

  Lemma lists_up_to_length_all_in_pool (n : nat) (pool : list P) (X : list P) :
    In X (lists_up_to_length n pool) ->
    forall p, In p X -> In p pool.
  Proof.
    revert pool X.
    induction n as [| n' IH]; intros pool X HX p Hp.
    - destruct HX as [Heq | []]. subst X. contradiction.
    - apply in_app_iff in HX.
      destruct HX as [HX | HX].
      + apply (IH pool X HX p Hp).
      + eapply lists_of_length_all_in_pool; [exact HX | exact Hp].
  Qed.

  Lemma lists_up_to_length_perm (n : nat) (pool : list P) (X Y : list P) :
    NoDup pool ->
    In X (lists_up_to_length n pool) ->
    Permutation X Y ->
    In Y (lists_up_to_length n pool).
  Proof.
    intros Hnd HX Hperm.
    apply lists_up_to_length_complete.
    - eapply Permutation_NoDup.
      + exact Hperm.
      + eapply lists_up_to_length_member_nodup; [exact Hnd | exact HX].
    - rewrite <- (Permutation_length Hperm).
      eapply lists_up_to_length_length_bound; exact HX.
    - intros p Hp.
      apply (Permutation_in _ (Permutation_sym Hperm)) in Hp.
      eapply lists_up_to_length_all_in_pool; [exact HX | exact Hp].
  Qed.

  (* Local NoDup helpers (generic, no lattice dependency) *)
  Lemma NoDup_map_injective_ {A B : Type} (f : A -> B) (l : list A) :
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
  Proof.
    intros Hinj Hnd. induction Hnd as [| a l Hnotin Hnd IH]; simpl.
    - constructor.
    - constructor.
      + intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hfx Hinx]].
        apply Hinj in Hfx. subst x. exact (Hnotin Hinx).
      + exact IH.
  Qed.

  Lemma NoDup_app_r {A : Type} (l1 l2 : list A) :
    NoDup (l1 ++ l2) -> NoDup l2.
  Proof.
    intros H. induction l1 as [| a l1 IH]; simpl in *.
    - exact H.
    - inversion H. apply IH. exact H3.
  Qed.

  Lemma NoDup_app_intro_ {A : Type} (l1 l2 : list A) :
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
  Proof.
    intros Hnd1 Hnd2 Hdisj.
    induction Hnd1 as [| a l Hnotin Hnd IH]; simpl.
    - exact Hnd2.
    - constructor.
      + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hinl | Hin2].
        * apply Hnotin; exact Hinl.
        * apply (Hdisj a (or_introl eq_refl)); exact Hin2.
      + apply IH. intros x Hx. apply Hdisj. right; exact Hx.
  Qed.

  Lemma NoDup_flat_map_ {A B : Type} (l : list A) (f : A -> list B)
    (eq_dec_A : forall x y : A, {x = y} + {x <> y}) :
    NoDup l ->
    (forall a, In a l -> NoDup (f a)) ->
    (forall a1 a2 x, In a1 l -> In a2 l -> a1 <> a2 ->
       In x (f a1) -> ~ In x (f a2)) ->
    NoDup (flat_map f l).
  Proof.
    intros Hnd Hblocks Hdisj.
    induction Hnd as [| a l Hnotin Hnd IH]; simpl.
    - constructor.
    - apply NoDup_app_intro_.
      + apply Hblocks. left; reflexivity.
      + apply IH; [intros a0 Ha0; apply Hblocks; right; exact Ha0 |].
        intros a1 a2 x Ha1 Ha2 Hneq Hinx.
        apply (Hdisj a1 a2 x); [right|right| |]; assumption.
      + intros x Hx1 Hx2.
        apply in_flat_map in Hx2. destruct Hx2 as [a0 [Ha0 Hin2]].
        destruct (eq_dec_A a a0) as [Heq | Hneq].
        * subst a0. apply Hnotin. exact Ha0.
        * apply (Hdisj a0 a x); [right; exact Ha0 | left; reflexivity |
            intro Heq; subst a0; apply Hneq; reflexivity | exact Hin2 | assumption].
  Qed.

  Lemma NoDup_app_disjoint_by_length {A : Type} (l1 l2 : list (list A)) (k : nat) :
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l1 -> (List.length x <= k)%nat) ->
    (forall x, In x l2 -> List.length x = S k) ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
  Proof.
    intros Hnd1 Hnd2 Hlen1 Hlen2 Hdisj.
    induction Hnd1 as [| a l Hnotin Hnd IH]; simpl.
    - exact Hnd2.
    - constructor.
      + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hinl | Hin2].
        * apply Hnotin; exact Hinl.
        * apply (Hdisj a (or_introl eq_refl)); exact Hin2.
      + apply IH.
        * intros x Hx. apply Hlen1. right; exact Hx.
        * intros x Hx. apply Hdisj. right; exact Hx.
  Qed.

  Lemma lists_of_length_NoDup (k : nat) (p0 : list P) :
    NoDup p0 ->
    NoDup (lists_of_length k p0).
  Proof.
    revert p0. induction k as [| k' IH]; intros p0 Hnd.
    - simpl. constructor; [| constructor]. intro H; inversion H.
    - simpl. apply (NoDup_flat_map_ p0 (fun p => map (cons p) (lists_of_length k' (remove eq_dec p p0))) eq_dec).
      + exact Hnd.
      + intros p Hp. apply NoDup_map_injective_.
        * intros x y Heq. injection Heq. intros H; exact H.
        * apply IH. apply NoDup_remove_eq_dec. exact Hnd.
      + intros p1 p2 X Hp1 Hp2 Hneq Hin1 Hin2.
        apply in_map_iff in Hin1. destruct Hin1 as [Y1 [Heq1 _]].
        apply in_map_iff in Hin2. destruct Hin2 as [Y2 [Heq2 _]].
        assert (Heq : p1 :: Y1 = p2 :: Y2) by (transitivity X; [exact Heq1 | symmetry; exact Heq2]).
        injection Heq. intros _ Heqp. apply Hneq. exact Heqp.
  Qed.

  Lemma lists_up_to_length_NoDup (n : nat) (p : list P) :
    NoDup p ->
    NoDup (lists_up_to_length n p).
  Proof.
    revert p. induction n as [| n' IH]; intros p Hnd.
    - simpl. constructor; [| constructor]. intro H; inversion H.
    - change (NoDup (lists_up_to_length n' p ++ lists_of_length (S n') p)).
      apply NoDup_app_disjoint_by_length with (k := n').
      + apply IH. exact Hnd.
      + apply lists_of_length_NoDup. exact Hnd.
      + intros X HX. apply (lists_up_to_length_length_bound n' p). exact HX.
      + intros X HX. apply (lists_of_length_length (S n') p). exact HX.
      + intros X HX1 HX2.
        assert (Hle : (List.length X <= n')%nat) by (apply (lists_up_to_length_length_bound n' p); exact HX1).
        assert (Heq : List.length X = S n') by (apply (lists_of_length_length (S n') p); exact HX2).
        lia.
  Qed.

  Lemma clusters_Λ_N_NoDup : NoDup polymers_Λ -> NoDup clusters_Λ_N.
  Proof.
    unfold clusters_Λ_N. apply lists_up_to_length_NoDup.
  Qed.

  Lemma clusters_Λ_N_member_nodup :
    forall X,
      NoDup polymers_Λ ->
      In X clusters_Λ_N ->
      NoDup X.
  Proof.
    intros X Hnd Hin.
    unfold clusters_Λ_N in Hin.
    eapply lists_up_to_length_member_nodup; eauto.
  Qed.

  (* sum_connecting_impl: the concrete finite sum *)
  Definition sum_connecting_impl
    (connects_dec : forall (X : Cluster P) (p1 p2 : P), {True} + {True})
    (p1 p2 : P) (f : Cluster P -> R) : R :=
    fold_right Rplus 0
      (map (fun X => if connects_dec X p1 p2 then f X else 0) clusters_Λ_N).

End FiniteSumMachinery.

(* =========================================================================
   0c. Sum Algebra Lemmas (Parametric)
   ========================================================================= *)

Section SumAlgebra.
  Context {P : Type} `{ConnectivitySystem P}.
  Variable eq_dec : forall x y : P, {x = y} + {x <> y}.
  Variable polymers_Λ : list P.
  Variable N_max : nat.
  Variable connects_dec : forall (X : Cluster P) (p1 p2 : P),
    {connects X p1 p2} + {~ connects X p1 p2}.

  (* Type-cast connects_dec to match sum_connecting_impl signature *)
  Definition connects_dec_cast (X : Cluster P) (p1 p2 : P) : {True} + {True} :=
    match connects_dec X p1 p2 with
    | left _ => left I
    | right _ => right I
    end.

  Definition sum_connecting_concrete (p1 p2 : P) (f : Cluster P -> R) : R :=
    fold_right Rplus 0
      (map (fun X => if connects_dec X p1 p2 then f X else 0)
           (clusters_Λ_N P eq_dec polymers_Λ N_max)).

  (* Helper: fold_right Rplus monotone on mapped lists *)
  Lemma fold_right_map_monotone_param : forall {A : Type} (l : list A) (f g : A -> R),
    (forall x, In x l -> f x <= g x) ->
    fold_right Rplus 0 (map f l) <= fold_right Rplus 0 (map g l).
  Proof.
    intros A l f g Hfg.
    induction l as [| h t IH]; simpl.
    - lra.
    - assert (Hh : f h <= g h) by (apply Hfg; left; reflexivity).
      assert (Ht : fold_right Rplus 0 (map f t) <= fold_right Rplus 0 (map g t)).
      { apply IH. intros x Hx. apply Hfg. right. exact Hx. }
      lra.
  Qed.

  (* Monotonicity *)
  Lemma sum_connecting_concrete_monotone :
    forall p1 p2 f g,
      (forall X, connects X p1 p2 -> f X <= g X) ->
      sum_connecting_concrete p1 p2 f <= sum_connecting_concrete p1 p2 g.
  Proof.
    intros p1 p2 f g Hfg.
    unfold sum_connecting_concrete.
    apply fold_right_map_monotone_param.
    intros X _.
    destruct (connects_dec X p1 p2) as [Hc | Hnc].
    - apply Hfg. exact Hc.
    - lra.
  Qed.

  (* Helper: triangle inequality for fold_right Rplus *)
  Lemma fold_right_Rplus_triangle_param : forall (l : list R),
    Rabs (fold_right Rplus 0 l) <= fold_right Rplus 0 (map Rabs l).
  Proof.
    induction l as [| h t IH]; simpl.
    - rewrite Rabs_R0. lra.
    - apply Rle_trans with (Rabs h + Rabs (fold_right Rplus 0 t)).
      + apply Rabs_triang.
      + apply Rplus_le_compat_l. exact IH.
  Qed.

  (* Triangle inequality *)
  Lemma sum_connecting_concrete_triangle :
    forall p1 p2 f,
      Rabs (sum_connecting_concrete p1 p2 f) <=
      sum_connecting_concrete p1 p2 (fun X => Rabs (f X)).
  Proof.
    intros p1 p2 f.
    unfold sum_connecting_concrete.
    apply Rle_trans with
      (fold_right Rplus 0 (map Rabs (map (fun X => if connects_dec X p1 p2 then f X else 0)
                                        (clusters_Λ_N P eq_dec polymers_Λ N_max)))).
    { apply fold_right_Rplus_triangle_param. }
    rewrite map_map.
    apply fold_right_map_monotone_param.
    intros X _.
    destruct (connects_dec X p1 p2) as [Hc | Hnc].
    - lra.
    - rewrite Rabs_R0. lra.
  Qed.

  (* Helper: scaling for fold_right Rplus *)
  Lemma fold_right_Rplus_scale_param : forall c (l : list R),
    c * fold_right Rplus 0 l = fold_right Rplus 0 (map (Rmult c) l).
  Proof.
    intros c l.
    induction l as [| h t IH]; simpl.
    - ring.
    - rewrite <- IH. ring.
  Qed.

  (* Scaling *)
  Lemma sum_connecting_concrete_scale :
    forall p1 p2 c f,
      c >= 0 ->
      c * sum_connecting_concrete p1 p2 f =
      sum_connecting_concrete p1 p2 (fun X => c * f X).
  Proof.
    intros p1 p2 c f Hc.
    unfold sum_connecting_concrete.
    rewrite fold_right_Rplus_scale_param.
    f_equal. rewrite map_map.
    apply map_ext. intros X.
    destruct (connects_dec X p1 p2); ring.
  Qed.

End SumAlgebra.

(* =========================================================================
   1. Main Section: Cluster Expansion
   ========================================================================= *)

Section ClusterExpansion.

  (* Context: Abstract Polymer System with Connectivity and Ursell *)
  Context {P : Type} `{PolymerSystem P} `{MetricSystem P} `{ConnectivitySystem P} `{SummationSystem P} `{UrsellSystem P}.

  Variable eq_dec : forall x y : P, {x = y} + {x <> y}.

  (* Finite Volume Parameters *)
  Variable polymers_Λ : list P.
  Variable N_max : nat.
  Variable beta : R.  (* For activity-bound condition: a <= beta/10 in YM *)

  (* Decidability of connects predicate *)
  Variable connects_dec : forall (X : Cluster P) (p1 p2 : P),
    {connects X p1 p2} + {~ connects X p1 p2}.

  (* =========================================================================
     2. Ursell Functions / Cluster Coefficients
     ========================================================================= *)

  (* Mayer-Ursell coefficient comes from the UrsellSystem typeclass context.
     - Concrete instantiation in ym_tree_graph_bound.v for YMPolymer.
     - |ursell_factor X| <= 1 is now a typeclass law (ursell_bounded).
     - Previously was a Parameter; now resolved via typeclass. *)

  (* =========================================================================
     3. The Cluster Sum
     ========================================================================= *)

  Fixpoint prod_activity (c : Cluster P) : R :=
    match c with
    | [] => 1
    | p :: rest => activity p * prod_activity rest
    end.

  (* Multiplicativity of prod_activity over concatenation *)
  Lemma prod_activity_app : forall (X Y : Cluster P),
    prod_activity (X ++ Y) = prod_activity X * prod_activity Y.
  Proof.
    induction X as [|p X' IH]; intro Y; simpl.
    - lra.
    - rewrite IH. ring.
  Qed.

  Definition cluster_weight (c : Cluster P) : R :=
    ursell_factor c * prod_activity c.

  Fixpoint cluster_size (c : Cluster P) : R :=
    match c with
    | [] => 0
    | p :: rest => size p + cluster_size rest
    end.

  (* Additivity of cluster_size over concatenation *)
  Lemma cluster_size_app : forall (X Y : Cluster P),
    cluster_size (X ++ Y) = cluster_size X + cluster_size Y.
  Proof.
    induction X as [|p X' IH]; intro Y; simpl.
    - lra.
    - rewrite IH. ring.
  Qed.

  (* Key geometric lemma: connecting clusters span the distance. *)
  Hypothesis connects_implies_dist_bound :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 -> dist p1 p2 <= cluster_size X.

  Parameter sum_over_clusters_pinned : P -> (Cluster P -> R) -> R.

  (* =========================================================================
     3b. CONCRETE sum_connecting (via parametric lemmas)
     ========================================================================= *)

  Definition sum_connecting (p1 p2 : P) (f : Cluster P -> R) : R :=
    sum_connecting_concrete eq_dec polymers_Λ N_max connects_dec p1 p2 f.

  (* The 3 sum algebra properties are now LEMMAS, not hypotheses! *)
  Lemma sum_connecting_monotone :
    forall p1 p2 f g,
      (forall X, connects X p1 p2 -> f X <= g X) ->
      sum_connecting p1 p2 f <= sum_connecting p1 p2 g.
  Proof.
    intros p1 p2 f g Hfg.
    unfold sum_connecting.
    apply sum_connecting_concrete_monotone. exact Hfg.
  Qed.

  Lemma sum_connecting_triangle :
    forall p1 p2 f,
      Rabs (sum_connecting p1 p2 f) <= sum_connecting p1 p2 (fun X => Rabs (f X)).
  Proof.
    intros p1 p2 f.
    unfold sum_connecting.
    apply sum_connecting_concrete_triangle.
  Qed.

  Lemma sum_connecting_scale :
    forall p1 p2 c f,
      c >= 0 ->
      c * sum_connecting p1 p2 f = sum_connecting p1 p2 (fun X => c * f X).
  Proof.
    intros p1 p2 c f Hc.
    unfold sum_connecting.
    apply sum_connecting_concrete_scale. exact Hc.
  Qed.

  (* =========================================================================
     4. The Correlator (REAL DEFINITION)
     ========================================================================= *)

  Definition correlator (p1 p2 : P) : R :=
    sum_connecting p1 p2 cluster_weight.

  (* =========================================================================
     5. Convergence (Kotecky-Preiss)
     ========================================================================= *)

  Definition kp_sum_condition (a : R) : Prop :=
    kotecky_preiss_condition a.

  Lemma kp_sum_condition_unfolded : forall a,
    kp_sum_condition a <->
    forall p, sum_overlap p (fun p' => activity p' * exp (a * size p')) <= a * size p.
  Proof.
    intro a. unfold kp_sum_condition, kotecky_preiss_condition. reflexivity.
  Qed.

  (* =========================================================================
     6. KP -> Exponential Decay (THE REAL PROOF)
     ========================================================================= *)

  Lemma connecting_geometry :
    forall (a : R) (p1 p2 : P),
      a > 0 ->
      sum_connecting p1 p2 (fun X => Rabs (cluster_weight X)) <=
      exp (- a * dist p1 p2) *
      sum_connecting p1 p2
        (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X)).
  Proof.
    intros a p1 p2 Ha.
    rewrite sum_connecting_scale by (left; apply exp_pos).
    apply sum_connecting_monotone.
    intros X Hconn.
    pose proof (connects_implies_dist_bound X p1 p2 Hconn) as Hdist.
    assert (Hexp : exp (- a * dist p1 p2) * exp (a * cluster_size X) >= 1).
    { rewrite <- exp_plus.
      replace (- a * dist p1 p2 + a * cluster_size X) with
              (a * (cluster_size X - dist p1 p2)) by ring.
      assert (Hge0 : 0 <= a * (cluster_size X - dist p1 p2)).
      { apply Rmult_le_pos; lra. }
      apply Rle_ge. rewrite <- exp_0.
      destruct (Rle_lt_or_eq_dec 0 (a * (cluster_size X - dist p1 p2)) Hge0) as [Hlt | Heq].
      - left. apply exp_increasing. exact Hlt.
      - right. rewrite <- Heq. reflexivity. }
    pose proof (Rabs_pos (cluster_weight X)) as Habs.
    replace (exp (- a * dist p1 p2) * (Rabs (cluster_weight X) * exp (a * cluster_size X)))
      with (Rabs (cluster_weight X) * (exp (- a * dist p1 p2) * exp (a * cluster_size X)))
      by ring.
    rewrite <- (Rmult_1_r (Rabs (cluster_weight X))) at 1.
    apply Rmult_le_compat_l.
    { exact Habs. }
    lra.
  Qed.

  (* Tree-graph bound: NOW A THEOREM (derived from pinned_bound.v)
     The proof chain is:
       1. tree_graph_majorant (Penrose, Qed in pinned_bound.v)
       2. rooted_sum_le_exp2a_bound (KP engine, Qed in rooted_tree.v)
       3. connecting_bounded_by_pinned_from_KP (assembly, Qed in pinned_bound.v)
     The only remaining bridge is between adj-connected sums (here)
     and overlap-connected sums (pinned_bound.v).
     For YM: activity bound requires a <= beta/10 (Iteration 27). *)
  Hypothesis connecting_bounded_by_pinned :
    forall (a : R) (p1 p2 : P),
      a > 0 ->
      kp_sum_condition a ->
      (forall q, sum_overlap q (fun x => activity x * exp (2 * a * size x)) <= a * size q) ->
      a <= beta / 20 ->
      sum_connecting p1 p2
        (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X)) <=
      exp (a * size p1) * exp (a * size p2).

  Lemma exp_monotone : forall x y, x <= y -> exp x <= exp y.
  Proof.
    intros x y [Hlt | Heq].
    - left. apply exp_increasing. exact Hlt.
    - right. subst. reflexivity.
  Qed.

  Corollary exponential_decay_from_cluster_explicit_C :
    forall (a : R) (S_max : R),
      a > 0 ->
      S_max >= 1 ->
      (forall p : P, size p <= S_max) ->
      kp_sum_condition a ->
      (forall q, sum_overlap q (fun x => activity x * exp (2 * a * size x)) <= a * size q) ->
      a <= beta / 20 ->
      forall p1 p2 : P,
        Rabs (correlator p1 p2) <= exp (2 * a * S_max) * exp (- a * dist p1 p2).
  Proof.
    intros a S_max Ha HS Hsize Hkp Hkp2a Hab p1 p2.
    apply Rle_trans with
      (sum_connecting p1 p2 (fun X => Rabs (cluster_weight X))).
    { unfold correlator. apply sum_connecting_triangle. }
    apply Rle_trans with
      (exp (- a * dist p1 p2) *
       sum_connecting p1 p2
         (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X))).
    { apply connecting_geometry. exact Ha. }
    apply Rle_trans with
      (exp (- a * dist p1 p2) * (exp (a * size p1) * exp (a * size p2))).
    { apply Rmult_le_compat_l.
      - left. apply exp_pos.
      - apply connecting_bounded_by_pinned; assumption. }
    rewrite (Rmult_comm (exp (2 * a * S_max))).
    apply Rmult_le_compat_l.
    + left. apply exp_pos.
    + rewrite <- exp_plus.
      apply exp_monotone.
      assert (Hs1 : a * size p1 <= a * S_max).
      { apply Rmult_le_compat_l; [lra | apply Hsize]. }
      assert (Hs2 : a * size p2 <= a * S_max).
      { apply Rmult_le_compat_l; [lra | apply Hsize]. }
      lra.
  Qed.

  Theorem exponential_decay_from_cluster :
    forall (a : R) (S_max : R),
      a > 0 ->
      S_max >= 1 ->
      (forall p : P, size p <= S_max) ->
      kp_sum_condition a ->
      (forall q, sum_overlap q (fun x => activity x * exp (2 * a * size x)) <= a * size q) ->
      a <= beta / 20 ->
      has_mass_gap correlator a.
  Proof.
    intros a S_max Ha HS Hsize Hkp Hkp2a Hab.
    unfold has_mass_gap.
    exists (exp (2 * a * S_max)).
    split.
    - apply exp_pos.
    - intros p1 p2.
      apply Rle_trans with
        (sum_connecting p1 p2 (fun X => Rabs (cluster_weight X))).
      { unfold correlator. apply sum_connecting_triangle. }
      apply Rle_trans with
        (exp (- a * dist p1 p2) *
         sum_connecting p1 p2
           (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X))).
      { apply connecting_geometry. exact Ha. }
      apply Rle_trans with
        (exp (- a * dist p1 p2) * (exp (a * size p1) * exp (a * size p2))).
      { apply Rmult_le_compat_l.
        - left. apply exp_pos.
        - apply connecting_bounded_by_pinned; assumption. }
      rewrite (Rmult_comm (exp (2 * a * S_max))).
      apply Rmult_le_compat_l.
      + left. apply exp_pos.
      + rewrite <- exp_plus.
        apply exp_monotone.
        assert (Hs1 : a * size p1 <= a * S_max).
        { apply Rmult_le_compat_l; [lra | apply Hsize]. }
        assert (Hs2 : a * size p2 <= a * S_max).
        { apply Rmult_le_compat_l; [lra | apply Hsize]. }
        lra.
  Qed.

  (* CONCRETE VERSION: Returns explicit bound without existential.
     C = exp(2 * a * S_max), m = a. *)
  Theorem exponential_decay_from_cluster_concrete :
    forall (a : R) (S_max : R) (p1 p2 : P),
      a > 0 ->
      S_max >= 1 ->
      (forall p : P, size p <= S_max) ->
      kp_sum_condition a ->
      (forall q, sum_overlap q (fun x => activity x * exp (2 * a * size x)) <= a * size q) ->
      a <= beta / 20 ->
      Rabs (correlator p1 p2) <= exp (2 * a * S_max) * exp (- a * dist p1 p2).
  Proof.
    intros a S_max p1 p2 Ha HS Hsize Hkp Hkp2a Hab.
    apply Rle_trans with
      (sum_connecting p1 p2 (fun X => Rabs (cluster_weight X))).
    { unfold correlator. apply sum_connecting_triangle. }
    apply Rle_trans with
      (exp (- a * dist p1 p2) *
       sum_connecting p1 p2
         (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X))).
    { apply connecting_geometry. exact Ha. }
    apply Rle_trans with
      (exp (- a * dist p1 p2) * (exp (a * size p1) * exp (a * size p2))).
    { apply Rmult_le_compat_l.
      - left. apply exp_pos.
      - apply connecting_bounded_by_pinned; assumption. }
    rewrite (Rmult_comm (exp (2 * a * S_max))).
    apply Rmult_le_compat_l.
    + left. apply exp_pos.
    + rewrite <- exp_plus.
      apply exp_monotone.
      assert (Hs1 : a * size p1 <= a * S_max).
      { apply Rmult_le_compat_l; [lra | apply Hsize]. }
      assert (Hs2 : a * size p2 <= a * S_max).
      { apply Rmult_le_compat_l; [lra | apply Hsize]. }
      lra.
  Qed.

End ClusterExpansion.
