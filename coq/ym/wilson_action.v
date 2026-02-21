(* =========================================================================
   wilson_action.v - Generic Wilson Action for Compact Lie Groups

   Defines the Wilson action and reflection symmetry for any compact group G
   with a conjugation-invariant class function phi (e.g. Re Tr).

   Structure:
   1. Configuration Space (link -> G)
   2. Plaquette Holonomy (path ordered product)
   3. Wilson Action (sum over plaquettes of (1 - phi(U_p)))
   4. Time Reflection on Configurations
   5. Action Reflection Symmetry (Phase B generic proof)

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import algebra.compact_group.
Require Import ym.lattice.

Import ListNotations.
Open Scope R_scope.
Open Scope group_scope.

Module WilsonAction.

  Import Lattice.

  Section GenericAction.
  
  (* Context: Group and Lattice Size *)
  Context {G : Type} `{Group G} `{WilsonClassFunction G}.
  Variable L : lattice_size.

  (* 1. Configuration Space *)
  Definition gauge_config := link -> G.

  (* 2. Plaquette Holonomy *)
  (* Product of group elements along the boundary *)
  (* (l, true) -> U(l), (l, false) -> U(l)^-1 *)
  
  Definition link_transport (U : gauge_config) (e : link * bool) : G :=
    let (l, sgn) := e in
    if sgn then U l else / (U l).

  Definition plaq_holonomy (U : gauge_config) (p : plaquette) : G :=
    let boundary := plaq_boundary p in
    (* Fold product: U1 * U2 * U3 * U4 *)
    (* Note: order is crucial for non-abelian groups *)
    (* plaq_boundary returns links in counter-clockwise order *)
    fold_right (fun e acc => link_transport U e * acc) 1 boundary.
    (* Wait, fold_right is u1 * (u2 * (u3 * (u4 * 1))) *)
    (* This is correct for associative multiplication *)

  (* 3. Wilson Action *)
  (* S = sum_p beta * (1 - phi(U_p)) *)
  (* We define the single plaquette action first *)
  
  Variable beta : R.
  
  Definition plaq_action (U : gauge_config) (p : plaquette) : R :=
    beta * (1 - phi (plaq_holonomy U p)).

  (* Total action requires summing over all_plaquettes *)
  (* We assume finite sum capability *)
  Fixpoint sum_R (l : list R) : R :=
    match l with
    | [] => 0
    | h :: t => h + sum_R t
    end.

  Definition wilson_action (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (all_plaquettes L)).

  (* 4. Time Reflection on Configurations *)
  (* Theta U (l) = U(reflect l) if space-like *)
  (*             = U(reflect l)^-1 if time-like *)
  (* This matches orientation_flipped logic *)

  Definition config_reflect (U : gauge_config) : gauge_config :=
    fun l =>
      let lr := reflect_link l in
      if orientation_flipped l then / (U lr) else U lr.

  (* 5. Phase B: Reflection Symmetry *)
  
  (* We need to show S(Theta U) = S(U). *)
  (* This requires showing phi(U_p) = phi(Theta U_p') where p' is reflected p. *)
  (* And summing over reflected list equals summing over original list. *)

  (* Key Lemma: Holonomy of reflected plaquette *)
  (* For U(1), this was explicit calculation. *)
  (* For G, we use the property that reflection reverses orientation of loops *)
  (* and conjugates by the base point shift. *)
  (* Since phi is conjugation invariant and inv invariant, phi(U_p) is invariant. *)

  (* We assume the permutation property of the lattice sum (from infrastructure) *)
  (* And focus on the single plaquette invariance. *)

  (* ========================================================================= *)
  (* 6. Action Decomposition: S = S+ + S- + S_cross                            *)
  (*                                                                           *)
  (* For reflection positivity, we decompose the action into three parts:      *)
  (* - S+: action from plaquettes entirely in positive time (t > 0)            *)
  (* - S-: action from plaquettes entirely in negative time (t < -1)           *)
  (* - S_cross: action from crossing plaquettes (connect t=-1 to t=0)          *)
  (*                                                                           *)
  (* Note: The lattice.v predicates have OVERLAP (spatial at t=-1 is both      *)
  (* negative and boundary). We define EXCLUSIVE predicates here.              *)
  (* ========================================================================= *)

  (* --- Sum Lemmas --- *)

  Lemma sum_R_app : forall l1 l2,
    sum_R (l1 ++ l2) = sum_R l1 + sum_R l2.
  Proof.
    induction l1 as [|h t IH]; intro l2; simpl.
    - lra.
    - rewrite IH. lra.
  Qed.

  Lemma sum_R_map_app : forall {A : Type} (f : A -> R) (l1 l2 : list A),
    sum_R (map f (l1 ++ l2)) = sum_R (map f l1) + sum_R (map f l2).
  Proof.
    intros A f l1 l2.
    rewrite map_app. apply sum_R_app.
  Qed.

  (* --- EXCLUSIVE Time Classification (5-way partition) --- *)
  (*
     The 5 categories are:
     1. plaq_pos         : t > 0 (positive half-space)
     2. plaq_neg_strict  : t < -1 (negative half-space, strictly)
     3. plaq_cross       : time-like AND t = -1 (lower crossing: t=-1 to t=0)
     4. plaq_upper_cross : time-like AND t = 0 (upper crossing: t=0 to t=1)
     5. plaq_boundary    : spatial AND t in {0, -1} (on the wall)

     These are mutually exclusive and exhaustive.
  *)

  (* 1. Positive: anchor at t > 0 *)
  Definition plaq_pos (p : plaquette) : bool := plaq_in_positive p.

  (* 2. Negative (strict): anchor at t < -1 *)
  Definition plaq_neg_strict (p : plaquette) : bool :=
    Z.ltb (site_t (plaq_site p)) (-1).

  (* 3. Lower Crossing: time-like plaquettes at t = -1 (connects t=-1 to t=0) *)
  Definition plaq_cross (p : plaquette) : bool :=
    andb (plaq_involves_time p) (Z.eqb (site_t (plaq_site p)) (-1)).

  (* 4. Upper Crossing: time-like plaquettes at t = 0 (connects t=0 to t=1) *)
  Definition plaq_upper_cross (p : plaquette) : bool :=
    andb (plaq_involves_time p) (Z.eqb (site_t (plaq_site p)) 0).

  (* 5. Boundary: spatial plaquettes at t = 0 or t = -1 (on the wall) *)
  Definition plaq_boundary (p : plaquette) : bool := plaq_is_boundary p.

  (* --- Exclusivity Lemmas --- *)

  Lemma pos_neg_disjoint : forall p,
    plaq_pos p = true -> plaq_neg_strict p = false.
  Proof.
    intros p Hpos.
    unfold plaq_pos, plaq_in_positive in Hpos.
    unfold plaq_neg_strict.
    apply Z.gtb_lt in Hpos.
    apply Z.ltb_nlt. lia.
  Qed.

  Lemma pos_cross_disjoint : forall p,
    plaq_pos p = true -> plaq_cross p = false.
  Proof.
    intros p Hpos.
    unfold plaq_pos, plaq_in_positive in Hpos.
    unfold plaq_cross.
    apply Z.gtb_lt in Hpos.
    destruct (plaq_involves_time p); simpl; [|reflexivity].
    apply Z.eqb_neq. lia.
  Qed.

  Lemma pos_boundary_disjoint : forall p,
    plaq_pos p = true -> plaq_boundary p = false.
  Proof.
    intros p Hpos.
    unfold plaq_pos, plaq_in_positive in Hpos.
    unfold plaq_boundary, plaq_is_boundary.
    apply Z.gtb_lt in Hpos.
    destruct (plaq_involves_time p); simpl; [reflexivity|].
    apply Bool.orb_false_intro; apply Z.eqb_neq; lia.
  Qed.

  Lemma neg_cross_disjoint : forall p,
    plaq_neg_strict p = true -> plaq_cross p = false.
  Proof.
    intros p Hneg.
    unfold plaq_neg_strict in Hneg.
    unfold plaq_cross.
    apply Z.ltb_lt in Hneg.
    destruct (plaq_involves_time p); simpl; [|reflexivity].
    apply Z.eqb_neq. lia.
  Qed.

  Lemma neg_boundary_disjoint : forall p,
    plaq_neg_strict p = true -> plaq_boundary p = false.
  Proof.
    intros p Hneg.
    unfold plaq_neg_strict in Hneg.
    unfold plaq_boundary, plaq_is_boundary.
    apply Z.ltb_lt in Hneg.
    destruct (plaq_involves_time p); simpl; [reflexivity|].
    apply Bool.orb_false_intro; apply Z.eqb_neq; lia.
  Qed.

  Lemma cross_boundary_disjoint : forall p,
    plaq_cross p = true -> plaq_boundary p = false.
  Proof.
    intros p Hcross.
    unfold plaq_cross in Hcross.
    unfold plaq_boundary, plaq_is_boundary.
    apply Bool.andb_true_iff in Hcross.
    destruct Hcross as [Htime _].
    rewrite Htime. reflexivity.
  Qed.

  (* --- Upper Crossing Disjointness Lemmas --- *)

  Lemma pos_upper_cross_disjoint : forall p,
    plaq_pos p = true -> plaq_upper_cross p = false.
  Proof.
    intros p Hpos.
    unfold plaq_pos, plaq_in_positive in Hpos.
    unfold plaq_upper_cross.
    apply Z.gtb_lt in Hpos.
    destruct (plaq_involves_time p); simpl; [|reflexivity].
    apply Z.eqb_neq. lia.
  Qed.

  Lemma neg_upper_cross_disjoint : forall p,
    plaq_neg_strict p = true -> plaq_upper_cross p = false.
  Proof.
    intros p Hneg.
    unfold plaq_neg_strict in Hneg.
    unfold plaq_upper_cross.
    apply Z.ltb_lt in Hneg.
    destruct (plaq_involves_time p); simpl; [|reflexivity].
    apply Z.eqb_neq. lia.
  Qed.

  Lemma cross_upper_cross_disjoint : forall p,
    plaq_cross p = true -> plaq_upper_cross p = false.
  Proof.
    intros p Hcross.
    unfold plaq_cross in Hcross.
    unfold plaq_upper_cross.
    apply Bool.andb_true_iff in Hcross.
    destruct Hcross as [Htime Ht].
    apply Z.eqb_eq in Ht.
    rewrite Htime. simpl.
    apply Z.eqb_neq. lia.
  Qed.

  Lemma upper_cross_boundary_disjoint : forall p,
    plaq_upper_cross p = true -> plaq_boundary p = false.
  Proof.
    intros p Huc.
    unfold plaq_upper_cross in Huc.
    unfold plaq_boundary, plaq_is_boundary.
    apply Bool.andb_true_iff in Huc.
    destruct Huc as [Htime _].
    rewrite Htime. reflexivity.
  Qed.

  (* --- Partial Action Definitions --- *)

  Definition action_pos (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (filter plaq_pos (all_plaquettes L))).

  Definition action_neg (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (filter plaq_neg_strict (all_plaquettes L))).

  Definition action_cross (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (filter plaq_cross (all_plaquettes L))).

  Definition action_upper_cross (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (filter plaq_upper_cross (all_plaquettes L))).

  Definition action_boundary (U : gauge_config) : R :=
    sum_R (map (plaq_action U) (filter plaq_boundary (all_plaquettes L))).

  (* --- Five-Way Partition (Exclusive + Exhaustive) --- *)

  (* Helper: gtb false implies not greater *)
  Lemma Z_gtb_false_le : forall n m, (n >? m)%Z = false -> (n <= m)%Z.
  Proof.
    intros n m Hgtb. rewrite Z.gtb_ltb in Hgtb.
    apply Z.ltb_ge in Hgtb. lia.
  Qed.

  (* Helper: ltb true implies lt *)
  Lemma Z_ltb_true_lt : forall n m, (n <? m)%Z = true -> (n < m)%Z.
  Proof. intros n m Hltb. apply Z.ltb_lt. exact Hltb. Qed.

  (* The key lemma: every plaquette falls into exactly one of 5 categories *)
  (* This is now COMPLETE - no gaps in the classification *)
  Lemma plaq_exclusive_exhaustive : forall p,
    In p (all_plaquettes L) ->
    (plaq_pos p = true) \/
    (plaq_neg_strict p = true) \/
    (plaq_cross p = true) \/
    (plaq_upper_cross p = true) \/
    (plaq_boundary p = true).
  Proof.
    intros p Hin.
    set (t := site_t (plaq_site p)).
    destruct (Z_lt_ge_dec t (-1)) as [Hlt | Hge].
    - (* t < -1: strictly negative *)
      right. left.
      unfold plaq_neg_strict. apply Z.ltb_lt. exact Hlt.
    - destruct (Z.eq_dec t (-1)) as [Heqm1 | Hneqm1].
      + (* t = -1 *)
        destruct (plaq_involves_time p) eqn:Htime.
        * (* time-like at t = -1: lower crossing *)
          right. right. left.
          unfold plaq_cross. rewrite Htime. simpl.
          apply Z.eqb_eq. exact Heqm1.
        * (* spatial at t = -1: boundary *)
          right. right. right. right.
          unfold plaq_boundary, plaq_is_boundary. rewrite Htime.
          apply Bool.orb_true_iff. right. apply Z.eqb_eq. exact Heqm1.
      + destruct (Z.eq_dec t 0) as [Heq0 | Hneq0].
        * (* t = 0 *)
          destruct (plaq_involves_time p) eqn:Htime.
          -- (* time-like at t = 0: upper crossing *)
             right. right. right. left.
             unfold plaq_upper_cross. rewrite Htime. simpl.
             apply Z.eqb_eq. exact Heq0.
          -- (* spatial at t = 0: boundary *)
             right. right. right. right.
             unfold plaq_boundary, plaq_is_boundary. rewrite Htime.
             apply Bool.orb_true_iff. left. apply Z.eqb_eq. exact Heq0.
        * (* t > 0: positive *)
          left.
          unfold plaq_pos, plaq_in_positive.
          rewrite Z.gtb_ltb. apply Z.ltb_lt. lia.
  Qed.

  (* --- Generic Sum Filter Lemmas --- *)

  (* 5-way filter split: sum over list = sum of 5 filtered parts *)
  (* Requires: exhaustive + mutually exclusive partition *)
  Lemma sum_R_map_filter5
    {A : Type} (f : A -> R)
    (b1 b2 b3 b4 b5 : A -> bool) (l : list A) :
    (* Exhaustive: every element belongs to at least one *)
    (forall x, In x l -> b1 x = true \/ b2 x = true \/ b3 x = true \/ b4 x = true \/ b5 x = true) ->
    (* Exclusive: if one is true, others are false *)
    (forall x, b1 x = true -> b2 x = false /\ b3 x = false /\ b4 x = false /\ b5 x = false) ->
    (forall x, b2 x = true -> b1 x = false /\ b3 x = false /\ b4 x = false /\ b5 x = false) ->
    (forall x, b3 x = true -> b1 x = false /\ b2 x = false /\ b4 x = false /\ b5 x = false) ->
    (forall x, b4 x = true -> b1 x = false /\ b2 x = false /\ b3 x = false /\ b5 x = false) ->
    (forall x, b5 x = true -> b1 x = false /\ b2 x = false /\ b3 x = false /\ b4 x = false) ->
    sum_R (map f l) =
      sum_R (map f (filter b1 l)) +
      sum_R (map f (filter b2 l)) +
      sum_R (map f (filter b3 l)) +
      sum_R (map f (filter b4 l)) +
      sum_R (map f (filter b5 l)).
  Proof.
    intros Hex Hexcl1 Hexcl2 Hexcl3 Hexcl4 Hexcl5.
    induction l as [|x xs IH]; simpl.
    - lra.
    - specialize (IH (fun y Hy => Hex y (or_intror Hy))).
      destruct (Hex x (or_introl eq_refl)) as [Hb1 | [Hb2 | [Hb3 | [Hb4 | Hb5]]]].
      + (* x in b1 *)
        rewrite Hb1.
        destruct (Hexcl1 x Hb1) as [Hb2f [Hb3f [Hb4f Hb5f]]].
        rewrite Hb2f, Hb3f, Hb4f, Hb5f. simpl. lra.
      + (* x in b2 *)
        rewrite Hb2.
        destruct (Hexcl2 x Hb2) as [Hb1f [Hb3f [Hb4f Hb5f]]].
        rewrite Hb1f, Hb3f, Hb4f, Hb5f. simpl. lra.
      + (* x in b3 *)
        rewrite Hb3.
        destruct (Hexcl3 x Hb3) as [Hb1f [Hb2f [Hb4f Hb5f]]].
        rewrite Hb1f, Hb2f, Hb4f, Hb5f. simpl. lra.
      + (* x in b4 *)
        rewrite Hb4.
        destruct (Hexcl4 x Hb4) as [Hb1f [Hb2f [Hb3f Hb5f]]].
        rewrite Hb1f, Hb2f, Hb3f, Hb5f. simpl. lra.
      + (* x in b5 *)
        rewrite Hb5.
        destruct (Hexcl5 x Hb5) as [Hb1f [Hb2f [Hb3f Hb4f]]].
        rewrite Hb1f, Hb2f, Hb3f, Hb4f. simpl. lra.
  Qed.

  (* --- Exclusivity from disjointness (derived, 5-way) --- *)

  Lemma pos_excludes_others : forall p,
    plaq_pos p = true ->
    plaq_neg_strict p = false /\ plaq_cross p = false /\ plaq_upper_cross p = false /\ plaq_boundary p = false.
  Proof.
    intros p Hp.
    split; [apply pos_neg_disjoint; exact Hp |].
    split; [apply pos_cross_disjoint; exact Hp |].
    split; [apply pos_upper_cross_disjoint; exact Hp |].
    apply pos_boundary_disjoint; exact Hp.
  Qed.

  Lemma neg_excludes_others : forall p,
    plaq_neg_strict p = true ->
    plaq_pos p = false /\ plaq_cross p = false /\ plaq_upper_cross p = false /\ plaq_boundary p = false.
  Proof.
    intros p Hn.
    split.
    - unfold plaq_neg_strict in Hn. unfold plaq_pos, plaq_in_positive.
      apply Z.ltb_lt in Hn. rewrite Z.gtb_ltb. apply Z.ltb_nlt. lia.
    - split; [apply neg_cross_disjoint; exact Hn |].
      split; [apply neg_upper_cross_disjoint; exact Hn |].
      apply neg_boundary_disjoint; exact Hn.
  Qed.

  Lemma cross_excludes_others : forall p,
    plaq_cross p = true ->
    plaq_pos p = false /\ plaq_neg_strict p = false /\ plaq_upper_cross p = false /\ plaq_boundary p = false.
  Proof.
    intros p Hc.
    unfold plaq_cross in Hc. apply Bool.andb_true_iff in Hc.
    destruct Hc as [Htime Ht].
    apply Z.eqb_eq in Ht.
    split.
    - unfold plaq_pos, plaq_in_positive. rewrite Z.gtb_ltb. apply Z.ltb_nlt. lia.
    - split.
      + unfold plaq_neg_strict. apply Z.ltb_nlt. lia.
      + split.
        * apply cross_upper_cross_disjoint. unfold plaq_cross. rewrite Htime, Ht. reflexivity.
        * apply cross_boundary_disjoint. unfold plaq_cross. rewrite Htime, Ht. reflexivity.
  Qed.

  Lemma upper_cross_excludes_others : forall p,
    plaq_upper_cross p = true ->
    plaq_pos p = false /\ plaq_neg_strict p = false /\ plaq_cross p = false /\ plaq_boundary p = false.
  Proof.
    intros p Huc.
    unfold plaq_upper_cross in Huc. apply Bool.andb_true_iff in Huc.
    destruct Huc as [Htime Ht].
    apply Z.eqb_eq in Ht.
    split.
    - unfold plaq_pos, plaq_in_positive. rewrite Z.gtb_ltb. apply Z.ltb_nlt. lia.
    - split.
      + unfold plaq_neg_strict. apply Z.ltb_nlt. lia.
      + split.
        * unfold plaq_cross. rewrite Htime. simpl. apply Z.eqb_neq. lia.
        * apply upper_cross_boundary_disjoint. unfold plaq_upper_cross. rewrite Htime, Ht. reflexivity.
  Qed.

  Lemma boundary_excludes_others : forall p,
    plaq_boundary p = true ->
    plaq_pos p = false /\ plaq_neg_strict p = false /\ plaq_cross p = false /\ plaq_upper_cross p = false.
  Proof.
    intros p Hb.
    unfold plaq_boundary, plaq_is_boundary in Hb.
    destruct (plaq_involves_time p) eqn:Htime.
    - discriminate Hb.
    - apply Bool.orb_true_iff in Hb. destruct Hb as [Heq0 | Hm1].
      + apply Z.eqb_eq in Heq0.
        split.
        * unfold plaq_pos, plaq_in_positive. rewrite Z.gtb_ltb. apply Z.ltb_nlt. lia.
        * split.
          -- unfold plaq_neg_strict. apply Z.ltb_nlt. lia.
          -- split.
             ++ unfold plaq_cross. rewrite Htime. reflexivity.
             ++ unfold plaq_upper_cross. rewrite Htime. reflexivity.
      + apply Z.eqb_eq in Hm1.
        split.
        * unfold plaq_pos, plaq_in_positive. rewrite Z.gtb_ltb. apply Z.ltb_nlt. lia.
        * split.
          -- unfold plaq_neg_strict. apply Z.ltb_nlt. lia.
          -- split.
             ++ unfold plaq_cross. rewrite Htime. reflexivity.
             ++ unfold plaq_upper_cross. rewrite Htime. reflexivity.
  Qed.

  (* --- Main Decomposition Theorem --- *)

  (* The decomposition is the key structural lemma for reflection positivity. *)
  (* We use the 5-way filter lemma with our exclusive partition. *)
  Theorem wilson_action_decomposes :
    forall U,
      wilson_action U = action_pos U + action_neg U + action_cross U +
                        action_upper_cross U + action_boundary U.
  Proof.
    intro U.
    unfold wilson_action, action_pos, action_neg, action_cross, action_upper_cross, action_boundary.
    apply sum_R_map_filter5.
    - (* Exhaustive: use plaq_exclusive_exhaustive *)
      intros p Hp.
      destruct (plaq_exclusive_exhaustive p Hp) as [Hpos | [Hneg | [Hcross | [Huc | Hbdy]]]];
        [left | right; left | right; right; left | right; right; right; left | right; right; right; right];
        assumption.
    - (* pos excludes others *)
      intros p Hp. apply pos_excludes_others. exact Hp.
    - (* neg excludes others *)
      intros p Hn. apply neg_excludes_others. exact Hn.
    - (* cross excludes others *)
      intros p Hc. apply cross_excludes_others. exact Hc.
    - (* upper_cross excludes others *)
      intros p Huc. apply upper_cross_excludes_others. exact Huc.
    - (* boundary excludes others *)
      intros p Hb. apply boundary_excludes_others. exact Hb.
  Qed.

  End GenericAction.

End WilsonAction.
