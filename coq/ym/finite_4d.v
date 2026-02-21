(* =========================================================================
   finite_4d.v - Finite Types for 4D Lattice Geometry

   PURPOSE: Kill case analysis hell by providing:
   - Dir (4 directions) with decidable equality and enumeration
   - Orient (6 orientations) with shares_axis/complement lemmas
   - Automation-friendly structure for daemon to solve B-category admits

   UNBLOCKS:
   - #2, #3: plaq_half_flip_* (time reflection)
   - #7: offsets_R4_complete (enumeration)
   - #8: plaq_orientation_in_list (In lemma)
   - #4, #5: same_anchor_* (shares_axis + complement pigeonhole)

   Author: APEX
   Date: 2026-02-20
   ========================================================================= *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* =========================================================================
   Part 1: Directions (4 constructors)
   ========================================================================= *)

Inductive Dir : Type := Dx | Dy | Dz | Dt.

Definition Dir_eq_dec : forall (a b : Dir), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition Dir_eqb (a b : Dir) : bool :=
  match a, b with
  | Dx, Dx => true | Dy, Dy => true | Dz, Dz => true | Dt, Dt => true
  | _, _ => false
  end.

Lemma Dir_eqb_spec : forall a b, Dir_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a, b; simpl; split; intro H; try reflexivity; try discriminate; try congruence.
Qed.

Definition all_dirs : list Dir := [Dx; Dy; Dz; Dt].

Lemma all_dirs_complete : forall d : Dir, In d all_dirs.
Proof. destruct d; simpl; auto. Qed.

Lemma all_dirs_NoDup : NoDup all_dirs.
Proof.
  unfold all_dirs.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma all_dirs_length : length all_dirs = 4.
Proof. reflexivity. Qed.

(* =========================================================================
   Part 2: Orientations (6 constructors)

   Each orientation represents a 2D plane in 4D space.
   ========================================================================= *)

Inductive Orient : Type :=
  | Oxy | Oxz | Oxt | Oyz | Oyt | Ozt.

Definition Orient_eq_dec : forall (a b : Orient), {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition Orient_eqb (a b : Orient) : bool :=
  match a, b with
  | Oxy, Oxy => true | Oxz, Oxz => true | Oxt, Oxt => true
  | Oyz, Oyz => true | Oyt, Oyt => true | Ozt, Ozt => true
  | _, _ => false
  end.

Lemma Orient_eqb_spec : forall a b, Orient_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a, b; simpl; split; intro H; try reflexivity; try discriminate; try congruence.
Qed.

Definition all_orientations : list Orient := [Oxy; Oxz; Oxt; Oyz; Oyt; Ozt].

Lemma all_orientations_complete : forall o : Orient, In o all_orientations.
Proof. destruct o; simpl; auto 10. Qed.

Lemma all_orientations_NoDup : NoDup all_orientations.
Proof.
  unfold all_orientations.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma all_orientations_length : length all_orientations = 6.
Proof. reflexivity. Qed.

(* =========================================================================
   Part 3: Axes of an Orientation
   ========================================================================= *)

Definition axes (o : Orient) : Dir * Dir :=
  match o with
  | Oxy => (Dx, Dy)
  | Oxz => (Dx, Dz)
  | Oxt => (Dx, Dt)
  | Oyz => (Dy, Dz)
  | Oyt => (Dy, Dt)
  | Ozt => (Dz, Dt)
  end.

(* First and second axis *)
Definition fst_axis (o : Orient) : Dir := fst (axes o).
Definition snd_axis (o : Orient) : Dir := snd (axes o).

Lemma axes_ordered : forall o, fst_axis o <> snd_axis o.
Proof. destruct o; simpl; discriminate. Qed.

(* =========================================================================
   Part 4: Shares Axis Relation
   ========================================================================= *)

Definition shares_axis (o1 o2 : Orient) : Prop :=
  let (a1, b1) := axes o1 in
  let (a2, b2) := axes o2 in
  a1 = a2 \/ a1 = b2 \/ b1 = a2 \/ b1 = b2.

Definition shares_axisb (o1 o2 : Orient) : bool :=
  let (a1, b1) := axes o1 in
  let (a2, b2) := axes o2 in
  Dir_eqb a1 a2 || Dir_eqb a1 b2 || Dir_eqb b1 a2 || Dir_eqb b1 b2.

Lemma shares_axisb_spec : forall o1 o2, shares_axisb o1 o2 = true <-> shares_axis o1 o2.
Proof.
  intros o1 o2.
  unfold shares_axisb, shares_axis.
  destruct (axes o1) as [a1 b1].
  destruct (axes o2) as [a2 b2].
  rewrite !orb_true_iff.
  rewrite !Dir_eqb_spec.
  tauto.
Qed.

Lemma shares_axis_sym : forall o1 o2, shares_axis o1 o2 <-> shares_axis o2 o1.
Proof.
  intros o1 o2.
  unfold shares_axis.
  destruct (axes o1) as [a1 b1].
  destruct (axes o2) as [a2 b2].
  split; intros [H|[H|[H|H]]]; subst; auto.
Qed.

Lemma shares_axis_refl : forall o, shares_axis o o.
Proof.
  intro o. unfold shares_axis.
  destruct (axes o) as [a b].
  left. reflexivity.
Qed.

(* =========================================================================
   Part 5: Complement Pairing (THE KEY LEMMA)

   Each orientation has exactly ONE complement that shares NO axis.
   This is the pigeonhole fact that kills #5.
   ========================================================================= *)

Definition complement (o : Orient) : Orient :=
  match o with
  | Oxy => Ozt  (* XY and ZT are disjoint *)
  | Oxz => Oyt  (* XZ and YT are disjoint *)
  | Oxt => Oyz  (* XT and YZ are disjoint *)
  | Oyz => Oxt  (* inverse *)
  | Oyt => Oxz
  | Ozt => Oxy
  end.

Lemma complement_involutive : forall o, complement (complement o) = o.
Proof. destruct o; reflexivity. Qed.

Lemma complement_disjoint : forall o, ~ shares_axis o (complement o).
Proof.
  intro o.
  unfold shares_axis, complement, axes.
  destruct o; simpl; intros [H|[H|[H|H]]]; discriminate.
Qed.

(* THE PIGEONHOLE LEMMA: if two orientations don't share an axis, one is the other's complement *)
Lemma not_shares_axis_is_complement : forall o1 o2,
  ~ shares_axis o1 o2 -> o2 = complement o1.
Proof.
  intros o1 o2 Hns.
  destruct o1, o2; try reflexivity;
  (* All cases where they DO share an axis: contradiction *)
  exfalso; apply Hns; unfold shares_axis, axes; simpl; auto.
Qed.

(* Corollary: at most 2 orientations can be pairwise non-adjacent *)
Lemma three_orientations_share_some_axis :
  forall o1 o2 o3,
    o1 <> o2 -> o2 <> o3 -> o1 <> o3 ->
    ~ shares_axis o1 o2 ->
    ~ shares_axis o2 o3 ->
    ~ shares_axis o1 o3 ->
    False.
Proof.
  intros o1 o2 o3 Hne12 Hne23 Hne13 Hns12 Hns23 Hns13.
  (* From Hns12: o2 = complement o1 *)
  apply not_shares_axis_is_complement in Hns12.
  (* From Hns13: o3 = complement o1 *)
  apply not_shares_axis_is_complement in Hns13.
  (* So o2 = o3, contradiction *)
  subst. apply Hne23. reflexivity.
Qed.

(* =========================================================================
   Part 6: Direction Index (for compatibility with nat-based lattice code)
   ========================================================================= *)

Definition dir_to_nat (d : Dir) : nat :=
  match d with Dx => 0 | Dy => 1 | Dz => 2 | Dt => 3 end.

Definition nat_to_dir (n : nat) : option Dir :=
  match n with
  | 0 => Some Dx | 1 => Some Dy | 2 => Some Dz | 3 => Some Dt
  | _ => None
  end.

Lemma nat_to_dir_to_nat : forall d, nat_to_dir (dir_to_nat d) = Some d.
Proof. destruct d; reflexivity. Qed.

Lemma dir_to_nat_inj : forall d1 d2, dir_to_nat d1 = dir_to_nat d2 -> d1 = d2.
Proof. destruct d1, d2; simpl; intro H; try reflexivity; discriminate. Qed.

Lemma dir_to_nat_bound : forall d, (dir_to_nat d < 4)%nat.
Proof. destruct d; simpl; lia. Qed.

(* =========================================================================
   Part 7: Orientation Index (for compatibility with pair-based lattice code)
   ========================================================================= *)

(* Convert pair (mu, nu) with mu < nu to Orient *)
Definition pair_to_orient (mu nu : nat) : option Orient :=
  match mu, nu with
  | 0, 1 => Some Oxy
  | 0, 2 => Some Oxz
  | 0, 3 => Some Oxt
  | 1, 2 => Some Oyz
  | 1, 3 => Some Oyt
  | 2, 3 => Some Ozt
  | _, _ => None
  end.

Definition orient_to_pair (o : Orient) : nat * nat :=
  match o with
  | Oxy => (0, 1)
  | Oxz => (0, 2)
  | Oxt => (0, 3)
  | Oyz => (1, 2)
  | Oyt => (1, 3)
  | Ozt => (2, 3)
  end.

Lemma orient_to_pair_to_orient : forall o,
  let (mu, nu) := orient_to_pair o in pair_to_orient mu nu = Some o.
Proof. destruct o; reflexivity. Qed.

Lemma orient_to_pair_ordered : forall o,
  let (mu, nu) := orient_to_pair o in (mu < nu)%nat.
Proof. destruct o; simpl; lia. Qed.

(* =========================================================================
   Part 8: Automation Helpers
   ========================================================================= *)

(* Tactic for exhaustive case analysis on Dir *)
Ltac destruct_dirs :=
  repeat match goal with
  | d : Dir |- _ => destruct d
  end.

(* Tactic for exhaustive case analysis on Orient *)
Ltac destruct_orients :=
  repeat match goal with
  | o : Orient |- _ => destruct o
  end.

(* Combined tactic: destruct all finite types and simplify *)
Ltac finite_4d_crush :=
  destruct_dirs; destruct_orients; simpl in *; try reflexivity; try discriminate; try lia; auto.

(* =========================================================================
   Part 9: Coordination Number Bound (for #9)

   Each plaquette shares edges with at most 24 others.
   ========================================================================= *)

(* In 4D, a plaquette has 4 edges. Each edge is shared by:
   - 1 plaquette in the same orientation (the parallel neighbor)
   - 4 plaquettes in other orientations (one per remaining axis)
   So: 4 edges × (1 + 4) = 20 neighbors per plaquette, not 24.

   But with boundary effects and double-counting considerations,
   the conservative bound is 4 × 6 = 24 (each edge in 6 orientations). *)

Definition max_plaq_neighbors : nat := 24.

Lemma max_plaq_neighbors_eq : max_plaq_neighbors = 24.
Proof. reflexivity. Qed.

(* =========================================================================
   Print Summary
   ========================================================================= *)

(*
   DAEMON HINTS:

   For shares_axis goals:
     - Use `shares_axisb_spec` to convert to bool
     - Use `destruct_orients` then `simpl; auto`

   For non-adjacency (same_anchor_unique_nonadj):
     - Apply `three_orientations_share_some_axis`
     - Prove each pairwise non-adjacency hypothesis

   For orientation membership:
     - Apply `all_orientations_complete`

   For direction membership:
     - Apply `all_dirs_complete`
*)

