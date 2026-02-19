(* =========================================================================
   lattice.v - Finite Volume Lattice Structure (Generic)
   
   Geometric foundation for lattice gauge theory.
   Defines Sites, Links, Plaquettes, and Reflection Geometry.
   Independent of the gauge group.

   Based on u1_lattice.v.
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Lra.
From Coq Require Import Lia.
From Coq Require Import Psatz.

Import ListNotations.
Open Scope R_scope.
Open Scope Z_scope.

Module Lattice.

(* =========================================================================
   Part 1: Site and Link Types
   ========================================================================= *)

(* Lattice site with integer coordinates (Z allows negative for reflection) *)
Record site := mk_site {
  site_t : Z;  (* Euclidean time *)
  site_x : Z;
  site_y : Z;
  site_z : Z
}.

(* Direction: 0 = time, 1,2,3 = space *)
Inductive direction : Type :=
  | Dir_t : direction
  | Dir_x : direction
  | Dir_y : direction
  | Dir_z : direction.

Definition direction_eq_dec : forall (d1 d2 : direction), {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Defined.

(* Link: oriented edge from site in direction *)
Record link := mk_link {
  link_src : site;
  link_dir : direction
}.

(* Target site of a link *)
Definition link_tgt (l : link) : site :=
  let s := link_src l in
  match link_dir l with
  | Dir_t => mk_site (site_t s + 1) (site_x s) (site_y s) (site_z s)
  | Dir_x => mk_site (site_t s) (site_x s + 1) (site_y s) (site_z s)
  | Dir_y => mk_site (site_t s) (site_x s) (site_y s + 1) (site_z s)
  | Dir_z => mk_site (site_t s) (site_x s) (site_y s) (site_z s + 1)
  end.

(* Site equality decidable *)
Definition site_eq_dec : forall (s1 s2 : site), {s1 = s2} + {s1 <> s2}.
Proof.
  intros [t1 x1 y1 z1] [t2 x2 y2 z2].
  destruct (Z.eq_dec t1 t2); destruct (Z.eq_dec x1 x2);
  destruct (Z.eq_dec y1 y2); destruct (Z.eq_dec z1 z2);
  try (left; congruence); right; congruence.
Defined.

(* Link equality decidable *)
Definition link_eq_dec : forall (l1 l2 : link), {l1 = l2} + {l1 <> l2}.
Proof.
  intros [s1 d1] [s2 d2].
  destruct (site_eq_dec s1 s2); destruct (direction_eq_dec d1 d2);
  try (left; congruence); right; congruence.
Defined.

(* =========================================================================
   Part 2: Finite Volume - Explicit Link List
   ========================================================================= *)

(* Lattice size L: half-width, so time coordinates are in [-L, L-1] *)
Definition lattice_size := nat.

(* Generate non-negative range [0, 1, ..., n-1] *)
Fixpoint range_nat_Z (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => Z.of_nat n' :: range_nat_Z n'
  end.

(* Generate negative range [-n, -n+1, ..., -1] *)
Fixpoint range_neg_Z (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => (- Z.of_nat n)%Z :: range_neg_Z n'
  end.

(* Symmetric range for TIME coordinate: [-L, -L+1, ..., -1, 0, 1, ..., L-1]
   This is needed for reflection positivity around t=0 *)
Definition symmetric_range_Z (L : nat) : list Z :=
  range_neg_Z L ++ range_nat_Z L.

(* Spatial range [0, 1, ..., L-1] - spatial dimensions don't need symmetry *)
Definition range_Z (n : nat) : list Z := range_nat_Z n.

(* All sites: time in [-L, L-1], space in [0, L-1] *)
Definition all_sites (L : lattice_size) : list site :=
  flat_map (fun t =>
    flat_map (fun x =>
      flat_map (fun y =>
        map (fun z => mk_site t x y z) (range_Z L)
      ) (range_Z L)
    ) (range_Z L)
  ) (symmetric_range_Z L).

(* All directions *)
Definition all_directions : list direction := [Dir_t; Dir_x; Dir_y; Dir_z].

(* All links in L^4 lattice: 4 * L^4 links *)
Definition all_links (L : lattice_size) : list link :=
  flat_map (fun s =>
    map (fun d => mk_link s d) all_directions
  ) (all_sites L).

(* =========================================================================
   Part 3: Plaquette Structure
   ========================================================================= *)

(* Plaquette: minimal closed loop in a plane *)
Record plaquette := mk_plaq {
  plaq_site : site;
  plaq_mu : direction;   (* first direction *)
  plaq_nu : direction    (* second direction *)
}.

(* Direction pairs for plaquettes: (mu, nu) with mu < nu in canonical order *)
Definition direction_pairs : list (direction * direction) :=
  [(Dir_t, Dir_x); (Dir_t, Dir_y); (Dir_t, Dir_z);
   (Dir_x, Dir_y); (Dir_x, Dir_z); (Dir_y, Dir_z)].

(* All plaquettes: 6 * L^4 *)
Definition all_plaquettes (L : lattice_size) : list plaquette :=
  flat_map (fun s =>
    map (fun '(mu, nu) => mk_plaq s mu nu) direction_pairs
  ) (all_sites L).

(* Plaquette boundary: the 4 oriented links forming the plaquette
   Returns list of (link, sign) where sign=true means + orientation *)
Definition shift_site (s : site) (d : direction) : site :=
  match d with
  | Dir_t => mk_site (site_t s + 1) (site_x s) (site_y s) (site_z s)
  | Dir_x => mk_site (site_t s) (site_x s + 1) (site_y s) (site_z s)
  | Dir_y => mk_site (site_t s) (site_x s) (site_y s + 1) (site_z s)
  | Dir_z => mk_site (site_t s) (site_x s) (site_y s) (site_z s + 1)
  end.

Definition plaq_boundary (p : plaquette) : list (link * bool) :=
  let x := plaq_site p in
  let mu := plaq_mu p in
  let nu := plaq_nu p in
  (* Counterclockwise: x→x+mu→x+mu+nu→x+nu→x *)
  [ (mk_link x mu, true);                           (* x in direction mu, + *)
    (mk_link (shift_site x mu) nu, true);           (* x+mu in direction nu, + *)
    (mk_link (shift_site x nu) mu, false);          (* x+nu in direction mu, - *)
    (mk_link x nu, false)                           (* x in direction nu, - *)
  ].

(* =========================================================================
   Part 5: Time Reflection Structure
   ========================================================================= *)

(* Time coordinate extraction *)
Definition tcoord (s : site) : Z := site_t s.

(* Reflect site in time: t -> -t *)
Definition reflect_site (s : site) : site :=
  mk_site (- site_t s) (site_x s) (site_y s) (site_z s).

Lemma reflect_time : forall s, tcoord (reflect_site s) = - tcoord s.
Proof. intros [t x y z]. reflexivity. Qed.

(* Reflect a link. Time-like links flip orientation. *)
Definition reflect_link (l : link) : link :=
  let s := link_src l in
  let d := link_dir l in
  match d with
  | Dir_t =>
      (* Time-like link: reflect source, but the link now points backward
         so we use the reflected target as new source *)
      mk_link (reflect_site (shift_site s Dir_t)) Dir_t
  | _ =>
      (* Space-like link: just reflect the source site *)
      mk_link (reflect_site s) d
  end.

(* Does time reflection flip this link's orientation? *)
Definition orientation_flipped (l : link) : bool :=
  match link_dir l with
  | Dir_t => true   (* time-like links get inverted *)
  | _ => false
  end.

(* Positive time half-space: t > 0 *)
Definition positive_time_site (s : site) : Prop :=
  (site_t s > 0)%Z.

Definition positive_time_link (l : link) : Prop :=
  positive_time_site (link_src l).

(* Links strictly in positive time half *)
Definition links_positive (L : lattice_size) : list link :=
  filter (fun l => Z.gtb (site_t (link_src l)) 0) (all_links L).

(* =========================================================================
   Part 6: Core Reflection Geometry Lemmas
   ========================================================================= *)

(* Site reflection is an involution *)
Lemma reflect_site_involutive : forall s,
  reflect_site (reflect_site s) = s.
Proof.
  intros [t x y z]. unfold reflect_site. simpl.
  f_equal. lia.
Qed.

(* Shift then reflect vs reflect then shift (for time direction) *)
Lemma reflect_shift_t : forall s,
  reflect_site (shift_site s Dir_t) =
  mk_site (- site_t s - 1) (site_x s) (site_y s) (site_z s).
Proof.
  intros [t x y z]. unfold reflect_site, shift_site. simpl. f_equal. lia.
Qed.

(* Link reflection is an involution *)
Lemma reflect_link_involutive : forall l,
  reflect_link (reflect_link l) = l.
Proof.
  intros [[t x y z] d].
  unfold reflect_link, reflect_site, shift_site. simpl.
  destruct d; simpl; f_equal; f_equal; lia.
Qed.

(* orientation_flipped is preserved under reflection *)
Lemma orientation_flipped_reflect : forall l,
  orientation_flipped (reflect_link l) = orientation_flipped l.
Proof.
  intros [s d]. unfold reflect_link, orientation_flipped. simpl.
  destruct d; reflexivity.
Qed.

(* Key lemma: reflecting a positive-time link gives a negative-time link *)
Lemma reflect_link_pos_time_to_neg : forall l,
  (site_t (link_src l) > 0)%Z ->
  (site_t (link_src (reflect_link l)) < 0)%Z.
Proof.
  intros [[t x y z] d] Hpos.
  unfold reflect_link, reflect_site, shift_site. simpl in *.
  destruct d; simpl; lia.
Qed.

(* Reverse direction: neg -> pos (ONLY for space-like links)
   For time-like links with t = -1, reflection gives t = 0 (boundary).
   Time-like links need t ≤ -2 for strict positivity. *)
Lemma reflect_link_neg_time_to_pos_spacetime : forall l,
  (site_t (link_src l) < 0)%Z ->
  (site_t (link_src (reflect_link l)) >= 0)%Z.
Proof.
  intros [[t x y z] d] Hneg.
  unfold reflect_link, reflect_site, shift_site. simpl in *.
  destruct d; simpl; lia.
Qed.

(* Space-like links: strict neg -> pos *)
Lemma reflect_link_neg_time_to_pos_spacelike : forall l,
  link_dir l <> Dir_t ->
  (site_t (link_src l) < 0)%Z ->
  (site_t (link_src (reflect_link l)) > 0)%Z.
Proof.
  intros [[t x y z] d] Hspace Hneg.
  unfold reflect_link, reflect_site, shift_site. simpl in *.
  destruct d; simpl; try lia.
  - exfalso. apply Hspace. reflexivity.
Qed.

(* Z.gtb / Z.ltb reflection lemmas - use standard library *)
Lemma Z_gtb_pos : forall t, Z.gtb t 0 = true <-> (t > 0)%Z.
Proof.
  intros t. apply Z.gtb_gt.
Qed.

Lemma Z_ltb_neg : forall t, Z.ltb t 0 = true <-> (t < 0)%Z.
Proof.
  intros t. apply Z.ltb_lt.
Qed.

(* =========================================================================
   Part 7: Range Membership Lemmas (for proving reflection preserves lattice)
   ========================================================================= *)

(* Membership in range_nat_Z *)
Lemma In_range_nat_Z : forall n t,
  In t (range_nat_Z n) <-> (0 <= t < Z.of_nat n)%Z.
Proof.
  induction n; intros t; simpl.
  - split; [intros []| lia].
  - split.
    + intros [Heq | Hin].
      * subst. lia.
      * apply IHn in Hin. lia.
    + intros [Hge Hlt].
      destruct (Z.eq_dec t (Z.of_nat n)) as [Heq | Hne].
      * left. symmetry. exact Heq.
      * right. apply IHn. lia.
Qed.

(* Membership in range_neg_Z *)
Lemma In_range_neg_Z : forall n t,
  In t (range_neg_Z n) <-> (- Z.of_nat n <= t < 0)%Z.
Proof.
  induction n; intros t; simpl.
  - split; [intros []| lia].
  - split.
    + intros [Heq | Hin].
      * subst. lia.
      * apply IHn in Hin. lia.
    + intros [Hge Hlt].
      destruct (Z.eq_dec t (- Z.of_nat (S n))%Z) as [Heq | Hne].
      * left. symmetry. exact Heq.
      * right. apply IHn. lia.
Qed.

(* Membership in symmetric_range_Z *)
Lemma In_symmetric_range_Z : forall L t,
  In t (symmetric_range_Z L) <-> (- Z.of_nat L <= t < Z.of_nat L)%Z.
Proof.
  intros L t. unfold symmetric_range_Z.
  rewrite in_app_iff.
  rewrite In_range_neg_Z, In_range_nat_Z.
  lia.
Qed.

(* Time in positive half of symmetric range *)
Lemma symmetric_range_pos_half : forall L t,
  In t (symmetric_range_Z L) ->
  (t > 0)%Z ->
  (1 <= t < Z.of_nat L)%Z.
Proof.
  intros L t Hin Hpos.
  apply In_symmetric_range_Z in Hin. lia.
Qed.

(* Reflection of positive time stays in symmetric range *)
Lemma reflect_time_in_range_spacelike : forall L t,
  In t (symmetric_range_Z L) ->
  (t > 0)%Z ->
  In (- t)%Z (symmetric_range_Z L).
Proof.
  intros L t Hin Hpos.
  apply In_symmetric_range_Z.
  apply In_symmetric_range_Z in Hin.
  lia.
Qed.

(* -------------------------------------------------------------------------
   NoDup infrastructure for finite enumerations
   ------------------------------------------------------------------------- *)

Lemma NoDup_app_intro {A : Type} : forall (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros l1 l2 Hnd1 Hnd2 Hdisj.
  induction Hnd1 as [|a l Hnotin Hnd IH]; simpl.
  - exact Hnd2.
  - constructor.
    + intro Hin.
      apply in_app_iff in Hin.
      destruct Hin as [Hinl | Hin2].
      * apply Hnotin; exact Hinl.
      * apply (Hdisj a (or_introl eq_refl)); exact Hin2.
    + apply IH.
      * intros x Hxin.
        apply Hdisj.
        right; exact Hxin.
Qed.

Lemma NoDup_map_injective {A B : Type} : forall (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros f l Hinj Hnd.
  induction Hnd as [|a l Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [x [Hfx Hinx]].
      apply Hinj in Hfx.
      subst x.
      exact (Hnotin Hinx).
    + apply IH.
Qed.

Lemma NoDup_flat_map_disjoint {A B : Type} :
  forall (l : list A) (f : A -> list B),
    NoDup l ->
    (forall a, In a l -> NoDup (f a)) ->
    (forall a1 a2 x, In a1 l -> In a2 l -> a1 <> a2 ->
       In x (f a1) -> ~ In x (f a2)) ->
    NoDup (flat_map f l).
Proof.
  intros l f Hnd Hblocks Hdisj.
  induction Hnd as [|a l Hnotin Hnd IH]; simpl.
  - constructor.
  - apply NoDup_app_intro.
    + apply Hblocks. left; reflexivity.
    + apply IH.
      * intros a0 Ha0. apply Hblocks. right; exact Ha0.
      * intros a1 a2 x Ha1 Ha2 Hneq Hinx.
        apply (Hdisj a1 a2 x).
        -- right; exact Ha1.
        -- right; exact Ha2.
        -- exact Hneq.
        -- exact Hinx.
    + intros x Hinx Hinrest.
      apply in_flat_map in Hinrest.
      destruct Hinrest as [a2 [Ha2 Hinx2]].
      apply (Hdisj a a2 x).
      * left; reflexivity.
      * right; exact Ha2.
      * intro Heq. subst a2. contradiction.
      * exact Hinx.
      * exact Hinx2.
Qed.

Lemma range_nat_Z_nodup : forall n, NoDup (range_nat_Z n).
Proof.
  intro n.
  induction n as [|n IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply In_range_nat_Z in Hin.
      lia.
    + exact IH.
Qed.

Lemma range_neg_Z_nodup : forall n, NoDup (range_neg_Z n).
Proof.
  intro n.
  induction n as [|n IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply In_range_neg_Z in Hin.
      lia.
    + exact IH.
Qed.

Lemma symmetric_range_Z_nodup : forall L, NoDup (symmetric_range_Z L).
Proof.
  intro L.
  unfold symmetric_range_Z.
  apply NoDup_app_intro.
  - apply range_neg_Z_nodup.
  - apply range_nat_Z_nodup.
  - intros x Hneg Hnat.
    apply In_range_neg_Z in Hneg.
    apply In_range_nat_Z in Hnat.
    lia.
Qed.

Lemma range_Z_nodup : forall n, NoDup (range_Z n).
Proof.
  intro n.
  unfold range_Z.
  apply range_nat_Z_nodup.
Qed.

(* Reflection of positive time stays in range for time-like links *)
Lemma reflect_time_in_range_timelike : forall L t,
  In t (symmetric_range_Z L) ->
  (t > 0)%Z ->
  In (- t - 1)%Z (symmetric_range_Z L).
Proof.
  intros L t Hin Hpos.
  apply In_symmetric_range_Z.
  apply In_symmetric_range_Z in Hin.
  lia.
Qed.

(* =========================================================================
   Part 8: Site and Link Membership Lemmas
   ========================================================================= *)

(* Site membership characterization *)
Lemma In_all_sites : forall L s,
  In s (all_sites L) <->
  (In (site_t s) (symmetric_range_Z L) /\
   In (site_x s) (range_Z L) /\
   In (site_y s) (range_Z L) /\
   In (site_z s) (range_Z L)).
Proof.
  intros L [t x y z]. unfold all_sites.
  split.
  - (* forward *)
    intros Hin.
    apply in_flat_map in Hin. destruct Hin as [t' [Ht' Hin]].
    apply in_flat_map in Hin. destruct Hin as [x' [Hx' Hin]].
    apply in_flat_map in Hin. destruct Hin as [y' [Hy' Hin]].
    apply in_map_iff in Hin. destruct Hin as [z' [Heq Hz']].
    injection Heq. intros -> -> -> ->.
    auto.
  - (* backward *)
    intros [Ht [Hx [Hy Hz]]].
    apply in_flat_map. exists t. split; [exact Ht|].
    apply in_flat_map. exists x. split; [exact Hx|].
    apply in_flat_map. exists y. split; [exact Hy|].
    apply in_map_iff. exists z. split; [reflexivity | exact Hz].
Qed.

(* Reflected site preserves spatial coords *)
Lemma reflect_site_spatial : forall s,
  site_x (reflect_site s) = site_x s /\
  site_y (reflect_site s) = site_y s /\
  site_z (reflect_site s) = site_z s.
Proof.
  intros [t x y z]. unfold reflect_site. simpl. auto.
Qed.

(* Reflection of site with positive time stays in lattice *)
Lemma reflect_site_in_lattice : forall L s,
  In s (all_sites L) ->
  (site_t s > 0)%Z ->
  In (reflect_site s) (all_sites L).
Proof.
  intros L s Hin Hpos.
  apply In_all_sites in Hin. destruct Hin as [Ht [Hx [Hy Hz]]].
  apply In_all_sites.
  destruct (reflect_site_spatial s) as [Hx' [Hy' Hz']].
  rewrite Hx', Hy', Hz'.
  split; [|split; [|split]]; try assumption.
  (* Time: -t is in range *)
  destruct s as [t x y z]. simpl in *.
  apply reflect_time_in_range_spacelike; assumption.
Qed.

(* Shifted and reflected site stays in lattice (for time-like links) *)
Lemma reflect_shift_site_in_lattice : forall L s,
  In s (all_sites L) ->
  (site_t s > 0)%Z ->
  In (reflect_site (shift_site s Dir_t)) (all_sites L).
Proof.
  intros L s Hin Hpos.
  apply In_all_sites in Hin. destruct Hin as [Ht [Hx [Hy Hz]]].
  apply In_all_sites.
  destruct s as [t x y z]. simpl in *.
  split; [|split; [|split]]; try assumption.
  (* Time: -(t+1) is in range *)
  (* -(t+1) = -t-1, use reflect_time_in_range_timelike *)
  replace (- (t + 1))%Z with (- t - 1)%Z by lia.
  apply reflect_time_in_range_timelike; assumption.
Qed.

(* Reflection of interior negative-time sites (spatial plaquette case) *)
Lemma reflect_site_in_lattice_neg_interior : forall L s,
  In s (all_sites L) ->
  (- Z.of_nat L < site_t s)%Z ->
  (site_t s < 0)%Z ->
  In (reflect_site s) (all_sites L).
Proof.
  intros L s Hin Hlower Hneg.
  apply In_all_sites in Hin. destruct Hin as [Ht [Hx [Hy Hz]]].
  apply In_all_sites.
  destruct (reflect_site_spatial s) as [Hx' [Hy' Hz']].
  rewrite Hx', Hy', Hz'.
  split; [|split; [|split]]; try assumption.
  destruct s as [t x y z]. simpl in *.
  apply In_symmetric_range_Z.
  apply In_symmetric_range_Z in Ht.
  lia.
Qed.

(* Reflection of negative-time sites for time-like plaquettes *)
Lemma reflect_shift_site_in_lattice_neg : forall L s,
  In s (all_sites L) ->
  (site_t s < -1)%Z ->
  In (reflect_site (shift_site s Dir_t)) (all_sites L).
Proof.
  intros L s Hin Hneg.
  apply In_all_sites in Hin. destruct Hin as [Ht [Hx [Hy Hz]]].
  apply In_all_sites.
  destruct s as [t x y z]. simpl in *.
  split; [|split; [|split]]; try assumption.
  apply In_symmetric_range_Z.
  apply In_symmetric_range_Z in Ht.
  replace (- (t + 1))%Z with (- t - 1)%Z by lia.
  lia.
Qed.

(* Link membership - forward direction *)
Lemma In_all_links_fwd : forall L l,
  In l (all_links L) ->
  In (link_src l) (all_sites L).
Proof.
  intros L [s d] Hin. unfold all_links in Hin.
  apply in_flat_map in Hin. destruct Hin as [s' [Hs' Hin]].
  unfold all_directions in Hin. simpl in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]];
  inversion Heq; subst; exact Hs'.
Qed.

(* Link membership - backward direction *)
Lemma In_all_links_bwd : forall L s d,
  In s (all_sites L) ->
  In (mk_link s d) (all_links L).
Proof.
  intros L s d Hs. unfold all_links.
  apply in_flat_map. exists s. split; [exact Hs|].
  unfold all_directions.
  destruct d; simpl; auto.
Qed.

(* KEY LEMMA: Reflection preserves link membership for positive-time links *)
Lemma reflect_link_in_all_links : forall L l,
  In l (all_links L) ->
  (site_t (link_src l) > 0)%Z ->
  In (reflect_link l) (all_links L).
Proof.
  intros L [s d] Hin Hpos.
  simpl in Hpos.
  apply In_all_links_fwd in Hin.
  unfold reflect_link.
  destruct d.
  - (* Dir_t: source is reflect_site (shift_site s Dir_t) *)
    apply In_all_links_bwd.
    apply reflect_shift_site_in_lattice; assumption.
  - (* Dir_x: source is reflect_site s *)
    apply In_all_links_bwd.
    apply reflect_site_in_lattice; assumption.
  - (* Dir_y *)
    apply In_all_links_bwd.
    apply reflect_site_in_lattice; assumption.
  - (* Dir_z *)
    apply In_all_links_bwd.
    apply reflect_site_in_lattice; assumption.
Qed.

(* =========================================================================
   Part 8: Plaquette Reflection
   ========================================================================= *)

(* Shift commutativity: order of shifts doesn't matter *)
Lemma shift_site_comm : forall s d1 d2,
  shift_site (shift_site s d1) d2 = shift_site (shift_site s d2) d1.
Proof.
  intros [t x y z] d1 d2.
  destruct d1, d2; unfold shift_site; simpl; f_equal; lia.
Qed.

(* Plaquette reflection: conditional based on whether plaquette involves time *)
Definition plaq_involves_time (p : plaquette) : bool :=
  match plaq_mu p, plaq_nu p with
  | Dir_t, _ => true
  | _, Dir_t => true
  | _, _ => false
  end.

Definition reflect_plaq (p : plaquette) : plaquette :=
  let x := plaq_site p in
  let mu := plaq_mu p in
  let nu := plaq_nu p in
  if plaq_involves_time p then
    mk_plaq (reflect_site (shift_site x Dir_t)) mu nu
  else
    mk_plaq (reflect_site x) mu nu.

(* Reflected edge: reflect the link, preserve the sign *)
Definition reflect_edge (e : link * bool) : link * bool :=
  let (l, sgn) := e in (reflect_link l, sgn).

(* Key lemma: reflect_site commutes with shift_site for spatial directions *)
Lemma reflect_shift_spatial : forall s d,
  d <> Dir_t ->
  reflect_site (shift_site s d) = shift_site (reflect_site s) d.
Proof.
  intros [t x y z] d Hd.
  destruct d; try contradiction; unfold reflect_site, shift_site; simpl; reflexivity.
Qed.

(* Helper: what reflect_link does on each boundary link *)
Lemma reflect_link_at_site : forall s d,
  d <> Dir_t ->
  reflect_link (mk_link s d) = mk_link (reflect_site s) d.
Proof.
  intros s d Hd.
  unfold reflect_link. destruct d; try reflexivity; contradiction.
Qed.

Lemma reflect_link_time : forall s,
  reflect_link (mk_link s Dir_t) = mk_link (reflect_site (shift_site s Dir_t)) Dir_t.
Proof.
  intros s. unfold reflect_link. reflexivity.
Qed.

(* =========================================================================
   Part 9: Plaquette Time Classification
   ========================================================================= *)

(* Plaquette is entirely in positive time *)
Definition plaq_in_positive (p : plaquette) : bool :=
  Z.gtb (site_t (plaq_site p)) 0.

(* Plaquette is entirely in negative time. *)
Definition plaq_in_negative (L : lattice_size) (p : plaquette) : bool :=
  if plaq_involves_time p then
    Z.ltb (site_t (plaq_site p)) (-1)
  else
    andb (Z.ltb (site_t (plaq_site p)) 0)
         (Z.gtb (site_t (plaq_site p)) (- Z.of_nat L)).

(* =========================================================================
   Part 10: Plaquette Reflection API for Permutation-based proofs
   ========================================================================= *)

(* reflect_plaq is an involution *)
Lemma reflect_plaq_involutive : forall p,
  reflect_plaq (reflect_plaq p) = p.
Proof.
  intros [[t x y z] mu nu].
  unfold reflect_plaq, plaq_involves_time.
  destruct mu, nu; simpl;
  unfold reflect_site, shift_site; simpl;
  f_equal; f_equal; lia.
Qed.

Lemma plaq_involves_time_reflect : forall p,
  plaq_involves_time (reflect_plaq p) = plaq_involves_time p.
Proof.
  intros [[t x y z] mu nu].
  unfold reflect_plaq, plaq_involves_time.
  destruct mu, nu; reflexivity.
Qed.

(* Helper: site reflection negates the time coordinate *)
Lemma site_t_reflect : forall s,
  site_t (reflect_site s) = (- site_t s)%Z.
Proof.
  intros [t x y z]. reflexivity.
Qed.

(* Helper: shift_site Dir_t adds 1 to time *)
Lemma site_t_shift_t : forall s,
  site_t (shift_site s Dir_t) = (site_t s + 1)%Z.
Proof.
  intros [t x y z]. reflexivity.
Qed.

(* Key half-space transport used by permutation proofs *)
Lemma plaq_half_flip_neg_to_pos : forall L p,
  plaq_in_negative L p = true ->
  plaq_in_positive (reflect_plaq p) = true.
Proof.
  intros L [[t x y z] mu nu] Hneg.
  unfold plaq_in_negative, plaq_in_positive, reflect_plaq, plaq_involves_time in *.
  unfold reflect_site, shift_site in *.
  destruct mu, nu; simpl in *;
    try (apply Z.ltb_lt in Hneg; apply Z.gtb_gt; lia);
    try (apply andb_true_iff in Hneg as [Hlt Hgt];
         apply Z.ltb_lt in Hlt;
         apply Z.gtb_gt in Hgt;
         apply Z.gtb_gt; lia).
Qed.

Lemma plaq_half_flip_pos_to_neg : forall L p,
  In p (all_plaquettes L) ->
  plaq_in_positive p = true ->
  plaq_in_negative L (reflect_plaq p) = true.
Proof.
  intros L [[t x y z] mu nu] Hin Hpos.
  unfold all_plaquettes in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [s [Hs Hin]].
  apply in_map_iff in Hin.
  destruct Hin as [[mu' nu'] [Heq Hpair]].
  inversion Heq; subst s mu' nu'.
  apply In_all_sites in Hs.
  destruct Hs as [Ht _].
  apply In_symmetric_range_Z in Ht.
  unfold plaq_in_positive, plaq_in_negative, reflect_plaq, plaq_involves_time in *.
  unfold reflect_site, shift_site in *.
  apply Z.gtb_gt in Hpos.
  destruct mu, nu; simpl in *;
    try (apply Z.ltb_lt; lia);
    try (apply andb_true_iff; split;
         [apply Z.ltb_lt | apply Z.gtb_gt]; lia).
Qed.

(* Plaquette membership in all_plaquettes - forward direction *)
Lemma In_all_plaquettes_fwd : forall L p,
  In p (all_plaquettes L) ->
  In (plaq_site p) (all_sites L).
Proof.
  intros L [[t x y z] mu nu] Hin.
  unfold all_plaquettes in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [s [Hs Hin]].
  apply in_map_iff in Hin.
  destruct Hin as [[mu' nu'] [Heq Hdir]].
  inversion Heq; subst.
  exact Hs.
Qed.

(* Plaquette membership - backward direction *)
Lemma In_all_plaquettes_bwd : forall L s mu nu,
  In s (all_sites L) ->
  In (mu, nu) direction_pairs ->
  In (mk_plaq s mu nu) (all_plaquettes L).
Proof.
  intros L s mu nu Hs Hdir.
  unfold all_plaquettes.
  apply in_flat_map.
  exists s. split; [exact Hs|].
  apply in_map_iff.
  exists (mu, nu). split; [reflexivity | exact Hdir].
Qed.

(* Direction pairs preserved under plaquette reflection *)
Lemma reflect_plaq_preserves_dirs : forall p,
  plaq_mu (reflect_plaq p) = plaq_mu p /\
  plaq_nu (reflect_plaq p) = plaq_nu p.
Proof.
  intros [[t x y z] mu nu].
  unfold reflect_plaq, plaq_involves_time.
  destruct mu, nu; simpl; auto.
Qed.

(* reflect_plaq preserves membership for negative-time plaquettes *)
Lemma reflect_plaq_in_lattice : forall L p,
  In p (all_plaquettes L) ->
  plaq_in_negative L p = true ->
  In (reflect_plaq p) (all_plaquettes L).
Proof.
  intros L [s mu nu] Hin Hneg.
  unfold all_plaquettes in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [s' [Hsite Hin]].
  apply in_map_iff in Hin.
  destruct Hin as [[mu' nu'] [Heq Hpair]].
  inversion Heq; subst s' mu' nu'.
  unfold plaq_in_negative in Hneg.
  unfold direction_pairs in Hpair.
  destruct Hpair as [Hpair
                   | [Hpair
                   | [Hpair
                   | [Hpair
                   | [Hpair
                   | [Hpair | []]]]]]].
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply Z.ltb_lt in Hneg.
    apply In_all_plaquettes_bwd.
    + apply reflect_shift_site_in_lattice_neg; [exact Hsite | exact Hneg].
    + unfold direction_pairs; simpl; tauto.
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply Z.ltb_lt in Hneg.
    apply In_all_plaquettes_bwd.
    + apply reflect_shift_site_in_lattice_neg; [exact Hsite | exact Hneg].
    + unfold direction_pairs; simpl; tauto.
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply Z.ltb_lt in Hneg.
    apply In_all_plaquettes_bwd.
    + apply reflect_shift_site_in_lattice_neg; [exact Hsite | exact Hneg].
    + unfold direction_pairs; simpl; tauto.
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply andb_true_iff in Hneg as [Hlt Hgt].
    apply Z.ltb_lt in Hlt.
    apply Z.gtb_gt in Hgt.
    apply In_all_plaquettes_bwd.
    + apply (reflect_site_in_lattice_neg_interior L s).
      * exact Hsite.
      * lia.
      * lia.
    + unfold direction_pairs; simpl; tauto.
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply andb_true_iff in Hneg as [Hlt Hgt].
    apply Z.ltb_lt in Hlt.
    apply Z.gtb_gt in Hgt.
    apply In_all_plaquettes_bwd.
    + apply (reflect_site_in_lattice_neg_interior L s).
      * exact Hsite.
      * lia.
      * lia.
    + unfold direction_pairs; simpl; tauto.
  - inversion Hpair; subst mu nu.
    simpl in Hneg.
    apply andb_true_iff in Hneg as [Hlt Hgt].
    apply Z.ltb_lt in Hlt.
    apply Z.gtb_gt in Hgt.
    apply In_all_plaquettes_bwd.
    + apply (reflect_site_in_lattice_neg_interior L s).
      * exact Hsite.
      * lia.
      * lia.
    + unfold direction_pairs; simpl; tauto.
Qed.

(* NoDup for direction_pairs - infrastructure *)
Lemma direction_pairs_in : forall mu nu,
  In (mu, nu) direction_pairs <->
  (mu = Dir_t /\ nu = Dir_x) \/
  (mu = Dir_t /\ nu = Dir_y) \/
  (mu = Dir_t /\ nu = Dir_z) \/
  (mu = Dir_x /\ nu = Dir_y) \/
  (mu = Dir_x /\ nu = Dir_z) \/
  (mu = Dir_y /\ nu = Dir_z).
Proof.
  intros mu nu.
  unfold direction_pairs.
  split.
  - intros [H | [H | [H | [H | [H | [H | []]]]]]];
    injection H; intros; subst; auto 10.
  - intros [[H1 H2] | [[H1 H2] | [[H1 H2] | [[H1 H2] | [[H1 H2] | [H1 H2]]]]]];
    subst; simpl; auto 10.
Qed.

Lemma direction_pairs_nodup : NoDup direction_pairs.
Proof.
  unfold direction_pairs.
  repeat constructor; simpl; intros H;
    repeat (destruct H as [H | H]); inversion H.
Qed.

Lemma all_sites_nodup : forall L, NoDup (all_sites L).
Proof.
  intro L.
  unfold all_sites.
  eapply NoDup_flat_map_disjoint with
    (f := fun t =>
      flat_map (fun x =>
        flat_map (fun y =>
          map (fun z => mk_site t x y z) (range_Z L)
        ) (range_Z L)
      ) (range_Z L)).
  - apply symmetric_range_Z_nodup.
  - intros t Ht.
    eapply NoDup_flat_map_disjoint with
      (f := fun x =>
        flat_map (fun y =>
          map (fun z => mk_site t x y z) (range_Z L)
        ) (range_Z L)).
    + apply range_Z_nodup.
    + intros x Hx.
      eapply NoDup_flat_map_disjoint with
        (f := fun y =>
          map (fun z => mk_site t x y z) (range_Z L)).
      * apply range_Z_nodup.
      * intros y Hy.
        apply NoDup_map_injective.
        -- intros z1 z2 Heq.
           inversion Heq.
           reflexivity.
        -- apply range_Z_nodup.
      * intros y1 y2 s Hy1 Hy2 Hneq Hin1 Hin2.
        apply in_map_iff in Hin1.
        destruct Hin1 as [z1 [Hs1 Hz1]].
        apply in_map_iff in Hin2.
        destruct Hin2 as [z2 [Hs2 Hz2]].
        rewrite <- Hs1 in Hs2.
        inversion Hs2; subst.
        exact (Hneq eq_refl).
    + intros x1 x2 s Hx1 Hx2 Hneq Hin1 Hin2.
      apply in_flat_map in Hin1.
      destruct Hin1 as [y1 [Hy1 Hin1]].
      apply in_map_iff in Hin1.
      destruct Hin1 as [z1 [Hs1 Hz1]].
      apply in_flat_map in Hin2.
      destruct Hin2 as [y2 [Hy2 Hin2]].
      apply in_map_iff in Hin2.
      destruct Hin2 as [z2 [Hs2 Hz2]].
      rewrite <- Hs1 in Hs2.
      inversion Hs2; subst.
      exact (Hneq eq_refl).
  - intros t1 t2 s Ht1 Ht2 Hneq Hin1 Hin2.
    apply in_flat_map in Hin1.
    destruct Hin1 as [x1 [Hx1 Hin1]].
    apply in_flat_map in Hin1.
    destruct Hin1 as [y1 [Hy1 Hin1]].
    apply in_map_iff in Hin1.
    destruct Hin1 as [z1 [Hs1 Hz1]].
    apply in_flat_map in Hin2.
    destruct Hin2 as [x2 [Hx2 Hin2]].
    apply in_flat_map in Hin2.
    destruct Hin2 as [y2 [Hy2 Hin2]].
    apply in_map_iff in Hin2.
    destruct Hin2 as [z2 [Hs2 Hz2]].
    rewrite <- Hs1 in Hs2.
    inversion Hs2; subst.
    exact (Hneq eq_refl).
Qed.

Lemma all_plaquettes_nodup : forall L, NoDup (all_plaquettes L).
Proof.
  intro L.
  unfold all_plaquettes.
  eapply NoDup_flat_map_disjoint with
    (f := fun s => map (fun '(mu, nu) => mk_plaq s mu nu) direction_pairs).
  - apply all_sites_nodup.
  - intros s Hs.
    apply NoDup_map_injective.
    + intros [mu1 nu1] [mu2 nu2] Heq.
      inversion Heq.
      reflexivity.
    + apply direction_pairs_nodup.
  - intros s1 s2 p Hs1 Hs2 Hneq Hin1 Hin2.
    apply in_map_iff in Hin1.
    destruct Hin1 as [[mu1 nu1] [Hp1 Hpair1]].
    apply in_map_iff in Hin2.
    destruct Hin2 as [[mu2 nu2] [Hp2 Hpair2]].
    rewrite <- Hp1 in Hp2.
    inversion Hp2; subst.
    exact (Hneq eq_refl).
Qed.

(* Recover direction pair from plaquette membership *)
Lemma In_all_plaquettes_dir : forall L p,
  In p (all_plaquettes L) ->
  In (plaq_mu p, plaq_nu p) direction_pairs.
Proof.
  intros L [[t x y z] mu nu] Hin.
  unfold all_plaquettes in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [s [Hs Hin]].
  apply in_map_iff in Hin.
  destruct Hin as [[mu' nu'] [Heq Hdir]].
  inversion Heq; subst.
  exact Hdir.
Qed.

End Lattice.
