(* =========================================================================
   ym/lattice_4d_coordination.v

   Zero-axiom proof of exact 4D hypercubic lattice plaquette edge-sharing
   coordination (= 21 distinct canonical neighbors, <= 24 bound) across all
   of Z^4, eliminating the legacy `Axiom plaq_wellformed`.

   Depends ONLY on Coq Standard Library and `ym.lattice` (0 Admitted, 0 Axiom).
   ========================================================================= *)

From Coq Require Import Reals Lra Lia ZArith Bool List.
Require Import ym.lattice.

Import ListNotations.
Import Lattice.

Open Scope Z_scope.

Module Lattice4DCoord.

  (* =======================================================================
     1. Well-formedness, Equality, Edges, and Overlap on ym.lattice
     ======================================================================= *)

  Definition wf_plaq (p : plaquette) : Prop :=
    In (plaq_mu p, plaq_nu p) direction_pairs.

  Definition plaq_eq_dec : forall (p1 p2 : plaquette), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros [s1 mu1 nu1] [s2 mu2 nu2].
    destruct (site_eq_dec s1 s2); destruct (direction_eq_dec mu1 mu2);
    destruct (direction_eq_dec nu1 nu2);
    try (left; congruence); right; congruence.
  Defined.

  Definition plaq_raw_edges (p : plaquette) : list (site * site) :=
    let v0 := plaq_site p in
    let v1 := shift_site v0 (plaq_mu p) in
    let v2 := shift_site v0 (plaq_nu p) in
    let v3 := shift_site v1 (plaq_nu p) in
    [(v0, v1); (v0, v2); (v1, v3); (v2, v3)].

  Definition same_undirected_edge (e1 e2 : site * site) : Prop :=
    (fst e1 = fst e2 /\ snd e1 = snd e2) \/
    (fst e1 = snd e2 /\ snd e1 = fst e2).

  Definition site_eqb (s1 s2 : site) : bool :=
    if site_eq_dec s1 s2 then true else false.

  Lemma site_eqb_true_iff : forall s1 s2, site_eqb s1 s2 = true <-> s1 = s2.
  Proof.
    intros s1 s2. unfold site_eqb.
    destruct (site_eq_dec s1 s2); split; intro H; try assumption; try reflexivity; discriminate || contradiction.
  Qed.

  Definition same_undirected_edge_bool (e1 e2 : site * site) : bool :=
    (site_eqb (fst e1) (fst e2) && site_eqb (snd e1) (snd e2)) ||
    (site_eqb (fst e1) (snd e2) && site_eqb (snd e1) (fst e2)).

  Lemma same_undirected_edge_bool_spec : forall e1 e2,
    same_undirected_edge_bool e1 e2 = true <-> same_undirected_edge e1 e2.
  Proof.
    intros e1 e2.
    unfold same_undirected_edge_bool, same_undirected_edge.
    rewrite orb_true_iff, !andb_true_iff, !site_eqb_true_iff.
    tauto.
  Qed.

  Definition plaq_shares_edge (p1 p2 : plaquette) : Prop :=
    p1 <> p2 /\
    exists e1 e2,
      In e1 (plaq_raw_edges p1) /\
      In e2 (plaq_raw_edges p2) /\
      same_undirected_edge e1 e2.

  Definition plaq_shares_edge_bool (p1 p2 : plaquette) : bool :=
    negb (if plaq_eq_dec p1 p2 then true else false) &&
    existsb (fun e1 => existsb (fun e2 => same_undirected_edge_bool e1 e2)
                               (plaq_raw_edges p2))
            (plaq_raw_edges p1).

  Lemma plaq_shares_edge_bool_spec : forall p1 p2,
    plaq_shares_edge_bool p1 p2 = true <-> plaq_shares_edge p1 p2.
  Proof.
    intros p1 p2. unfold plaq_shares_edge_bool, plaq_shares_edge.
    rewrite andb_true_iff, negb_true_iff, existsb_exists.
    split.
    - intros [Hne [e1 [He1 Hex2]]].
      rewrite existsb_exists in Hex2.
      destruct Hex2 as [e2 [He2 Hsame]].
      apply same_undirected_edge_bool_spec in Hsame.
      split.
      + destruct (plaq_eq_dec p1 p2); [discriminate | exact n].
      + exists e1, e2. repeat split; assumption.
    - intros [Hne [e1 [e2 [He1 [He2 Hsame]]]]].
      split.
      + destruct (plaq_eq_dec p1 p2); [contradiction | reflexivity].
      + exists e1. split; [exact He1 |].
        rewrite existsb_exists. exists e2. split; [exact He2 |].
        apply same_undirected_edge_bool_spec. exact Hsame.
  Qed.

  Definition plaq_overlap (p1 p2 : plaquette) : Prop :=
    p1 = p2 \/ plaq_shares_edge p1 p2.

  Definition plaq_overlap_bool (p1 p2 : plaquette) : bool :=
    (if plaq_eq_dec p1 p2 then true else false) || plaq_shares_edge_bool p1 p2.

  Lemma plaq_overlap_bool_spec : forall p1 p2,
    plaq_overlap_bool p1 p2 = true <-> plaq_overlap p1 p2.
  Proof.
    intros p1 p2. unfold plaq_overlap_bool, plaq_overlap.
    rewrite orb_true_iff, plaq_shares_edge_bool_spec.
    destruct (plaq_eq_dec p1 p2); split; intros H;
      try (left; assumption);
      try (right; assumption);
      destruct H as [H | H]; try (left; reflexivity); try (right; exact H);
      try discriminate; try contradiction.
  Qed.

  (* =======================================================================
     2. Coordinate-Sum Proof of Anchor Manhattan Bound <= 2 (ZERO axioms!)
     ======================================================================= *)

  Definition site_manhattan (s1 s2 : site) : Z :=
    Z.abs (site_t s1 - site_t s2) +
    Z.abs (site_x s1 - site_x s2) +
    Z.abs (site_y s1 - site_y s2) +
    Z.abs (site_z s1 - site_z s2).

  Definition site_coord_sum (s : site) : Z :=
    site_t s + site_x s + site_y s + site_z s.

  Lemma shift_site_coord_sum : forall s d,
    site_coord_sum (shift_site s d) = site_coord_sum s + 1.
  Proof.
    intros [t x y z] []; unfold site_coord_sum, shift_site; simpl; lia.
  Qed.

  Lemma shift_site_manhattan_1 : forall s d,
    site_manhattan s (shift_site s d) = 1.
  Proof.
    intros [t x y z] []; unfold site_manhattan, shift_site; simpl; lia.
  Qed.

  Lemma site_manhattan_refl : forall s, site_manhattan s s = 0.
  Proof.
    intros [t x y z]. unfold site_manhattan; simpl; lia.
  Qed.

  Lemma site_manhattan_sym : forall s1 s2, site_manhattan s1 s2 = site_manhattan s2 s1.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2]. unfold site_manhattan; simpl; lia.
  Qed.

  Lemma site_manhattan_triangle : forall s1 s2 s3,
    site_manhattan s1 s3 <= site_manhattan s1 s2 + site_manhattan s2 s3.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2] [t3 x3 y3 z3].
    unfold site_manhattan; simpl; lia.
  Qed.

  (* Every raw edge (a, b) of p satisfies coord_sum(b) = coord_sum(a) + 1
     and manhattan(anchor(p), a) <= 1. *)
  Lemma plaq_raw_edge_props : forall p e,
    In e (plaq_raw_edges p) ->
    site_coord_sum (snd e) = site_coord_sum (fst e) + 1 /\
    site_manhattan (plaq_site p) (fst e) <= 1.
  Proof.
    intros p e He.
    unfold plaq_raw_edges in He. simpl in He.
    destruct He as [He | [He | [He | [He | []]]]]; subst e; simpl.
    - split; [apply shift_site_coord_sum | rewrite site_manhattan_refl; lia].
    - split; [apply shift_site_coord_sum | rewrite site_manhattan_refl; lia].
    - split; [apply shift_site_coord_sum | rewrite shift_site_manhattan_1; lia].
    - split.
      + rewrite !shift_site_coord_sum. lia.
      + rewrite shift_site_manhattan_1. lia.
  Qed.

  Lemma shares_edge_anchor_manhattan : forall p1 p2,
    plaq_shares_edge p1 p2 ->
    site_manhattan (plaq_site p1) (plaq_site p2) <= 2.
  Proof.
    intros p1 p2 [_ [e1 [e2 [He1 [He2 Hsame]]]]].
    destruct (plaq_raw_edge_props p1 e1 He1) as [Hsum1 Hdist1].
    destruct (plaq_raw_edge_props p2 e2 He2) as [Hsum2 Hdist2].
    destruct Hsame as [[Hfst Hsnd] | [Hfst Hsnd]].
    - pose proof (site_manhattan_triangle (plaq_site p1) (fst e1) (plaq_site p2)) as Htri.
      rewrite Hfst in Htri, Hdist1.
      rewrite (site_manhattan_sym (fst e2) (plaq_site p2)) in Htri.
      lia.
    - (* Swapped case is impossible since both edges increase coord_sum by +1. *)
      exfalso.
      rewrite Hfst in Hsum1. rewrite Hsnd in Hsum1. lia.
  Qed.

  Lemma overlap_anchor_manhattan : forall p1 p2,
    plaq_overlap p1 p2 ->
    site_manhattan (plaq_site p1) (plaq_site p2) <= 2.
  Proof.
    intros p1 p2 [Heq | Hsh].
    - subst. rewrite site_manhattan_refl. lia.
    - exact (shares_edge_anchor_manhattan p1 p2 Hsh).
  Qed.

  (* =======================================================================
     3. Constructive L1-Ball Radius-2 Offset Enumeration & Translation
     ======================================================================= *)

  Fixpoint z_range_sym (n : nat) : list Z :=
    match n with
    | O => [0]
    | S n' => (- Z.of_nat n) :: z_range_sym n' ++ [Z.of_nat n]
    end.

  Definition all_offsets_cube (r : nat) : list (Z * Z * Z * Z) :=
    let rg := z_range_sym r in
    flat_map (fun t =>
      flat_map (fun x =>
        flat_map (fun y =>
          map (fun z => (t, x, y, z)) rg
        ) rg
      ) rg
    ) rg.

  Definition z4_manhattan (d : Z * Z * Z * Z) : Z :=
    let '(t, x, y, z) := d in Z.abs t + Z.abs x + Z.abs y + Z.abs z.

  Definition offsets_R2 : list (Z * Z * Z * Z) :=
    filter (fun d => Z.leb (z4_manhattan d) 2) (all_offsets_cube 2).

  Definition apply_offset (s : site) (d : Z * Z * Z * Z) : site :=
    let '(dt, dx, dy, dz) := d in
    mk_site (site_t s + dt) (site_x s + dx) (site_y s + dy) (site_z s + dz).

  Lemma z_range_sym_complete : forall n x,
    Z.abs x <= Z.of_nat n -> In x (z_range_sym n).
  Proof.
    induction n as [| n' IH]; intros x H; simpl.
    - left. simpl in H. lia.
    - destruct (Z.eq_dec x (- Z.of_nat (S n'))) as [Heq | Hne1].
      + left. symmetry. exact Heq.
      + right. apply in_app_iff.
        destruct (Z.eq_dec x (Z.of_nat (S n'))) as [Heq' | Hne2].
        * right. left. symmetry. exact Heq'.
        * left. apply IH. rewrite Nat2Z.inj_succ in H. lia.
  Qed.

  Lemma offsets_R2_complete : forall dt dx dy dz,
    Z.abs dt + Z.abs dx + Z.abs dy + Z.abs dz <= 2 ->
    In (dt, dx, dy, dz) offsets_R2.
  Proof.
    intros dt dx dy dz H.
    unfold offsets_R2. apply filter_In. split.
    - unfold all_offsets_cube.
      apply in_flat_map. exists dt. split; [apply z_range_sym_complete; lia |].
      apply in_flat_map. exists dx. split; [apply z_range_sym_complete; lia |].
      apply in_flat_map. exists dy. split; [apply z_range_sym_complete; lia |].
      apply in_map. apply z_range_sym_complete. lia.
    - unfold z4_manhattan. apply Z.leb_le. exact H.
  Qed.

  Definition neighbor_candidates (p : plaquette) : list plaquette :=
    let anchor := plaq_site p in
    flat_map (fun delta =>
      map (fun '(mu, nu) => mk_plaq (apply_offset anchor delta) mu nu)
          direction_pairs
    ) offsets_R2.

  Definition plaq_neighbors (p : plaquette) : list plaquette :=
    filter (plaq_overlap_bool p) (neighbor_candidates p).

  (* =======================================================================
     4. Soundness, Well-Formedness Preservation, and Completeness
     ======================================================================= *)

  Lemma plaq_neighbors_sound : forall p q,
    In q (plaq_neighbors p) -> plaq_overlap p q.
  Proof.
    intros p q Hin.
    unfold plaq_neighbors in Hin.
    apply filter_In in Hin. destruct Hin as [_ Hb].
    apply plaq_overlap_bool_spec. exact Hb.
  Qed.

  Lemma plaq_neighbors_wf : forall p q,
    In q (plaq_neighbors p) -> wf_plaq q.
  Proof.
    intros p q Hin.
    unfold plaq_neighbors, neighbor_candidates in Hin.
    apply filter_In in Hin. destruct Hin as [Hcand _].
    apply in_flat_map in Hcand. destruct Hcand as [delta [_ Hmap]].
    apply in_map_iff in Hmap. destruct Hmap as [[mu nu] [Heq Hdp]].
    subst q. exact Hdp.
  Qed.

  Lemma neighbor_candidates_complete_wf : forall p q,
    wf_plaq q ->
    site_manhattan (plaq_site p) (plaq_site q) <= 2 ->
    In q (neighbor_candidates p).
  Proof.
    intros p q Hwfq Hdist.
    unfold neighbor_candidates.
    set (sp := plaq_site p).
    set (sq := plaq_site q).
    set (delta := (site_t sq - site_t sp,
                   site_x sq - site_x sp,
                   site_y sq - site_y sp,
                   site_z sq - site_z sp)).
    apply in_flat_map. exists delta. split.
    - apply offsets_R2_complete.
      unfold delta, site_manhattan, sp, sq in *. lia.
    - apply in_map_iff. exists (plaq_mu q, plaq_nu q). split.
      + destruct q as [[tq xq yq zq] muq nuq].
        unfold apply_offset, delta, sp, sq in *. simpl in *.
        f_equal. f_equal; lia.
      + exact Hwfq.
  Qed.

  Lemma plaq_neighbors_complete_wf : forall p q,
    wf_plaq q ->
    plaq_overlap p q ->
    In q (plaq_neighbors p).
  Proof.
    intros p q Hwfq Hov.
    unfold plaq_neighbors. apply filter_In. split.
    - apply neighbor_candidates_complete_wf; [exact Hwfq | apply overlap_anchor_manhattan; exact Hov].
    - apply plaq_overlap_bool_spec. exact Hov.
  Qed.

  Lemma plaq_neighbors_spec_wf : forall p q,
    wf_plaq q ->
    (In q (plaq_neighbors p) <-> plaq_overlap p q).
  Proof.
    intros p q Hwfq. split.
    - apply plaq_neighbors_sound.
    - apply plaq_neighbors_complete_wf; exact Hwfq.
  Qed.

  (* =======================================================================
     5. Duplicate-Free Proof (NoDup) via Decidable Reflection on offsets_R2
     ======================================================================= *)

  Definition offset_eq_dec : forall (a b : Z * Z * Z * Z), {a = b} + {a <> b}.
  Proof.
    intros [[[t1 x1] y1] z1] [[[t2 x2] y2] z2].
    destruct (Z.eq_dec t1 t2); destruct (Z.eq_dec x1 x2);
    destruct (Z.eq_dec y1 y2); destruct (Z.eq_dec z1 z2);
    try (left; congruence); right; congruence.
  Defined.

  Fixpoint mem_bool {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A) (l : list A) : bool :=
    match l with
    | [] => false
    | h :: t => if eq_dec x h then true else mem_bool eq_dec x t
    end.

  Lemma mem_bool_false_iff {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
    forall x l, mem_bool eq_dec x l = false -> ~ In x l.
  Proof.
    intros x l. induction l as [| h t IH]; simpl; intros H Hin.
    - exact Hin.
    - destruct (eq_dec x h) as [Heq | Hne]; [discriminate |].
      destruct Hin as [Heq | Ht]; [exact (Hne (eq_sym Heq)) | exact (IH H Ht)].
  Qed.

  Fixpoint nodup_bool {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => negb (mem_bool eq_dec h t) && nodup_bool eq_dec t
    end.

  Lemma nodup_bool_NoDup {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
    forall l, nodup_bool eq_dec l = true -> NoDup l.
  Proof.
    induction l as [| h t IH]; simpl; intros H.
    - constructor.
    - apply andb_true_iff in H. destruct H as [Hm Hnd].
      apply negb_true_iff in Hm.
      constructor.
      + apply (mem_bool_false_iff eq_dec). exact Hm.
      + apply IH. exact Hnd.
  Qed.

  Lemma offsets_R2_NoDup : NoDup offsets_R2.
  Proof.
    apply (nodup_bool_NoDup offset_eq_dec).
    vm_compute. reflexivity.
  Qed.

  Lemma apply_offset_inj : forall s d1 d2,
    apply_offset s d1 = apply_offset s d2 -> d1 = d2.
  Proof.
    intros [ts xs ys zs] [[[t1 x1] y1] z1] [[[t2 x2] y2] z2] H.
    unfold apply_offset in H. simpl in H.
    inversion H. repeat f_equal; lia.
  Qed.

  Lemma NoDup_app_disjoint {A : Type} : forall (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [| h t IH]; simpl; intros l2 H1 H2 Hdisj.
    - exact H2.
    - inversion H1; subst.
      constructor.
      + intro Hin. apply in_app_iff in Hin. destruct Hin as [Ht | Hl2].
        * exact (H3 Ht).
        * exact (Hdisj h (or_introl eq_refl) Hl2).
      + apply IH; try assumption.
        intros x Hx. apply Hdisj. right. exact Hx.
  Qed.

  Lemma NoDup_map_inj {A B : Type} (f : A -> B) :
    (forall x y, f x = f y -> x = y) ->
    forall l, NoDup l -> NoDup (map f l).
  Proof.
    intros Hinj l Hnd. induction Hnd as [| h t Hnot Hnd IH]; simpl; constructor.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq Hx]].
      apply Hinj in Heq. subst. exact (Hnot Hx).
    - exact IH.
  Qed.

  Lemma NoDup_neighbor_candidates : forall p, NoDup (neighbor_candidates p).
  Proof.
    intro p. unfold neighbor_candidates.
    set (anchor := plaq_site p).
    assert (Hgen : forall L, NoDup L ->
      NoDup (flat_map (fun delta =>
        map (fun '(mu, nu) => mk_plaq (apply_offset anchor delta) mu nu) direction_pairs) L)).
    { induction L as [| d ds IH]; intros Hnd.
      - constructor.
      - cbn [flat_map]. inversion Hnd; subst.
        apply NoDup_app_disjoint.
        + apply NoDup_map_inj.
          * intros [m1 n1] [m2 n2] Heq. inversion Heq. reflexivity.
          * exact direction_pairs_nodup.
        + apply IH. exact H2.
        + intros q Hq1 Hq2.
          apply in_map_iff in Hq1. destruct Hq1 as [[m1 n1] [Heq1 _]].
          apply in_flat_map in Hq2. destruct Hq2 as [d' [Hd' Hq2]].
          apply in_map_iff in Hq2. destruct Hq2 as [[m2 n2] [Heq2 _]].
          rewrite <- Heq1 in Heq2. inversion Heq2 as [Hs].
          apply apply_offset_inj in Hs. subst d'. exact (H1 Hd'). }
    apply Hgen. exact offsets_R2_NoDup.
  Qed.

  Lemma plaq_neighbors_NoDup : forall p, NoDup (plaq_neighbors p).
  Proof.
    intro p. unfold plaq_neighbors.
    apply NoDup_filter. apply NoDup_neighbor_candidates.
  Qed.

  (* =======================================================================
     6. Translation Equivariance & Exact Cardinality = 21 (<= 24)
     ======================================================================= *)

  Definition site_add (s t : site) : site :=
    mk_site (site_t s + site_t t) (site_x s + site_x t)
            (site_y s + site_y t) (site_z s + site_z t).

  Definition site_opp (s : site) : site :=
    mk_site (- site_t s) (- site_x s) (- site_y s) (- site_z s).

  Definition translate_plaq (p : plaquette) (t : site) : plaquette :=
    mk_plaq (site_add (plaq_site p) t) (plaq_mu p) (plaq_nu p).

  Lemma site_add_inj_r : forall s1 s2 t,
    site_add s1 t = site_add s2 t -> s1 = s2.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2] [tt tx ty tz] H.
    unfold site_add in H; simpl in H; inversion H; f_equal; lia.
  Qed.

  Lemma shift_site_translate : forall s d t,
    shift_site (site_add s t) d = site_add (shift_site s d) t.
  Proof.
    intros [st sx sy sz] [] [tt tx ty tz];
    unfold shift_site, site_add; simpl; f_equal; lia.
  Qed.

  Lemma apply_offset_translate : forall s d t,
    apply_offset (site_add s t) d = site_add (apply_offset s d) t.
  Proof.
    intros [st sx sy sz] [[[dt dx] dy] dz] [tt tx ty tz].
    unfold apply_offset, site_add; simpl; f_equal; lia.
  Qed.

  Lemma plaq_raw_edges_translate : forall p t,
    plaq_raw_edges (translate_plaq p t) =
    map (fun e => (site_add (fst e) t, site_add (snd e) t)) (plaq_raw_edges p).
  Proof.
    intros p t. unfold plaq_raw_edges, translate_plaq. simpl.
    rewrite !shift_site_translate. reflexivity.
  Qed.

  Lemma same_undirected_edge_translate : forall e1 e2 t,
    same_undirected_edge (site_add (fst e1) t, site_add (snd e1) t)
                         (site_add (fst e2) t, site_add (snd e2) t) <->
    same_undirected_edge e1 e2.
  Proof.
    intros [a1 b1] [a2 b2] t. unfold same_undirected_edge; simpl.
    split; intros [[H1 H2] | [H1 H2]].
    - left; split; apply (site_add_inj_r _ _ t); assumption.
    - right; split; apply (site_add_inj_r _ _ t); assumption.
    - left; subst; auto.
    - right; subst; auto.
  Qed.

  Lemma translate_plaq_inj : forall p1 p2 t,
    translate_plaq p1 t = translate_plaq p2 t -> p1 = p2.
  Proof.
    intros [[t1 x1 y1 z1] m1 n1] [[t2 x2 y2 z2] m2 n2] [tt tx ty tz] H.
    unfold translate_plaq, site_add in H; simpl in H.
    inversion H; subst. f_equal. f_equal; lia.
  Qed.

  Lemma plaq_shares_edge_translate : forall p1 p2 t,
    plaq_shares_edge (translate_plaq p1 t) (translate_plaq p2 t) <->
    plaq_shares_edge p1 p2.
  Proof.
    intros p1 p2 t. unfold plaq_shares_edge.
    rewrite !plaq_raw_edges_translate.
    split.
    - intros [Hne [e1' [e2' [He1' [He2' Hsame]]]]].
      apply in_map_iff in He1'. destruct He1' as [e1 [Heq1 He1]].
      apply in_map_iff in He2'. destruct He2' as [e2 [Heq2 He2]].
      subst e1' e2'. apply same_undirected_edge_translate in Hsame.
      split.
      + intro Heq. apply Hne. subst. reflexivity.
      + exists e1, e2. repeat split; assumption.
    - intros [Hne [e1 [e2 [He1 [He2 Hsame]]]]].
      split.
      + intro Heq. apply Hne. exact (translate_plaq_inj p1 p2 t Heq).
      + exists (site_add (fst e1) t, site_add (snd e1) t),
               (site_add (fst e2) t, site_add (snd e2) t).
        repeat split.
        * apply (in_map (fun e => (site_add (fst e) t, site_add (snd e) t))). exact He1.
        * apply (in_map (fun e => (site_add (fst e) t, site_add (snd e) t))). exact He2.
        * apply same_undirected_edge_translate. exact Hsame.
  Qed.

  Lemma plaq_overlap_translate : forall p1 p2 t,
    plaq_overlap (translate_plaq p1 t) (translate_plaq p2 t) <->
    plaq_overlap p1 p2.
  Proof.
    intros p1 p2 t. unfold plaq_overlap.
    rewrite plaq_shares_edge_translate.
    split; intros [H | H].
    - left. exact (translate_plaq_inj p1 p2 t H).
    - right. exact H.
    - left. subst. reflexivity.
    - right. exact H.
  Qed.

  Lemma plaq_overlap_bool_translate : forall p1 p2 t,
    plaq_overlap_bool (translate_plaq p1 t) (translate_plaq p2 t) =
    plaq_overlap_bool p1 p2.
  Proof.
    intros p1 p2 t.
    destruct (plaq_overlap_bool p1 p2) eqn:E1;
    destruct (plaq_overlap_bool (translate_plaq p1 t) (translate_plaq p2 t)) eqn:E2;
    try reflexivity.
    - apply plaq_overlap_bool_spec in E1.
      apply (proj2 (plaq_overlap_translate p1 p2 t)) in E1.
      apply plaq_overlap_bool_spec in E1. rewrite E1 in E2. discriminate.
    - apply plaq_overlap_bool_spec in E2.
      apply (proj1 (plaq_overlap_translate p1 p2 t)) in E2.
      apply plaq_overlap_bool_spec in E2. rewrite E2 in E1. discriminate.
  Qed.

  Lemma neighbor_candidates_translate : forall p t,
    neighbor_candidates (translate_plaq p t) =
    map (fun q => translate_plaq q t) (neighbor_candidates p).
  Proof.
    intros p t. unfold neighbor_candidates.
    change (plaq_site (translate_plaq p t)) with (site_add (plaq_site p) t).
    generalize offsets_R2 as L. intro L.
    induction L as [| d ds IH]; [reflexivity |].
    cbn [flat_map]. rewrite map_app, IH. f_equal.
    rewrite map_map. apply map_ext.
    intros [mu nu]. unfold translate_plaq; simpl.
    rewrite apply_offset_translate. reflexivity.
  Qed.

  Lemma map_filter_comm {A B : Type} (f : A -> B) (p : A -> bool) (q : B -> bool) :
    forall l, (forall x, In x l -> q (f x) = p x) ->
    map f (filter p l) = filter q (map f l).
  Proof.
    induction l as [| h t IH]; simpl; intros Hpq; [reflexivity |].
    rewrite (Hpq h (or_introl eq_refl)).
    destruct (p h).
    - simpl. f_equal. apply IH. intros x Hx. apply Hpq. right. exact Hx.
    - apply IH. intros x Hx. apply Hpq. right. exact Hx.
  Qed.

  Lemma plaq_neighbors_translate : forall p t,
    plaq_neighbors (translate_plaq p t) =
    map (fun q => translate_plaq q t) (plaq_neighbors p).
  Proof.
    intros p t. unfold plaq_neighbors.
    rewrite neighbor_candidates_translate.
    symmetry. apply map_filter_comm.
    intros q _. apply plaq_overlap_bool_translate.
  Qed.

  Lemma plaq_neighbors_length_origin : forall s mu nu,
    length (plaq_neighbors (mk_plaq s mu nu)) =
    length (plaq_neighbors (mk_plaq (mk_site 0 0 0 0) mu nu)).
  Proof.
    intros s mu nu.
    assert (Heq : mk_plaq (mk_site 0 0 0 0) mu nu =
                  translate_plaq (mk_plaq s mu nu) (site_opp s)).
    { destruct s as [st sx sy sz].
      unfold translate_plaq, site_add, site_opp; simpl; f_equal; f_equal; lia. }
    rewrite Heq, plaq_neighbors_translate, map_length. reflexivity.
  Qed.

  (* Exact 4D coordination count: 1 self + 4 edges * 5 other plaquettes = 21. *)
  Theorem plaq_neighbors_exact_21 : forall p,
    wf_plaq p ->
    length (plaq_neighbors p) = 21%nat.
  Proof.
    intros [s mu nu] Hwf.
    unfold wf_plaq, direction_pairs in Hwf. simpl in Hwf.
    rewrite plaq_neighbors_length_origin.
    destruct Hwf as [H | [H | [H | [H | [H | [H | []]]]]]];
    inversion H; subst; vm_compute; reflexivity.
  Qed.

  Theorem plaq_coordination_bound_24 : forall p,
    wf_plaq p ->
    (INR (length (plaq_neighbors p)) <= 24)%R.
  Proof.
    intros p Hwf.
    rewrite (plaq_neighbors_exact_21 p Hwf).
    assert (H21 : INR 21 = 21%R) by (unfold INR; simpl; ring).
    rewrite H21. lra.
  Qed.

End Lattice4DCoord.
