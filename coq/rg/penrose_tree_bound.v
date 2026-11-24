(* =========================================================================
   penrose_tree_bound.v

   Self-contained, zero-project-axiom formalization of the genuine Ursell
   function (Mayer cluster coefficient) and Penrose's 1967 Tree-Graph
   Inequality via the BFS partition scheme:

     |phi^T(gamma_1, ..., gamma_n)| <= #{spanning trees of G(gamma_1, ..., gamma_n)}

   Depends ONLY on Coq standard library (Reals, Arith, Bool, List, Lia, Lra).
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
Import ListNotations.
Open Scope R_scope.

Module PenroseTreeBound.

  (* =======================================================================
     1. Core Graph, Sublist, Connectedness, and Ursell Definitions
     ======================================================================= *)

  Definition edge_eqb (e1 e2 : nat * nat) : bool :=
    Nat.eqb (fst e1) (fst e2) && Nat.eqb (snd e1) (snd e2).

  Lemma edge_eqb_spec : forall e1 e2, edge_eqb e1 e2 = true <-> e1 = e2.
  Proof.
    intros [a1 b1] [a2 b2]. unfold edge_eqb; simpl.
    rewrite andb_true_iff, !Nat.eqb_eq. split.
    - intros [-> ->]. reflexivity.
    - intro H. inversion H. split; reflexivity.
  Qed.

  Lemma edge_eq_dec : forall e1 e2 : nat * nat, {e1 = e2} + {e1 <> e2}.
  Proof.
    intros [a1 b1] [a2 b2].
    destruct (Nat.eq_dec a1 a2); destruct (Nat.eq_dec b1 b2);
      try (left; congruence); right; congruence.
  Qed.

  Definition edge_mem (e : nat * nat) (H : list (nat * nat)) : bool :=
    existsb (edge_eqb e) H.

  Lemma edge_mem_iff : forall e H, edge_mem e H = true <-> In e H.
  Proof.
    intros e H. unfold edge_mem. rewrite existsb_exists. split.
    - intros [x [Hin Heq]]. apply edge_eqb_spec in Heq. subst. exact Hin.
    - intro Hin. exists e. split; [exact Hin | apply edge_eqb_spec; reflexivity].
  Qed.

  Definition mk_edge (u v : nat) : nat * nat :=
    if Nat.ltb u v then (u, v) else (v, u).

  Definition has_edge (H : list (nat * nat)) (u v : nat) : Prop :=
    In (u, v) H \/ In (v, u) H.

  Definition has_edgeb (H : list (nat * nat)) (u v : nat) : bool :=
    edge_mem (u, v) H || edge_mem (v, u) H.

  Lemma has_edgeb_iff : forall H u v, has_edgeb H u v = true <-> has_edge H u v.
  Proof.
    intros H u v. unfold has_edgeb, has_edge.
    rewrite orb_true_iff, !edge_mem_iff. tauto.
  Qed.

  Lemma has_edge_sym : forall H u v, has_edge H u v -> has_edge H v u.
  Proof. intros H u v [H1 | H2]; [right | left]; assumption. Qed.

  Definition wf_edges (n : nat) (E : list (nat * nat)) : Prop :=
    NoDup E /\ Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) E.

  Lemma wf_has_edge_mk : forall n H u v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    has_edge H u v <-> In (mk_edge u v) H.
  Proof.
    intros n H u v Hwf. unfold has_edge, mk_edge.
    destruct (Nat.ltb_spec u v).
    - split; [intros [Hin | Hin]; [exact Hin |] | intro Hin; left; exact Hin].
      rewrite Forall_forall in Hwf. specialize (Hwf (v, u) Hin). simpl in Hwf. lia.
    - split; [intros [Hin | Hin]; [| exact Hin] | intro Hin; right; exact Hin].
      rewrite Forall_forall in Hwf. specialize (Hwf (u, v) Hin). simpl in Hwf. lia.
  Qed.

  Lemma wf_has_edge_lt : forall n H u v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    has_edge H u v -> (u < n)%nat /\ (v < n)%nat /\ u <> v.
  Proof.
    intros n H u v Hwf [Hin | Hin];
      rewrite Forall_forall in Hwf; specialize (Hwf _ Hin); simpl in Hwf; lia.
  Qed.

  (* All sublists (subsets in original order) of a list *)
  Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
    match l with
    | [] => [[]]
    | x :: xs =>
        let subs := sublists xs in
        subs ++ map (cons x) subs
    end.

  (* BFS expansion on vertices {0, ..., n-1} *)
  Definition expand_once (H : list (nat * nat)) (S : list nat) : list nat :=
    S ++ flat_map (fun e =>
      (if existsb (Nat.eqb (fst e)) S then [snd e] else []) ++
      (if existsb (Nat.eqb (snd e)) S then [fst e] else [])) H.

  Fixpoint expand_iter (k : nat) (H : list (nat * nat)) (S : list nat) : list nat :=
    match k with
    | 0%nat => S
    | S k' => expand_iter k' H (expand_once H S)
    end.

  Definition is_connectedb (n : nat) (H : list (nat * nat)) : bool :=
    match n with
    | 0%nat => false
    | S _ => forallb (fun v => existsb (Nat.eqb v) (expand_iter n H [0%nat])) (seq 0 n)
    end.

  (* Incompatibility graph edges for an ordered tuple X : list P *)
  Fixpoint pairs_with_head {P : Type} (overlap_b : P -> P -> bool)
    (i : nat) (x : P) (j : nat) (xs : list P) : list (nat * nat) :=
    match xs with
    | [] => []
    | y :: ys =>
        if overlap_b x y
        then (i, j) :: pairs_with_head overlap_b i x (S j) ys
        else pairs_with_head overlap_b i x (S j) ys
    end.

  Fixpoint graph_edges_from {P : Type} (overlap_b : P -> P -> bool)
    (i : nat) (X : list P) : list (nat * nat) :=
    match X with
    | [] => []
    | x :: xs =>
        pairs_with_head overlap_b i x (S i) xs ++ graph_edges_from overlap_b (S i) xs
    end.

  Definition graph_edges {P : Type} (overlap_b : P -> P -> bool) (X : list P) : list (nat * nat) :=
    graph_edges_from overlap_b 0 X.

  (* Genuine Ursell function phi^T on a graph (n, E) *)
  Definition ursell_graph (n : nat) (E : list (nat * nat)) : R :=
    fold_right Rplus 0
      (map (fun H => if is_connectedb n H then (-1) ^ (length H) else 0) (sublists E)).

  Definition ursell_fn {P : Type} (overlap_b : P -> P -> bool) (X : list P) : R :=
    ursell_graph (length X) (graph_edges overlap_b X).

  (* Spanning trees of (n, E): connected subgraphs with n - 1 edges *)
  Definition is_treeb (n : nat) (H : list (nat * nat)) : bool :=
    is_connectedb n H && Nat.eqb (length H) (n - 1).

  Definition spanning_trees (n : nat) (E : list (nat * nat)) : list (list (nat * nat)) :=
    filter (is_treeb n) (sublists E).

  Definition tree_count {P : Type} (overlap_b : P -> P -> bool) (X : list P) : nat :=
    length (spanning_trees (length X) (graph_edges overlap_b X)).

  (* =======================================================================
     2. Properties of sublists and graph_edges
     ======================================================================= *)

  Lemma sublists_incl : forall {A : Type} (E H : list A),
    In H (sublists E) -> incl H E.
  Proof.
    induction E as [| x xs IH]; intros H Hin.
    - simpl in Hin. destruct Hin as [<- | []]. intros y [].
    - simpl in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + intros y Hy. right. exact (IH H Hin y Hy).
      + apply in_map_iff in Hin. destruct Hin as [H' [<- Hin']].
        intros y [<- | Hy]; [left; reflexivity | right; exact (IH H' Hin' y Hy)].
  Qed.

  Lemma sublists_NoDup_elem : forall {A : Type} (E H : list A),
    NoDup E -> In H (sublists E) -> NoDup H.
  Proof.
    induction E as [| x xs IH]; intros H Hnd Hin.
    - simpl in Hin. destruct Hin as [<- | []]. constructor.
    - inversion Hnd as [| ? ? Hnot Hnd']; subst.
      simpl in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + exact (IH H Hnd' Hin).
      + apply in_map_iff in Hin. destruct Hin as [H' [<- Hin']].
        constructor.
        * intro Hx. apply Hnot. exact (sublists_incl xs H' Hin' x Hx).
        * exact (IH H' Hnd' Hin').
  Qed.

  Lemma NoDup_app_local : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
  Proof.
    induction l1 as [| a xs IH]; intros l2 Hnd1 Hnd2 Hdisj; simpl; [exact Hnd2 |].
    inversion Hnd1 as [| ? ? Hnot Hnd1']; subst.
    constructor.
    - intro Hin. apply in_app_iff in Hin. destruct Hin as [H1 | H2]; [contradiction |].
      exact (Hdisj a (or_introl eq_refl) H2).
    - apply IH; [exact Hnd1' | exact Hnd2 | intros x Hx; apply Hdisj; right; exact Hx].
  Qed.

  Lemma NoDup_map_in : forall {A B : Type} (f : A -> B) (l : list A),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
  Proof.
    induction l as [| a xs IH]; intros Hnd Hinj; simpl.
    - constructor.
    - inversion Hnd as [| ? ? Hnot Hnd']; subst.
      constructor.
      + intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
        assert (a = y) by (apply Hinj; [left; reflexivity | right; exact Hy | symmetry; exact Heq]).
        subst. contradiction.
      + apply IH; [exact Hnd' |].
        intros x y Hx Hy Hxy. apply Hinj; [right; exact Hx | right; exact Hy | exact Hxy].
  Qed.

  Lemma sublists_NoDup_list : forall {A : Type} (E : list A),
    NoDup E -> NoDup (sublists E).
  Proof.
    induction E as [| x xs IH]; intro Hnd.
    - simpl. constructor; [intro H; exact H | constructor].
    - inversion Hnd as [| ? ? Hnot Hnd']; subst.
      simpl. apply NoDup_app_local.
      + exact (IH Hnd').
      + apply NoDup_map_in; [exact (IH Hnd') | intros a b _ _ H; inversion H; reflexivity].
      + intros H Hin1 Hin2.
        apply in_map_iff in Hin2. destruct Hin2 as [H' [Heq Hin']].
        subst H. apply Hnot.
        apply (sublists_incl xs (x :: H') Hin1). left. reflexivity.
  Qed.

  Lemma filter_in_sublists : forall {A : Type} (f : A -> bool) (E : list A),
    In (filter f E) (sublists E).
  Proof.
    induction E as [| x xs IH]; simpl.
    - left. reflexivity.
    - apply in_app_iff. destruct (f x).
      + right. apply in_map. exact IH.
      + left. exact IH.
  Qed.

  Lemma sublists_ext : forall {A : Type} (E H1 H2 : list A),
    NoDup E ->
    In H1 (sublists E) ->
    In H2 (sublists E) ->
    (forall x, In x H1 <-> In x H2) ->
    H1 = H2.
  Proof.
    induction E as [| a xs IH]; intros H1 H2 Hnd Hin1 Hin2 Hiff.
    - simpl in Hin1, Hin2. destruct Hin1 as [<- | []]; destruct Hin2 as [<- | []]; reflexivity.
    - inversion Hnd as [| ? ? Hnot Hnd']; subst.
      simpl in Hin1, Hin2.
      apply in_app_iff in Hin1. apply in_app_iff in Hin2.
      destruct Hin1 as [Hin1 | Hin1]; destruct Hin2 as [Hin2 | Hin2].
      + exact (IH H1 H2 Hnd' Hin1 Hin2 Hiff).
      + apply in_map_iff in Hin2. destruct Hin2 as [H2' [<- Hin2']].
        exfalso. apply Hnot.
        apply (sublists_incl xs H1 Hin1 a). apply Hiff. left; reflexivity.
      + apply in_map_iff in Hin1. destruct Hin1 as [H1' [<- Hin1']].
        exfalso. apply Hnot.
        apply (sublists_incl xs H2 Hin2 a). apply Hiff. left; reflexivity.
      + apply in_map_iff in Hin1. destruct Hin1 as [H1' [<- Hin1']].
        apply in_map_iff in Hin2. destruct Hin2 as [H2' [<- Hin2']].
        f_equal. apply (IH H1' H2' Hnd' Hin1' Hin2').
        intro y. split; intro Hy.
        * assert (Hy1 : In y (a :: H1')) by (right; exact Hy).
          apply Hiff in Hy1. destruct Hy1 as [Heq | Hy2]; [| exact Hy2].
          subst y. exfalso. apply Hnot. exact (sublists_incl xs H1' Hin1' a Hy).
        * assert (Hy2 : In y (a :: H2')) by (right; exact Hy).
          apply Hiff in Hy2. destruct Hy2 as [Heq | Hy1]; [| exact Hy1].
          subst y. exfalso. apply Hnot. exact (sublists_incl xs H2' Hin2' a Hy).
  Qed.

  Lemma sublists_Forall : forall {A : Type} (Q : A -> Prop) (E H : list A),
    Forall Q E -> In H (sublists E) -> Forall Q H.
  Proof.
    intros A Q E H Hall Hin.
    rewrite Forall_forall in *. intros x Hx.
    apply Hall. exact (sublists_incl E H Hin x Hx).
  Qed.

  Lemma pairs_with_head_in : forall {P : Type} (ob : P -> P -> bool) i x j xs u v,
    In (u, v) (pairs_with_head ob i x j xs) <->
    u = i /\ (j <= v)%nat /\ (v < j + length xs)%nat /\
    exists y, nth_error xs (v - j) = Some y /\ ob x y = true.
  Proof.
    intros P ob i x j xs. revert j.
    induction xs as [| y ys IH]; intros j u v; simpl.
    - split; [intros [] | intros [_ [H1 [H2 _]]]; lia].
    - destruct (ob x y) eqn:Hxy; simpl.
      + rewrite IH. split.
        * intros [Heq | [-> [Hle [Hlt [z [Hnth Hz]]]]]].
          -- inversion Heq; subst. repeat split; try lia.
             exists y. rewrite Nat.sub_diag. simpl. split; [reflexivity | exact Hxy].
          -- repeat split; try lia.
             exists z. replace (v - j)%nat with (S (v - S j)) by lia.
             simpl. split; assumption.
        * intros [-> [Hle [Hlt [z [Hnth Hz]]]]].
          destruct (Nat.eq_dec v j) as [-> | Hne].
          -- left; reflexivity.
          -- right. repeat split; try lia.
             exists z. replace (v - j)%nat with (S (v - S j)) in Hnth by lia.
             simpl in Hnth. split; assumption.
      + rewrite IH. split.
        * intros [-> [Hle [Hlt [z [Hnth Hz]]]]].
          repeat split; try lia.
          exists z. replace (v - j)%nat with (S (v - S j)) by lia.
          simpl. split; assumption.
        * intros [-> [Hle [Hlt [z [Hnth Hz]]]]].
          destruct (Nat.eq_dec v j) as [-> | Hne].
          -- rewrite Nat.sub_diag in Hnth. simpl in Hnth. inversion Hnth; subst.
             congruence.
          -- repeat split; try lia.
             exists z. replace (v - j)%nat with (S (v - S j)) in Hnth by lia.
             simpl in Hnth. split; assumption.
  Qed.

  Lemma pairs_with_head_NoDup : forall {P : Type} (ob : P -> P -> bool) i x j xs,
    NoDup (pairs_with_head ob i x j xs).
  Proof.
    intros P ob i x j xs. revert j.
    induction xs as [| y ys IH]; intro j; simpl.
    - constructor.
    - destruct (ob x y); [| apply IH].
      constructor; [| apply IH].
      intro Hin. apply pairs_with_head_in in Hin. lia.
  Qed.

  Lemma graph_edges_from_in : forall {P : Type} (ob : P -> P -> bool) i X u v,
    In (u, v) (graph_edges_from ob i X) <->
    (i <= u)%nat /\ (u < v)%nat /\ (v < i + length X)%nat /\
    exists x y, nth_error X (u - i) = Some x /\ nth_error X (v - i) = Some y /\ ob x y = true.
  Proof.
    intros P ob i X. revert i.
    induction X as [| x xs IH]; intros i u v; simpl.
    - split; [intros [] | intros [H1 [H2 [H3 _]]]; lia].
    - rewrite in_app_iff, pairs_with_head_in, IH. split.
      + intros [[-> [Hle [Hlt [y [Hnth Hy]]]]] | [Hle [Hlt1 [Hlt2 [a [b [Ha [Hb Hab]]]]]]]].
        * repeat split; try lia.
          exists x, y. rewrite Nat.sub_diag. simpl.
          replace (v - i)%nat with (S (v - S i)) by lia. simpl.
          repeat split; assumption.
        * repeat split; try lia.
          exists a, b.
          replace (u - i)%nat with (S (u - S i)) by lia.
          replace (v - i)%nat with (S (v - S i)) by lia. simpl.
          repeat split; assumption.
      + intros [Hle [Hlt1 [Hlt2 [a [b [Ha [Hb Hab]]]]]]].
        destruct (Nat.eq_dec u i) as [-> | Hne].
        * left. repeat split; try lia.
          rewrite Nat.sub_diag in Ha. simpl in Ha. inversion Ha; subst a.
          replace (v - i)%nat with (S (v - S i)) in Hb by lia. simpl in Hb.
          exists b. split; assumption.
        * right. repeat split; try lia.
          replace (u - i)%nat with (S (u - S i)) in Ha by lia.
          replace (v - i)%nat with (S (v - S i)) in Hb by lia. simpl in Ha, Hb.
          exists a, b. repeat split; assumption.
  Qed.

  Lemma graph_edges_from_NoDup : forall {P : Type} (ob : P -> P -> bool) i X,
    NoDup (graph_edges_from ob i X).
  Proof.
    intros P ob i X. revert i.
    induction X as [| x xs IH]; intro i; simpl.
    - constructor.
    - apply NoDup_app_local; [apply pairs_with_head_NoDup | apply IH |].
      intros [u v] H1 H2.
      apply pairs_with_head_in in H1. apply graph_edges_from_in in H2. lia.
  Qed.

  Lemma graph_edges_in : forall {P : Type} (ob : P -> P -> bool) (X : list P) u v,
    In (u, v) (graph_edges ob X) <->
    (u < v)%nat /\ (v < length X)%nat /\
    exists x y, nth_error X u = Some x /\ nth_error X v = Some y /\ ob x y = true.
  Proof.
    intros P ob X u v. unfold graph_edges.
    rewrite graph_edges_from_in.
    rewrite !Nat.sub_0_r. simpl. split; [intros [_ H]; exact H | intros H; split; [lia | exact H]].
  Qed.

  Lemma graph_edges_wf : forall {P : Type} (ob : P -> P -> bool) (X : list P),
    wf_edges (length X) (graph_edges ob X).
  Proof.
    intros P ob X. split.
    - apply graph_edges_from_NoDup.
    - rewrite Forall_forall. intros [u v] Hin.
      apply graph_edges_in in Hin. simpl. lia.
  Qed.

  (* =======================================================================
     3. Reachability, Walks, Loop Erasure, and BFS Distance / Parent
     ======================================================================= *)

  Inductive reachable (H : list (nat * nat)) : nat -> nat -> Prop :=
  | reach_refl : forall u, reachable H u u
  | reach_step : forall u v w, has_edge H u v -> reachable H v w -> reachable H u w.

  Lemma reachable_trans : forall H u v w,
    reachable H u v -> reachable H v w -> reachable H u w.
  Proof.
    intros H u v w H1 H2. induction H1; [exact H2 | eapply reach_step; eauto].
  Qed.

  Lemma reachable_sym : forall H u v,
    reachable H u v -> reachable H v u.
  Proof.
    intros H u v Hr. induction Hr.
    - apply reach_refl.
    - eapply reachable_trans; [exact IHHr | eapply reach_step; [apply has_edge_sym; exact H0 | apply reach_refl]].
  Qed.

  Lemma reachable_mono : forall H1 H2 u v,
    incl H1 H2 -> reachable H1 u v -> reachable H2 u v.
  Proof.
    intros H1 H2 u v Hincl Hr. induction Hr; [apply reach_refl |].
    eapply reach_step; [| exact IHHr].
    destruct H as [Ha | Hb]; [left | right]; apply Hincl; assumption.
  Qed.

  Inductive reachable_k (H : list (nat * nat)) : nat -> nat -> nat -> Prop :=
  | rk_refl : forall k u, reachable_k H k u u
  | rk_step : forall k u v w, has_edge H u v -> reachable_k H k v w -> reachable_k H (S k) u w.

  Lemma reachable_k_mono : forall H k1 k2 u v,
    (k1 <= k2)%nat -> reachable_k H k1 u v -> reachable_k H k2 u v.
  Proof.
    intros H k1 k2 u v Hle Hr. revert k2 Hle.
    induction Hr; intros k2 Hle.
    - apply rk_refl.
    - destruct k2 as [| k2']; [lia |].
      eapply rk_step; [exact H0 | apply IHHr; lia].
  Qed.

  Lemma reachable_k_right : forall H k u v w,
    reachable_k H k u v -> has_edge H v w -> reachable_k H (S k) u w.
  Proof.
    intros H k u v w Hr He. induction Hr.
    - eapply rk_step; [exact He | apply rk_refl].
    - eapply rk_step; [exact H0 | exact (IHHr He)].
  Qed.

  Lemma reachable_k_to_reachable : forall H k u v,
    reachable_k H k u v -> reachable H u v.
  Proof.
    intros H k u v Hr. induction Hr; [apply reach_refl | eapply reach_step; eauto].
  Qed.

  Lemma expand_once_iff : forall H S v,
    In v (expand_once H S) <-> In v S \/ exists u, In u S /\ has_edge H u v.
  Proof.
    intros H S v. unfold expand_once. rewrite in_app_iff, in_flat_map. split.
    - intros [Hin | [[a b] [He Hmem]]]; [left; exact Hin | right].
      simpl in Hmem. rewrite in_app_iff in Hmem.
      destruct Hmem as [H1 | H2].
      + destruct (existsb (Nat.eqb a) S) eqn:Ea; [| inversion H1].
        destruct H1 as [<- | []].
        apply existsb_exists in Ea. destruct Ea as [u [Hu Hueq]].
        apply Nat.eqb_eq in Hueq. subst u.
        exists a. split; [exact Hu | left; exact He].
      + destruct (existsb (Nat.eqb b) S) eqn:Eb; [| inversion H2].
        destruct H2 as [<- | []].
        apply existsb_exists in Eb. destruct Eb as [u [Hu Hueq]].
        apply Nat.eqb_eq in Hueq. subst u.
        exists b. split; [exact Hu | right; exact He].
    - intros [Hin | [u [Hu [He | He]]]]; [left; exact Hin | right | right].
      + exists (u, v). split; [exact He |].
        simpl. apply in_app_iff. left.
        assert (Eu : existsb (Nat.eqb u) S = true).
        { apply existsb_exists. exists u. split; [exact Hu | apply Nat.eqb_refl]. }
        rewrite Eu. left; reflexivity.
      + exists (v, u). split; [exact He |].
        simpl. apply in_app_iff. right.
        assert (Eu : existsb (Nat.eqb u) S = true).
        { apply existsb_exists. exists u. split; [exact Hu | apply Nat.eqb_refl]. }
        rewrite Eu. left; reflexivity.
  Qed.

  Lemma expand_iter_iff : forall k H S v,
    In v (expand_iter k H S) <-> exists u, In u S /\ reachable_k H k u v.
  Proof.
    induction k as [| k' IH]; intros H S v; simpl.
    - split.
      + intro Hin. exists v. split; [exact Hin | apply rk_refl].
      + intros [u [Hu Hr]]. inversion Hr; subst. exact Hu.
    - rewrite IH. split.
      + intros [w [Hw Hr]]. apply expand_once_iff in Hw.
        destruct Hw as [Hw | [u [Hu He]]].
        * exists w. split; [exact Hw | eapply reachable_k_mono; [| exact Hr]; lia].
        * exists u. split; [exact Hu | eapply rk_step; [exact He | exact Hr]].
      + intros [u [Hu Hr]]. inversion Hr; subst.
        * exists v. split; [apply expand_once_iff; left; exact Hu | apply rk_refl].
        * exists v0. split; [apply expand_once_iff; right; exists u; split; assumption | exact H2].
  Qed.

  Lemma expand_iter_0_iff : forall k H v,
    existsb (Nat.eqb v) (expand_iter k H [0%nat]) = true <-> reachable_k H k 0 v.
  Proof.
    intros k H v. rewrite existsb_exists. split.
    - intros [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x.
      apply expand_iter_iff in Hin. destruct Hin as [u [[<- | []] Hr]]. exact Hr.
    - intro Hr. exists v. split; [| apply Nat.eqb_refl].
      apply expand_iter_iff. exists 0%nat. split; [left; reflexivity | exact Hr].
  Qed.

  (* Walks and simple-path loop erasure *)
  Inductive walk (H : list (nat * nat)) : nat -> nat -> list nat -> Prop :=
  | walk_nil : forall u, walk H u u [u]
  | walk_cons : forall u v w rest,
      has_edge H u v -> walk H v w rest -> walk H u w (u :: rest).

  Lemma walk_len_pos : forall H u v w, walk H u v w -> (1 <= length w)%nat.
  Proof. intros H u v w Hw. destruct Hw; simpl; lia. Qed.

  Lemma walk_to_reachable_k : forall H u v w,
    walk H u v w -> reachable_k H (length w - 1) u v.
  Proof.
    intros H u v w Hw. induction Hw.
    - simpl. apply rk_refl.
    - pose proof (walk_len_pos _ _ _ _ Hw).
      simpl length. replace (S (length rest) - 1)%nat with (S (length rest - 1)) by lia.
      eapply rk_step; [exact H0 | exact IHHw].
  Qed.

  Lemma reachable_to_walk : forall H u v,
    reachable H u v -> exists w, walk H u v w.
  Proof.
    intros H u v Hr. induction Hr.
    - exists [u]. apply walk_nil.
    - destruct IHHr as [wk Hwk]. exists (u :: wk). eapply walk_cons; eauto.
  Qed.

  Lemma walk_vertices_lt : forall n H u v w,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (u < n)%nat -> walk H u v w -> Forall (fun x => (x < n)%nat) w.
  Proof.
    intros n H u v w Hwf Hu Hw. induction Hw.
    - constructor; [exact Hu | constructor].
    - pose proof (wf_has_edge_lt n H u v Hwf H0) as [_ [Hv _]].
      constructor; [exact Hu | exact (IHHw Hv)].
  Qed.

  Lemma walk_split_at : forall H u v w x,
    walk H u v w -> In x w ->
    exists w2, walk H x v w2 /\ (length w2 <= length w)%nat.
  Proof.
    intros H u v w x Hw. induction Hw; intro Hin.
    - destruct Hin as [<- | []]. exists [u]. split; [apply walk_nil | simpl; lia].
    - destruct Hin as [<- | Hin].
      + exists (u :: rest). split; [eapply walk_cons; eauto | lia].
      + destruct (IHHw Hin) as [w2 [Hw2 Hle]].
        exists w2. split; [exact Hw2 | simpl; lia].
  Qed.

  Lemma walk_to_simple_walk : forall H u v w,
    walk H u v w ->
    exists w', walk H u v w' /\ NoDup w' /\ (length w' <= length w)%nat.
  Proof.
    intros H u v w. revert u v.
    induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length nat))).
    intros u v Hw. destruct Hw as [u | u x v rest He Hrest].
    - exists [u]. repeat split; [apply walk_nil | constructor; [intros [] | constructor] | lia].
    - destruct (in_dec Nat.eq_dec u rest) as [Hin | Hnot].
      + destruct (walk_split_at H x v rest u Hrest Hin) as [w2 [Hw2 Hle]].
        assert (Hlt : (length w2 < length (u :: rest))%nat) by (simpl; lia).
        destruct (IH w2 Hlt u v Hw2) as [w' [Hw' [Hnd Hle']]].
        exists w'. repeat split; [exact Hw' | exact Hnd | simpl; lia].
      + assert (Hlt : (length rest < length (u :: rest))%nat) by (simpl; lia).
        destruct (IH rest Hlt x v Hrest) as [w' [Hw' [Hnd Hle']]].
        destruct (in_dec Nat.eq_dec u w') as [Hin' | Hnot'].
        * destruct (walk_split_at H x v w' u Hw' Hin') as [w2 [Hw2 Hle2]].
          assert (Hlt2 : (length w2 < length (u :: rest))%nat) by (simpl; lia).
          destruct (IH w2 Hlt2 u v Hw2) as [w'' [Hw'' [Hnd'' Hle'']]].
          exists w''. repeat split; [exact Hw'' | exact Hnd'' | simpl; lia].
        * exists (u :: w'). repeat split.
          -- eapply walk_cons; eauto.
          -- constructor; assumption.
          -- simpl; lia.
  Qed.

  Lemma reachable_bounded_length : forall n H u v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (u < n)%nat ->
    reachable H u v ->
    reachable_k H (n - 1) u v.
  Proof.
    intros n H u v Hwf Hu Hr.
    destruct (reachable_to_walk H u v Hr) as [w Hw].
    destruct (walk_to_simple_walk H u v w Hw) as [w' [Hw' [Hnd _]]].
    pose proof (walk_vertices_lt n H u v w' Hwf Hu Hw') as Hlt.
    assert (Hincl : incl w' (seq 0 n)).
    { intros z Hz. apply in_seq. rewrite Forall_forall in Hlt. specialize (Hlt z Hz). lia. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite seq_length in Hlen.
    eapply reachable_k_mono; [| apply walk_to_reachable_k; exact Hw'].
    lia.
  Qed.

  Lemma is_connectedb_iff : forall n H,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    is_connectedb n H = true <-> (0 < n)%nat /\ forall v, (v < n)%nat -> reachable H 0 v.
  Proof.
    intros n H Hwf. destruct n as [| n'].
    - simpl. split; [discriminate | intros [Hgt _]; lia].
    - unfold is_connectedb. rewrite forallb_forall. split.
      + intro Hall. split; [lia |].
        intros v Hv.
        assert (Hin : In v (seq 0 (S n'))) by (apply in_seq; lia).
        specialize (Hall v Hin). apply expand_iter_0_iff in Hall.
        exact (reachable_k_to_reachable H (S n') 0 v Hall).
      + intros [_ Hall] v Hin. apply in_seq in Hin.
        apply expand_iter_0_iff.
        eapply reachable_k_mono; [| apply (reachable_bounded_length (S n') H 0 v Hwf); [lia | apply Hall; lia]].
        lia.
  Qed.

  (* BFS distance and minimum-index parent *)
  Fixpoint bfs_dist_aux (d fuel : nat) (H : list (nat * nat)) (v : nat) : nat :=
    match fuel with
    | 0%nat => d
    | S fuel' =>
        if existsb (Nat.eqb v) (expand_iter d H [0%nat])
        then d
        else bfs_dist_aux (S d) fuel' H v
    end.

  Definition bfs_dist (n : nat) (H : list (nat * nat)) (v : nat) : nat :=
    bfs_dist_aux 0 n H v.

  Lemma bfs_dist_aux_spec : forall fuel d H v k,
    (d <= k)%nat -> (k <= d + fuel)%nat ->
    (forall j, (j < d)%nat -> ~ reachable_k H j 0 v) ->
    reachable_k H k 0 v ->
    let r := bfs_dist_aux d fuel H v in
    (r <= k)%nat /\ reachable_k H r 0 v /\ (forall j, (j < r)%nat -> ~ reachable_k H j 0 v).
  Proof.
    induction fuel as [| fuel' IH]; intros d H v k Hdk Hkdf Hnone Hrk; simpl.
    - assert (k = d) by lia. subst k. repeat split; [lia | exact Hrk | exact Hnone].
    - destruct (existsb (Nat.eqb v) (expand_iter d H [0%nat])) eqn:Ed.
      + apply expand_iter_0_iff in Ed.
        repeat split; [exact Hdk | exact Ed | exact Hnone].
      + assert (Hnotd : ~ reachable_k H d 0 v).
        { intro Hr. apply expand_iter_0_iff in Hr. congruence. }
        assert (Hdk' : (S d <= k)%nat).
        { destruct (Nat.eq_dec d k); [subst; contradiction | lia]. }
        apply (IH (S d) H v k Hdk' ltac:(lia)); [| exact Hrk].
        intros j Hj. destruct (Nat.eq_dec j d); [subst; exact Hnotd | apply Hnone; lia].
  Qed.

  Lemma bfs_dist_spec : forall n H v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable H 0 v ->
    reachable_k H (bfs_dist n H v) 0 v /\
    (forall j, (j < bfs_dist n H v)%nat -> ~ reachable_k H j 0 v) /\
    (bfs_dist n H v < n)%nat.
  Proof.
    intros n H v Hwf Hn Hr.
    pose proof (reachable_bounded_length n H 0 v Hwf Hn Hr) as Hrk.
    pose proof (bfs_dist_aux_spec n 0 H v (n - 1) ltac:(lia) ltac:(lia) (fun j Hj => ltac:(lia)) Hrk)
      as [Hle [Hr' Hmin]].
    unfold bfs_dist. repeat split; [exact Hr' | exact Hmin | lia].
  Qed.

  Lemma bfs_dist_0 : forall n H, (0 < n)%nat -> bfs_dist n H 0 = 0%nat.
  Proof.
    intros [| n'] H Hn; [lia |].
    unfold bfs_dist. simpl. reflexivity.
  Qed.

  Lemma bfs_dist_nonzero : forall n H v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable H 0 v -> v <> 0%nat -> (0 < bfs_dist n H v)%nat.
  Proof.
    intros n H v Hwf Hn Hr Hne.
    destruct (bfs_dist_spec n H v Hwf Hn Hr) as [Hrk _].
    destruct (bfs_dist n H v) eqn:Ed; [| lia].
    inversion Hrk; subst; contradiction.
  Qed.

  Lemma bfs_dist_le_of_rk : forall n H v k,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable_k H k 0 v -> (bfs_dist n H v <= k)%nat.
  Proof.
    intros n H v k Hwf Hn Hrk.
    destruct (bfs_dist_spec n H v Hwf Hn (reachable_k_to_reachable H k 0 v Hrk)) as [_ [Hmin _]].
    destruct (le_lt_dec (bfs_dist n H v) k); [exact l |].
    exfalso. exact (Hmin k l Hrk).
  Qed.

  Lemma bfs_dist_edge_step : forall n H u v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable H 0 u -> has_edge H u v ->
    (bfs_dist n H v <= S (bfs_dist n H u))%nat.
  Proof.
    intros n H u v Hwf Hn Hru He.
    destruct (bfs_dist_spec n H u Hwf Hn Hru) as [Hrku _].
    apply (bfs_dist_le_of_rk n H v (S (bfs_dist n H u)) Hwf Hn).
    exact (reachable_k_right H (bfs_dist n H u) 0 u v Hrku He).
  Qed.

  Lemma reachable_k_last_step : forall H k u v,
    reachable_k H (S k) u v ->
    u = v \/ exists w, reachable_k H k u w /\ has_edge H w v.
  Proof.
    induction k as [| k' IH]; intros u v Hr.
    - inversion Hr as [| ? ? v0 ? He Hrest]; subst; [left; reflexivity |].
      inversion Hrest; subst. right. exists u. split; [apply rk_refl | exact He].
    - inversion Hr as [| ? ? v0 ? He Hrest]; subst; [left; reflexivity |].
      destruct (IH v0 v Hrest) as [<- | [w [Hw Hew]]].
      + right. exists u. split; [apply rk_refl | exact He].
      + right. exists w. split; [eapply rk_step; [exact He | exact Hw] | exact Hew].
  Qed.

  Lemma bfs_exists_pred : forall n H v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable H 0 v -> v <> 0%nat ->
    exists u, (u < n)%nat /\ has_edge H u v /\ S (bfs_dist n H u) = bfs_dist n H v.
  Proof.
    intros n H v Hwf Hn Hr Hne.
    destruct (bfs_dist_spec n H v Hwf Hn Hr) as [Hrkv [Hmin _]].
    pose proof (bfs_dist_nonzero n H v Hwf Hn Hr Hne) as Hpos.
    destruct (bfs_dist n H v) as [| d] eqn:Ed; [lia |].
    destruct (reachable_k_last_step H d 0 v Hrkv) as [Heq | [u [Hrku He]]].
    - congruence.
    - pose proof (wf_has_edge_lt n H u v Hwf He) as [Hu _].
      pose proof (bfs_dist_le_of_rk n H u d Hwf Hn Hrku) as Hle.
      pose proof (bfs_dist_edge_step n H u v Hwf Hn (reachable_k_to_reachable H d 0 u Hrku) He) as Hstep.
      exists u. repeat split; [exact Hu | exact He | lia].
  Qed.

  Fixpoint find_min_nat (p : nat -> bool) (start fuel : nat) : nat :=
    match fuel with
    | 0%nat => start
    | S fuel' => if p start then start else find_min_nat p (S start) fuel'
    end.

  Lemma find_min_nat_spec : forall fuel p start u,
    (start <= u)%nat -> (u < start + fuel)%nat -> p u = true ->
    (forall x, (start <= x < start)%nat -> p x = false) ->
    let r := find_min_nat p start fuel in
    (start <= r)%nat /\ (r <= u)%nat /\ p r = true /\
    (forall x, (start <= x < r)%nat -> p x = false).
  Proof.
    induction fuel as [| fuel' IH]; intros p start u Hsu Huf Hpu _; simpl.
    - lia.
    - destruct (p start) eqn:Hs.
      + repeat split; [lia | exact Hsu | exact Hs | intros x Hx; lia].
      + assert (Hne : start <> u) by (intro Heq; subst; congruence).
        destruct (IH p (S start) u ltac:(lia) ltac:(lia) Hpu ltac:(intros; lia))
          as [H1 [H2 [H3 H4]]].
        repeat split; [lia | exact H2 | exact H3 |].
        intros x Hx. destruct (Nat.eq_dec x start); [subst; exact Hs | apply H4; lia].
  Qed.

  Definition bfs_parent (n : nat) (H : list (nat * nat)) (v : nat) : nat :=
    find_min_nat (fun u => has_edgeb H u v && Nat.eqb (S (bfs_dist n H u)) (bfs_dist n H v)) 0 n.

  Lemma bfs_parent_spec : forall n H v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) H ->
    (0 < n)%nat -> reachable H 0 v -> v <> 0%nat ->
    let u := bfs_parent n H v in
    (u < n)%nat /\ has_edge H u v /\ S (bfs_dist n H u) = bfs_dist n H v /\
    (forall u', (u' < n)%nat -> has_edge H u' v -> S (bfs_dist n H u') = bfs_dist n H v -> (u <= u')%nat).
  Proof.
    intros n H v Hwf Hn Hr Hne.
    destruct (bfs_exists_pred n H v Hwf Hn Hr Hne) as [u0 [Hu0 [He0 Hd0]]].
    set (p := fun u => has_edgeb H u v && Nat.eqb (S (bfs_dist n H u)) (bfs_dist n H v)).
    assert (Hpu0 : p u0 = true).
    { unfold p. rewrite andb_true_iff, has_edgeb_iff, Nat.eqb_eq. split; assumption. }
    pose proof (find_min_nat_spec n p 0 u0 ltac:(lia) ltac:(lia) Hpu0 ltac:(intros; lia))
      as [_ [Hle [Hpr Hmin]]].
    change (find_min_nat p 0 n) with (bfs_parent n H v) in *.
    unfold p in Hpr. rewrite andb_true_iff, has_edgeb_iff, Nat.eqb_eq in Hpr.
    destruct Hpr as [Her Hdr].
    repeat split; [lia | exact Her | exact Hdr |].
    intros u' Hu' He' Hd'.
    destruct (le_lt_dec (bfs_parent n H v) u'); [exact l |].
    assert (Hpu' : p u' = true).
    { unfold p. rewrite andb_true_iff, has_edgeb_iff, Nat.eqb_eq. split; assumption. }
    specialize (Hmin u' ltac:(lia)). congruence.
  Qed.

  (* =======================================================================
     4. Penrose BFS Tree Map tau, Lower Bound |H| >= n - 1, and Unique Parent
     ======================================================================= *)

  Definition is_tau_edge (n : nat) (H : list (nat * nat)) (e : nat * nat) : bool :=
    let '(u, v) := e in
    ((Nat.eqb (S (bfs_dist n H u)) (bfs_dist n H v)) && (Nat.eqb (bfs_parent n H v) u)) ||
    ((Nat.eqb (S (bfs_dist n H v)) (bfs_dist n H u)) && (Nat.eqb (bfs_parent n H u) v)).

  Definition tau (n : nat) (E H : list (nat * nat)) : list (nat * nat) :=
    filter (is_tau_edge n H) E.

  Lemma tau_in_sublists : forall n E H, In (tau n E H) (sublists E).
  Proof. intros n E H. unfold tau. apply filter_in_sublists. Qed.

  Lemma tau_edge_iff : forall n E H e,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    In e (tau n E H) <->
    exists v, (1 <= v < n)%nat /\ e = mk_edge (bfs_parent n H v) v.
  Proof.
    intros n E H [a b] [HndE HwfE] HinH Hconn.
    pose proof (sublists_Forall _ E H HwfE HinH) as HwfH.
    apply (is_connectedb_iff n H HwfH) in Hconn. destruct Hconn as [Hn Hreach].
    unfold tau. rewrite filter_In. unfold is_tau_edge.
    rewrite orb_true_iff, !andb_true_iff, !Nat.eqb_eq. split.
    - intros [HinE [[Hd Hp] | [Hd Hp]]].
      + rewrite Forall_forall in HwfE. specialize (HwfE (a, b) HinE). simpl in HwfE.
        exists b. split; [lia |].
        subst a. unfold mk_edge.
        destruct (Nat.ltb_spec (bfs_parent n H b) b); [reflexivity | lia].
      + rewrite Forall_forall in HwfE. specialize (HwfE (a, b) HinE). simpl in HwfE.
        assert (Ha0 : a <> 0%nat).
        { intro Ha. subst a. rewrite bfs_dist_0 in Hd; lia. }
        exists a. split; [lia |].
        subst b. unfold mk_edge.
        destruct (Nat.ltb_spec (bfs_parent n H a) a); [lia | reflexivity].
    - intros [v [Hv Heq]].
      pose proof (bfs_parent_spec n H v HwfH Hn (Hreach v ltac:(lia)) ltac:(lia))
        as [Hpv [Hev [Hdv _]]].
      pose proof (wf_has_edge_lt n H (bfs_parent n H v) v HwfH Hev) as [_ [_ Hne]].
      assert (HinHv : In (mk_edge (bfs_parent n H v) v) H).
      { apply (wf_has_edge_mk n H _ _ HwfH). exact Hev. }
      assert (HinEv : In (a, b) E).
      { rewrite Heq. exact (sublists_incl E H HinH _ HinHv). }
      split; [exact HinEv |].
      unfold mk_edge in Heq. destruct (Nat.ltb_spec (bfs_parent n H v) v).
      + inversion Heq; subst. left; split; [exact Hdv | reflexivity].
      + inversion Heq; subst. right; split; [exact Hdv | reflexivity].
  Qed.

  Lemma tau_incl_H : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    incl (tau n E H) H.
  Proof.
    intros n E H [HndE HwfE] HinH Hconn e Hin.
    pose proof (sublists_Forall _ E H HwfE HinH) as HwfH.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    apply (tau_edge_iff n E H e (conj HndE HwfE) HinH Hconn) in Hin.
    destruct Hin as [v [Hv ->]].
    pose proof (bfs_parent_spec n H v HwfH Hn (Hreach v ltac:(lia)) ltac:(lia)) as [_ [Hev _]].
    apply (wf_has_edge_mk n H _ _ HwfH). exact Hev.
  Qed.

  Lemma tau_length : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    length (tau n E H) = (n - 1)%nat.
  Proof.
    intros n E H HwfE HinH Hconn.
    destruct HwfE as [HndE HforE].
    pose proof (sublists_Forall _ E H HforE HinH) as HwfH.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    set (f := fun v => mk_edge (bfs_parent n H v) v).
    assert (Hnd_tau : NoDup (tau n E H)) by (apply NoDup_filter; exact HndE).
    assert (Hnd_map : NoDup (map f (seq 1 (n - 1)))).
    { apply NoDup_map_in; [apply seq_NoDup |].
      intros v1 v2 Hv1 Hv2 Heq.
      apply in_seq in Hv1. apply in_seq in Hv2.
      pose proof (bfs_parent_spec n H v1 HwfH Hn (Hreach v1 ltac:(lia)) ltac:(lia)) as [_ [_ [Hd1 _]]].
      pose proof (bfs_parent_spec n H v2 HwfH Hn (Hreach v2 ltac:(lia)) ltac:(lia)) as [_ [_ [Hd2 _]]].
      unfold f, mk_edge in Heq.
      destruct (Nat.ltb_spec (bfs_parent n H v1) v1);
      destruct (Nat.ltb_spec (bfs_parent n H v2) v2);
      injection Heq as Heq1 Heq2.
      - exact Heq2.
      - rewrite Heq1 in Hd1; rewrite <- Heq2 in Hd2; lia.
      - rewrite Heq2 in Hd1; rewrite <- Heq1 in Hd2; lia.
      - exact Heq1. }
    assert (H1 : incl (tau n E H) (map f (seq 1 (n - 1)))).
    { intros e Hin.
      apply (tau_edge_iff n E H e (conj HndE HforE) HinH Hconn) in Hin.
      destruct Hin as [v [Hv ->]].
      change (mk_edge (bfs_parent n H v) v) with (f v). apply in_map. apply in_seq. lia. }
    assert (H2 : incl (map f (seq 1 (n - 1))) (tau n E H)).
    { intros e Hin. apply in_map_iff in Hin. destruct Hin as [v [<- Hv]].
      apply in_seq in Hv.
      apply (tau_edge_iff n E H (f v) (conj HndE HforE) HinH Hconn).
      exists v. split; [lia | reflexivity]. }
    pose proof (NoDup_incl_length Hnd_tau H1) as L1.
    pose proof (NoDup_incl_length Hnd_map H2) as L2.
    rewrite map_length, seq_length in L1, L2. lia.
  Qed.

  Lemma connected_length_ge : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    (n - 1 <= length H)%nat.
  Proof.
    intros n E H HwfE HinH Hconn.
    rewrite <- (tau_length n E H HwfE HinH Hconn).
    apply NoDup_incl_length.
    - apply NoDup_filter. exact (proj1 HwfE).
    - exact (tau_incl_H n E H HwfE HinH Hconn).
  Qed.

  Lemma tau_bfs_dist_le : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    forall d v, (v < n)%nat -> bfs_dist n H v = d ->
    reachable_k (tau n E H) d 0 v.
  Proof.
    intros n E H HwfE HinH Hconn d.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HwfH.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    induction d as [| d' IH]; intros v Hv Hd.
    - destruct (Nat.eq_dec v 0) as [-> | Hne]; [apply rk_refl |].
      pose proof (bfs_dist_nonzero n H v HwfH Hn (Hreach v Hv) Hne). lia.
    - assert (Hne : v <> 0%nat).
      { intro H0. subst v. rewrite bfs_dist_0 in Hd; lia. }
      pose proof (bfs_parent_spec n H v HwfH Hn (Hreach v Hv) Hne) as [Hpu [_ [Hdu _]]].
      assert (Hrku : reachable_k (tau n E H) d' 0 (bfs_parent n H v)).
      { apply IH; [exact Hpu | lia]. }
      eapply reachable_k_right; [exact Hrku |].
      apply (wf_has_edge_mk n (tau n E H) _ _ (sublists_Forall _ E _ (proj2 HwfE) (tau_in_sublists n E H))).
      apply (tau_edge_iff n E H _ HwfE HinH Hconn).
      exists v. split; [lia | reflexivity].
  Qed.

  Lemma tau_connected : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    is_connectedb n (tau n E H) = true.
  Proof.
    intros n E H HwfE HinH Hconn.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HwfH.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    apply (is_connectedb_iff n (tau n E H) (sublists_Forall _ E _ (proj2 HwfE) (tau_in_sublists n E H))).
    split; [exact Hn |].
    intros v Hv.
    eapply reachable_k_to_reachable.
    exact (tau_bfs_dist_le n E H HwfE HinH Hconn (bfs_dist n H v) v Hv eq_refl).
  Qed.

  Lemma tau_is_spanning_tree : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    In (tau n E H) (spanning_trees n E).
  Proof.
    intros n E H HwfE HinH Hconn.
    unfold spanning_trees. apply filter_In. split.
    - apply tau_in_sublists.
    - unfold is_treeb. rewrite andb_true_iff, Nat.eqb_eq. split.
      + exact (tau_connected n E H HwfE HinH Hconn).
      + exact (tau_length n E H HwfE HinH Hconn).
  Qed.

  Lemma tau_idempotent_on_tree : forall n E T,
    wf_edges n E -> In T (spanning_trees n E) ->
    tau n E T = T.
  Proof.
    intros n E T HwfE HinT.
    unfold spanning_trees in HinT. apply filter_In in HinT.
    destruct HinT as [HinSub Htree].
    unfold is_treeb in Htree. rewrite andb_true_iff, Nat.eqb_eq in Htree.
    destruct Htree as [Hconn Hlen].
    assert (Hincl : incl (tau n E T) T) by (exact (tau_incl_H n E T HwfE HinSub Hconn)).
    assert (Hnd_tau : NoDup (tau n E T)) by (apply NoDup_filter; exact (proj1 HwfE)).
    assert (Hnd_T : NoDup T) by (exact (sublists_NoDup_elem E T (proj1 HwfE) HinSub)).
    assert (Hlen_eq : length (tau n E T) = length T).
    { rewrite (tau_length n E T HwfE HinSub Hconn). lia. }
    apply (sublists_ext E (tau n E T) T (proj1 HwfE) (tau_in_sublists n E T) HinSub).
    intro e. split; [apply Hincl |].
    intro HeT.
    destruct (in_dec edge_eq_dec e (tau n E T)) as [Hin | Hnot]; [exact Hin |].
    exfalso.
    assert (Hnd' : NoDup (e :: tau n E T)) by (constructor; assumption).
    assert (Hincl' : incl (e :: tau n E T) T).
    { intros x [<- | Hx]; [exact HeT | exact (Hincl x Hx)]. }
    pose proof (NoDup_incl_length Hnd' Hincl') as Hcontra.
    simpl in Hcontra. lia.
  Qed.

  (* =======================================================================
     5. Penrose Upper Envelope in_M and Exact Fiber Equivalence
     ======================================================================= *)

  Definition in_M (n : nat) (T : list (nat * nat)) (e : nat * nat) : bool :=
    let '(u, v) := e in
    let du := bfs_dist n T u in
    let dv := bfs_dist n T v in
    Nat.eqb du dv ||
    (Nat.eqb (S du) dv && Nat.leb (bfs_parent n T v) u) ||
    (Nat.eqb (S dv) du && Nat.leb (bfs_parent n T u) v).

  Lemma in_M_of_tree_edge : forall n E T e,
    wf_edges n E -> In T (spanning_trees n E) -> In e T ->
    in_M n T e = true.
  Proof.
    intros n E T [a b] HwfE HinT HeT.
    pose proof HinT as HinT'.
    unfold spanning_trees in HinT'. apply filter_In in HinT'.
    destruct HinT' as [HinSub Htree].
    unfold is_treeb in Htree. rewrite andb_true_iff, Nat.eqb_eq in Htree.
    destruct Htree as [Hconn _].
    rewrite <- (tau_idempotent_on_tree n E T HwfE HinT) in HeT.
    unfold tau in HeT. apply filter_In in HeT. destruct HeT as [_ His].
    unfold is_tau_edge in His. unfold in_M.
    rewrite orb_true_iff, !andb_true_iff, !Nat.eqb_eq in His.
    rewrite !orb_true_iff, !andb_true_iff, !Nat.eqb_eq, !Nat.leb_le.
    destruct His as [[Hd Hp] | [Hd Hp]].
    - left; right. split; [exact Hd | lia].
    - right. split; [exact Hd | lia].
  Qed.

  Lemma bfs_dist_eq_tau : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    forall v, (v < n)%nat -> bfs_dist n (tau n E H) v = bfs_dist n H v.
  Proof.
    intros n E H HwfE HinH Hconn v Hv.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HwfH.
    pose proof (sublists_Forall _ E _ (proj2 HwfE) (tau_in_sublists n E H)) as HwfT.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    assert (Hle1 : (bfs_dist n (tau n E H) v <= bfs_dist n H v)%nat).
    { apply (bfs_dist_le_of_rk n (tau n E H) v (bfs_dist n H v) HwfT Hn).
      exact (tau_bfs_dist_le n E H HwfE HinH Hconn (bfs_dist n H v) v Hv eq_refl). }
    assert (Hle2 : (bfs_dist n H v <= bfs_dist n (tau n E H) v)%nat).
    { pose proof (tau_connected n E H HwfE HinH Hconn) as HconnT.
      apply (is_connectedb_iff n _ HwfT) in HconnT. destruct HconnT as [_ HreachT].
      destruct (bfs_dist_spec n (tau n E H) v HwfT Hn (HreachT v Hv)) as [HrkT _].
      apply (bfs_dist_le_of_rk n H v (bfs_dist n (tau n E H) v) HwfH Hn).
      clear - HrkT HwfE HinH Hconn.
      induction HrkT; [apply rk_refl |].
      eapply rk_step; [| exact IHHrkT].
      destruct H0 as [Ha | Hb]; [left | right];
        apply (tau_incl_H n E H HwfE HinH Hconn); assumption. }
    lia.
  Qed.

  Lemma bfs_parent_eq_tau : forall n E H,
    wf_edges n E -> In H (sublists E) -> is_connectedb n H = true ->
    forall v, (1 <= v < n)%nat -> bfs_parent n (tau n E H) v = bfs_parent n H v.
  Proof.
    intros n E H HwfE HinH Hconn v Hv.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HwfH.
    pose proof (sublists_Forall _ E _ (proj2 HwfE) (tau_in_sublists n E H)) as HwfT.
    pose proof Hconn as Hconn'.
    apply (is_connectedb_iff n H HwfH) in Hconn'. destruct Hconn' as [Hn Hreach].
    pose proof (tau_connected n E H HwfE HinH Hconn) as HconnT.
    apply (is_connectedb_iff n _ HwfT) in HconnT. destruct HconnT as [_ HreachT].
    pose proof (bfs_parent_spec n H v HwfH Hn (Hreach v ltac:(lia)) ltac:(lia)) as [HuH [HeH [HdH HminH]]].
    pose proof (bfs_parent_spec n (tau n E H) v HwfT Hn (HreachT v ltac:(lia)) ltac:(lia)) as [HuT [HeT [HdT HminT]]].
    assert (H1 : (bfs_parent n (tau n E H) v <= bfs_parent n H v)%nat).
    { apply HminT; [exact HuH | |].
      - apply (wf_has_edge_mk n _ _ _ HwfT).
        apply (tau_edge_iff n E H _ HwfE HinH Hconn). exists v. split; [exact Hv | reflexivity].
      - rewrite !bfs_dist_eq_tau; try assumption; lia. }
    assert (H2 : (bfs_parent n H v <= bfs_parent n (tau n E H) v)%nat).
    { apply HminH; [exact HuT | |].
      - destruct HeT as [Ha | Hb]; [left | right];
          apply (tau_incl_H n E H HwfE HinH Hconn); assumption.
      - rewrite <- (bfs_dist_eq_tau n E H HwfE HinH Hconn (bfs_parent n (tau n E H) v) HuT).
        rewrite <- (bfs_dist_eq_tau n E H HwfE HinH Hconn v ltac:(lia)).
        exact HdT. }
    lia.
  Qed.

  Lemma in_M_step_dist : forall n T H k u v,
    (forall e, In e H -> in_M n T e = true) ->
    reachable_k H k u v ->
    (bfs_dist n T v <= bfs_dist n T u + k)%nat.
  Proof.
    intros n T H k u v Hall Hrk. induction Hrk.
    - lia.
    - assert (Hstep : (bfs_dist n T v <= S (bfs_dist n T u))%nat).
      { destruct H0 as [Hin | Hin]; specialize (Hall _ Hin); unfold in_M in Hall;
          rewrite !orb_true_iff, !andb_true_iff, !Nat.eqb_eq, !Nat.leb_le in Hall; lia. }
      lia.
  Qed.

  Theorem penrose_fiber_iff : forall n E T H,
    wf_edges n E ->
    In T (spanning_trees n E) ->
    In H (sublists E) ->
    (is_connectedb n H = true /\ tau n E H = T) <->
    ((forall e, In e T -> In e H) /\ (forall e, In e H -> in_M n T e = true)).
  Proof.
    intros n E T H HwfE HinT HinH.
    pose proof HinT as HinT'.
    unfold spanning_trees in HinT'. apply filter_In in HinT'.
    destruct HinT' as [HinSubT HtreeT].
    unfold is_treeb in HtreeT. rewrite andb_true_iff, Nat.eqb_eq in HtreeT.
    destruct HtreeT as [HconnT HlenT].
    pose proof (sublists_Forall _ E T (proj2 HwfE) HinSubT) as HwfT.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HwfH.
    pose proof HconnT as HconnT'.
    apply (is_connectedb_iff n T HwfT) in HconnT'. destruct HconnT' as [Hn HreachT].
    split.
    - intros [HconnH Htau]. split.
      + intros e HeT. rewrite <- Htau in HeT.
        exact (tau_incl_H n E H HwfE HinH HconnH e HeT).
      + intros [u v] HeH.
        pose proof (sublists_Forall _ E H (proj2 HwfE) HinH) as HforH.
        rewrite Forall_forall in HforH. pose proof (HforH (u, v) HeH) as Huv. simpl in Huv.
        pose proof HconnH as HconnH'.
        apply (is_connectedb_iff n H HwfH) in HconnH'. destruct HconnH' as [_ HreachH].
        assert (Hdu : bfs_dist n T u = bfs_dist n H u).
        { rewrite <- Htau. apply bfs_dist_eq_tau; try assumption; lia. }
        assert (Hdv : bfs_dist n T v = bfs_dist n H v).
        { rewrite <- Htau. apply bfs_dist_eq_tau; try assumption; lia. }
        pose proof (bfs_dist_edge_step n H u v HwfH Hn (HreachH u ltac:(lia)) (or_introl HeH)) as Hs1.
        pose proof (bfs_dist_edge_step n H v u HwfH Hn (HreachH v ltac:(lia)) (or_intror HeH)) as Hs2.
        unfold in_M. rewrite !orb_true_iff, !andb_true_iff, !Nat.eqb_eq, !Nat.leb_le.
        rewrite Hdu, Hdv.
        destruct (Nat.eq_dec (bfs_dist n H u) (bfs_dist n H v)) as [Heqd | Hned].
        * left; left; exact Heqd.
        * destruct (le_lt_dec (bfs_dist n H u) (bfs_dist n H v)).
          -- left; right. split; [lia |].
             assert (Hv1 : (1 <= v < n)%nat) by lia.
             rewrite <- Htau, (bfs_parent_eq_tau n E H HwfE HinH HconnH v Hv1).
             destruct (bfs_parent_spec n H v HwfH Hn (HreachH v ltac:(lia)) ltac:(lia)) as [_ [_ [_ Hmin]]].
             apply Hmin; [lia | left; exact HeH | lia].
          -- right. split; [lia |].
             assert (Hu0 : u <> 0%nat).
             { intro H0. subst u. rewrite bfs_dist_0 in *; lia. }
             assert (Hu1 : (1 <= u < n)%nat) by lia.
             rewrite <- Htau, (bfs_parent_eq_tau n E H HwfE HinH HconnH u Hu1).
             destruct (bfs_parent_spec n H u HwfH Hn (HreachH u ltac:(lia)) Hu0) as [_ [_ [_ Hmin]]].
             apply Hmin; [lia | right; exact HeH | lia].
    - intros [HsubTH HinMH].
      assert (HconnH : is_connectedb n H = true).
      { apply (is_connectedb_iff n H HwfH). split; [exact Hn |].
        intros v Hv. eapply reachable_mono; [exact HsubTH | exact (HreachT v Hv)]. }
      split; [exact HconnH |].
      pose proof HconnH as HconnH'.
      apply (is_connectedb_iff n H HwfH) in HconnH'. destruct HconnH' as [_ HreachH].
      (* Step 1: bfs_dist n H v = bfs_dist n T v for all v < n *)
      assert (Hdist_eq : forall v, (v < n)%nat -> bfs_dist n H v = bfs_dist n T v).
      { intros v Hv.
        assert (H1 : (bfs_dist n H v <= bfs_dist n T v)%nat).
        { destruct (bfs_dist_spec n T v HwfT Hn (HreachT v Hv)) as [HrkT _].
          apply (bfs_dist_le_of_rk n H v (bfs_dist n T v) HwfH Hn).
          clear - HrkT HsubTH. induction HrkT; [apply rk_refl |].
          eapply rk_step; [| exact IHHrkT].
          destruct H0 as [Ha | Hb]; [left | right]; apply HsubTH; assumption. }
        assert (H2 : (bfs_dist n T v <= bfs_dist n H v)%nat).
        { destruct (bfs_dist_spec n H v HwfH Hn (HreachH v Hv)) as [HrkH _].
          pose proof (in_M_step_dist n T H (bfs_dist n H v) 0 v HinMH HrkH) as Hst.
          rewrite bfs_dist_0 in Hst; lia. }
        lia. }
      (* Step 2: bfs_parent n H v = bfs_parent n T v for all 1 <= v < n *)
      assert (Hpar_eq : forall v, (1 <= v < n)%nat -> bfs_parent n H v = bfs_parent n T v).
      { intros v Hv.
        pose proof (bfs_parent_spec n H v HwfH Hn (HreachH v ltac:(lia)) ltac:(lia)) as [HuH [HeH [HdH HminH]]].
        pose proof (bfs_parent_spec n T v HwfT Hn (HreachT v ltac:(lia)) ltac:(lia)) as [HuT [HeT [HdT HminT]]].
        assert (H1 : (bfs_parent n H v <= bfs_parent n T v)%nat).
        { apply HminH; [exact HuT | |].
          - destruct HeT as [Ha | Hb]; [left | right]; apply HsubTH; assumption.
          - rewrite !Hdist_eq; try lia; exact HdT. }
        assert (H2 : (bfs_parent n T v <= bfs_parent n H v)%nat).
        { assert (HeM : in_M n T (mk_edge (bfs_parent n H v) v) = true).
          { apply HinMH. apply (wf_has_edge_mk n H _ _ HwfH). exact HeH. }
          rewrite !Hdist_eq in HdH; try lia.
          unfold mk_edge, in_M in HeM.
          destruct (Nat.ltb_spec (bfs_parent n H v) v);
            rewrite !orb_true_iff, !andb_true_iff, !Nat.eqb_eq, !Nat.leb_le in HeM; lia. }
        lia. }
      (* Step 3: tau n E H = tau n E T = T *)
      rewrite <- (tau_idempotent_on_tree n E T HwfE HinT).
      apply (sublists_ext E (tau n E H) (tau n E T) (proj1 HwfE) (tau_in_sublists n E H) (tau_in_sublists n E T)).
      intro e.
      rewrite (tau_edge_iff n E H e HwfE HinH HconnH).
      rewrite (tau_edge_iff n E T e HwfE HinSubT HconnT).
      split; intros [v [Hv Heq]]; exists v; split; try exact Hv;
        [rewrite <- Hpar_eq | rewrite Hpar_eq]; assumption.
  Qed.

  (* =======================================================================
     6. Exact Interval Sum Lemma and Penrose Tree-Graph Bound
     ======================================================================= *)

  Lemma fold_right_Rplus_app : forall l1 l2,
    fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
  Proof.
    induction l1 as [| a xs IH]; intro l2; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma fold_right_Rplus_ext : forall {A : Type} (f g : A -> R) (l : list A),
    (forall x, In x l -> f x = g x) ->
    fold_right Rplus 0 (map f l) = fold_right Rplus 0 (map g l).
  Proof.
    induction l as [| a xs IH]; intro Hext; simpl; [reflexivity |].
    rewrite (Hext a (or_introl eq_refl)).
    f_equal. apply IH. intros x Hx. apply Hext. right; exact Hx.
  Qed.

  Lemma fold_right_Rplus_0 : forall {A : Type} (l : list A),
    fold_right Rplus 0 (map (fun _ => 0) l) = 0.
  Proof. induction l; simpl; [reflexivity | rewrite IHl; ring]. Qed.

  Lemma fold_right_Rplus_scale : forall {A : Type} (c : R) (f : A -> R) (l : list A),
    fold_right Rplus 0 (map (fun x => c * f x) l) = c * fold_right Rplus 0 (map f l).
  Proof.
    induction l as [| a xs IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma forallb_ext_in : forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
  Proof.
    induction l as [| a xs IH]; intro Hext; simpl; [reflexivity |].
    rewrite (Hext a (or_introl eq_refl)).
    f_equal. apply IH. intros x Hx. apply Hext; right; exact Hx.
  Qed.

  Lemma sum_sublists_interval : forall (E : list (nat * nat)) (in_T in_M_f : nat * nat -> bool),
    NoDup E ->
    (forall e, In e E -> in_T e = true -> in_M_f e = true) ->
    fold_right Rplus 0
      (map (fun H =>
        if forallb (fun e => negb (in_T e) || edge_mem e H) E && forallb in_M_f H
        then (-1) ^ (length H) else 0) (sublists E)) =
    if existsb (fun e => in_M_f e && negb (in_T e)) E
    then 0
    else (-1) ^ (length (filter in_T E)).
  Proof.
    induction E as [| x xs IH]; intros in_T in_M_f Hnd Himp.
    - simpl. ring.
    - inversion Hnd as [| ? ? Hnot Hnd']; subst.
      assert (Himp' : forall e, In e xs -> in_T e = true -> in_M_f e = true).
      { intros e He Ht. apply Himp; [right; exact He | exact Ht]. }
      simpl sublists. rewrite map_app, fold_right_Rplus_app, map_map.
      (* Simplify predicates on H in sublists xs *)
      assert (Hmem_xs : forall H, In H (sublists xs) -> edge_mem x H = false).
      { intros H Hin. destruct (edge_mem x H) eqn:Ex; [| reflexivity].
        apply edge_mem_iff in Ex. exfalso. apply Hnot. exact (sublists_incl xs H Hin x Ex). }
      assert (Hmem_cons_self : forall H, edge_mem x (x :: H) = true).
      { intro H. apply edge_mem_iff. left; reflexivity. }
      assert (Hmem_cons_other : forall e H, In e xs -> edge_mem e (x :: H) = edge_mem e H).
      { intros e H He. unfold edge_mem; simpl.
        destruct (edge_eqb e x) eqn:Ex; [| reflexivity].
        apply edge_eqb_spec in Ex. subst e. contradiction. }
      assert (Hfor_cons : forall H,
        forallb (fun e => negb (in_T e) || edge_mem e (x :: H)) xs =
        forallb (fun e => negb (in_T e) || edge_mem e H) xs).
      { intro H. apply forallb_ext_in. intros e He. rewrite (Hmem_cons_other e H He). reflexivity. }
      destruct (in_T x) eqn:Htx.
      + (* Case 1: in_T x = true -> in_M_f x = true *)
        assert (Hmx : in_M_f x = true) by (apply Himp; [left; reflexivity | exact Htx]).
        assert (Hpart1 :
          fold_right Rplus 0
            (map (fun H =>
              if forallb (fun e => negb (in_T e) || edge_mem e H) (x :: xs) && forallb in_M_f H
              then (-1) ^ (length H) else 0) (sublists xs)) = 0).
        { transitivity (fold_right Rplus 0 (map (fun _ => 0) (sublists xs)));
            [| apply fold_right_Rplus_0].
          apply fold_right_Rplus_ext. intros H Hin.
          cbn [forallb]. rewrite Htx, (Hmem_xs H Hin). reflexivity. }
        assert (Hpart2 :
          fold_right Rplus 0
            (map (fun H =>
              if forallb (fun e => negb (in_T e) || edge_mem e (x :: H)) (x :: xs) &&
                 forallb in_M_f (x :: H)
              then (-1) ^ (length (x :: H)) else 0) (sublists xs)) =
          (-1) * fold_right Rplus 0
            (map (fun H =>
              if forallb (fun e => negb (in_T e) || edge_mem e H) xs && forallb in_M_f H
              then (-1) ^ (length H) else 0) (sublists xs))).
        { rewrite <- fold_right_Rplus_scale.
          apply fold_right_Rplus_ext. intros H Hin.
          cbn [forallb]. rewrite Htx, Hmx, Hmem_cons_self, Hfor_cons. simpl.
          destruct (forallb (fun e => negb (in_T e) || edge_mem e H) xs && forallb in_M_f H); ring. }
        rewrite Hpart1, Hpart2, (IH in_T in_M_f Hnd' Himp').
        cbn [existsb filter length]. rewrite Htx, andb_false_r. simpl orb.
        destruct (existsb (fun e => in_M_f e && negb (in_T e)) xs); simpl; ring.
      + (* Case 2: in_T x = false *)
        assert (Hpart1 :
          fold_right Rplus 0
            (map (fun H =>
              if forallb (fun e => negb (in_T e) || edge_mem e H) (x :: xs) && forallb in_M_f H
              then (-1) ^ (length H) else 0) (sublists xs)) =
          fold_right Rplus 0
            (map (fun H =>
              if forallb (fun e => negb (in_T e) || edge_mem e H) xs && forallb in_M_f H
              then (-1) ^ (length H) else 0) (sublists xs))).
        { apply fold_right_Rplus_ext. intros H Hin.
          cbn [forallb]. rewrite Htx. reflexivity. }
        destruct (in_M_f x) eqn:Hmx.
        * (* Subcase 2a: in_T x = false, in_M_f x = true -> exact cancellation! *)
          assert (Hpart2 :
            fold_right Rplus 0
              (map (fun H =>
                if forallb (fun e => negb (in_T e) || edge_mem e (x :: H)) (x :: xs) &&
                   forallb in_M_f (x :: H)
                then (-1) ^ (length (x :: H)) else 0) (sublists xs)) =
            (-1) * fold_right Rplus 0
              (map (fun H =>
                if forallb (fun e => negb (in_T e) || edge_mem e H) xs && forallb in_M_f H
                then (-1) ^ (length H) else 0) (sublists xs))).
          { rewrite <- fold_right_Rplus_scale.
            apply fold_right_Rplus_ext. intros H Hin.
            cbn [forallb]. rewrite Htx, Hmx, Hfor_cons. simpl.
            destruct (forallb (fun e => negb (in_T e) || edge_mem e H) xs && forallb in_M_f H); ring. }
          rewrite Hpart1, Hpart2.
          cbn [existsb]. rewrite Htx, Hmx. simpl. ring.
        * (* Subcase 2b: in_T x = false, in_M_f x = false *)
          assert (Hpart2 :
            fold_right Rplus 0
              (map (fun H =>
                if forallb (fun e => negb (in_T e) || edge_mem e (x :: H)) (x :: xs) &&
                   forallb in_M_f (x :: H)
                then (-1) ^ (length (x :: H)) else 0) (sublists xs)) = 0).
          { transitivity (fold_right Rplus 0 (map (fun _ => 0) (sublists xs)));
              [| apply fold_right_Rplus_0].
            apply fold_right_Rplus_ext. intros H Hin.
            cbn [forallb]. rewrite Hmx, andb_false_r. reflexivity. }
          rewrite Hpart1, Hpart2, (IH in_T in_M_f Hnd' Himp').
          cbn [existsb filter]. rewrite Htx, Hmx. simpl.
          destruct (existsb (fun e => in_M_f e && negb (in_T e)) xs); ring.
  Qed.

  (* Double-sum swapping and partition of a sum over a finite list *)
  Lemma fold_right_Rplus_swap : forall {A B : Type} (f : A -> B -> R) (la : list A) (lb : list B),
    fold_right Rplus 0 (map (fun a => fold_right Rplus 0 (map (fun b => f a b) lb)) la) =
    fold_right Rplus 0 (map (fun b => fold_right Rplus 0 (map (fun a => f a b) la)) lb).
  Proof.
    induction la as [| a la' IH]; intro lb; simpl.
    - symmetry. apply fold_right_Rplus_0.
    - rewrite IH. clear IH.
      induction lb as [| b lb' IHb]; simpl; [ring |].
      rewrite <- IHb. ring.
  Qed.

  Lemma fold_right_Rplus_indicator : forall {A : Type} (eqb : A -> A -> bool) (x : A) (v : R) (l : list A),
    (forall a b, eqb a b = true <-> a = b) ->
    NoDup l ->
    fold_right Rplus 0 (map (fun y => if eqb x y then v else 0) l) =
    if existsb (eqb x) l then v else 0.
  Proof.
    induction l as [| a xs IH]; intros Heqb Hnd; simpl; [reflexivity |].
    inversion Hnd as [| ? ? Hnot Hnd']; subst.
    destruct (eqb x a) eqn:Exa.
    - apply Heqb in Exa. subst a.
      assert (Hzero : fold_right Rplus 0 (map (fun y => if eqb x y then v else 0) xs) = 0).
      { transitivity (fold_right Rplus 0 (map (fun _ => 0) xs)); [| apply fold_right_Rplus_0].
        apply fold_right_Rplus_ext. intros y Hy.
        destruct (eqb x y) eqn:Exy; [| reflexivity].
        apply Heqb in Exy. subst y. contradiction. }
      rewrite Hzero. simpl. ring.
    - rewrite (IH Heqb Hnd'). simpl. ring.
  Qed.

  Fixpoint list_edge_eqb (l1 l2 : list (nat * nat)) : bool :=
    match l1, l2 with
    | [], [] => true
    | e1 :: t1, e2 :: t2 => edge_eqb e1 e2 && list_edge_eqb t1 t2
    | _, _ => false
    end.

  Lemma list_edge_eqb_spec : forall l1 l2, list_edge_eqb l1 l2 = true <-> l1 = l2.
  Proof.
    induction l1 as [| e1 t1 IH]; intros [| e2 t2]; simpl;
      try (split; [discriminate | discriminate]).
    - split; reflexivity.
    - rewrite andb_true_iff, edge_eqb_spec, IH. split.
      + intros [-> ->]; reflexivity.
      + intro H; inversion H; split; reflexivity.
  Qed.

  Lemma Rabs_fold_right_Rplus_le : forall {A : Type} (f g : A -> R) (l : list A),
    (forall x, In x l -> Rabs (f x) <= g x) ->
    Rabs (fold_right Rplus 0 (map f l)) <= fold_right Rplus 0 (map g l).
  Proof.
    induction l as [| a xs IH]; intro Hle; simpl.
    - rewrite Rabs_R0. lra.
    - eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat.
      + apply Hle; left; reflexivity.
      + apply IH. intros x Hx. apply Hle; right; exact Hx.
  Qed.

  Lemma fold_right_Rplus_const1 : forall {A : Type} (l : list A),
    fold_right Rplus 0 (map (fun _ => 1) l) = INR (length l).
  Proof.
    induction l as [| a xs IH]; [reflexivity |].
    cbn [map fold_right length]. rewrite IH, S_INR. ring.
  Qed.

  Lemma Rabs_pow_neg1 : forall k, Rabs ((-1) ^ k) = 1.
  Proof.
    induction k as [| k' IH]; simpl.
    - rewrite Rabs_R1. reflexivity.
    - rewrite Rabs_mult, IH. unfold Rabs. destruct (Rcase_abs (-1)); lra.
  Qed.

  (* Main Penrose Theorem for any graph (n, E) *)
  Theorem penrose_tree_graph_bound_graph : forall n E,
    wf_edges n E ->
    Rabs (ursell_graph n E) <= INR (length (spanning_trees n E)).
  Proof.
    intros n E HwfE.
    unfold ursell_graph.
    (* Partition over T in spanning_trees n E via tau n E H *)
    assert (Hpart :
      fold_right Rplus 0
        (map (fun H => if is_connectedb n H then (-1) ^ length H else 0) (sublists E)) =
      fold_right Rplus 0
        (map (fun T =>
          fold_right Rplus 0
            (map (fun H =>
              if is_connectedb n H && list_edge_eqb (tau n E H) T
              then (-1) ^ length H else 0) (sublists E)))
          (spanning_trees n E))).
    { rewrite fold_right_Rplus_swap.
      apply fold_right_Rplus_ext. intros H HinH.
      destruct (is_connectedb n H) eqn:Hconn; simpl.
      - rewrite (fold_right_Rplus_indicator list_edge_eqb (tau n E H) ((-1) ^ length H)
                   (spanning_trees n E) list_edge_eqb_spec
                   (NoDup_filter _ (sublists_NoDup_list E (proj1 HwfE)))).
        assert (HinT : existsb (list_edge_eqb (tau n E H)) (spanning_trees n E) = true).
        { apply existsb_exists. exists (tau n E H). split.
          - exact (tau_is_spanning_tree n E H HwfE HinH Hconn).
          - apply list_edge_eqb_spec. reflexivity. }
        rewrite HinT. reflexivity.
      - symmetry. apply fold_right_Rplus_0. }
    rewrite Hpart.
    rewrite <- (fold_right_Rplus_const1 (spanning_trees n E)).
    apply Rabs_fold_right_Rplus_le.
    intros T HinT.
    (* Replace inner sum condition using penrose_fiber_iff and apply sum_sublists_interval *)
    assert (Hinner :
      fold_right Rplus 0
        (map (fun H =>
          if is_connectedb n H && list_edge_eqb (tau n E H) T
          then (-1) ^ length H else 0) (sublists E)) =
      fold_right Rplus 0
        (map (fun H =>
          if forallb (fun e => negb (edge_mem e T) || edge_mem e H) E && forallb (in_M n T) H
          then (-1) ^ length H else 0) (sublists E))).
    { apply fold_right_Rplus_ext. intros H HinH.
      assert (Hb :
        (is_connectedb n H && list_edge_eqb (tau n E H) T) =
        (forallb (fun e => negb (edge_mem e T) || edge_mem e H) E && forallb (in_M n T) H)).
      { apply eq_true_iff_eq.
        rewrite !andb_true_iff, list_edge_eqb_spec, !forallb_forall.
        rewrite (penrose_fiber_iff n E T H HwfE HinT HinH).
        pose proof HinT as HinT'. unfold spanning_trees in HinT'.
        apply filter_In in HinT'. destruct HinT' as [HinSubT _].
        split; intros [H1 H2]; split.
        - intros e HeE. rewrite orb_true_iff, negb_true_iff, edge_mem_iff.
          destruct (edge_mem e T) eqn:Et; [right; apply H1; apply edge_mem_iff; exact Et | left; reflexivity].
        - exact H2.
        - intros e HeT.
          specialize (H1 e (sublists_incl E T HinSubT e HeT)).
          rewrite orb_true_iff, negb_true_iff, edge_mem_iff in H1.
          destruct H1 as [Hf | Hin]; [apply edge_mem_iff in HeT; congruence | exact Hin].
        - exact H2. }
      rewrite Hb. reflexivity. }
    rewrite Hinner.
    rewrite (sum_sublists_interval E (fun e => edge_mem e T) (in_M n T) (proj1 HwfE)).
    - destruct (existsb (fun e => in_M n T e && negb (edge_mem e T)) E).
      + rewrite Rabs_R0. lra.
      + rewrite Rabs_pow_neg1. lra.
    - intros e HeE Het. apply edge_mem_iff in Het.
      exact (in_M_of_tree_edge n E T e HwfE HinT Het).
  Qed.

  (* Public Penrose Tree-Graph Bound for any polymer tuple X *)
  Theorem penrose_tree_graph_bound : forall {P : Type} (overlap_b : P -> P -> bool) (X : list P),
    Rabs (ursell_fn overlap_b X) <= INR (tree_count overlap_b X).
  Proof.
    intros P ob X. unfold ursell_fn, tree_count.
    apply penrose_tree_graph_bound_graph.
    apply graph_edges_wf.
  Qed.

  (* Disconnected tuples have Ursell weight 0 *)
  Lemma ursell_nonzero_connected : forall {P : Type} (ob : P -> P -> bool) (X : list P),
    ursell_fn ob X <> 0 ->
    is_connectedb (length X) (graph_edges ob X) = true.
  Proof.
    intros P ob X Hnz.
    destruct (is_connectedb (length X) (graph_edges ob X)) eqn:Hc; [reflexivity |].
    exfalso. apply Hnz.
    unfold ursell_fn, ursell_graph.
    transitivity (fold_right Rplus 0 (map (fun _ => 0) (sublists (graph_edges ob X))));
      [| apply fold_right_Rplus_0].
    apply fold_right_Rplus_ext. intros H HinH.
    destruct (is_connectedb (length X) H) eqn:HcH; [| reflexivity].
    pose proof (graph_edges_wf ob X) as [_ HforE].
    pose proof (sublists_Forall _ _ H HforE HinH) as HforH.
    apply (is_connectedb_iff _ _ HforH) in HcH. destruct HcH as [Hn Hreach].
    assert (HconnE : is_connectedb (length X) (graph_edges ob X) = true).
    { apply (is_connectedb_iff _ _ HforE). split; [exact Hn |].
      intros v Hv. eapply reachable_mono; [exact (sublists_incl _ H HinH) | exact (Hreach v Hv)]. }
    congruence.
  Qed.

  (* =======================================================================
     7. Graph Relabeling (Permutation) Invariance of ursell_fn & tree_count
     ======================================================================= *)

  Definition map_edge (sigma : nat -> nat) (e : nat * nat) : nat * nat :=
    mk_edge (sigma (fst e)) (sigma (snd e)).

  Definition relabel_subgraph (sigma : nat -> nat) (E2 H1 : list (nat * nat)) : list (nat * nat) :=
    filter (fun e2 => existsb (fun e1 => edge_eqb (map_edge sigma e1) e2) H1) E2.

  Lemma relabel_in_sublists : forall sigma E2 H1,
    In (relabel_subgraph sigma E2 H1) (sublists E2).
  Proof. intros sigma E2 H1. unfold relabel_subgraph. apply filter_in_sublists. Qed.

  Lemma has_edge_relabel : forall n sigma inv E1 E2 H1 u v,
    wf_edges n E1 -> wf_edges n E2 ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> (inv x < n)%nat) ->
    (forall x, (x < n)%nat -> inv (sigma x) = x) ->
    (forall x, (x < n)%nat -> sigma (inv x) = x) ->
    (forall e1, In e1 E1 -> In (map_edge sigma e1) E2) ->
    In H1 (sublists E1) ->
    (u < n)%nat -> (v < n)%nat ->
    has_edge (relabel_subgraph sigma E2 H1) (sigma u) (sigma v) <-> has_edge H1 u v.
  Proof.
    intros n sigma inv E1 E2 H1 u v Hwf1 Hwf2 Hs Hi His Hsi Hmap Hin1 Hu Hv.
    pose proof (sublists_Forall _ E1 H1 (proj2 Hwf1) Hin1) as Hfor1.
    pose proof (sublists_Forall _ E2 _ (proj2 Hwf2) (relabel_in_sublists sigma E2 H1)) as Hfor2.
    rewrite (wf_has_edge_mk n _ _ _ Hfor2), (wf_has_edge_mk n _ _ _ Hfor1).
    unfold relabel_subgraph. rewrite filter_In, existsb_exists. split.
    - intros [_ [[a b] [Hab Heq]]]. apply edge_eqb_spec in Heq.
      rewrite Forall_forall in Hfor1. pose proof (Hfor1 (a, b) Hab) as Hablt. simpl in Hablt.
      unfold map_edge, mk_edge in Heq; simpl in Heq.
      destruct (Nat.ltb_spec (sigma a) (sigma b));
      destruct (Nat.ltb_spec (sigma u) (sigma v));
      injection Heq as Ha1 Hb1.
      + assert (a = u) by (rewrite <- (His a ltac:(lia)), <- (His u Hu), Ha1; reflexivity).
        assert (b = v) by (rewrite <- (His b ltac:(lia)), <- (His v Hv), Hb1; reflexivity).
        subst a b. unfold mk_edge. destruct (Nat.ltb_spec u v); [exact Hab | lia].
      + assert (a = v) by (rewrite <- (His a ltac:(lia)), <- (His v Hv), Ha1; reflexivity).
        assert (b = u) by (rewrite <- (His b ltac:(lia)), <- (His u Hu), Hb1; reflexivity).
        subst a b. unfold mk_edge. destruct (Nat.ltb_spec u v); [lia | exact Hab].
      + assert (b = u) by (rewrite <- (His b ltac:(lia)), <- (His u Hu), Ha1; reflexivity).
        assert (a = v) by (rewrite <- (His a ltac:(lia)), <- (His v Hv), Hb1; reflexivity).
        subst a b. unfold mk_edge. destruct (Nat.ltb_spec u v); [lia | exact Hab].
      + assert (b = v) by (rewrite <- (His b ltac:(lia)), <- (His v Hv), Ha1; reflexivity).
        assert (a = u) by (rewrite <- (His a ltac:(lia)), <- (His u Hu), Hb1; reflexivity).
        subst a b. unfold mk_edge. destruct (Nat.ltb_spec u v); [exact Hab | lia].
    - intro HinH1.
      assert (Huv_ne : u <> v).
      { intro Heq; subst v. rewrite Forall_forall in Hfor1.
        specialize (Hfor1 (mk_edge u u) HinH1). unfold mk_edge in Hfor1.
        destruct (Nat.ltb_spec u u); simpl in Hfor1; lia. }
      assert (Heq : map_edge sigma (mk_edge u v) = mk_edge (sigma u) (sigma v)).
      { unfold map_edge, mk_edge.
        destruct (Nat.ltb_spec u v); simpl;
        destruct (Nat.ltb_spec (sigma u) (sigma v));
        destruct (Nat.ltb_spec (sigma v) (sigma u)); try reflexivity;
        exfalso; apply Huv_ne; rewrite <- (His u Hu), <- (His v Hv); f_equal; lia. }
      split.
      + rewrite <- Heq. apply Hmap. exact (sublists_incl E1 H1 Hin1 _ HinH1).
      + exists (mk_edge u v). split; [exact HinH1 | apply edge_eqb_spec; exact Heq].
  Qed.

  Lemma relabel_connected_iff : forall n sigma inv E1 E2 H1,
    wf_edges n E1 -> wf_edges n E2 ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> (inv x < n)%nat) ->
    (forall x, (x < n)%nat -> inv (sigma x) = x) ->
    (forall x, (x < n)%nat -> sigma (inv x) = x) ->
    (forall e1, In e1 E1 -> In (map_edge sigma e1) E2) ->
    In H1 (sublists E1) ->
    is_connectedb n (relabel_subgraph sigma E2 H1) = is_connectedb n H1.
  Proof.
    intros n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap Hin1.
    pose proof (sublists_Forall _ E1 H1 (proj2 Hwf1) Hin1) as Hfor1.
    pose proof (sublists_Forall _ E2 _ (proj2 Hwf2) (relabel_in_sublists sigma E2 H1)) as Hfor2.
    apply eq_true_iff_eq.
    rewrite (is_connectedb_iff n _ Hfor2), (is_connectedb_iff n _ Hfor1).
    assert (Hreach_fwd : forall u v, (u < n)%nat -> reachable H1 u v ->
      reachable (relabel_subgraph sigma E2 H1) (sigma u) (sigma v)).
    { intros u v Hu Hr. induction Hr; [apply reach_refl |].
      pose proof (wf_has_edge_lt n H1 u v Hfor1 H) as [_ [Hv _]].
      eapply reach_step; [| exact (IHHr Hv)].
      apply (has_edge_relabel n sigma inv E1 E2 H1 u v Hwf1 Hwf2 Hs Hi His Hsi Hmap Hin1 Hu Hv).
      exact H. }
    assert (Hreach_bwd : forall u v, (u < n)%nat ->
      reachable (relabel_subgraph sigma E2 H1) u v ->
      reachable H1 (inv u) (inv v)).
    { intros u v Hu Hr. induction Hr; [apply reach_refl |].
      pose proof (wf_has_edge_lt n _ u v Hfor2 H) as [_ [Hv _]].
      eapply reach_step; [| exact (IHHr Hv)].
      apply (has_edge_relabel n sigma inv E1 E2 H1 (inv u) (inv v)
               Hwf1 Hwf2 Hs Hi His Hsi Hmap Hin1 (Hi u Hu) (Hi v Hv)).
      rewrite !Hsi; assumption. }
    split; intros [Hn Hr]; split; try exact Hn.
    - intros v Hv.
      assert (H0 : reachable (relabel_subgraph sigma E2 H1) (sigma 0%nat) (sigma v)).
      { eapply reachable_trans; [apply reachable_sym; apply Hr; apply Hs; exact Hn | apply Hr; apply Hs; exact Hv]. }
      pose proof (Hreach_bwd (sigma 0%nat) (sigma v) (Hs 0%nat Hn) H0) as H1'.
      rewrite !His in H1'; try lia; exact H1'.
    - intros v Hv.
      assert (H0 : reachable H1 (inv 0%nat) (inv v)).
      { eapply reachable_trans; [apply reachable_sym; apply Hr; apply Hi; exact Hn | apply Hr; apply Hi; exact Hv]. }
      pose proof (Hreach_fwd (inv 0%nat) (inv v) (Hi 0%nat Hn) H0) as H1'.
      rewrite !Hsi in H1'; try lia; exact H1'.
  Qed.

  Lemma relabel_length : forall n sigma inv E1 E2 H1,
    wf_edges n E1 -> wf_edges n E2 ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> (inv x < n)%nat) ->
    (forall x, (x < n)%nat -> inv (sigma x) = x) ->
    (forall x, (x < n)%nat -> sigma (inv x) = x) ->
    (forall e1, In e1 E1 -> In (map_edge sigma e1) E2) ->
    In H1 (sublists E1) ->
    length (relabel_subgraph sigma E2 H1) = length H1.
  Proof.
    intros n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap Hin1.
    pose proof (sublists_NoDup_elem E1 H1 (proj1 Hwf1) Hin1) as Hnd1.
    pose proof (sublists_Forall _ E1 H1 (proj2 Hwf1) Hin1) as Hfor1.
    assert (Hnd_r : NoDup (relabel_subgraph sigma E2 H1)) by (apply NoDup_filter; exact (proj1 Hwf2)).
    assert (Hnd_m : NoDup (map (map_edge sigma) H1)).
    { apply NoDup_map_in; [exact Hnd1 |].
      intros [a1 b1] [a2 b2] H1' H2' Heq.
      rewrite Forall_forall in Hfor1.
      pose proof (Hfor1 (a1, b1) H1') as L1. pose proof (Hfor1 (a2, b2) H2') as L2. simpl in L1, L2.
      unfold map_edge, mk_edge in Heq; simpl in Heq.
      destruct (Nat.ltb_spec (sigma a1) (sigma b1));
      destruct (Nat.ltb_spec (sigma a2) (sigma b2));
      injection Heq as Ha1 Hb1.
      - assert (a1 = a2) by (rewrite <- (His a1 ltac:(lia)), <- (His a2 ltac:(lia)), Ha1; reflexivity).
        assert (b1 = b2) by (rewrite <- (His b1 ltac:(lia)), <- (His b2 ltac:(lia)), Hb1; reflexivity).
        congruence.
      - assert (a1 = b2) by (rewrite <- (His a1 ltac:(lia)), <- (His b2 ltac:(lia)), Ha1; reflexivity).
        assert (b1 = a2) by (rewrite <- (His b1 ltac:(lia)), <- (His a2 ltac:(lia)), Hb1; reflexivity).
        lia.
      - assert (a1 = b2) by (rewrite <- (His a1 ltac:(lia)), <- (His b2 ltac:(lia)), Hb1; reflexivity).
        assert (b1 = a2) by (rewrite <- (His b1 ltac:(lia)), <- (His a2 ltac:(lia)), Ha1; reflexivity).
        lia.
      - assert (a1 = a2) by (rewrite <- (His a1 ltac:(lia)), <- (His a2 ltac:(lia)), Hb1; reflexivity).
        assert (b1 = b2) by (rewrite <- (His b1 ltac:(lia)), <- (His b2 ltac:(lia)), Ha1; reflexivity).
        congruence. }
    assert (Hincl1 : incl (relabel_subgraph sigma E2 H1) (map (map_edge sigma) H1)).
    { intros e2 He2. unfold relabel_subgraph in He2. apply filter_In in He2.
      destruct He2 as [_ Hex]. apply existsb_exists in Hex.
      destruct Hex as [e1 [He1 Heq]]. apply edge_eqb_spec in Heq. subst e2.
      apply in_map. exact He1. }
    assert (Hincl2 : incl (map (map_edge sigma) H1) (relabel_subgraph sigma E2 H1)).
    { intros e2 He2. apply in_map_iff in He2. destruct He2 as [e1 [<- He1]].
      unfold relabel_subgraph. apply filter_In. split.
      - apply Hmap. exact (sublists_incl E1 H1 Hin1 e1 He1).
      - apply existsb_exists. exists e1. split; [exact He1 | apply edge_eqb_spec; reflexivity]. }
    pose proof (NoDup_incl_length Hnd_r Hincl1) as L1.
    pose proof (NoDup_incl_length Hnd_m Hincl2) as L2.
    rewrite map_length in L1, L2. lia.
  Qed.

  Lemma relabel_roundtrip : forall n sigma inv E1 E2 H1,
    wf_edges n E1 -> wf_edges n E2 ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> (inv x < n)%nat) ->
    (forall x, (x < n)%nat -> inv (sigma x) = x) ->
    (forall x, (x < n)%nat -> sigma (inv x) = x) ->
    (forall e1, In e1 E1 -> In (map_edge sigma e1) E2) ->
    (forall e2, In e2 E2 -> In (map_edge inv e2) E1) ->
    In H1 (sublists E1) ->
    relabel_subgraph inv E1 (relabel_subgraph sigma E2 H1) = H1.
  Proof.
    intros n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hmap2 Hin1.
    pose proof (sublists_Forall _ E1 H1 (proj2 Hwf1) Hin1) as Hfor1.
    apply (sublists_ext E1 _ H1 (proj1 Hwf1) (relabel_in_sublists _ _ _) Hin1).
    intros [u v].
    assert (Hbi : In (u, v) E1 -> (u < v)%nat /\ (v < n)%nat).
    { intro He. pose proof (proj2 Hwf1) as Hf. rewrite Forall_forall in Hf.
      exact (Hf (u, v) He). }
    split.
    - intro Hin.
      assert (HinE : In (u, v) E1) by (exact (sublists_incl E1 _ (relabel_in_sublists _ _ _) _ Hin)).
      pose proof (Hbi HinE) as [Huv Hvn].
      assert (Hedge : has_edge (relabel_subgraph inv E1 (relabel_subgraph sigma E2 H1)) (inv (sigma u)) (inv (sigma v))).
      { rewrite !His; try lia. left; exact Hin. }
      apply (has_edge_relabel n inv sigma E2 E1 (relabel_subgraph sigma E2 H1)
               (sigma u) (sigma v) Hwf2 Hwf1 Hi Hs Hsi His Hmap2 (relabel_in_sublists sigma E2 H1)
               (Hs u ltac:(lia)) (Hs v Hvn)) in Hedge.
      apply (has_edge_relabel n sigma inv E1 E2 H1 u v Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hin1
               ltac:(lia) Hvn) in Hedge.
      apply (wf_has_edge_mk n H1 u v Hfor1) in Hedge.
      unfold mk_edge in Hedge. destruct (Nat.ltb_spec u v); [exact Hedge | lia].
    - intro Hin.
      assert (HinE : In (u, v) E1) by (exact (sublists_incl E1 H1 Hin1 _ Hin)).
      pose proof (Hbi HinE) as [Huv Hvn].
      assert (Hedge : has_edge (relabel_subgraph inv E1 (relabel_subgraph sigma E2 H1)) (inv (sigma u)) (inv (sigma v))).
      { apply (has_edge_relabel n inv sigma E2 E1 (relabel_subgraph sigma E2 H1)
                 (sigma u) (sigma v) Hwf2 Hwf1 Hi Hs Hsi His Hmap2 (relabel_in_sublists sigma E2 H1)
                 (Hs u ltac:(lia)) (Hs v Hvn)).
        apply (has_edge_relabel n sigma inv E1 E2 H1 u v Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hin1
                 ltac:(lia) Hvn).
        left; exact Hin. }
      rewrite !His in Hedge; try lia.
      pose proof (sublists_Forall _ E1 _ (proj2 Hwf1) (relabel_in_sublists inv E1 (relabel_subgraph sigma E2 H1))) as HforR.
      apply (wf_has_edge_mk n _ u v HforR) in Hedge.
      unfold mk_edge in Hedge. destruct (Nat.ltb_spec u v); [exact Hedge | lia].
  Qed.

  Lemma fold_right_Rplus_perm : forall l1 l2,
    Permutation l1 l2 ->
    fold_right Rplus 0 l1 = fold_right Rplus 0 l2.
  Proof.
    intros l1 l2 Hp. induction Hp; simpl; lra.
  Qed.

  Lemma NoDup_Permutation_of_iff : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 <-> In x l2) ->
    Permutation l1 l2.
  Proof.
    intros A l1 l2 Hnd1 Hnd2 Hiff.
    apply NoDup_Permutation; assumption.
  Qed.

  Lemma Permutation_filter_local : forall {A : Type} (f : A -> bool) (l1 l2 : list A),
    Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
  Proof.
    intros A f l1 l2 Hp. induction Hp; simpl.
    - constructor.
    - destruct (f x); [constructor |]; exact IHHp.
    - destruct (f x); destruct (f y); try constructor; apply Permutation_refl.
    - eapply perm_trans; eassumption.
  Qed.

  Theorem graph_iso_ursell_and_trees : forall n sigma inv E1 E2,
    wf_edges n E1 -> wf_edges n E2 ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> (inv x < n)%nat) ->
    (forall x, (x < n)%nat -> inv (sigma x) = x) ->
    (forall x, (x < n)%nat -> sigma (inv x) = x) ->
    (forall e1, In e1 E1 -> In (map_edge sigma e1) E2) ->
    (forall e2, In e2 E2 -> In (map_edge inv e2) E1) ->
    ursell_graph n E1 = ursell_graph n E2 /\
    length (spanning_trees n E1) = length (spanning_trees n E2).
  Proof.
    intros n sigma inv E1 E2 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hmap2.
    set (phi := relabel_subgraph sigma E2).
    set (psi := relabel_subgraph inv E1).
    assert (Hperm : Permutation (map phi (sublists E1)) (sublists E2)).
    { apply NoDup_Permutation_of_iff.
      - apply NoDup_map_in; [apply sublists_NoDup_list; exact (proj1 Hwf1) |].
        intros H1 H2 Hin1 Hin2 Heq.
        rewrite <- (relabel_roundtrip n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hmap2 Hin1).
        rewrite <- (relabel_roundtrip n sigma inv E1 E2 H2 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hmap2 Hin2).
        unfold phi in Heq. rewrite Heq. reflexivity.
      - apply sublists_NoDup_list; exact (proj1 Hwf2).
      - intro H2. split.
        + intro Hin. apply in_map_iff in Hin. destruct Hin as [H1 [<- _]].
          apply filter_in_sublists.
        + intro Hin2. apply in_map_iff. exists (psi H2). split.
          * exact (relabel_roundtrip n inv sigma E2 E1 H2 Hwf2 Hwf1 Hi Hs Hsi His Hmap2 Hmap1 Hin2).
          * apply filter_in_sublists. }
    split.
    - unfold ursell_graph.
      rewrite <- (fold_right_Rplus_perm _ _ (Permutation_map _ Hperm)).
      rewrite map_map.
      apply fold_right_Rplus_ext. intros H1 Hin1.
      unfold phi.
      rewrite (relabel_connected_iff n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hin1).
      rewrite (relabel_length n sigma inv E1 E2 H1 Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hin1).
      reflexivity.
    - unfold spanning_trees.
      assert (HpermT : Permutation (filter (is_treeb n) (map phi (sublists E1)))
                                   (filter (is_treeb n) (sublists E2))).
      { apply Permutation_filter_local. exact Hperm. }
      rewrite <- (Permutation_length HpermT).
      clear HpermT Hperm.
      assert (Hfilt : filter (is_treeb n) (map phi (sublists E1)) =
                      map phi (filter (is_treeb n) (sublists E1))).
      { assert (Hgen : forall l, incl l (sublists E1) ->
          filter (is_treeb n) (map phi l) = map phi (filter (is_treeb n) l)).
        { induction l as [| h t IH]; intro Hincl; simpl; [reflexivity |].
          assert (Hh : In h (sublists E1)) by (apply Hincl; left; reflexivity).
          assert (Htb : is_treeb n (phi h) = is_treeb n h).
          { unfold is_treeb, phi.
            rewrite (relabel_connected_iff n sigma inv E1 E2 h Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hh).
            rewrite (relabel_length n sigma inv E1 E2 h Hwf1 Hwf2 Hs Hi His Hsi Hmap1 Hh).
            reflexivity. }
          rewrite Htb. destruct (is_treeb n h); simpl;
            [f_equal |]; apply IH; intros z Hz; apply Hincl; right; exact Hz. }
        apply Hgen. intros z Hz; exact Hz. }
      rewrite Hfilt, map_length. reflexivity.
  Qed.

End PenroseTreeBound.
