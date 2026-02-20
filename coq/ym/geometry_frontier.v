(* =========================================================================
   geometry_frontier.v - YM Geometry Frontier Interface

   Collects all geometric assumptions that are not discharged in small_field.v:
   - plaquette decidable equality
   - adjacency ("shares edge") structure
   - graph-distance structure
   - distance extraction from connecting clusters

   CONTRACT:
   These are the only geometry assumptions consumed by Phase F
   (`coq/ym/small_field.v`) for the lattice mass-gap pillar.
   ========================================================================= *)

From Coq Require Import Reals Lra List Lia Bool.
Require Import Classical ClassicalEpsilon.
Require Import rg.polymer_types.
Require Import rg.cluster_expansion.

Import ListNotations.

Open Scope R_scope.

(* =========================================================================
   Type-level Path Witness (exported for use across sections)

   A path represented as a list of ALL vertices visited.
   For path p1 -> v1 -> v2 -> ... -> p2, the list is [p1; v1; v2; ...; p2].
   Number of edges = length - 1.

   This is defined outside Section so it's accessible everywhere.
   ========================================================================= *)

Section AdjPathList.
  Context {P : Type} `{ConnectivitySystem P}.

  Inductive adj_path_list : Cluster P -> P -> P -> list P -> Type :=
  | adj_path_single : forall X p,
      In p X -> adj_path_list X p p [p]
  | adj_path_cons : forall X p q r l,
      In p X -> adj p q -> adj_path_list X q r l ->
      adj_path_list X p r (p :: l).

End AdjPathList.

Arguments adj_path_list {P} {_} _ _ _ _.
Arguments adj_path_single {P} {_} _ _ _.
Arguments adj_path_cons {P} {_} _ _ _ _ _ _ _ _.

(* =========================================================================
   Simple Paths and NoDup Machinery

   Key lemmas for the witness axioms:
   1. NoDup + all_in → length bound (pigeonhole) - FULLY PROVED
   2. adj_path_list_all_in - vertices in path are in cluster - FULLY PROVED

   The path witness extraction itself requires either:
   - A constructive BFS on the finite cluster, OR
   - A strengthened connects_dec that returns witnesses

   For now, we prove everything that CAN be proved constructively,
   and the witness extraction remains an interface requirement.
   ========================================================================= *)

Section SimplePathMachinery.
  Context {P : Type} `{ConnectivitySystem P}.
  Variable eq_dec : forall (p1 p2 : P), {p1 = p2} + {p1 <> p2}.

  (* =========================================================================
     1. NoDup utilities
     ========================================================================= *)

  (* Remove first occurrence of x from list *)
  Fixpoint remove_first (x : P) (l : list P) : list P :=
    match l with
    | [] => []
    | h :: t => if eq_dec x h then t else h :: remove_first x t
    end.

  Lemma remove_first_length : forall x l,
    In x l -> (length (remove_first x l) < length l)%nat.
  Proof.
    intros x l. induction l as [|h t IH]; simpl.
    - intros [].
    - destruct (eq_dec x h) as [Heq | Hneq].
      + intros _. lia.
      + intros [Heq | Hin].
        * exfalso. apply Hneq. symmetry. exact Heq.
        * simpl. specialize (IH Hin). lia.
  Qed.

  (* Helper: if x in l and x <> target, then x in (remove_first target l) *)
  Lemma In_remove_first_other : forall target x l,
    In x l -> x <> target -> In x (remove_first target l).
  Proof.
    intros target x l. induction l as [|h t IH]; simpl.
    - intros [].
    - intros Hx Hne.
      destruct (eq_dec target h) as [Hth | Htnh].
      + (* target = h, so remove_first returns t *)
        destruct Hx as [Hxh | Hin].
        * (* Hxh : h = x, Hth : target = h, so x = target *)
          (* Need to prove False from Hne : x <> target *)
          exfalso. apply Hne.
          transitivity h; [symmetry; exact Hxh | symmetry; exact Hth].
        * exact Hin.
      + (* target <> h *)
        destruct Hx as [Hxh | Hin].
        * left. exact Hxh.
        * right. apply IH; assumption.
  Qed.

  (* =========================================================================
     2. NoDup + inclusion → length bound (pigeonhole principle)

     This is the KEY lemma that makes path length bounds work.
     ========================================================================= *)

  Lemma NoDup_incl_length :
    forall (l1 l2 : list P),
      NoDup l1 ->
      (forall x, In x l1 -> In x l2) ->
      (length l1 <= length l2)%nat.
  Proof.
    intros l1. induction l1 as [|h t IH]; simpl.
    - intros l2 _ _. lia.
    - intros l2 Hnodup Hincl.
      inversion Hnodup as [| h' t' Hnotin Hnodup_t]. subst.
      assert (Hh_in : In h l2) by (apply Hincl; left; reflexivity).
      assert (Hlen : (length (remove_first h l2) < length l2)%nat).
      { apply remove_first_length. exact Hh_in. }
      assert (Ht_incl : forall x, In x t -> In x (remove_first h l2)).
      { intros x Hx.
        assert (Hx_l2 : In x l2) by (apply Hincl; right; exact Hx).
        assert (Hx_ne_h : x <> h) by (intro Hxh; subst; contradiction).
        apply In_remove_first_other; assumption. }
      specialize (IH (remove_first h l2) Hnodup_t Ht_incl).
      lia.
  Qed.

  (* =========================================================================
     3. adj_path_list_all_in: path vertices are in cluster
     ========================================================================= *)

  Lemma adj_path_list_all_in_simple :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l -> forall v, In v l -> In v X.
  Proof.
    intros X p1 p2 l Hpath.
    induction Hpath as [X' p Hin | X' p q r l' Hinp Hadj Hrest IH].
    - intros v [Heq | Habs]; [subst; exact Hin | destruct Habs].
    - intros v [Heq | Htail].
      + subst. exact Hinp.
      + apply IH. exact Htail.
  Qed.

  (* =========================================================================
     4. Path length bound: NoDup path in cluster has length <= cluster length

     This is the pigeonhole bound we need for the axiom.
     ========================================================================= *)

  Lemma simple_path_length_bound :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l ->
      NoDup l ->
      (length l <= length X)%nat.
  Proof.
    intros X p1 p2 l Hpath Hnodup.
    apply NoDup_incl_length; [exact Hnodup |].
    intros x Hx.
    exact (adj_path_list_all_in_simple X p1 p2 l Hpath x Hx).
  Qed.

End SimplePathMachinery.

(* =========================================================================
   Loop Erasure: Convert any path to a simple (NoDup) path

   Given adj_path_list X p1 p2 l, we find the LAST occurrence of each vertex
   and skip the intermediate loop. This produces a simple path.

   The algorithm: for each vertex in the path, if it appears later,
   we "fast-forward" to that later occurrence.
   ========================================================================= *)

Section LoopErasure.
  Context {P : Type} `{ConnectivitySystem P}.
  Variable eq_dec : forall (p1 p2 : P), {p1 = p2} + {p1 <> p2}.

  (* Check if x appears in list *)
  Fixpoint mem (x : P) (l : list P) : bool :=
    match l with
    | [] => false
    | h :: t => if eq_dec x h then true else mem x t
    end.

  Lemma mem_In : forall x l, mem x l = true <-> In x l.
  Proof.
    intros x l. induction l as [|h t IH]; simpl.
    - split; [discriminate | intros []].
    - destruct (eq_dec x h) as [Heq | Hne].
      + split; [intros _; left; symmetry; exact Heq | intros _; reflexivity].
      + rewrite IH. split.
        * intros Hin. right. exact Hin.
        * intros [Hhx | Hin]; [exfalso; apply Hne; symmetry; exact Hhx | exact Hin].
  Qed.

  (* Skip to last occurrence: given x and l where x ∈ l, return suffix starting at last x *)
  Fixpoint skip_to_last (x : P) (l : list P) : list P :=
    match l with
    | [] => []
    | h :: t =>
        if eq_dec x h then
          if mem x t then skip_to_last x t else l
        else skip_to_last x t
    end.

  (* Loop erase with fuel: remove all loops by skipping to last occurrence of head *)
  (* Fuel ensures termination - we use length as fuel *)
  Fixpoint loop_erase_fuel (fuel : nat) (l : list P) : list P :=
    match fuel with
    | O => l  (* out of fuel, return as-is *)
    | S fuel' =>
        match l with
        | [] => []
        | h :: t =>
            if mem h t then loop_erase_fuel fuel' (skip_to_last h (h :: t))
            else h :: loop_erase_fuel fuel' t
        end
    end.

  (* With enough fuel (length l), loop_erase_fuel terminates correctly *)
  Definition loop_erase_safe (l : list P) : list P :=
    loop_erase_fuel (length l) l.

  (* Helper: skip_to_last preserves endpoints for paths *)
  Lemma skip_to_last_head : forall x l,
    In x l -> exists t, skip_to_last x l = x :: t.
  Proof.
    intros x l. induction l as [|h t IH]; simpl.
    - intros [].
    - intros Hin.
      destruct (eq_dec x h) as [Heq | Hne].
      + subst. destruct (mem h t) eqn:Hmem.
        * apply IH. apply mem_In. exact Hmem.
        * exists t. reflexivity.
      + destruct Hin as [Hhx | Hin].
        * exfalso. apply Hne. symmetry. exact Hhx.
        * apply IH. exact Hin.
  Qed.

  (* Helper: skip_to_last gives a suffix *)
  Lemma skip_to_last_suffix : forall x l,
    In x l -> exists prefix, l = prefix ++ skip_to_last x l.
  Proof.
    intros x l. induction l as [|h t IH]; simpl.
    - intros [].
    - intros Hin.
      destruct (eq_dec x h) as [Heq | Hne].
      + subst. destruct (mem h t) eqn:Hmem.
        * destruct (IH (proj1 (mem_In h t) Hmem)) as [prefix Hpre].
          exists (h :: prefix). simpl. f_equal. exact Hpre.
        * exists []. reflexivity.
      + destruct Hin as [Hhx | Hin].
        * exfalso. apply Hne. symmetry. exact Hhx.
        * destruct (IH Hin) as [prefix Hpre].
          exists (h :: prefix). simpl. f_equal. exact Hpre.
  Qed.

  (* Helper: skip_to_last is strictly shorter when there's a later occurrence *)
  Lemma skip_to_last_shorter : forall x l,
    mem x l = true ->
    (length (skip_to_last x (x :: l)) < length (x :: l))%nat.
  Proof.
    intros x l Hmem.
    simpl. destruct (eq_dec x x) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
    rewrite Hmem.
    (* skip_to_last x l is a suffix of l, so length <= length l *)
    (* and skip_to_last x (x::l) = skip_to_last x l when mem x l = true *)
    (* Need: length (skip_to_last x l) < S (length l) *)
    (* This follows from skip_to_last being a suffix *)
    destruct (skip_to_last_suffix x l (proj1 (mem_In x l) Hmem)) as [prefix Hpre].
    assert (Hlen : (length l = length prefix + length (skip_to_last x l))%nat).
    { rewrite Hpre at 1. rewrite app_length. reflexivity. }
    lia.
  Qed.

  (* Helper: skip_to_last h (h::t) with mem h t = true simplifies to skip_to_last h t *)
  Lemma skip_to_last_cons_mem_true : forall h t,
    mem h t = true ->
    skip_to_last h (h :: t) = skip_to_last h t.
  Proof.
    intros h t Hmem.
    simpl. destruct (eq_dec h h) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
    rewrite Hmem. reflexivity.
  Qed.

  (* Helper: skip_to_last h (h::t) with mem h t = false is h::t *)
  Lemma skip_to_last_cons_mem_false : forall h t,
    mem h t = false ->
    skip_to_last h (h :: t) = h :: t.
  Proof.
    intros h t Hmem.
    simpl. destruct (eq_dec h h) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
    rewrite Hmem. reflexivity.
  Qed.

  (* Helper: loop_erase_fuel step equations *)
  Lemma loop_erase_fuel_step_mem_true : forall fuel h t,
    mem h t = true ->
    loop_erase_fuel (S fuel) (h :: t) = loop_erase_fuel fuel (skip_to_last h (h :: t)).
  Proof.
    intros fuel h t Hmem.
    simpl. rewrite Hmem. reflexivity.
  Qed.

  Lemma loop_erase_fuel_step_mem_false : forall fuel h t,
    mem h t = false ->
    loop_erase_fuel (S fuel) (h :: t) = h :: loop_erase_fuel fuel t.
  Proof.
    intros fuel h t Hmem.
    simpl. rewrite Hmem. reflexivity.
  Qed.

  (* Helper: any output element comes from the input list *)
  Lemma loop_erase_fuel_In_sublist :
    forall (fuel : nat) (l : list P) (x : P),
      In x (loop_erase_fuel fuel l) ->
      In x l.
  Proof.
    induction fuel as [|fuel IH]; intros l x Hin.
    - (* fuel = 0: returns l unchanged *)
      simpl in Hin. exact Hin.
    - destruct l as [|h t].
      + (* l = [] *)
        simpl in Hin. contradiction.
      + (* l = h :: t *)
        destruct (mem h t) eqn:Hmem.
        * (* cycle case: mem h t = true *)
          rewrite (loop_erase_fuel_step_mem_true fuel h t Hmem) in Hin.
          rewrite (skip_to_last_cons_mem_true h t Hmem) in Hin.
          specialize (IH (skip_to_last h t) x Hin).
          (* Use suffix lemma to lift membership *)
          assert (Hin_t : In h t) by (apply mem_In; exact Hmem).
          destruct (skip_to_last_suffix h t Hin_t) as [pref Heq].
          right. rewrite Heq.
          apply in_or_app. right. exact IH.
        * (* keep-head case: mem h t = false *)
          rewrite (loop_erase_fuel_step_mem_false fuel h t Hmem) in Hin.
          destruct Hin as [Hx | Hx].
          { subst x. left. reflexivity. }
          { right. apply IH. exact Hx. }
  Qed.

  (* Helper: if mem h t = false then h is not in the erased tail *)
  Lemma loop_erase_fuel_mem_false_notin :
    forall (fuel : nat) (h : P) (t : list P),
      mem h t = false ->
      ~ In h (loop_erase_fuel fuel t).
  Proof.
    intros fuel h t Hmem Hin.
    (* output membership implies input membership *)
    assert (Hin_t : In h t).
    { eapply loop_erase_fuel_In_sublist; eauto. }
    (* then mem must be true, contradiction *)
    assert (Hmem_true : mem h t = true).
    { apply (proj2 (mem_In h t)). exact Hin_t. }
    congruence.
  Qed.

  (* NoDup after loop_erase_fuel with sufficient fuel - FULLY PROVED *)
  Lemma loop_erase_fuel_NoDup : forall fuel l,
    (length l <= fuel)%nat ->
    NoDup (loop_erase_fuel fuel l).
  Proof.
    induction fuel as [|fuel IH]; intros l Hlen.
    - (* fuel=0: return l; length l <= 0 means l = [] *)
      simpl. destruct l as [|h t]; simpl in *; try lia.
      constructor.
    - destruct l as [|h t].
      + (* l = [] *)
        simpl. constructor.
      + (* l = h :: t *)
        simpl.
        destruct (mem h t) eqn:Hmem.
        * (* recurse on strictly shorter list *)
          (* Goal: NoDup (loop_erase_fuel fuel (if eq_dec h h then ... else ...)) *)
          destruct (eq_dec h h) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
          (* Goal: NoDup (loop_erase_fuel fuel (skip_to_last h t)) *)
          pose proof (skip_to_last_shorter h t Hmem) as Hlt.
          (* Use helper to simplify skip_to_last h (h :: t) = skip_to_last h t *)
          rewrite (skip_to_last_cons_mem_true h t Hmem) in Hlt.
          (* Hlt: length (skip_to_last h t) < length (h :: t) = S (length t) *)
          simpl in Hlt.
          (* Hlen: S (length t) <= S fuel *)
          simpl in Hlen.
          (* Goal: NoDup (loop_erase_fuel fuel (skip_to_last h t)) *)
          apply IH. lia.
        * (* keep h, recurse on tail *)
          constructor.
          -- apply (loop_erase_fuel_mem_false_notin fuel h t Hmem).
          -- apply IH. simpl in Hlen. lia.
  Qed.

  (* =========================================================================
     Suffix Lemma: suffix of an adj_path_list is an adj_path_list

     Key insight: if l = prefix ++ (q :: suffix) and adj_path_list X p1 p2 l,
     then adj_path_list X q p2 (q :: suffix).
     ========================================================================= *)

  Lemma adj_path_list_suffix :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l ->
      forall prefix q suffix,
        l = prefix ++ (q :: suffix) ->
        adj_path_list X q p2 (q :: suffix).
  Proof.
    intros X p1 p2 l Hpath.
    induction Hpath as [X' p Hin | X' p r s l' Hinp Hadj Hrest IH].
    - (* adj_path_single: l = [p] *)
      intros prefix q suffix Heq.
      destruct prefix as [| h t]; simpl in Heq.
      + (* prefix = [] *)
        injection Heq as Hq Hsuff.
        subst q. destruct suffix; [| discriminate].
        apply adj_path_single. exact Hin.
      + (* prefix = h :: t, impossible since [p] = h :: t ++ q :: suffix *)
        destruct t; simpl in Heq; discriminate.
    - (* adj_path_cons: l = p :: l' *)
      intros prefix q suffix Heq.
      destruct prefix as [| h t]; simpl in Heq.
      + (* prefix = [], so p = q and l' = suffix *)
        injection Heq as Hpq Hl'.
        subst q suffix.
        (* Goal: adj_path_list X' p s (p :: l') *)
        (* We have exactly adj_path_cons evidence *)
        exact (adj_path_cons X' p r s l' Hinp Hadj Hrest).
      + (* prefix = h :: t, so p = h and l' = t ++ q :: suffix *)
        injection Heq as Hph Hl'.
        subst h.
        apply IH with (prefix := t).
        exact Hl'.
  Qed.

  (* Helper: skip_to_last on (h::t) when mem h t gives a list starting with h *)
  Lemma skip_to_last_starts_with_h : forall h t,
    In h t ->
    exists suffix, skip_to_last h (h :: t) = h :: suffix.
  Proof.
    intros h t Hin.
    simpl. destruct (eq_dec h h) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
    destruct (mem h t) eqn:Hmem.
    - (* mem h t = true *)
      apply skip_to_last_head. apply mem_In. exact Hmem.
    - (* mem h t = false, but we have In h t - contradiction *)
      exfalso.
      assert (Hmem_true : mem h t = true) by (apply (proj2 (mem_In h t)); exact Hin).
      congruence.
  Qed.

  (* Computational: skip_to_last with mem=true starts with x *)
  Lemma skip_to_last_head_eq : forall x l,
    mem x l = true ->
    skip_to_last x l = x :: tl (skip_to_last x l).
  Proof.
    intros x l Hmem.
    revert x Hmem.
    induction l as [|h t IH]; intros x Hmem.
    - simpl in Hmem. discriminate.
    - destruct (eq_dec x h) as [Heq | Hne].
      + subst x. destruct (mem h t) eqn:Hmem_t.
        * simpl. destruct (eq_dec h h) as [_ | Habs]; [| exfalso; apply Habs; reflexivity].
          rewrite Hmem_t. apply IH. exact Hmem_t.
        * simpl. destruct (eq_dec h h) as [_ | Habs]; [| exfalso; apply Habs; reflexivity].
          rewrite Hmem_t. simpl. reflexivity.
      + simpl in Hmem. destruct (eq_dec x h) as [Habs | _]; [exfalso; apply Hne; exact Habs |].
        simpl. destruct (eq_dec x h) as [Habs | _]; [exfalso; apply Hne; exact Habs |].
        apply IH. exact Hmem.
  Qed.

  (* Computational prefix: get the prefix of l before skip_to_last x l *)
  Fixpoint prefix_before_last (x : P) (l : list P) : list P :=
    match l with
    | [] => []
    | h :: t =>
        if eq_dec x h then
          if mem x t then h :: prefix_before_last x t else []
        else h :: prefix_before_last x t
    end.

  (* The computational prefix gives the same decomposition *)
  Lemma prefix_before_last_spec : forall x l,
    mem x l = true ->
    l = prefix_before_last x l ++ skip_to_last x l.
  Proof.
    intros x l Hmem.
    revert x Hmem.
    induction l as [|h t IH]; intros x Hmem.
    - (* l = [] *) simpl in Hmem. discriminate.
    - (* l = h :: t *)
      (* First destruct eq_dec, then simplify *)
      destruct (eq_dec x h) as [Heq | Hne].
      + (* x = h *)
        subst x.
        destruct (mem h t) eqn:Hmem_t.
        * (* mem h t = true *)
          simpl. destruct (eq_dec h h) as [_ | Habs]; [| exfalso; apply Habs; reflexivity].
          rewrite Hmem_t. simpl. f_equal. apply IH. exact Hmem_t.
        * (* mem h t = false *)
          simpl. destruct (eq_dec h h) as [_ | Habs]; [| exfalso; apply Habs; reflexivity].
          rewrite Hmem_t. simpl. reflexivity.
      + (* x <> h *)
        (* mem x (h::t) = mem x t when x <> h *)
        simpl in Hmem. destruct (eq_dec x h) as [Habs | _]; [exfalso; apply Hne; exact Habs |].
        (* Now Hmem : mem x t = true *)
        simpl. destruct (eq_dec x h) as [Habs | _]; [exfalso; apply Hne; exact Habs |].
        simpl. f_equal. apply IH. exact Hmem.
  Qed.

  (* Loop erase preserves adj_path_list structure *)
  Lemma loop_erase_fuel_preserves_adj_path :
    forall fuel (X : Cluster P) (p1 p2 : P) (l : list P),
      (length l <= fuel)%nat ->
      adj_path_list X p1 p2 l ->
      adj_path_list X p1 p2 (loop_erase_fuel fuel l).
  Proof.
    induction fuel as [|fuel IH]; intros X p1 p2 l Hlen Hpath.
    - (* fuel = 0, l must be [] *)
      simpl. destruct l; simpl in Hlen; try lia.
      inversion Hpath.
    - destruct l as [|h t].
      + (* l = [], impossible for adj_path_list *)
        simpl. inversion Hpath.
      + (* l = h :: t *)
        destruct (mem h t) eqn:Hmem.
        * (* h appears in t: skip to last occurrence *)
          rewrite (loop_erase_fuel_step_mem_true fuel h t Hmem).
          rewrite (skip_to_last_cons_mem_true h t Hmem).
          (* Goal: adj_path_list X p1 p2 (loop_erase_fuel fuel (skip_to_last h t)) *)
          (* Invert Hpath to extract p1 = h *)
          inversion Hpath as [X' p' Hin' | X' p' q' r' t' Hinp' Hadj' Hrest'].
          -- (* adj_path_single: impossible since t is non-empty (mem h t = true) *)
             (* If [p'] = h :: t, then t = [] which contradicts mem h t = true *)
             subst. simpl in Hmem. discriminate.
          -- (* adj_path_cons: p' = h, so p1 = h *)
             subst.
             (* Now Hpath : adj_path_list X h p2 (h :: t) *)
             (* Use computational head equation *)
             pose proof (skip_to_last_head_eq h t Hmem) as Hskip.
             rewrite Hskip.
             set (suffix := tl (skip_to_last h t)).
             assert (Hdecomp : h :: t = prefix_before_last h (h :: t) ++ (h :: suffix)).
             { unfold suffix.
               simpl. destruct (eq_dec h h) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
               rewrite Hmem.
               simpl. f_equal. rewrite <- Hskip. apply prefix_before_last_spec. exact Hmem. }
             assert (Hsuffix_path : adj_path_list X h p2 (h :: suffix)).
             { apply (adj_path_list_suffix X h p2 (h :: t) Hpath
                       (prefix_before_last h (h :: t)) h suffix).
               exact Hdecomp. }
             apply IH.
             ++ (* length bound *)
                pose proof (skip_to_last_shorter h t Hmem) as Hlt.
                rewrite (skip_to_last_cons_mem_true h t Hmem) in Hlt.
                assert (Hlen_eq : length (h :: suffix) = length (skip_to_last h t)).
                { unfold suffix. rewrite Hskip. reflexivity. }
                rewrite Hlen_eq. simpl in Hlt. simpl in Hlen. lia.
             ++ exact Hsuffix_path.
        * (* h not in t: keep h and recurse on t *)
          rewrite (loop_erase_fuel_step_mem_false fuel h t Hmem).
          inversion Hpath; subst.
          -- (* adj_path_single: [h] path means t = [] *)
             destruct fuel; simpl; apply adj_path_single; assumption.
          -- (* adj_path_cons: we get In h X, adj h q, adj_path_list X q p2 t *)
             eapply adj_path_cons; try eassumption.
             apply IH.
             ++ simpl in Hlen. lia.
             ++ eassumption.
  Qed.

  (* MAIN THEOREM: adj_path_list_loop_erase - FULLY PROVED *)
  Lemma adj_path_list_loop_erase :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l ->
      { l' : list P & (adj_path_list X p1 p2 l' * NoDup l')%type }.
  Proof.
    intros X p1 p2 l Hpath.
    refine (existT _ (loop_erase_fuel (length l) l) _).
    split.
    - apply loop_erase_fuel_preserves_adj_path with (fuel := length l).
      + lia.
      + exact Hpath.
    - apply loop_erase_fuel_NoDup. lia.
  Qed.

End LoopErasure.

(* =========================================================================
   Constructive Path Finding via BFS (Paths-in-Frontier)

   Key insight: each frontier element carries its full path back to source.
   This makes soundness immediate - we directly return a certified path.

   Frontier element: (current_vertex, path_from_source_to_current)
   where the path is stored in reverse (current at head, source at end).
   ========================================================================= *)

Section ConstructivePathFinding.
  Context {P : Type} `{ConnectivitySystem P}.
  Variable eq_dec : forall (p1 p2 : P), {p1 = p2} + {p1 <> p2}.

  (* In_dec from eq_dec *)
  Definition In_dec_from_eq (x : P) (l : list P) : {In x l} + {~ In x l} :=
    in_dec eq_dec x l.

  (* Check if vertex is in visited set *)
  Definition is_visited (v : P) (visited : list P) : bool :=
    existsb (fun w => if eq_dec v w then true else false) visited.

  (* Expand one frontier path to all adjacent unvisited vertices *)
  (* Returns list of (new_vertex, extended_path) pairs *)
  Definition expand_path (cluster : list P) (visited : list P)
                         (current : P) (path : list P) : list (P * list P) :=
    map (fun v => (v, v :: path))
        (filter (fun v =>
           negb (is_visited v visited) &&
           if adj_dec current v then true else false
        ) cluster).

  (* Expand entire frontier *)
  Definition expand_frontier (cluster : list P) (visited : list P)
                             (frontier : list (P * list P)) : list (P * list P) :=
    flat_map (fun vp => expand_path cluster visited (fst vp) (snd vp)) frontier.

  (* Extract visited vertices from frontier *)
  Definition frontier_vertices (frontier : list (P * list P)) : list P :=
    map fst frontier.

  (* BFS with fuel - frontier carries paths *)
  Fixpoint bfs_paths_fuel (fuel : nat) (cluster : list P) (target : P)
                          (visited : list P)
                          (frontier : list (P * list P))
           : option (list P) :=
    match fuel with
    | O => None
    | S fuel' =>
        (* Check if target is in current frontier *)
        match find (fun vp => if eq_dec (fst vp) target then true else false) frontier with
        | Some (_, path) => Some (rev path)  (* Found! Return path *)
        | None =>
            (* Expand frontier *)
            let new_visited := frontier_vertices frontier ++ visited in
            let new_frontier := expand_frontier cluster new_visited frontier in
            match new_frontier with
            | [] => None  (* No progress, target unreachable *)
            | _ => bfs_paths_fuel fuel' cluster target new_visited new_frontier
            end
        end
    end.

  (* Start BFS from source *)
  Definition find_path (cluster : list P) (source target : P) : option (list P) :=
    if eq_dec source target then Some [source]
    else bfs_paths_fuel (length cluster) cluster target [] [(source, [source])].

  (* =========================================================================
     Soundness: the returned path is a valid adj_path_list

     Key invariant: every (v, path) in frontier satisfies:
     1. path is non-empty with head = v
     2. rev path is an adj_path_list from source to v
     3. all vertices in path are in cluster
     ========================================================================= *)

  (* Build adj_path_list from reversed path list *)
  (* rev_path has source at head, current at end *)
  Fixpoint adj_path_list_of_rev (X : Cluster P) (rev_path : list P) : Prop :=
    match rev_path with
    | [] => False
    | [p] => In p X
    | p :: ((q :: _) as rest) => In p X /\ adj p q /\ adj_path_list_of_rev X rest
    end.

  (* Invariant for frontier paths *)
  Definition frontier_path_valid (X : Cluster P) (source : P) (vp : P * list P) : Prop :=
    let (v, path) := vp in
    path <> [] /\
    hd v path = v /\
    (forall x, In x path -> In x X) /\
    (* The reversed path forms a valid adj_path_list structure *)
    match rev path with
    | [] => False
    | s :: _ => s = source
    end.

  (* Helper: if path = [v] and In v X, then adj_path_list X v v [v] *)
  Lemma singleton_path_valid :
    forall X v, In v X -> adj_path_list X v v [v].
  Proof.
    intros X v Hin.
    apply adj_path_single. exact Hin.
  Qed.

  (* Helper: extending a valid path with adjacent vertex *)
  Lemma extend_path_valid :
    forall X p1 p2 l q,
      adj_path_list X p1 p2 l ->
      In q X ->
      adj p2 q ->
      adj_path_list X p1 q (l ++ [q]).
  Proof.
    intros X p1 p2 l q Hpath Hinq Hadj.
    induction Hpath as [X' p Hin | X' p r s l' Hinp Hadj' Hrest IH].
    - (* single: l = [p], p1 = p2 = p, so l ++ [q] = [p; q] *)
      simpl. apply (adj_path_cons X' p q q [q]).
      + exact Hin.
      + exact Hadj.
      + apply adj_path_single. exact Hinq.
    - (* cons: l = p :: l', so l ++ [q] = p :: (l' ++ [q]) *)
      simpl. apply (adj_path_cons X' p r q (l' ++ [q])).
      + exact Hinp.
      + exact Hadj'.
      + exact (IH Hinq Hadj).
  Qed.

  (* Key lemma: extending backward path by cons corresponds to extend_path_valid *)
  (* Path stored as [current; ...; source], so rev gives [source; ...; current] *)
  (* Extending with next :: path gives rev (next :: path) = rev path ++ [next] *)
  Lemma path_extend_via_cons :
    forall X source current (path : list P) next,
      adj_path_list X source current (rev path) ->
      In next X ->
      adj current next ->
      adj_path_list X source next (rev (next :: path)).
  Proof.
    intros X source current path next Hpath Hin Hadj.
    (* rev (next :: path) = rev path ++ [next] by definition of rev *)
    simpl.
    (* Goal: adj_path_list X source next (rev path ++ [next]) *)
    eapply extend_path_valid; eassumption.
  Qed.

  (* =========================================================================
     CERTIFIED BFS - Frontier carries Type-level certificates

     Key insight: store adj_path_list proof directly in frontier entries.
     This makes soundness trivial and avoids Prop→Type elimination.
     ========================================================================= *)

  (* Certified frontier entry: (vertex, reverse_path, proof) *)
  (* path is stored reversed: [current; ...; source] *)
  (* rev path gives the forward path: [source; ...; current] *)
  Definition Cert (X : Cluster P) (source : P) : Type :=
    { vp : P * list P & adj_path_list X source (fst vp) (rev (snd vp)) }.

  (* Extract vertex from cert *)
  Definition cert_vertex {X source} (c : Cert X source) : P :=
    fst (projT1 c).

  (* Extract reverse path from cert *)
  Definition cert_path {X source} (c : Cert X source) : list P :=
    snd (projT1 c).

  (* Extract proof from cert *)
  Definition cert_proof {X source} (c : Cert X source)
    : adj_path_list X source (cert_vertex c) (rev (cert_path c)) :=
    projT2 c.

  (* Build initial certificate for source vertex *)
  Definition initial_cert (X : Cluster P) (source : P) (Hin : In source X)
    : Cert X source :=
    existT _ (source, [source]) (adj_path_single X source Hin).

  (* Expand one certified path to adjacent unvisited vertices *)
  Definition expand_path_cert
    (X : Cluster P) (visited : list P) (source : P)
    (current : P) (path : list P)
    (Hcur : adj_path_list X source current (rev path))
    : list (Cert X source) :=
    (* For each vertex v in cluster that is unvisited and adjacent to current *)
    flat_map (fun v =>
      match In_dec_from_eq v X with
      | left Hin_v =>
          if andb (negb (is_visited v visited))
                  (if adj_dec current v then true else false)
          then
            match adj_dec current v with
            | left Hadj =>
                (* Build cert for (v, v :: path) *)
                (* rev (v :: path) = rev path ++ [v] *)
                let new_proof := path_extend_via_cons X source current path v Hcur Hin_v Hadj in
                [ existT _ (v, v :: path) new_proof ]
            | right _ => []  (* impossible due to boolean check *)
            end
          else []
      | right _ => []  (* v not in cluster, skip *)
      end
    ) X.

  (* Expand entire certified frontier *)
  Definition expand_frontier_cert
    (X : Cluster P) (visited : list P) (source : P)
    (frontier : list (Cert X source)) : list (Cert X source) :=
    flat_map (fun c =>
      let '(existT _ (cur, path) Hcur) := c in
      expand_path_cert X visited source cur path Hcur
    ) frontier.

  (* Extract vertices from certified frontier *)
  Definition frontier_vertices_cert {X source}
    (frontier : list (Cert X source)) : list P :=
    map cert_vertex frontier.

  (* Certified BFS with fuel *)
  Fixpoint bfs_cert_fuel
    (fuel : nat) (X : Cluster P) (target source : P)
    (visited : list P) (frontier : list (Cert X source))
    : option (Cert X source) :=
    match fuel with
    | O => None
    | S fuel' =>
        (* Check if target is in current frontier *)
        match find (fun c => if eq_dec (cert_vertex c) target then true else false)
                   frontier with
        | Some c => Some c  (* Found! Return the certificate *)
        | None =>
            let new_visited := frontier_vertices_cert frontier ++ visited in
            let new_frontier := expand_frontier_cert X new_visited source frontier in
            match new_frontier with
            | [] => None  (* No progress, target unreachable *)
            | _ => bfs_cert_fuel fuel' X target source new_visited new_frontier
            end
        end
    end.

  (* Start certified BFS from source *)
  Definition find_path_cert (X : Cluster P) (source target : P) (Hin : In source X)
    : option (Cert X source) :=
    if eq_dec source target
    then Some (initial_cert X source Hin)
    else bfs_cert_fuel (length X) X target source [] [initial_cert X source Hin].

  (* =========================================================================
     SOUNDNESS: Trivial because certificate contains the proof
     ========================================================================= *)

  Lemma find_path_cert_sound :
    forall (X : Cluster P) (source target : P) (Hin : In source X) (c : Cert X source),
      find_path_cert X source target Hin = Some c ->
      adj_path_list X source (cert_vertex c) (rev (cert_path c)).
  Proof.
    intros X source target Hin c Hfind.
    (* The certificate already contains the proof *)
    exact (cert_proof c).
  Qed.

  (* Helper: bfs_cert_fuel returns cert with matching vertex *)
  Lemma bfs_cert_fuel_vertex :
    forall fuel X target source visited frt c,
      bfs_cert_fuel fuel X target source visited frt = Some c ->
      cert_vertex c = target.
  Proof.
    induction fuel as [| fuel' IH]; intros X target source visited frt c Hfind.
    - simpl in Hfind. discriminate.
    - simpl in Hfind.
      destruct (find _ frt) as [c' |] eqn:Hfind_eq.
      + (* find succeeded *)
        injection Hfind as Hc. subst c'.
        apply find_some in Hfind_eq.
        destruct Hfind_eq as [_ Hpred].
        destruct (eq_dec (cert_vertex c) target) as [Heq' | Hne'].
        * exact Heq'.
        * discriminate.
      + (* find failed, recurse *)
        destruct (expand_frontier_cert _ _ _ frt) as [| x xs] eqn:Hexp.
        * discriminate.
        * apply IH with (visited := frontier_vertices_cert frt ++ visited) (frt := x :: xs).
          exact Hfind.
  Qed.

  (* If BFS succeeds and target not in frontier, expansion must be non-empty *)
  Lemma bfs_cert_success_expansion_nonempty :
    forall fuel X target source visited frontier,
      (fuel >= 1)%nat ->
      find (fun c => if eq_dec (cert_vertex c) target then true else false) frontier = None ->
      bfs_cert_fuel fuel X target source visited frontier <> None ->
      expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier <> [].
  Proof.
    intros fuel X target source visited frontier Hfuel Hfind Hsucc.
    destruct fuel as [|fuel']; [lia|].
    simpl in Hsucc.
    rewrite Hfind in Hsucc.
    destruct (expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier) as [|c cs] eqn:Hexp.
    - (* Expansion empty - then BFS returns None, contradicts Hsucc *)
      exfalso. apply Hsucc. reflexivity.
    - (* Expansion non-empty - done *)
      intro Habs. discriminate.
  Qed.

  (* Certificate vertex matches target *)
  Lemma find_path_cert_target :
    forall (X : Cluster P) (source target : P) (Hin : In source X) (c : Cert X source),
      find_path_cert X source target Hin = Some c ->
      cert_vertex c = target.
  Proof.
    intros X source target Hin c Hfind.
    unfold find_path_cert in Hfind.
    destruct (eq_dec source target) as [Heq | Hne].
    - (* source = target *)
      injection Hfind as Hc. subst c.
      unfold cert_vertex, initial_cert. simpl. exact Heq.
    - (* source <> target: use helper *)
      apply bfs_cert_fuel_vertex with
        (fuel := length X) (X := X) (source := source)
        (visited := []) (frt := [initial_cert X source Hin]).
      exact Hfind.
  Qed.

  (* Combined soundness for certified BFS *)
  Lemma find_path_cert_gives_path :
    forall (X : Cluster P) (source target : P) (Hin : In source X) (c : Cert X source),
      find_path_cert X source target Hin = Some c ->
      adj_path_list X source target (rev (cert_path c)).
  Proof.
    intros X source target Hin c Hfind.
    rewrite <- (find_path_cert_target X source target Hin c Hfind).
    exact (find_path_cert_sound X source target Hin c Hfind).
  Qed.

  (* =========================================================================
     Bridge: Original find_path relates to certified version

     Strategy: Use Forall2 synchronization to track per-element correspondence.
     This is cleaner than map equality because each cert carries its proof.
     ========================================================================= *)

  (* Synchronization relation: each orig pair corresponds to a cert *)
  Definition sync_frontier (X : Cluster P) (source : P)
    (frontier_orig : list (P * list P))
    (frontier_cert : list (Cert X source)) : Prop :=
    Forall2 (fun vp c =>
       cert_vertex c = fst vp /\
       cert_path c = snd vp
    ) frontier_orig frontier_cert.

  (* Forall2 implies map equality (derived) *)
  Lemma sync_frontier_map_fst :
    forall X source frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      map fst frontier_orig = map cert_vertex frontier_cert.
  Proof.
    intros X source fo fc Hsync.
    induction Hsync as [|[v p] c fo' fc' [Hv Hp] _ IH].
    - reflexivity.
    - simpl. rewrite Hv. f_equal. exact IH.
  Qed.

  Lemma sync_frontier_map_snd :
    forall X source frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      map snd frontier_orig = map cert_path frontier_cert.
  Proof.
    intros X source fo fc Hsync.
    induction Hsync as [|[v p] c fo' fc' [Hv Hp] _ IH].
    - reflexivity.
    - simpl. rewrite Hp. f_equal. exact IH.
  Qed.

  (* Generic Forall2 lemma for flat_map synchronization *)
  Lemma Forall2_flat_map_sync :
    forall (A B C : Type) (R : A -> B -> Prop)
           (f : A -> list C) (g : B -> list C)
           (la : list A) (lb : list B),
      Forall2 R la lb ->
      (forall a b, R a b -> f a = g b) ->
      flat_map f la = flat_map g lb.
  Proof.
    intros A B C R f g la lb HF2 Hfg.
    induction HF2 as [|a b la' lb' Hab _ IH].
    - reflexivity.
    - simpl. rewrite (Hfg a b Hab). f_equal. exact IH.
  Qed.

  (* Helper: flat_map with conditional singleton equals map over filter *)
  Lemma flat_map_filter_map :
    forall (A B : Type) (f : A -> B) (pred : A -> bool) (l : list A),
      flat_map (fun a => if pred a then [f a] else []) l =
      map f (filter pred l).
  Proof.
    intros A B f pred l.
    induction l as [|h t IH]; simpl.
    - reflexivity.
    - destruct (pred h) eqn:Hpred; simpl.
      + f_equal. exact IH.
      + exact IH.
  Qed.

  (* Helper: In v X when iterating over X means In_dec succeeds *)
  Lemma In_dec_from_eq_In :
    forall (v : P) (X : list P),
      In v X ->
      exists Hin, In_dec_from_eq v X = left Hin.
  Proof.
    intros v X HIn.
    unfold In_dec_from_eq.
    destruct (in_dec eq_dec v X) as [Hin|Hnot].
    - exists Hin. reflexivity.
    - exfalso. exact (Hnot HIn).
  Qed.

  (* Helper: In_dec_from_eq returns left when element is in list *)
  Lemma In_dec_from_eq_left :
    forall v X, In v X -> exists pf, In_dec_from_eq v X = left pf.
  Proof.
    intros v X Hin.
    unfold In_dec_from_eq.
    destruct (in_dec eq_dec v X) as [pf|Hnot].
    - exists pf. reflexivity.
    - exfalso. exact (Hnot Hin).
  Qed.

  (* Helper: pointwise projection for a single element v in X *)
  Lemma expand_path_projects_elem :
    forall X visited source current path v
           (Hcur : adj_path_list X source current (rev path))
           (Hin : In v X),
      map (fun c => (cert_vertex c, cert_path c))
        (match In_dec_from_eq v X with
         | left Hin_v =>
             if andb (negb (is_visited v visited))
                     (if adj_dec current v then true else false)
             then
               match adj_dec current v with
               | left Hadj =>
                   [existT _ (v, v :: path) (path_extend_via_cons X source current path v Hcur Hin_v Hadj)]
               | right _ => []
               end
             else []
         | right _ => []
         end)
      = if andb (negb (is_visited v visited))
                (if adj_dec current v then true else false)
        then [(v, v :: path)]
        else [].
  Proof.
    intros X visited source current path v Hcur Hin.
    (* Since v ∈ X, In_dec_from_eq v X = left _ *)
    destruct (In_dec_from_eq v X) as [Hin_v|Hnot].
    - (* In_dec returned left - expected case *)
      destruct (andb (negb (is_visited v visited))
                     (if adj_dec current v then true else false)) eqn:Hcond.
      + (* Condition true *)
        destruct (adj_dec current v) as [Hadj|Hnadj].
        * (* Adjacent - produces singleton *)
          simpl. reflexivity.
        * (* Not adjacent but cond true - contradiction *)
          simpl in Hcond.
          destruct (is_visited v visited); simpl in Hcond; discriminate.
      + (* Condition false - produces empty *)
        reflexivity.
    - (* In_dec returned right - contradiction since v ∈ X *)
      exfalso. exact (Hnot Hin).
  Qed.

  (* Helper: flat_map equality when functions agree pointwise on list elements *)
  Lemma flat_map_ext_in :
    forall (A B : Type) (f g : A -> list B) (l : list A),
      (forall a, In a l -> f a = g a) ->
      flat_map f l = flat_map g l.
  Proof.
    intros A B f g l Hfg.
    induction l as [|h t IH]; simpl.
    - reflexivity.
    - rewrite (Hfg h (or_introl eq_refl)).
      f_equal. apply IH.
      intros a Ha. apply Hfg. right. exact Ha.
  Qed.

  (* Helper: map distributes over flat_map *)
  Lemma map_flat_map :
    forall (A B C : Type) (f : B -> C) (g : A -> list B) (l : list A),
      map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
  Proof.
    intros A B C f g l.
    induction l as [|h t IH]; simpl.
    - reflexivity.
    - rewrite map_app. f_equal. exact IH.
  Qed.

  (* Helper: rewrite expand_path as flat_map *)
  Lemma expand_path_as_flat_map :
    forall X visited current path,
      expand_path X visited current path =
      flat_map (fun v =>
        if andb (negb (is_visited v visited))
                (if adj_dec current v then true else false)
        then [(v, v :: path)]
        else []
      ) X.
  Proof.
    intros X visited current path.
    unfold expand_path.
    (* Use flat_map_filter_map in reverse *)
    rewrite flat_map_filter_map.
    reflexivity.
  Qed.

  (* Key lemma: expand_path and expand_path_cert produce the same vertex/path pairs *)
  (* This holds pointwise when we have the cert's proof *)
  Lemma expand_path_projects :
    forall X visited source current path
           (Hcur : adj_path_list X source current (rev path)),
      map (fun c => (cert_vertex c, cert_path c)) (expand_path_cert X visited source current path Hcur)
      = expand_path X visited current path.
  Proof.
    intros X visited source current path Hcur.
    unfold expand_path_cert.
    rewrite expand_path_as_flat_map.
    (* Both are flat_map over X. Need: map proj (flat_map f X) = flat_map g X *)
    (* Use: map f (flat_map g l) = flat_map (fun x => map f (g x)) l *)
    rewrite map_flat_map.
    (* Now both are flat_map over X, need pointwise equality *)
    apply flat_map_ext_in.
    intros v Hin.
    (* Apply pointwise lemma *)
    exact (expand_path_projects_elem X visited source current path v Hcur Hin).
  Qed.

  (* Helper: Forall2 preserved through flat_map when per-element functions produce Forall2 outputs *)
  Lemma Forall2_flat_map :
    forall (A B C D : Type) (R : A -> B -> Prop) (S : C -> D -> Prop)
           (f : A -> list C) (g : B -> list D)
           (la : list A) (lb : list B),
      Forall2 R la lb ->
      (forall a b, R a b -> Forall2 S (f a) (g b)) ->
      Forall2 S (flat_map f la) (flat_map g lb).
  Proof.
    intros A B C D R S f g la lb HF2 Hfg.
    induction HF2 as [|a b la' lb' Hab _ IH].
    - (* Base case: empty lists *)
      simpl. constructor.
    - (* Inductive case: a::la', b::lb' *)
      simpl. apply Forall2_app.
      + exact (Hfg a b Hab).
      + exact IH.
  Qed.

  (* Helper: convert (v, path) to sync relation with cert *)
  Lemma expand_path_produces_sync :
    forall X visited source current path
           (Hcur : adj_path_list X source current (rev path)),
      Forall2 (fun vp c => cert_vertex c = fst vp /\ cert_path c = snd vp)
        (expand_path X visited current path)
        (expand_path_cert X visited source current path Hcur).
  Proof.
    intros X visited source current path Hcur.
    (* Use expand_path_projects: map proj certs = orig
       So the lists have same length and corresponding elements match *)
    pose proof (expand_path_projects X visited source current path Hcur) as Hproj.
    (* Build Forall2 from the projection equality *)
    remember (expand_path X visited current path) as orig.
    remember (expand_path_cert X visited source current path Hcur) as certs.
    clear Heqorig Heqcerts.
    revert orig Hproj.
    induction certs as [|c certs' IH]; intros orig Hproj.
    - (* certs = [] *)
      simpl in Hproj. symmetry in Hproj. subst orig. constructor.
    - (* certs = c :: certs' *)
      destruct orig as [|vp orig'].
      + (* orig = [] but certs <> [] - contradiction *)
        simpl in Hproj. discriminate.
      + (* orig = vp :: orig' *)
        simpl in Hproj. injection Hproj as Hvp Hrest.
        constructor.
        * (* Show cert_vertex c = fst vp /\ cert_path c = snd vp *)
          split.
          -- (* cert_vertex c = fst vp *)
             destruct vp as [v pth]. simpl in Hvp.
             injection Hvp as Hv Hp. simpl. exact Hv.
          -- (* cert_path c = snd vp *)
             destruct vp as [v pth]. simpl in Hvp.
             injection Hvp as Hv Hp. simpl. exact Hp.
        * (* Forall2 on tails *)
          exact (IH orig' Hrest).
  Qed.

  (* Synchronization preserved by expand_frontier *)
  Lemma expand_frontier_sync :
    forall X visited source frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      sync_frontier X source
        (expand_frontier X visited frontier_orig)
        (expand_frontier_cert X visited source frontier_cert).
  Proof.
    intros X visited source frontier_orig frontier_cert Hsync.
    unfold sync_frontier in *.
    unfold expand_frontier, expand_frontier_cert.
    (* Apply Forall2_flat_map *)
    apply Forall2_flat_map with
      (R := fun vp c => cert_vertex c = fst vp /\ cert_path c = snd vp).
    - exact Hsync.
    - (* Show per-element expansion preserves sync *)
      intros vp c [Hv Hp].
      (* Extract cert fields *)
      destruct c as [[cur pth] Hcur]. simpl in Hv, Hp.
      (* Hv : cur = fst vp, Hp : pth = snd vp *)
      (* Use rewrite instead of subst to handle dependency *)
      rewrite <- Hv, <- Hp.
      (* Now need: Forall2 ... (expand_path X visited cur pth) (expand_path_cert X visited source cur pth Hcur) *)
      exact (expand_path_produces_sync X visited source cur pth Hcur).
  Qed.

  (* Find returns something if target is in frontier vertices *)
  (* Uses sigma type (Type) instead of exists (Prop) to allow case analysis *)
  (* Key: iterate over list using decidable eq_dec, avoiding Prop elimination *)
  Fixpoint find_cert_with_vertex
    (X : Cluster P) (source target : P)
    (frontier_cert : list (Cert X source))
    : option (Cert X source) :=
    match frontier_cert with
    | [] => None
    | c :: rest =>
        if eq_dec (cert_vertex c) target
        then Some c
        else find_cert_with_vertex X source target rest
    end.

  Lemma find_cert_with_vertex_spec :
    forall (X : Cluster P) (source target : P) (frontier_cert : list (Cert X source)) c,
      find_cert_with_vertex X source target frontier_cert = Some c ->
      cert_vertex c = target.
  Proof.
    intros X source target fc c.
    induction fc as [|h t IH]; simpl.
    - discriminate.
    - destruct (eq_dec (cert_vertex h) target) as [Heq|Hne].
      + intro Hsome. injection Hsome as Hc. subst c. exact Heq.
      + exact IH.
  Qed.

  Lemma find_cert_eq_find :
    forall (X : Cluster P) (source target : P) (frontier_cert : list (Cert X source)),
      find_cert_with_vertex X source target frontier_cert =
      find (fun c0 => if eq_dec (cert_vertex c0) target then true else false) frontier_cert.
  Proof.
    intros X source target fc.
    induction fc as [|h t IH]; simpl.
    - reflexivity.
    - destruct (eq_dec (cert_vertex h) target) as [Heq|Hne].
      + reflexivity.
      + exact IH.
  Qed.

  Lemma find_cert_complete :
    forall (X : Cluster P) (source target : P) (frontier_cert : list (Cert X source)),
      In target (frontier_vertices_cert frontier_cert) ->
      find_cert_with_vertex X source target frontier_cert <> None.
  Proof.
    intros X source target fc Hin.
    induction fc as [|h t IH]; simpl.
    - (* Empty - contradiction via In *)
      unfold frontier_vertices_cert in Hin. simpl in Hin. contradiction.
    - destruct (eq_dec (cert_vertex h) target) as [Heq|Hne].
      + discriminate.
      + apply IH. unfold frontier_vertices_cert in Hin. simpl in Hin.
        destruct Hin as [Hh | Hin_t].
        * exfalso. apply Hne. exact Hh.
        * exact Hin_t.
  Qed.

  (* Helper: find in Forall2-related lists returns corresponding elements *)
  Lemma find_Forall2_correspond :
    forall (X : Cluster P) (source : P)
           (fo : list (P * list P)) (fc : list (Cert X source))
           (target : P) (path : list P) (c : Cert X source),
      Forall2 (fun vp c => cert_vertex c = fst vp /\ cert_path c = snd vp) fo fc ->
      find (fun vp => if eq_dec (fst vp) target then true else false) fo = Some (target, path) ->
      find (fun c0 => if eq_dec (cert_vertex c0) target then true else false) fc = Some c ->
      cert_path c = path.
  Proof.
    intros X source fo fc target path c HF2 Hfind_orig Hfind_cert.
    (* The find functions find the first matching element.
       Forall2 says fo and fc have same length and element-wise correspondence.
       If fo has (target, path) at index i, then fc has some c' at index i with
       cert_vertex c' = target and cert_path c' = path.
       Since find returns the FIRST match, and the lists have corresponding
       first-matches (same index), we get the same path. *)
    revert fc c HF2 Hfind_cert.
    induction fo as [|[v p] fo' IH]; intros fc c HF2 Hfind_cert.
    - (* fo = [] *)
      simpl in Hfind_orig. discriminate.
    - (* fo = (v, p) :: fo' *)
      inversion HF2 as [|vp' c' fo'' fc' [Hcv Hcp] HF2' Hfo Hfc]; subst.
      simpl in *. destruct (eq_dec v target) as [Heq|Hne].
      + (* v = target: first element matches in orig *)
        subst v. injection Hfind_orig as Hpath. subst p.
        (* In cert, cert_vertex c' = target by Hcv, so find returns c' *)
        rewrite Hcv in Hfind_cert.
        destruct (eq_dec target target) as [_|Habs]; [|exfalso; exact (Habs eq_refl)].
        injection Hfind_cert as Hc. subst c.
        (* cert_path c' = path follows from Hcp *)
        simpl in Hcp. exact Hcp.
      + (* v <> target: recurse *)
        (* cert_vertex c' = v <> target, so find skips c' *)
        rewrite Hcv in Hfind_cert.
        destruct (eq_dec v target) as [Habs|_]; [exfalso; exact (Hne Habs)|].
        exact (IH Hfind_orig fc' c HF2' Hfind_cert).
  Qed.

  (* Main lemma: find succeeds for target in frontier *)
  Lemma find_in_frontier :
    forall (X : Cluster P) (source target : P) (frontier_cert : list (Cert X source)),
      In target (frontier_vertices_cert frontier_cert) ->
      { c : Cert X source |
        find (fun c0 => if eq_dec (cert_vertex c0) target then true else false)
             frontier_cert = Some c /\
        cert_vertex c = target }.
  Proof.
    intros X source target fc Hin.
    (* Use find_cert_with_vertex which we can case-analyze (option is Type) *)
    pose proof (find_cert_complete X source target fc Hin) as Hne.
    destruct (find_cert_with_vertex X source target fc) as [c|] eqn:Hfind.
    - exists c. split.
      + rewrite <- find_cert_eq_find. exact Hfind.
      + exact (find_cert_with_vertex_spec X source target fc c Hfind).
    - exfalso. apply Hne. reflexivity.
  Qed.

  (* Bridge lemma using sync_frontier *)
  Lemma bfs_sync :
    forall fuel X target source visited frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      (forall l, bfs_paths_fuel fuel X target visited frontier_orig = Some l ->
        { c : Cert X source |
          bfs_cert_fuel fuel X target source visited frontier_cert = Some c /\
          rev (cert_path c) = l /\ cert_vertex c = target }).
  Proof.
    induction fuel as [|fuel' IH]; intros X target source visited fo fc Hsync l Hsome.
    - simpl in Hsome. discriminate.
    - simpl in Hsome.
      destruct (find (fun vp => if eq_dec (fst vp) target then true else false) fo)
        as [[v path]|] eqn:Hfind_orig.
      + (* find succeeded in original *)
        injection Hsome as Hl. subst l.
        (* Get the predicate info - but keep Hfind_orig equation *)
        pose proof (find_some _ _ Hfind_orig) as [Hin_orig Hpred].
        simpl in Hpred. destruct (eq_dec v target) as [Heq|Hne]; [|discriminate].
        subst v.
        (* target is in frontier_orig, so it's in frontier_vertices_cert *)
        assert (Hin_cert : In target (frontier_vertices_cert fc)).
        { unfold frontier_vertices_cert.
          rewrite <- (sync_frontier_map_fst X source fo fc Hsync).
          apply in_map_iff. exists (target, path). split; [reflexivity | exact Hin_orig]. }
        destruct (find_in_frontier X source target fc Hin_cert) as [c [Hfind_cert Hcv]].
        exists c.
        simpl. rewrite Hfind_cert.
        split; [reflexivity|].
        split.
        * (* rev (cert_path c) = rev path *)
          (* Use find_Forall2_correspond to show cert_path c = path *)
          f_equal.
          exact (find_Forall2_correspond X source fo fc target path c Hsync Hfind_orig Hfind_cert).
        * exact Hcv.
      + (* find failed, recurse *)
        (* Need to show certified BFS also recurses with synchronized expanded frontier *)
        simpl.
        (* In cert version, find also fails since frontiers are synchronized *)
        assert (Hfind_cert_none :
          find (fun c0 => if eq_dec (cert_vertex c0) target then true else false) fc = None).
        { (* If find succeeded in fc, then target would be in frontier_vertices_cert,
             which means target is in frontier_vertices fo (by sync),
             which means find would succeed in fo - contradiction with Hfind_orig = None *)
          destruct (find (fun c0 => if eq_dec (cert_vertex c0) target then true else false) fc)
            as [c|] eqn:Hfc; [|reflexivity].
          exfalso.
          apply find_some in Hfc. destruct Hfc as [Hin_c Hpred_c].
          simpl in Hpred_c. destruct (eq_dec (cert_vertex c) target) as [Heq_c|]; [|discriminate].
          (* c is in fc with cert_vertex c = target *)
          (* So target is in frontier_vertices fo *)
          assert (Hin_fo : In target (frontier_vertices fo)).
          { unfold frontier_vertices.
            rewrite (sync_frontier_map_fst X source fo fc Hsync).
            unfold frontier_vertices_cert.
            apply in_map_iff. exists c. split; [exact Heq_c | exact Hin_c]. }
          unfold frontier_vertices in Hin_fo.
          apply in_map_iff in Hin_fo.
          destruct Hin_fo as [[v' p'] [Hv' Hin']].
          simpl in Hv'. subst v'.
          (* Now find in fo should succeed - but Hfind_orig says None *)
          pose proof (find_none _ _ Hfind_orig (target, p') Hin') as Hpred_none.
          simpl in Hpred_none. destruct (eq_dec target target); [discriminate | contradiction]. }
        rewrite Hfind_cert_none.
        (* frontier_vertices fo = frontier_vertices_cert fc by sync *)
        pose proof (sync_frontier_map_fst X source fo fc Hsync) as Hfv_eq.
        unfold frontier_vertices, frontier_vertices_cert in Hfv_eq.
        (* Hsome has a match on expand_frontier. Need to destruct to extract the BFS equation. *)
        (* Remember the expansion result for rewriting *)
        remember (expand_frontier X (frontier_vertices fo ++ visited) fo) as exp_orig eqn:Hexp.
        destruct exp_orig as [|x xs].
        * (* Expansion empty - contradiction with Hsome *)
          discriminate.
        * (* Expansion non-empty - Hsome now has the right type *)
          (* Now both recurse. Need sync on expanded frontiers *)
          pose proof (expand_frontier_sync X (frontier_vertices fo ++ visited) source fo fc Hsync) as Hsync'.
          rewrite <- Hexp in Hsync'.
          (* Also need to destruct cert expansion to eliminate match in goal *)
          assert (Hfv_eq' : frontier_vertices fo = frontier_vertices_cert fc).
          { unfold frontier_vertices, frontier_vertices_cert. exact Hfv_eq. }
          (* Rewrite the frontier_vertices in expand_frontier_cert *)
          (* Use sync to show exp_cert is non-empty when exp_orig is non-empty *)
          assert (Hexp_cert_eq : expand_frontier_cert X (frontier_vertices fo ++ visited) source fc =
                                 expand_frontier_cert X (frontier_vertices_cert fc ++ visited) source fc).
          { rewrite Hfv_eq'. reflexivity. }
          (* Convert Hsync' to use frontier_vertices_cert fc *)
          rewrite Hexp_cert_eq in Hsync'.
          remember (expand_frontier_cert X (frontier_vertices_cert fc ++ visited) source fc) as exp_cert eqn:Hexp_cert.
          destruct exp_cert as [|c' cs].
          -- (* Cert expansion empty - contradiction with sync *)
             (* Hsync' says (x::xs) and [] are Forall2-related - impossible *)
             (* After destruct, Hsync' : sync_frontier X source (x::xs) [] *)
             pose proof (Forall2_length Hsync') as Hlen.
             simpl in Hlen. discriminate.
          -- (* Cert expansion non-empty *)
             (* After destruct, goal has c' :: cs which simplifies the match *)
             simpl.
             (* Apply IH *)
             pose proof (IH X target source (frontier_vertices_cert fc ++ visited)
                           (x :: xs) (c' :: cs)) as IH'.
             (* Need: sync_frontier for (x::xs) and (c'::cs) *)
             (* After destruct, Hsync' already has the concrete terms *)
             specialize (IH' Hsync').
             (* Need: bfs_paths_fuel for (x::xs) *)
             assert (Hsome' : bfs_paths_fuel fuel' X target (frontier_vertices_cert fc ++ visited) (x :: xs) = Some l).
             { rewrite <- Hfv_eq'. exact Hsome. }
             exact (IH' l Hsome').
  Qed.

  (* Reverse sync: if original BFS returns None, certified BFS also returns None *)
  Lemma bfs_sync_None :
    forall fuel X target source visited frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      bfs_paths_fuel fuel X target visited frontier_orig = None ->
      bfs_cert_fuel fuel X target source visited frontier_cert = None.
  Proof.
    induction fuel as [|fuel' IH]; intros X target source visited fo fc Hsync Hnone.
    - reflexivity.
    - simpl in Hnone. simpl.
      (* Case: find in original frontier *)
      destruct (find (fun vp => if eq_dec (fst vp) target then true else false) fo)
        as [[v path]|] eqn:Hfind_orig.
      + (* find succeeded - but then original BFS would return Some, contradiction *)
        discriminate.
      + (* find failed in original *)
        (* By sync, find also fails in certified frontier *)
        assert (Hfind_cert :
          find (fun c => if eq_dec (cert_vertex c) target then true else false) fc = None).
        { destruct (find (fun c => if eq_dec (cert_vertex c) target then true else false) fc)
            as [c|] eqn:Hfc.
          - (* find succeeded in certified - derive contradiction *)
            apply find_some in Hfc. destruct Hfc as [Hin_c Hpred_c].
            simpl in Hpred_c.
            destruct (eq_dec (cert_vertex c) target) as [Hcv|Hcv]; [|discriminate].
            (* cert_vertex c = target, so target is in frontier_vertices fo *)
            (* By sync, map fst fo = map cert_vertex fc = frontier_vertices_cert fc *)
            assert (Hin_fo : In target (map fst fo)).
            { rewrite (sync_frontier_map_fst X source fo fc Hsync).
              apply in_map_iff. exists c. split; [exact Hcv | exact Hin_c]. }
            apply in_map_iff in Hin_fo.
            destruct Hin_fo as [[v' p'] [Hv' Hin_v']].
            simpl in Hv'. subst v'.
            (* But then find should have found it in original *)
            pose proof (find_none _ _ Hfind_orig (target, p') Hin_v') as Hpred'.
            simpl in Hpred'.
            destruct (eq_dec target target); [discriminate | contradiction].
          - reflexivity. }
        rewrite Hfind_cert.
        (* The key insight: expanded frontiers remain synchronized *)
        (* frontier_vertices fo = frontier_vertices_cert fc by sync *)
        pose proof (sync_frontier_map_fst X source fo fc Hsync) as Hfv_eq.
        unfold frontier_vertices, frontier_vertices_cert in Hfv_eq.
        assert (Hfv : frontier_vertices fo = frontier_vertices_cert fc).
        { unfold frontier_vertices, frontier_vertices_cert. exact Hfv_eq. }
        (* Hnone tells us the original BFS continued with expansion *)
        (* Destruct the original expansion result *)
        remember (expand_frontier X (frontier_vertices fo ++ visited) fo) as exp_orig eqn:Hexp_orig.
        destruct exp_orig as [|x xs].
        * (* Original expansion empty - original BFS returns None *)
          (* Show certified expansion is also empty by sync *)
          pose proof (expand_frontier_sync X (frontier_vertices fo ++ visited) source fo fc Hsync) as Hsync'.
          rewrite <- Hexp_orig in Hsync'.
          (* Certified expansion with frontier_vertices_cert fc = frontier_vertices fo (by Hfv) *)
          rewrite <- Hfv.
          destruct (expand_frontier_cert X (frontier_vertices fo ++ visited) source fc) as [|c' cs'] eqn:Hexp_cert.
          -- (* Cert expansion empty - goal is None = None *)
             reflexivity.
          -- (* Cert expansion non-empty - contradiction with Hsync' *)
             (* Hsync' : sync_frontier _ _ [] (c' :: cs') - length mismatch *)
             apply Forall2_length in Hsync'. simpl in Hsync'. discriminate.
        * (* Original expansion non-empty - apply IH *)
          (* Show certified expansion is also non-empty and synchronized *)
          pose proof (expand_frontier_sync X (frontier_vertices fo ++ visited) source fo fc Hsync) as Hsync'.
          rewrite <- Hexp_orig in Hsync'.
          (* Certified expansion *)
          rewrite <- Hfv.
          destruct (expand_frontier_cert X (frontier_vertices fo ++ visited) source fc) as [|c' cs'] eqn:Hexp_cert.
          -- (* Cert expansion empty - contradiction with sync *)
             (* Hsync' : sync_frontier _ _ (x::xs) [] - length mismatch *)
             apply Forall2_length in Hsync'. simpl in Hsync'. discriminate.
          -- (* Cert expansion non-empty - use IH *)
             simpl.
             (* Apply IH with synchronized expanded frontiers *)
             apply IH with (frontier_orig := x :: xs).
             ++ (* Show sync *)
                exact Hsync'.
             ++ (* Show original BFS with expansion returns None *)
                (* Hnone has the match, after destruct it's the recursive result *)
                exact Hnone.
  Qed.

  (* Key corollary: if cert BFS <> None, then orig BFS <> None *)
  Lemma bfs_nonNone_from_cert :
    forall fuel X target source visited frontier_orig frontier_cert,
      sync_frontier X source frontier_orig frontier_cert ->
      bfs_cert_fuel fuel X target source visited frontier_cert <> None ->
      bfs_paths_fuel fuel X target visited frontier_orig <> None.
  Proof.
    intros fuel X target source visited fo fc Hsync Hcert_nonNone.
    intro Horig_None.
    apply Hcert_nonNone.
    exact (bfs_sync_None fuel X target source visited fo fc Hsync Horig_None).
  Qed.

  (* Initial frontier is synchronized *)
  Lemma initial_sync :
    forall X source (Hin : In source X),
      sync_frontier X source [(source, [source])] [initial_cert X source Hin].
  Proof.
    intros X source Hin.
    constructor.
    - split; reflexivity.
    - constructor.
  Qed.

  (* The path found by find_path is valid, given membership *)
  Lemma find_path_sound :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      In p1 X ->
      find_path X p1 p2 = Some l ->
      adj_path_list X p1 p2 l.
  Proof.
    intros X p1 p2 l Hin1 Hfind.
    unfold find_path in Hfind.
    destruct (eq_dec p1 p2) as [Heq | Hne].
    - (* p1 = p2 *)
      injection Hfind as Hl. subst l p2.
      apply adj_path_single. exact Hin1.
    - (* p1 <> p2: Use bridge to certified BFS *)
      (* Initial frontiers are synchronized *)
      pose proof (initial_sync X p1 Hin1) as Hsync.
      destruct (bfs_sync (length X) X p2 p1 [] _ _ Hsync l Hfind)
        as [c [Hc [Hpath Htarget]]].
      rewrite <- Hpath, <- Htarget.
      exact (cert_proof c).
  Qed.

  (* =========================================================================
     COMPLETENESS: BFS finds target if path exists

     Strategy: Show BFS visits all reachable vertices within fuel = |X| steps.
     Key invariant: after k steps, all vertices at path-distance ≤ k from source
     are either visited or in frontier.
     ========================================================================= *)

  (* Helper: BFS never returns None if target is in frontier (with enough fuel) *)
  Lemma bfs_finds_in_frontier :
    forall (bfs_fuel : nat) X target visited frontier,
      (bfs_fuel >= 1)%nat ->
      In target (frontier_vertices frontier) ->
      bfs_paths_fuel bfs_fuel X target visited frontier <> None.
  Proof.
    induction bfs_fuel as [| bfs_fuel' IH]; intros X target visited frontier Hn Hin.
    - lia.
    - simpl.
      destruct (find _ frontier) as [[v path] |] eqn:Hfind.
      + discriminate.
      + (* find didn't find target, but target is in frontier - contradiction *)
        exfalso.
        (* If target is in frontier_vertices, then some (target, _) is in frontier *)
        unfold frontier_vertices in Hin.
        apply in_map_iff in Hin.
        destruct Hin as [[v' p'] [Hv' Hin']].
        simpl in Hv'. subst v'.
        (* But then find should have found it *)
        (* Use find_none to show contradiction *)
        assert (Hfind' : forall x, In x frontier ->
                  (fun vp => if eq_dec (fst vp) target then true else false) x = false).
        { apply find_none. exact Hfind. }
        specialize (Hfind' (target, p') Hin').
        simpl in Hfind'.
        destruct (eq_dec target target) as [_ | Hne]; [discriminate | contradiction].
  Qed.

  (* =========================================================================
     BFS Completeness via Path Length

     Key insight: BFS explores level by level. If there's a path of length k,
     target is found within k iterations. Since any simple path in cluster X
     has length <= |X|, fuel = |X| suffices.
     ========================================================================= *)

  (* Helper: adj_path_list always has length >= 1 *)
  Lemma adj_path_list_length_ge_1 :
    forall X source target l,
      adj_path_list X source target l -> (length l >= 1)%nat.
  Proof.
    intros X source target l Hpath.
    destruct Hpath; simpl; lia.
  Qed.

  (* Helper: the source vertex of an adj_path_list is in the cluster *)
  Lemma adj_path_list_source_in_X :
    forall X source target l,
      adj_path_list X source target l -> In source X.
  Proof.
    intros X source target l Hpath.
    destruct Hpath as [X' p Hin | X' p q r l' Hin Hadj Hpath'].
    - exact Hin.
    - exact Hin.
  Qed.

  (* Helper: adj_path_list step inversion - if length > 1, extract the step *)
  (* Returns Type-level witness since adj_path_list is Type *)
  Definition adj_path_list_step_inv :
    forall X v target l,
      adj_path_list X v target l ->
      ((v = target) * (l = [target]))%type +
      { w : P & { l' : list P &
        (adj v w * adj_path_list X w target l' * (l = v :: l') * In v X)%type }}.
  Proof.
    intros X v target l Hpath.
    destruct Hpath as [X' p Hin | X' p q r l' Hin Hadj Hpath'].
    - left. split; reflexivity.
    - right. exists q, l'. repeat split; assumption.
  Defined.

  (* Helper: if w is in frontier_vertices but find returns None, contradiction *)
  Lemma find_cert_by_vertex_complete :
    forall (X : Cluster P) (source : P) (l : list (Cert X source)) (w : P),
      In w (frontier_vertices_cert l) ->
      find (fun c => if eq_dec (cert_vertex c) w then true else false) l = None ->
      False.
  Proof.
    intros X source l.
    unfold frontier_vertices_cert.
    induction l as [|c_h l_t IHl]; intros w Hin Hfind.
    - simpl in Hin. contradiction.
    - simpl in Hin. destruct Hin as [Heq | Htail].
      + (* w = cert_vertex c_h *)
        simpl in Hfind.
        destruct (eq_dec (cert_vertex c_h) w) as [_|Hne].
        * discriminate Hfind.
        * exfalso. apply Hne. exact Heq.
      + (* In w (map cert_vertex l_t) *)
        simpl in Hfind.
        destruct (eq_dec (cert_vertex c_h) w) as [_|Hne].
        * discriminate Hfind.
        * apply IHl with w; assumption.
  Qed.

  (* Helper: certified BFS finds target if it's in frontier *)
  Lemma bfs_cert_finds_in_frontier :
    forall fuel X target source visited frontier,
      (fuel >= 1)%nat ->
      In target (frontier_vertices_cert frontier) ->
      bfs_cert_fuel fuel X target source visited frontier <> None.
  Proof.
    intros fuel X target source visited frontier Hfuel Hin.
    destruct fuel as [|fuel']; [lia|].
    simpl.
    (* Target is in frontier vertices, so find succeeds *)
    destruct (find (fun c => if eq_dec (cert_vertex c) target then true else false)
                   frontier) as [c|] eqn:Hfind.
    - (* Found - BFS returns Some *)
      discriminate.
    - (* find returned None but target in frontier - contradiction *)
      exfalso.
      (* Get cert with target vertex from frontier *)
      unfold frontier_vertices_cert in Hin.
      apply in_map_iff in Hin.
      destruct Hin as [c [Hcv Hin_c]].
      (* find_none says all elements fail predicate *)
      pose proof (find_none _ _ Hfind c Hin_c) as Hpred.
      simpl in Hpred.
      rewrite Hcv in Hpred.
      destruct (eq_dec target target); [discriminate | contradiction].
  Qed.

  (* Helper: is_visited reflects In membership *)
  Lemma is_visited_true_iff :
    forall w visited, is_visited w visited = true <-> In w visited.
  Proof.
    intros w visited.
    unfold is_visited.
    rewrite existsb_exists.
    split.
    - intros [x [Hin Heq]].
      destruct (eq_dec w x) as [Hwx|Hne]; [|discriminate].
      subst x. exact Hin.
    - intro Hin. exists w. split; [exact Hin|].
      destruct (eq_dec w w) as [_|Hne]; [reflexivity | exfalso; exact (Hne eq_refl)].
  Qed.

  (* Key lemma: expanding frontier adds adjacent unvisited vertices *)
  Lemma expand_frontier_cert_has_neighbor :
    forall X visited source frontier c w,
      In c frontier ->
      adj (cert_vertex c) w ->
      In w X ->
      ~ In w visited ->
      In w (frontier_vertices_cert (expand_frontier_cert X visited source frontier)).
  Proof.
    intros X visited source frontier c w Hin_c Hadj Hin_w Hnot_visited.
    unfold frontier_vertices_cert, expand_frontier_cert.
    rewrite map_flat_map.
    apply in_flat_map.
    exists c. split; [exact Hin_c|].
    (* Show w appears in expand_path_cert for c *)
    destruct c as [[v path] Hcur]. simpl in Hadj.
    unfold expand_path_cert.
    rewrite map_flat_map.
    apply in_flat_map.
    exists w. split.
    - (* w is in X, so In w X *)
      exact Hin_w.
    - (* Show w passes filter and produces [w] after map *)
      destruct (In_dec_from_eq w X) as [Hin_w'|Hnot_w].
      + (* In_dec succeeds *)
        (* Check the condition: unvisited and adjacent *)
        assert (Hcond_true : negb (is_visited w visited) && (if adj_dec v w then true else false) = true).
        { apply Bool.andb_true_iff. split.
          - (* w not visited *)
            destruct (is_visited w visited) eqn:Hvis.
            + exfalso. apply is_visited_true_iff in Hvis. exact (Hnot_visited Hvis).
            + reflexivity.
          - (* adj v w *)
            destruct (adj_dec v w) as [_|Hnadj].
            + reflexivity.
            + exfalso. exact (Hnadj Hadj). }
        rewrite Hcond_true.
        destruct (adj_dec v w) as [Hadj'|Hnadj].
        * simpl. left. reflexivity.
        * exfalso. exact (Hnadj Hadj).
      + (* In_dec fails - contradiction with Hin_w *)
        exfalso. exact (Hnot_w Hin_w).
  Qed.

  (* BFS invariant: all neighbors of visited vertices in X are in frontier ∪ visited *)
  Definition bfs_invariant (X : Cluster P) {source : P}
    (frontier : list (Cert X source)) (visited : list P) : Prop :=
    forall v w, In v visited -> adj v w -> In w X ->
      In w (frontier_vertices_cert frontier ++ visited).

  (* Empty visited trivially satisfies the invariant *)
  Lemma bfs_invariant_empty :
    forall X source (frontier : list (Cert X source)),
      bfs_invariant X frontier [].
  Proof.
    intros X source frontier v w Hv_vis _ _.
    (* visited = [], so In v [] is False *)
    inversion Hv_vis.
  Qed.

  (* Type-level witness for shorter path from frontier vertex *)
  Definition shorter_path_witness (X : Cluster P) (source : P)
    (frontier : list (Cert X source)) (target : P) (len : nat) : Type :=
    { c : Cert X source &
      { l' : list P &
        (In c frontier * adj_path_list X (cert_vertex c) target l' * (length l' < len)%nat)%type }}.

  (* Key lemma: If BFS invariant holds and there's a path from visited vertex to target,
     and target is not in frontier ∪ visited, then we can find a frontier vertex
     with a strictly shorter path to target.
     This lemma handles the "path through visited" case.
     Returns Type-level witness to avoid universe issues with adj_path_list. *)
  Lemma visited_path_shorter :
    forall X source (frontier : list (Cert X source)) visited v target l,
      bfs_invariant X frontier visited ->
      In v visited ->
      adj_path_list X v target l ->
      ~ In target (frontier_vertices_cert frontier ++ visited) ->
      shorter_path_witness X source frontier target (length l).
  Proof.
    intros X source frontier visited v target l Hinv Hv_vis Hpath Ht_not_in.
    (* Induction on the path length *)
    remember (length l) as n eqn:Hlen.
    generalize dependent l. generalize dependent v.
    induction n as [|n' IHn]; intros v Hv_vis l Hpath Hlen.
    - (* n = 0, so length l = 0 - impossible, adj_path_list requires length >= 1 *)
      pose proof (adj_path_list_length_ge_1 X v target l Hpath) as Hge1.
      exfalso. lia.
    - (* n = S n' *)
      (* Decompose the path: either v = target or there's a step *)
      destruct (adj_path_list_step_inv X v target l Hpath) as [[Hv_eq _] | [w [l' [[[Hadj Hpath'] Hl_eq] Hv_in]]]].
      + (* v = target - contradiction with Ht_not_in *)
        exfalso. apply Ht_not_in. apply in_or_app. right. rewrite <- Hv_eq. exact Hv_vis.
      + (* Path v -> w -> ... -> target *)
        (* w is a neighbor of visited v, so w is in frontier ∪ visited by invariant *)
        assert (Hw_in_X : In w X) by (apply adj_path_list_source_in_X with target l'; exact Hpath').
        pose proof (Hinv v w Hv_vis Hadj Hw_in_X) as Hw_fr_vis.
        (* Use find to constructively locate w in frontier *)
        remember (find (fun c => if eq_dec (cert_vertex c) w then true else false) frontier) as find_w eqn:Hfind_w.
        destruct find_w as [c_found | ].
        * (* Found certificate for w in frontier *)
          symmetry in Hfind_w.
          apply find_some in Hfind_w. destruct Hfind_w as [Hc_in Hpred].
          simpl in Hpred. destruct (eq_dec (cert_vertex c_found) w) as [Hc_eq | Hc_ne]; [|discriminate].
          exists c_found, l'. split; [split|].
          -- exact Hc_in.
          -- rewrite Hc_eq. exact Hpath'.
          -- (* length l' < length l *)
             rewrite Hlen. rewrite Hl_eq. simpl. lia.
        * (* w not found in frontier by find - must be in visited *)
          symmetry in Hfind_w.
          assert (Hw_not_fr : ~ In w (frontier_vertices_cert frontier)).
          { intro Hw_fr. unfold frontier_vertices_cert in Hw_fr.
            apply in_map_iff in Hw_fr. destruct Hw_fr as [cx [Hcx_eq Hcx_in]].
            pose proof (find_none _ _ Hfind_w cx Hcx_in) as Hpred.
            simpl in Hpred. rewrite Hcx_eq in Hpred.
            destruct (eq_dec w w) as [_|Hne]; [discriminate | contradiction]. }
          assert (Hw_vis : In w visited).
          { apply in_app_or in Hw_fr_vis.
            destruct Hw_fr_vis as [Hw_fr | Hw_vis]; [contradiction | exact Hw_vis]. }
          assert (Hlen' : (length l' = n')%nat).
          { rewrite Hl_eq in Hlen. simpl in Hlen. lia. }
          assert (Hpath'_len : shorter_path_witness X source frontier target (length l')).
          { rewrite Hlen'. apply (IHn w Hw_vis l' Hpath' (eq_sym Hlen')). }
          destruct Hpath'_len as [c [l'' [[Hc_in Hpath''] Hlen'']]].
          exists c, l''. split; [split|].
          -- exact Hc_in.
          -- exact Hpath''.
          -- (* length l'' < length l' < length l *)
             rewrite Hlen. rewrite Hl_eq. simpl. lia.
  Qed.

  (* BFS invariant is preserved by expansion *)
  (* New visited = frontier_vertices ++ old visited *)
  (* New frontier = expand_frontier_cert X new_visited source frontier *)
  Lemma bfs_invariant_preserved :
    forall X source (frontier : list (Cert X source)) visited,
      bfs_invariant X frontier visited ->
      let new_visited := frontier_vertices_cert frontier ++ visited in
      let new_frontier := expand_frontier_cert X new_visited source frontier in
      bfs_invariant X new_frontier new_visited.
  Proof.
    intros X source frontier visited Hinv new_visited new_frontier.
    unfold bfs_invariant.
    intros v w Hv_new_vis Hadj Hw_in_X.
    (* v is in new_visited = frontier_vertices_cert frontier ++ visited *)
    apply in_app_or in Hv_new_vis.
    destruct Hv_new_vis as [Hv_in_fr | Hv_in_old].
    - (* v was in old frontier_vertices *)
      (* w is adjacent to v, which was in old frontier *)
      (* Either w is in new_visited, or w is in new_frontier (added by expansion) *)
      unfold frontier_vertices_cert in Hv_in_fr.
      apply in_map_iff in Hv_in_fr.
      destruct Hv_in_fr as [cv [Hcv_eq Hcv_in]].
      (* cv is a certificate in old frontier with cert_vertex cv = v *)
      destruct (In_dec eq_dec w new_visited) as [Hw_vis | Hw_fresh].
      + (* w already in new_visited *)
        apply in_or_app. right. exact Hw_vis.
      + (* w is fresh - it will be added to new_frontier *)
        apply in_or_app. left.
        rewrite <- Hcv_eq in Hadj.
        apply expand_frontier_cert_has_neighbor with cv; auto.
    - (* v was in old visited *)
      (* By old invariant, w is in old_frontier ∪ old_visited *)
      (* old_frontier ⊆ new_visited, old_visited ⊆ new_visited *)
      (* So w is in new_visited *)
      pose proof (Hinv v w Hv_in_old Hadj Hw_in_X) as Hw_old.
      apply in_or_app. right.
      (* w is in frontier_vertices_cert frontier ++ visited *)
      (* which equals new_visited *)
      exact Hw_old.
  Qed.

  (* Reachability witness for BFS completeness - uses sigma types *)
  Definition frontier_reaches (X : Cluster P) (source : P)
    (frontier_cert : list (Cert X source)) (target : P) (path_len : nat) : Type :=
    { c : Cert X source &
      { l : list P &
        (In c frontier_cert *
         adj_path_list X (cert_vertex c) target l *
         (length l <= S path_len)%nat)%type }}.

  (* Certified BFS completeness: if path exists with length <= fuel, BFS finds it *)
  (* We prove this for certified BFS first, then derive for original *)
  (* Note: fuel >= 1 required since bfs_cert_fuel 0 always returns None *)
  (* The BFS invariant ensures paths through visited vertices lead to shorter paths from frontier *)
  Lemma bfs_cert_complete_aux :
    forall (path_len : nat) fuel X target source visited
           (frontier_cert : list (Cert X source)),
      (path_len < fuel)%nat ->  (* Changed from <= to < to ensure fuel >= 1 *)
      (* Target reachable from some frontier vertex in path_len steps *)
      frontier_reaches X source frontier_cert target path_len ->
      ~ In target visited ->
      (* BFS invariant: neighbors of visited vertices are in frontier ∪ visited *)
      bfs_invariant X frontier_cert visited ->
      bfs_cert_fuel fuel X target source visited frontier_cert <> None.
  Proof.
    (* Induction on path_len with generalized fuel *)
    induction path_len as [|path_len' IH]; intros fuel X target source visited frontier Hfuel Hreach Hnot_vis Hinv.
    - (* Base case: path_len = 0, target reachable in 0 steps means target is in frontier *)
      (* Hfuel : 0 < fuel, so fuel >= 1 *)
      destruct fuel as [|fuel']; [lia|].
      destruct Hreach as [c [l [[Hin_c Hpath] Hlen]]].
      (* length l <= 1 and adj_path_list means l = [target] and cert_vertex c = target *)
      pose proof (adj_path_list_length_ge_1 X (cert_vertex c) target l Hpath) as Hlen1.
      assert (Hlen_eq : length l = 1%nat) by lia.
      destruct l as [|v l']; [simpl in Hlen_eq; lia|].
      destruct l' as [|]; [|simpl in Hlen_eq; lia].
      (* l = [v], so adj_path_list X (cert_vertex c) target [v] *)
      (* This means v = target = cert_vertex c *)
      destruct (adj_path_list_step_inv X (cert_vertex c) target [v] Hpath) as [Hbase | Hstep].
      + (* Single vertex case *)
        destruct Hbase as [Heq_c Heq_l].
        apply bfs_cert_finds_in_frontier; [lia | ].
        rewrite <- Heq_c.
        unfold frontier_vertices_cert. apply in_map_iff.
        exists c. split; [reflexivity | exact Hin_c].
      + (* Step case: impossible - lengths don't match *)
        destruct Hstep as [w [l'' [[[Hadj Hpath'] Heq_l] Hin_v]]].
        (* From Heq_l: [v] = cert_vertex c :: l'', so length [v] = length (cert_vertex c :: l'') *)
        (* length [v] = 1, length (cert_vertex c :: l'') = 1 + length l'' *)
        (* So length l'' = 0, but adj_path_list requires length l'' >= 1 *)
        pose proof (adj_path_list_length_ge_1 X w target l'' Hpath') as Hlen''.
        assert (Habs : length l'' = 0%nat).
        { assert (H_len_eq_1 : length [v] = length (cert_vertex c :: l'')) by (rewrite Heq_l; reflexivity).
          simpl in H_len_eq_1. lia. }
        lia.

    - (* Inductive case: path_len = S path_len' *)
      destruct Hreach as [c [l [[Hin_c Hpath] Hlen]]].
      (* Either target is directly reachable (in frontier) or we need to step *)
      destruct (adj_path_list_step_inv X (cert_vertex c) target l Hpath) as [[Heq_v Heq_l] | [w [l' [[[Hadj Hpath'] Heq_l] Hin_v]]]].

      + (* cert_vertex c = target - target already in frontier *)
        (* Heq_v : cert_vertex c = target *)
        assert (Hin_target : In target (frontier_vertices_cert frontier)).
        { unfold frontier_vertices_cert. apply in_map_iff.
          exists c. split; [exact Heq_v | exact Hin_c]. }
        apply bfs_cert_finds_in_frontier; [lia | exact Hin_target].

      + (* There's a step: adj (cert_vertex c) w, adj_path_list X w target l' *)
        (* l = cert_vertex c :: l', so length l' = length l - 1 *)
        assert (Hlen' : le (length l') (S path_len')) by (rewrite Heq_l in Hlen; simpl in Hlen; lia).

        (* We need: fuel >= 1 to take a BFS step *)
        destruct fuel as [|fuel']; [lia|].
        simpl.

        (* Check if target in current frontier *)
        destruct (find (fun c0 => if eq_dec (cert_vertex c0) target then true else false) frontier) as [cfound|] eqn:Hfind.
        * (* Found target - done *)
          discriminate.
        * (* Not found - need to expand and recurse *)
          (* Derive In w X from adj_path_list *)
          assert (Hin_w : In w X) by (apply adj_path_list_source_in_X with target l'; exact Hpath').

          (* Case split: is w in the extended visited set? *)
          destruct (In_dec eq_dec w (frontier_vertices_cert frontier ++ visited)) as [Hw_vis | Hw_fresh].

          -- (* w is in frontier_vertices ++ visited *)
             (* Sub-case: w in frontier_vertices OR w in visited *)
             apply in_app_or in Hw_vis.
             destruct Hw_vis as [Hw_frontier | Hw_visited].

             ++ (* w is in frontier_vertices_cert frontier *)
                (* There exists c' in frontier with cert_vertex c' = w *)
                unfold frontier_vertices_cert in Hw_frontier.
                apply in_map_iff in Hw_frontier.
                destruct Hw_frontier as [c_w [Hcw_eq Hcw_in]].
                (* c_w is in frontier, cert_vertex c_w = w *)
                (* We have path from w to target of length l' *)
                (* Check if w = target (then target in frontier - contradiction with Hfind) *)
                destruct (eq_dec w target) as [Hw_target | Hw_not_target].
                ** (* w = target - but then target is in frontier, contradiction *)
                   (* Hw_target : w = target, Hcw_eq : cert_vertex c_w = w *)
                   assert (Hcw_target : cert_vertex c_w = target) by (rewrite <- Hw_target; exact Hcw_eq).
                   exfalso.
                   pose proof (find_none _ _ Hfind c_w Hcw_in) as Hpred.
                   simpl in Hpred.
                   rewrite Hcw_target in Hpred.
                   destruct (eq_dec target target) as [_|Hne]; [discriminate | contradiction].
                ** (* w ≠ target - use c_w with path l' *)
                   (* c_w has cert_vertex c_w = w, path from w to target is l' *)
                   (* This gives frontier_reaches with path_len' *)
                   (* But we can't directly use IH because we need to recurse *)
                   (* For now: the expansion will still find w's neighbors *)
                   (* Key insight: we can use c_w directly if we continue BFS *)
                   (* Since target wasn't found in current frontier, we must continue *)
                   remember (expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier) as new_frontier eqn:Hnf.
                   destruct new_frontier as [|c'' cs'] eqn:Hnf'.
                   --- (* Empty expansion - derive contradiction *)
                       exfalso.
                       (* Since w ≠ target, decompose path to get next vertex *)
                       destruct (adj_path_list_step_inv X w target l' Hpath') as [[Heq_w _] | [next [l'' [[[Hadj_next Hpath''] Heq_l''] _]]]].
                       +++ (* w = target - direct contradiction *)
                           apply Hw_not_target. exact Heq_w.
                       +++ (* There's a step w -> next *)
                           assert (Hin_next : In next X) by (apply adj_path_list_source_in_X with target l''; exact Hpath'').
                           (* Check if next is in visited set for expansion *)
                           destruct (In_dec eq_dec next (frontier_vertices_cert frontier ++ visited)) as [Hnext_vis | Hnext_fresh].
                           *** (* next in frontier_vertices ++ visited *)
                               apply in_app_or in Hnext_vis.
                               destruct Hnext_vis as [Hnext_frontier | Hnext_visited].
                               ---- (* next in frontier_vertices - there's a shorter path *)
                                    (* Get certificate c_next for next *)
                                    unfold frontier_vertices_cert in Hnext_frontier.
                                    apply in_map_iff in Hnext_frontier.
                                    destruct Hnext_frontier as [c_next [Hcnext_eq Hcnext_in]].
                                    (* Build frontier_reaches with path_len' *)
                                    assert (Hreach' : frontier_reaches X source frontier target path_len').
                                    { exists c_next. exists l''.
                                      split; [split|].
                                      - exact Hcnext_in.
                                      - rewrite Hcnext_eq. exact Hpath''.
                                      - (* length l'' <= S path_len' *)
                                        rewrite Heq_l'' in Hlen'. simpl in Hlen'. lia. }
                                    (* Apply IH to get bfs_cert_fuel fuel' ... <> None *)
                                    assert (Hsucc : bfs_cert_fuel fuel' X target source visited frontier <> None).
                                    { apply IH; [lia | exact Hreach' | exact Hnot_vis | exact Hinv]. }
                                    (* BFS succeeds, so expansion is non-empty *)
                                    assert (Hexp_nonempty : expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier <> []).
                                    { apply bfs_cert_success_expansion_nonempty with fuel' target; [lia | exact Hfind | exact Hsucc]. }
                                    (* But expansion is empty - contradiction *)
                                    exfalso. apply Hexp_nonempty. symmetry. exact Hnf.
                               ---- (* next in visited - use visited_path_shorter *)
                                    (* Target not in frontier ++ visited *)
                                    assert (Ht_not_in : ~ In target (frontier_vertices_cert frontier ++ visited)).
                                    { intro Habs. apply in_app_or in Habs.
                                      destruct Habs as [Ht_fr | Ht_vis].
                                      - unfold frontier_vertices_cert in Ht_fr.
                                        apply in_map_iff in Ht_fr.
                                        destruct Ht_fr as [ct [Hct_eq Hct_in]].
                                        pose proof (find_none _ _ Hfind ct Hct_in) as Hpred.
                                        simpl in Hpred. rewrite Hct_eq in Hpred.
                                        destruct (eq_dec target target); [discriminate | contradiction].
                                      - exact (Hnot_vis Ht_vis). }
                                    (* Get shorter path from frontier via visited_path_shorter *)
                                    pose proof (visited_path_shorter X source frontier visited next target l'' Hinv Hnext_visited Hpath'' Ht_not_in) as Hshorter.
                                    destruct Hshorter as [c_short [l_short [[Hcs_in Hpath_short] Hlen_short]]].
                                    (* Build frontier_reaches with shorter path *)
                                    assert (Hreach' : frontier_reaches X source frontier target path_len').
                                    { exists c_short. exists l_short.
                                      split; [split|].
                                      - exact Hcs_in.
                                      - exact Hpath_short.
                                      - (* length l_short < length l'' <= S path_len' *)
                                        rewrite Heq_l'' in Hlen'. simpl in Hlen'. lia. }
                                    (* Apply IH to get BFS success *)
                                    assert (Hsucc : bfs_cert_fuel fuel' X target source visited frontier <> None).
                                    { apply IH; [lia | exact Hreach' | exact Hnot_vis | exact Hinv]. }
                                    (* BFS succeeds, so expansion non-empty *)
                                    assert (Hexp_nonempty : expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier <> []).
                                    { apply bfs_cert_success_expansion_nonempty with fuel' target; [lia | exact Hfind | exact Hsucc]. }
                                    (* Contradiction with Hnf (empty expansion) *)
                                    exfalso. apply Hexp_nonempty. symmetry. exact Hnf.
                           *** (* next is fresh - contradicts empty expansion *)
                               assert (Hin_exp : In next (frontier_vertices_cert (expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier))).
                               { apply expand_frontier_cert_has_neighbor with c_w.
                                 - exact Hcw_in.
                                 - rewrite Hcw_eq. exact Hadj_next.
                                 - exact Hin_next.
                                 - exact Hnext_fresh. }
                               (* Hnf : [] = expand_frontier_cert ..., so rewrite directly *)
                               rewrite <- Hnf in Hin_exp.
                               simpl in Hin_exp. exact Hin_exp.
                   --- (* Non-empty expansion - check if target in new frontier first *)
                       destruct (In_dec eq_dec target (frontier_vertices_cert (c'' :: cs'))) as [Htarget_new | Htarget_not_new].
                       +++ (* target IS in new frontier - BFS finds it directly *)
                           apply bfs_cert_finds_in_frontier; [lia | exact Htarget_new].
                       +++ (* target NOT in new frontier - apply IH *)
                           assert (Hnot_vis_ext : ~ In target (frontier_vertices_cert frontier ++ visited)).
                           { intro Habs. apply in_app_or in Habs. destruct Habs as [Ht_fr | Ht_vis].
                             - unfold frontier_vertices_cert in Ht_fr.
                               apply in_map_iff in Ht_fr.
                               destruct Ht_fr as [ct [Hct_eq Hct_in]].
                               pose proof (find_none _ _ Hfind ct Hct_in) as Hpred.
                               simpl in Hpred. rewrite Hct_eq in Hpred.
                               destruct (eq_dec target target); [discriminate | contradiction].
                             - exact (Hnot_vis Ht_vis). }
                           (* Need the preserved invariant for the new frontier/visited *)
                           (* After destruct, Hnf has form: c'' :: cs' = expand_frontier_cert ... *)
                           assert (Hinv_new : bfs_invariant X (c'' :: cs') (frontier_vertices_cert frontier ++ visited)).
                           { pose proof (bfs_invariant_preserved X source frontier visited Hinv) as Hinv_pres.
                             unfold bfs_invariant in Hinv_pres |- *.
                             intros v' w' Hv'_in Hadj' Hw'_in.
                             specialize (Hinv_pres v' w' Hv'_in Hadj' Hw'_in).
                             rewrite Hnf.
                             exact Hinv_pres. }
                           apply IH with (fuel := fuel'); [lia | | exact Hnot_vis_ext | exact Hinv_new].
                           (* Need frontier_reaches for c'' :: cs' *)
                           (* Since w ≠ target, destruct the path to get next vertex *)
                           destruct (adj_path_list_step_inv X w target l' Hpath') as [[Heq_w _] | [next [l'' [[[Hadj_wn Hpath''] Heq_l''] Hin_w_X]]]].
                           *** (* w = target - contradiction with Hw_not_target *)
                               exfalso. apply Hw_not_target. exact Heq_w.
                           *** (* There's a step from w to next *)
                               (* next is adjacent to w, adj_path_list X next target l'' *)
                               (* Check if next is in new frontier *)
                               assert (Hin_next : In next X) by (apply adj_path_list_source_in_X with target l''; exact Hpath'').
                               destruct (In_dec eq_dec next (frontier_vertices_cert (c'' :: cs'))) as [Hnext_in | Hnext_not_in].
                               ---- (* next is in new frontier - use it *)
                                    unfold frontier_reaches.
                                    remember (find (fun c0 => if eq_dec (cert_vertex c0) next then true else false) (c'' :: cs')) as find_next eqn:Hfind_next.
                                    destruct find_next as [c_next | ].
                                    ++++ symmetry in Hfind_next.
                                         exists c_next. exists l''.
                                         split; [split|].
                                         **** apply find_some in Hfind_next. destruct Hfind_next as [Hcn_in _]. exact Hcn_in.
                                         **** apply find_some in Hfind_next. destruct Hfind_next as [_ Hpred].
                                              simpl in Hpred. destruct (eq_dec (cert_vertex c_next) next) as [Hcn_eq | Hcn_ne].
                                              ----- rewrite Hcn_eq. exact Hpath''.
                                              ----- discriminate.
                                         **** (* length l'' <= S path_len' *)
                                              rewrite Heq_l'' in Hlen'. simpl in Hlen'. lia.
                                    ++++ (* find returned None - contradiction with Hnext_in *)
                                         exfalso.
                                         apply (find_cert_by_vertex_complete X source (c'' :: cs') next Hnext_in (eq_sym Hfind_next)).
                               ---- (* next not in new frontier - it must be in new_visited *)
                                    (* new_visited = frontier_vertices_cert frontier ++ visited *)
                                    (* If next were fresh, it would be in new_frontier by expansion *)
                                    (* Since next is not in new_frontier, next is in new_visited *)
                                    assert (Hnext_in_nv : In next (frontier_vertices_cert frontier ++ visited)).
                                    { (* If not, then next would be in expansion (contradiction) *)
                                      destruct (In_dec eq_dec next (frontier_vertices_cert frontier ++ visited)) as [Hin_nv | Hnot_nv].
                                      - exact Hin_nv.
                                      - exfalso.
                                        (* next is fresh, adjacent to w (in frontier), in X *)
                                        (* So next would be in expansion = c'' :: cs' *)
                                        assert (Hnext_in_exp : In next (frontier_vertices_cert (c'' :: cs'))).
                                        { rewrite Hnf.
                                          apply expand_frontier_cert_has_neighbor with c_w.
                                          - exact Hcw_in.
                                          - rewrite Hcw_eq. exact Hadj_wn.
                                          - exact Hin_next.
                                          - exact Hnot_nv. }
                                        exact (Hnext_not_in Hnext_in_exp). }
                                    (* next is in frontier_vertices OR visited - use In_dec for Type *)
                                    destruct (In_dec eq_dec next (frontier_vertices_cert frontier)) as [Hnext_in_fr | Hnext_not_fr].
                                    ++++ (* next in OLD frontier but NOT in NEW frontier *)
                                         (* next is now in new_visited = frontier_vertices_cert frontier ++ visited *)
                                         (* Use visited_path_shorter with NEW state to find shorter path from NEW frontier *)
                                         assert (Hnext_in_new_vis : In next (frontier_vertices_cert frontier ++ visited)).
                                         { apply in_or_app. left. exact Hnext_in_fr. }
                                         (* Target not in expanded frontier ++ new_visited *)
                                         assert (Ht_not_combined : ~ In target (frontier_vertices_cert (c'' :: cs') ++ (frontier_vertices_cert frontier ++ visited))).
                                         { intro Habs. apply in_app_or in Habs.
                                           destruct Habs as [Ht_new | Ht_old]; [exact (Htarget_not_new Ht_new) | exact (Hnot_vis_ext Ht_old)]. }
                                         pose proof (visited_path_shorter X source (c'' :: cs') (frontier_vertices_cert frontier ++ visited) next target l'' Hinv_new Hnext_in_new_vis Hpath'' Ht_not_combined) as Hshorter.
                                         destruct Hshorter as [c_short [l_short [[Hcs_in Hpath_short] Hlen_short]]].
                                         exists c_short. exists l_short.
                                         split; [split|].
                                         ***** exact Hcs_in.
                                         ***** exact Hpath_short.
                                         ***** rewrite Heq_l'' in Hlen'. simpl in Hlen'. lia.
                                    ++++ (* next not in frontier - must be in visited *)
                                         (* Derive next in visited from Hnext_in_nv and Hnext_not_fr *)
                                         assert (Hnext_in_vis : In next visited).
                                         { apply in_app_or in Hnext_in_nv.
                                           destruct Hnext_in_nv as [Hfr | Hvis]; [contradiction | exact Hvis]. }
                                         (* next is also in new_visited = frontier_vertices_cert frontier ++ visited *)
                                         assert (Hnext_new_vis : In next (frontier_vertices_cert frontier ++ visited)).
                                         { apply in_or_app. right. exact Hnext_in_vis. }
                                         (* Target not in expanded frontier ++ new_visited *)
                                         assert (Ht_not_combined : ~ In target (frontier_vertices_cert (c'' :: cs') ++ (frontier_vertices_cert frontier ++ visited))).
                                         { intro Habs. apply in_app_or in Habs.
                                           destruct Habs as [Ht_new | Ht_old]; [exact (Htarget_not_new Ht_new) | exact (Hnot_vis_ext Ht_old)]. }
                                         (* Use visited_path_shorter with NEW state *)
                                         pose proof (visited_path_shorter X source (c'' :: cs') (frontier_vertices_cert frontier ++ visited) next target l'' Hinv_new Hnext_new_vis Hpath'' Ht_not_combined) as Hshorter.
                                         destruct Hshorter as [c_short [l_short [[Hcs_in Hpath_short] Hlen_short]]].
                                         exists c_short. exists l_short.
                                         split; [split|].
                                         ***** exact Hcs_in.
                                         ***** exact Hpath_short.
                                         ***** (* length l_short < length l'' <= S path_len' *)
                                               rewrite Heq_l'' in Hlen'. simpl in Hlen'. lia.

             ++ (* w is in visited - check if target is in new frontier *)
                remember (expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier) as new_frontier eqn:Hnf.
                destruct new_frontier as [|c'' cs'] eqn:Hnf'.
                ** (* Empty expansion *)
                   (* w is visited and has path to target via Hpath' *)
                   (* Use visited_path_shorter to find shorter path from frontier *)
                   assert (Ht_not_in : ~ In target (frontier_vertices_cert frontier ++ visited)).
                   { intro Habs. apply in_app_or in Habs.
                     destruct Habs as [Ht_fr | Ht_vis].
                     - unfold frontier_vertices_cert in Ht_fr.
                       apply in_map_iff in Ht_fr.
                       destruct Ht_fr as [ct [Hct_eq Hct_in]].
                       pose proof (find_none _ _ Hfind ct Hct_in) as Hpred.
                       simpl in Hpred. rewrite Hct_eq in Hpred.
                       destruct (eq_dec target target); [discriminate | contradiction].
                     - exact (Hnot_vis Ht_vis). }
                   pose proof (visited_path_shorter X source frontier visited w target l' Hinv Hw_visited Hpath' Ht_not_in) as Hshorter.
                   destruct Hshorter as [c_short [l_short [[Hcs_in Hpath_short] Hlen_short]]].
                   (* Build frontier_reaches with shorter path *)
                   assert (Hreach' : frontier_reaches X source frontier target path_len').
                   { exists c_short. exists l_short.
                     split; [split|].
                     - exact Hcs_in.
                     - exact Hpath_short.
                     - lia. }
                   (* Apply IH to get BFS success *)
                   assert (Hsucc : bfs_cert_fuel fuel' X target source visited frontier <> None).
                   { apply IH; [lia | exact Hreach' | exact Hnot_vis | exact Hinv]. }
                   (* BFS succeeds, so expansion non-empty *)
                   assert (Hexp_nonempty : expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier <> []).
                   { apply bfs_cert_success_expansion_nonempty with fuel' target; [lia | exact Hfind | exact Hsucc]. }
                   (* Contradiction with Hnf (empty expansion) *)
                   exfalso. apply Hexp_nonempty. symmetry. exact Hnf.
                ** (* Non-empty expansion - check if target in new frontier *)
                   destruct (In_dec eq_dec target (frontier_vertices_cert (c'' :: cs'))) as [Htarget_new | Htarget_not_new].
                   --- (* target IS in new frontier - BFS finds it directly *)
                       apply bfs_cert_finds_in_frontier; [lia | exact Htarget_new].
                   --- (* target NOT in new frontier - apply IH *)
                       assert (Hnot_vis_ext : ~ In target (frontier_vertices_cert frontier ++ visited)).
                       { intro Habs. apply in_app_or in Habs. destruct Habs as [Ht_fr | Ht_vis].
                         - unfold frontier_vertices_cert in Ht_fr.
                           apply in_map_iff in Ht_fr.
                           destruct Ht_fr as [ct [Hct_eq Hct_in]].
                           pose proof (find_none _ _ Hfind ct Hct_in) as Hpred.
                           simpl in Hpred. rewrite Hct_eq in Hpred.
                           destruct (eq_dec target target); [discriminate | contradiction].
                         - exact (Hnot_vis Ht_vis). }
                       (* Need invariant for new frontier/visited *)
                       assert (Hinv_new : bfs_invariant X (c'' :: cs') (frontier_vertices_cert frontier ++ visited)).
                       { pose proof (bfs_invariant_preserved X source frontier visited Hinv) as Hinv_pres.
                         unfold bfs_invariant in Hinv_pres |- *.
                         intros v' w' Hv'_in Hadj' Hw'_in.
                         specialize (Hinv_pres v' w' Hv'_in Hadj' Hw'_in).
                         rewrite Hnf. exact Hinv_pres. }
                       apply IH with (fuel := fuel'); [lia | | exact Hnot_vis_ext | exact Hinv_new].
                       (* w is visited, so w is in new_visited *)
                       (* Use visited_path_shorter to find certificate in new frontier *)
                       assert (Hw_new_vis : In w (frontier_vertices_cert frontier ++ visited)).
                       { apply in_or_app. right. exact Hw_visited. }
                       assert (Ht_not_combined : ~ In target (frontier_vertices_cert (c'' :: cs') ++ (frontier_vertices_cert frontier ++ visited))).
                       { intro Habs. apply in_app_or in Habs.
                         destruct Habs as [Ht_new | Ht_old]; [exact (Htarget_not_new Ht_new) | exact (Hnot_vis_ext Ht_old)]. }
                       pose proof (visited_path_shorter X source (c'' :: cs') (frontier_vertices_cert frontier ++ visited) w target l' Hinv_new Hw_new_vis Hpath' Ht_not_combined) as Hshorter.
                       destruct Hshorter as [c_short [l_short [[Hcs_in Hpath_short] Hlen_short]]].
                       exists c_short. exists l_short.
                       split; [split|].
                       +++ exact Hcs_in.
                       +++ exact Hpath_short.
                       +++ lia.

          -- (* w is fresh (not in frontier_vertices ++ visited) *)
             (* w will be added to expanded frontier by expand_frontier_cert_has_neighbor *)
             remember (expand_frontier_cert X (frontier_vertices_cert frontier ++ visited) source frontier) as new_frontier eqn:Hnf.

             (* w is in new_frontier *)
             assert (Hw_in_new : In w (frontier_vertices_cert new_frontier)).
             { rewrite Hnf.
               apply expand_frontier_cert_has_neighbor with c.
               - exact Hin_c.
               - exact Hadj.
               - exact Hin_w.
               - exact Hw_fresh. }

             destruct new_frontier as [|c' cs] eqn:Hnf'.
             ++ (* Empty expansion - contradiction with Hw_in_new *)
                simpl in Hw_in_new. contradiction.
             ++ (* Non-empty expansion - check if target is in new frontier *)
                (* First check if target is in the new frontier - if so, BFS finds it directly *)
                destruct (In_dec eq_dec target (frontier_vertices_cert (c' :: cs))) as [Htarget_new | Htarget_not_new].
                ** (* target IS in new frontier - BFS finds it directly *)
                   apply bfs_cert_finds_in_frontier; [lia | exact Htarget_new].
                ** (* target NOT in new frontier - apply IH *)
                   (* Need invariant for new frontier/visited *)
                   assert (Hinv_new : bfs_invariant X (c' :: cs) (frontier_vertices_cert frontier ++ visited)).
                   { pose proof (bfs_invariant_preserved X source frontier visited Hinv) as Hinv_pres.
                     unfold bfs_invariant in Hinv_pres |- *.
                     intros v' w' Hv'_in Hadj' Hw'_in.
                     specialize (Hinv_pres v' w' Hv'_in Hadj' Hw'_in).
                     rewrite Hnf. exact Hinv_pres. }
                   apply IH with (fuel := fuel'); [lia | | | exact Hinv_new].
                   --- (* Construct frontier_reaches witness *)
                       unfold frontier_reaches.
                       (* Use constructive find to locate cert with cert_vertex = w *)
                       remember (find (fun c0 => if eq_dec (cert_vertex c0) w then true else false) (c' :: cs)) as find_result eqn:Hfind_w.
                       destruct find_result as [c_new | ] eqn:Hfind_w'.
                       +++ (* Found cert c_new with cert_vertex c_new = w *)
                           symmetry in Hfind_w.
                           exists c_new. exists l'.
                           split; [split|].
                           *** (* In c_new (c' :: cs) *)
                               apply find_some in Hfind_w. destruct Hfind_w as [Hin_cn Hpred_cn].
                               exact Hin_cn.
                           *** (* adj_path_list from cert_vertex c_new to target *)
                               apply find_some in Hfind_w. destruct Hfind_w as [_ Hpred_cn].
                               simpl in Hpred_cn. destruct (eq_dec (cert_vertex c_new) w) as [Hcn_eq | Hcn_ne].
                               ---- rewrite Hcn_eq. exact Hpath'.
                               ---- discriminate.
                           *** exact Hlen'.
                       +++ (* find returned None - contradiction with Hw_in_new *)
                           exfalso.
                           apply (find_cert_by_vertex_complete X source (c' :: cs) w Hw_in_new (eq_sym Hfind_w)).
                   --- (* ~ In target (frontier_vertices_cert frontier ++ visited) *)
                       intro Habs.
                       apply in_app_or in Habs.
                       destruct Habs as [Ht_fr | Ht_vis].
                       +++ (* target in old frontier - contradiction with Hfind *)
                           unfold frontier_vertices_cert in Ht_fr.
                           apply in_map_iff in Ht_fr.
                           destruct Ht_fr as [ct [Hct_eq Hct_in]].
                           pose proof (find_none _ _ Hfind ct Hct_in) as Hpred.
                           simpl in Hpred. rewrite Hct_eq in Hpred.
                           destruct (eq_dec target target); [discriminate | contradiction].
                       +++ (* target in visited - contradiction with Hnot_vis *)
                           exact (Hnot_vis Ht_vis).
  Qed.

  (* BFS completeness with proper path-length hypothesis *)
  (* Note: fuel >= length l ensures at least 1 iteration for the check *)
  Lemma bfs_cert_complete_with_path :
    forall fuel X target source l (Hin : In source X),
      adj_path_list X source target l ->
      (length l <= fuel)%nat ->  (* Strengthened from S fuel to fuel *)
      bfs_cert_fuel fuel X target source [] [initial_cert X source Hin] <> None.
  Proof.
    intros fuel X target source l Hin Hpath Hlen.
    (* path_len = length l - 1, need path_len < fuel *)
    (* From Hlen: length l <= fuel and length l >= 1, so length l - 1 < fuel *)
    pose proof (adj_path_list_length_ge_1 X source target l Hpath) as Hlen1.
    apply (bfs_cert_complete_aux (length l - 1) fuel X target source []
             [initial_cert X source Hin]).
    - lia.  (* length l - 1 < fuel from length l >= 1 and length l <= fuel *)
    - (* Construct frontier_reaches using sigma types *)
      unfold frontier_reaches.
      exists (initial_cert X source Hin).
      exists l.
      split; [split|].
      + left. reflexivity.
      + (* adj_path_list from cert_vertex (initial_cert ...) = source *)
        unfold initial_cert, cert_vertex. simpl. exact Hpath.
      + lia.
    - intro Habs. simpl in Habs. contradiction.
    - (* bfs_invariant for initial state: empty visited trivially satisfies *)
      apply bfs_invariant_empty.
  Qed.

  (* path_in_cluster implies target is in X *)
  Lemma path_in_cluster_target_in :
    forall X p q, path_in_cluster X p q -> In q X.
  Proof.
    intros X p q Hpqpath.
    induction Hpqpath as [X' p' Hin | X' p' q' r' Hin Hadj Hpath' IH].
    - exact Hin.
    - exact IH.
  Qed.

  (* path_in_cluster implies source is in X - moved here for use below *)
  Lemma path_in_cluster_source_in_early :
    forall X p q, path_in_cluster X p q -> In p X.
  Proof.
    intros X p q Hpqpath.
    induction Hpqpath as [X' p' Hin | X' p' q' r' Hin Hadj Hpath' IH].
    - exact Hin.
    - exact Hin.
  Qed.

  (* =========================================================================
     PATH WITNESS EXTRACTION

     Bridge from path_in_cluster (Prop) to adj_path_list (Type).
     Uses classical epsilon to extract the concrete witness list.
     ========================================================================= *)

  (* Prop predicate: a list witnesses an adj_path_list *)
  Definition adj_path_listP (X : Cluster P) (p q : P) (l : list P) : Prop :=
    exists t : adj_path_list X p q l, True.

  (* Classical choice: pick a list that works if one exists *)
  Definition pick_path_list (X : Cluster P) (p q : P) : list P :=
    epsilon (inhabits nil) (fun l => adj_path_listP X p q l).

  Lemma pick_path_list_spec :
    forall X p q,
      (exists l, adj_path_listP X p q l) ->
      adj_path_listP X p q (pick_path_list X p q).
  Proof.
    intros X p q Hpqex.
    unfold pick_path_list.
    apply epsilon_spec.
    exact Hpqex.
  Qed.

  (* path_in_cluster implies existence of adj_path_listP witness *)
  Lemma path_in_cluster_exists_adj_path_listP :
    forall X p q,
      path_in_cluster X p q ->
      exists l, adj_path_listP X p q l.
  Proof.
    intros X p q Hpqpath.
    induction Hpqpath as [X' p' Hin | X' p' q' r' Hin Hadj Hpath' IH].
    - (* path_refl *)
      exists [p']. unfold adj_path_listP.
      exists (adj_path_single X' p' Hin). exact I.
    - (* path_step *)
      destruct IH as [l Hl].
      exists (p' :: l). unfold adj_path_listP in *.
      destruct Hl as [t _].
      exists (adj_path_cons X' p' q' r' l Hin Hadj t). exact I.
  Qed.

  (* Main witness lemma: extract Type-level witness from Prop path *)
  Lemma path_in_cluster_witness :
    forall X p q,
      path_in_cluster X p q ->
      { l : list P & adj_path_list X p q l }.
  Proof.
    intros X p q Hpqpath.
    (* get existence in Prop *)
    pose proof (path_in_cluster_exists_adj_path_listP X p q Hpqpath) as Hex.
    (* use epsilon to pick a concrete list *)
    set (l := pick_path_list X p q).
    assert (HlP : adj_path_listP X p q l).
    { apply pick_path_list_spec. exact Hex. }
    unfold adj_path_listP in HlP.
    (* Use constructive_indefinite_description to extract Type-level witness from Prop *)
    pose proof (@constructive_indefinite_description (adj_path_list X p q l) (fun _ => True) HlP) as [t _].
    exists l. exact t.
  Qed.

  (* path_in_cluster implies source is in X *)
  Lemma path_in_cluster_source_in :
    forall X p q, path_in_cluster X p q -> In p X.
  Proof.
    intros X p q Hpqpath.
    induction Hpqpath as [X' p' Hin | X' p' q' r' Hin Hadj Hpath' IH].
    - exact Hin.
    - exact Hin.
  Qed.

  (* Derive original BFS completeness from certified version *)
  (* Key insight: BFS with sufficient fuel explores all connected vertices *)
  (* Strategy: extract adj_path_list witness, loop-erase to NoDup, use bfs_cert_complete_with_path *)
  Lemma bfs_complete_with_path :
    forall (bfs_fuel : nat) X target source,
      (bfs_fuel >= length X)%nat ->  (* Strengthened: need fuel >= cluster size for path bound *)
      In target X ->
      path_in_cluster X source target ->
      bfs_paths_fuel bfs_fuel X target [] [(source, [source])] <> None.
  Proof.
    intros bfs_fuel X target source Hfuel Htarget Hpath.
    pose proof (path_in_cluster_source_in X source target Hpath) as Hsource_in.
    pose proof (initial_sync X source Hsource_in) as Hsync.
    apply (bfs_nonNone_from_cert bfs_fuel X target source []
             [(source, [source])] [initial_cert X source Hsource_in]).
    - exact Hsync.
    - (* Use path_in_cluster_witness to extract adj_path_list *)
      destruct (path_in_cluster_witness X source target Hpath) as [l Hpath_list].
      (* Loop-erase to get NoDup path *)
      destruct (adj_path_list_loop_erase eq_dec X source target l Hpath_list) as [l' [Hpath' Hnodup]].
      (* Length bound from simple_path_length_bound *)
      assert (Hlen : (length l' <= length X)%nat).
      { exact (simple_path_length_bound eq_dec X source target l' Hpath' Hnodup). }
      (* Apply bfs_cert_complete_with_path *)
      apply (bfs_cert_complete_with_path bfs_fuel X target source l' Hsource_in Hpath').
      lia.
  Qed.

  (* If connects holds, find_path succeeds (completeness) *)
  Lemma find_path_complete :
    forall (X : Cluster P) (p1 p2 : P),
      In p1 X -> In p2 X -> path_in_cluster X p1 p2 ->
      find_path X p1 p2 <> None.
  Proof.
    intros X p1 p2 Hp1 Hp2 Hpath.
    unfold find_path.
    destruct (eq_dec p1 p2) as [Heq | Hne].
    - (* p1 = p2: returns Some [p1] *)
      discriminate.
    - (* p1 <> p2: BFS must find path *)
      apply bfs_complete_with_path.
      + (* fuel = length X >= length X *)
        lia.
      + exact Hp2.
      + exact Hpath.
  Qed.

  (* Combined: connects implies existence of adj_path_list witness *)
  (* Key: we case-analyze on the option directly (Type), avoiding Prop elimination *)
  Lemma connects_to_adj_path_list :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 ->
      { l : list P & adj_path_list X p1 p2 l }.
  Proof.
    intros X p1 p2 [Hin1 [Hin2 Hpath]].
    (* Case-analyze on the option result (Type-level) *)
    destruct (find_path X p1 p2) as [l |] eqn:Hfind.
    - (* Some l: path found *)
      exists l. exact (find_path_sound X p1 p2 l Hin1 Hfind).
    - (* None: impossible by completeness *)
      exfalso.
      apply (find_path_complete X p1 p2 Hin1 Hin2 Hpath).
      exact Hfind.
  Qed.

  (* Final theorem: connects implies simple path witness *)
  Theorem connects_to_simple_path :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 ->
      { l : list P & (adj_path_list X p1 p2 l * NoDup l)%type }.
  Proof.
    intros X p1 p2 Hconn.
    destruct (connects_to_adj_path_list X p1 p2 Hconn) as [l Hpath].
    exact (adj_path_list_loop_erase eq_dec X p1 p2 l Hpath).
  Qed.

End ConstructivePathFinding.

Class YMGeometryFrontier (P : Type) := {
  ym_eq_dec_frontier : forall (p1 p2 : P), {p1 = p2} + {p1 <> p2};

  (* Incompatibility relation used by KP sums / polymer expansion *)
  ym_overlap_frontier : P -> P -> Prop;
  ym_overlap_dec_frontier :
    forall p1 p2, {ym_overlap_frontier p1 p2} + {~ ym_overlap_frontier p1 p2};
  ym_overlap_sym_frontier :
    forall p1 p2, ym_overlap_frontier p1 p2 -> ym_overlap_frontier p2 p1;
  ym_overlap_refl_frontier :
    forall p, ym_overlap_frontier p p;

  ym_shares_edge_frontier : P -> P -> Prop;
  ym_shares_edge_dec_frontier :
    forall p1 p2, {ym_shares_edge_frontier p1 p2} + {~ ym_shares_edge_frontier p1 p2};
  ym_shares_edge_sym_frontier :
    forall p1 p2, ym_shares_edge_frontier p1 p2 -> ym_shares_edge_frontier p2 p1;

  ym_graph_dist_frontier : P -> P -> R;
  ym_graph_dist_nonneg_frontier :
    forall p1 p2, ym_graph_dist_frontier p1 p2 >= 0;
  ym_graph_dist_sym_frontier :
    forall p1 p2, ym_graph_dist_frontier p1 p2 = ym_graph_dist_frontier p2 p1;

  (* Metric properties for path-based distance bound *)
  ym_graph_dist_triangle_frontier :
    forall p1 p2 p3,
      ym_graph_dist_frontier p1 p3 <=
      ym_graph_dist_frontier p1 p2 + ym_graph_dist_frontier p2 p3;
  ym_graph_dist_refl_frontier :
    forall p, ym_graph_dist_frontier p p = 0;
  ym_shares_edge_dist_frontier :
    forall p1 p2, ym_shares_edge_frontier p1 p2 -> ym_graph_dist_frontier p1 p2 <= 1
}.

(* =========================================================================
   Cluster Size Bounds (separate section - needs MetricSystem for size)
   ========================================================================= *)

Section ClusterSizeBounds.
  Context {P : Type} `{PolymerSystem P} `{MetricSystem P}.

  (* Helper: Cluster size bounds length *)
  Lemma cluster_size_ge_length :
    forall (X : Cluster P), cluster_size X >= INR (length X).
  Proof.
    induction X as [| h t IH].
    - simpl. lra.
    - simpl cluster_size. simpl length. rewrite S_INR.
      pose proof (size_pos h) as Hsize.
      lra.
  Qed.

  (* Helper: cluster_size is nonneg *)
  Lemma cluster_size_nonneg :
    forall (X : Cluster P), cluster_size X >= 0.
  Proof.
    induction X as [| h t IH].
    - simpl. lra.
    - simpl. pose proof (size_pos h). lra.
  Qed.

End ClusterSizeBounds.

(* =========================================================================
   Metric Properties for connects_implies_dist_bound

   The proof of connects_implies_dist_bound requires:
   1. dist_triangle: triangle inequality
   2. adj_dist_bound: adj p q -> dist p q <= 1
   3. dist_refl: dist p p = 0
   4. Shortest-path-is-simple: any path can be shortened to use distinct vertices

   Given these, the proof is:
   - Shortest adj-path from p to r in X has at most (length X - 1) edges
   - Each edge has dist <= 1
   - Total dist <= (length X - 1) < length X <= cluster_size X

   For now, we keep this as a class hypothesis. The detailed proof
   requires defining "simple path" and proving it suffices.
   ========================================================================= *)

Section MetricPathBounds.
  Context {P : Type} `{PolymerSystem P} `{MetricSystem P} `{ConnectivitySystem P}.

  (* Triangle inequality for the metric *)
  Variable dist_triangle : forall p q r : P, dist p r <= dist p q + dist q r.

  (* Adjacency implies unit distance (graph metric) *)
  Variable adj_dist_bound : forall p q : P, adj p q -> dist p q <= 1.

  (* Self-distance is zero *)
  Variable dist_refl : forall p : P, dist p p = 0.

  (* =========================================================================
     Path Distance Lemmas (using adj_path_list from above)
     ========================================================================= *)

  (* Distance bound from path list: dist <= (length l - 1) *)
  Lemma dist_le_path_list_length :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l ->
      dist p1 p2 <= INR (length l - 1).
  Proof.
    intros X p1 p2 l Hpath.
    induction Hpath as [X' p Hin | X' p q r l' Hinp Hadj Hrest IH].
    - (* adj_path_single: [p], length = 1, edges = 0 *)
      simpl length. simpl. rewrite dist_refl. lra.
    - (* adj_path_cons: p :: l', length = S (length l') *)
      simpl length.
      pose proof (dist_triangle p q r) as Htri.
      pose proof (adj_dist_bound p q Hadj) as Hedge.
      (* Goal: dist p r <= INR (S (length l') - 1) = INR (length l') *)
      (* IH: dist q r <= INR (length l' - 1) *)
      (* Need: 1 + INR (length l' - 1) <= INR (length l') *)
      (* This holds because INR (length l' - 1) + 1 <= INR (length l') for l' non-empty *)
      destruct l' as [| h t].
      + (* l' = [], impossible from adj_path_list - single node path has non-empty list *)
        inversion Hrest.
      + (* l' = h :: t, so length l' = S (length t) >= 1 *)
        simpl length in IH. simpl length.
        (* IH: dist q r <= INR (S (length t) - 1) = INR (length t) *)
        (* Goal: dist p r <= INR (S (S (length t)) - 1) = INR (S (length t)) *)
        assert (Hih_simp : INR (S (length t) - 1) = INR (length t)) by (f_equal; lia).
        rewrite Hih_simp in IH.
        assert (Hgoal_simp : INR (S (S (length t)) - 1) = INR (S (length t))) by (f_equal; lia).
        rewrite Hgoal_simp.
        rewrite S_INR. lra.
  Qed.

  (* Path list length is bounded by cluster length (each vertex in X) *)
  (* This requires NoDup or similar - for now, weaker bound: length l <= length X + length l *)
  (* Actually, we need: all vertices in path are in X, and path is simple *)

  (* Simpler approach: path list vertices are all in X *)
  Lemma adj_path_list_all_in :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l -> forall v, In v l -> In v X.
  Proof.
    intros X p1 p2 l Hpath.
    induction Hpath as [X' p Hin | X' p q r l' Hinp Hadj Hrest IH].
    - (* single *)
      intros v [Heq | Habs]; [subst; exact Hin | destruct Habs].
    - (* cons *)
      intros v [Heq | Htail].
      + subst. exact Hinp.
      + apply IH. exact Htail.
  Qed.

  (* Key insight: if path visits only vertices in X and has no repeats,
     then length l <= length X. But proving "no repeats" is the hard part.

     Alternative: just bound by length X directly using pigeonhole.
     For YM, we can assume/prove this in the frontier. *)

  (* Frontier hypothesis: witness extraction *)
  Variable path_witness :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 -> { l : list P & adj_path_list X p1 p2 l }.

  (* Frontier hypothesis: path length bound (pigeonhole) *)
  Variable path_length_le_cluster :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l ->
      (length l <= length X)%nat.

  (* MAIN THEOREM: connects implies dist bound - NOW PROVABLE! *)
  Theorem connects_implies_dist_bound_proved :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 -> dist p1 p2 <= cluster_size X.
  Proof.
    intros X p1 p2 Hconn.
    destruct (path_witness X p1 p2 Hconn) as [l Hpath].
    pose proof (dist_le_path_list_length X p1 p2 l Hpath) as Hdist.
    pose proof (path_length_le_cluster X p1 p2 l Hpath) as Hlen.
    pose proof (cluster_size_ge_length X) as Hsize.
    apply Rle_trans with (INR (length l - 1)); [exact Hdist |].
    apply Rle_trans with (INR (length X)).
    - apply le_INR. lia.
    - lra.
  Qed.

End MetricPathBounds.

Section GeometryConnectsBound.
  Context {P : Type} `{PolymerSystem P} `{MetricSystem P} `{ConnectivitySystem P}.

  (* The frontier class now requires the two witness hypotheses.
     The raw dist bound follows from connects_implies_dist_bound_proved. *)

  (* We need eq_dec for simple_path_length_bound *)
  Variable eq_dec : forall (p1 p2 : P), {p1 = p2} + {p1 <> p2}.

  Class YMGeometryConnectsFrontier : Type := {
    (* Metric properties for the graph distance *)
    ym_dist_triangle_frontier : forall p q r : P, dist p r <= dist p q + dist q r;
    ym_adj_dist_bound_frontier : forall p q : P, adj p q -> dist p q <= 1;
    ym_dist_refl_frontier : forall p : P, dist p p = 0;

    (* Witness extraction: connects -> SIMPLE path (with NoDup) *)
    (* Using prod (Type * Prop) since adj_path_list is in Type *)
    ym_simple_path_witness_frontier :
      forall (X : Cluster P) (p1 p2 : P),
        connects X p1 p2 -> { l : list P & (adj_path_list X p1 p2 l * NoDup l)%type }
  }.

  (* Derived: path witness (projection) *)
  Lemma ym_path_witness_frontier `{YMGeometryConnectsFrontier} :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 -> { l : list P & adj_path_list X p1 p2 l }.
  Proof.
    intros X p1 p2 Hc.
    destruct (ym_simple_path_witness_frontier X p1 p2 Hc) as [l [Hpath _]].
    exists l. exact Hpath.
  Qed.

  (* Derived: path length bound for simple paths - NOW Qed! *)
  Lemma ym_simple_path_length_bound `{YMGeometryConnectsFrontier} :
    forall (X : Cluster P) (p1 p2 : P) (l : list P),
      adj_path_list X p1 p2 l -> NoDup l ->
      (length l <= length X)%nat.
  Proof.
    intros X p1 p2 l Hpath Hnodup.
    exact (simple_path_length_bound eq_dec X p1 p2 l Hpath Hnodup).
  Qed.

  (* The dist bound follows from the simple path witness *)
  Lemma ym_connects_implies_dist_bound_from_frontier
    `{YMGeometryConnectsFrontier} :
    forall (X : Cluster P) (p1 p2 : P),
      connects X p1 p2 -> dist p1 p2 <= cluster_size X.
  Proof.
    intros X p1 p2 Hconn.
    (* Get simple path from witness *)
    destruct (ym_simple_path_witness_frontier X p1 p2 Hconn) as [l [Hpath Hnodup]].
    (* Use dist_le_path_list_length from MetricPathBounds *)
    pose proof (dist_le_path_list_length
                  ym_dist_triangle_frontier
                  ym_adj_dist_bound_frontier
                  ym_dist_refl_frontier
                  X p1 p2 l Hpath) as Hdist.
    (* Use simple_path_length_bound *)
    pose proof (ym_simple_path_length_bound X p1 p2 l Hpath Hnodup) as Hlen.
    (* Use cluster_size_ge_length - now takes only X since it's in separate section *)
    pose proof (cluster_size_ge_length X) as Hsize.
    apply Rle_trans with (INR (length l - 1)); [exact Hdist |].
    apply Rle_trans with (INR (length X)).
    - apply le_INR. lia.
    - lra.
  Qed.

End GeometryConnectsBound.
