(* =========================================================================
   kotecky_preiss.v

   Genuine Kotecky-Preiss (1986) / Fernandez-Procacci (2007) Cluster
   Expansion Theorem in the standard ordered-tuple Ursell formulation
   (with 1 / n! symmetry factor, repetitions allowed, and genuine Ursell
   function phi^T):

     Under the elementary single-polymer Kotecky-Preiss condition:
       forall p, sum_{q in Lambda, overlap p q} |w(q)| * exp(a(q) + d(q)) <= a(p),

     we prove WITHOUT ANY ANALYTIC ASSUMPTIONS:
       1. Root-pinned exponential-moment bound:
            sum_{k=0}^N (1/k!) sum_{Y in Lambda^k} |phi^T(p0 :: Y)| * prod_{q in Y} (|w(q)| e^{d(q)}) <= exp(a(p0))
       2. 1-pinned overlap exponential-moment bound:
            sum_{n=1}^N (1/n!) sum_{X in Lambda^n, X overlaps p0} |phi^T(X)| * prod_{q in X} (|w(q)| e^{d(q)}) <= a(p0)
       3. Unconditional exponential decay of the genuine Ursell truncated
          two-point correlator G_{Lambda, N}(p1, p2):
            |G_{Lambda, N}(p1, p2)| <= a(p1) * exp(c) * exp(- c * dist(p1, p2)).

   Depends ONLY on Coq stdlib + rg.penrose_tree_bound + rg.poly_exp_bound + rg.tree_cut_bijection.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import penrose_tree_bound poly_exp_bound tree_cut_bijection.
Import ListNotations.
Import PenroseTreeBound PolyExpBound TreeCutBijection.
Open Scope R_scope.

Module KoteckyPreiss.

  (* =======================================================================
     1. Ordered Tuples (Repetitions Allowed), Series, and Basic Algebra
     ======================================================================= *)

  Fixpoint tuples_of_length {P : Type} (Lambda : list P) (n : nat) : list (list P) :=
    match n with
    | 0%nat => [[]]
    | S n' => flat_map (fun p => map (cons p) (tuples_of_length Lambda n')) Lambda
    end.

  Definition sum_over_tuples {P : Type} (Lambda : list P) (n : nat) (f : list P -> R) : R :=
    fold_right Rplus 0 (map f (tuples_of_length Lambda n)).

  Definition prod_list (l : list R) : R :=
    fold_right Rmult 1 l.

  Definition prod_weight {P : Type} (wt : P -> R) (X : list P) : R :=
    prod_list (map wt X).

  (* 1 / n! weighted cluster expansion truncated at cluster size <= N_max (n = 1..N_max) *)
  Fixpoint kp_series {P : Type} (Lambda : list P) (N_max : nat) (term : list P -> R) : R :=
    match N_max with
    | 0%nat => 0
    | S N' =>
        kp_series Lambda N' term +
        (/ INR (fact (S N'))) * sum_over_tuples Lambda (S N') term
    end.

  (* Root-pinned 1 / k! series for k = 0..N with p0 fixed at vertex 0 *)
  Fixpoint root_series {P : Type} (Lambda : list P) (N : nat) (p0 : P) (term : list P -> R) : R :=
    match N with
    | 0%nat => (/ INR (fact 0%nat)) * sum_over_tuples Lambda 0%nat (fun Y => term (p0 :: Y))
    | S N' =>
        root_series Lambda N' p0 term +
        (/ INR (fact (S N'))) * sum_over_tuples Lambda (S N') (fun Y => term (p0 :: Y))
    end.

  (* Genuine Ursell truncated two-point correlator (clusters overlapping both p1 and p2) *)
  Definition ursell_correlator {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (N_max : nat) (w : P -> R) (p1 p2 : P) : R :=
    kp_series Lambda N_max (fun X =>
      if existsb (ob p1) X && existsb (ob p2) X
      then ursell_fn ob X * prod_weight w X
      else 0).

  (* Overlap sum over Lambda *)
  Definition sum_overlap_Lambda {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (p : P) (f : P -> R) : R :=
    fold_right Rplus 0 (map (fun q => if ob p q then f q else 0) Lambda).

  Lemma tuples_of_length_len : forall {P : Type} (Lambda : list P) n Y,
    In Y (tuples_of_length Lambda n) -> length Y = n.
  Proof.
    intros P Lambda. induction n as [| n' IH]; intros Y Hin; simpl in *.
    - destruct Hin as [<- | []]. reflexivity.
    - apply in_flat_map in Hin. destruct Hin as [p [_ Hin']].
      apply in_map_iff in Hin'. destruct Hin' as [Y' [<- HY']].
      simpl. f_equal. exact (IH Y' HY').
  Qed.

  Lemma tuples_of_length_in : forall {P : Type} (Lambda : list P) n Y,
    In Y (tuples_of_length Lambda n) -> Forall (fun p => In p Lambda) Y.
  Proof.
    intros P Lambda. induction n as [| n' IH]; intros Y Hin; simpl in *.
    - destruct Hin as [<- | []]. constructor.
    - apply in_flat_map in Hin. destruct Hin as [p [Hp Hin']].
      apply in_map_iff in Hin'. destruct Hin' as [Y' [<- HY']].
      constructor; [exact Hp | exact (IH Y' HY')].
  Qed.

  Lemma fold_right_Rplus_flat_map : forall {A B : Type} (f : A -> list B) (g : B -> R) (l : list A),
    fold_right Rplus 0 (map g (flat_map f l)) =
    fold_right Rplus 0 (map (fun a => fold_right Rplus 0 (map g (f a))) l).
  Proof.
    induction l as [| a xs IH]; simpl; [reflexivity |].
    rewrite map_app, fold_right_Rplus_app, IH. reflexivity.
  Qed.

  Lemma sum_over_tuples_0 : forall {P : Type} (Lambda : list P) f,
    sum_over_tuples Lambda 0%nat f = f [].
  Proof. intros P Lambda f. unfold sum_over_tuples; simpl; ring. Qed.

  Lemma sum_over_tuples_S : forall {P : Type} (Lambda : list P) n f,
    sum_over_tuples Lambda (S n) f =
    fold_right Rplus 0 (map (fun p => sum_over_tuples Lambda n (fun Y => f (p :: Y))) Lambda).
  Proof.
    intros P Lambda n f. unfold sum_over_tuples. simpl tuples_of_length.
    rewrite fold_right_Rplus_flat_map. apply fold_right_Rplus_ext.
    intros p _. rewrite map_map. reflexivity.
  Qed.

  Lemma sum_over_tuples_ext : forall {P : Type} (Lambda : list P) n f g,
    (forall Y, In Y (tuples_of_length Lambda n) -> f Y = g Y) ->
    sum_over_tuples Lambda n f = sum_over_tuples Lambda n g.
  Proof.
    intros P Lambda n f g Hext. unfold sum_over_tuples.
    apply fold_right_Rplus_ext. exact Hext.
  Qed.

  Lemma fold_right_Rplus_le : forall {A : Type} (f g : A -> R) (l : list A),
    (forall x, In x l -> f x <= g x) ->
    fold_right Rplus 0 (map f l) <= fold_right Rplus 0 (map g l).
  Proof.
    induction l as [| a xs IH]; intro Hle; simpl; [lra |].
    apply Rplus_le_compat; [apply Hle; left; reflexivity | apply IH; intros x Hx; apply Hle; right; exact Hx].
  Qed.

  Lemma fold_right_Rplus_nonneg : forall {A : Type} (f : A -> R) (l : list A),
    (forall x, In x l -> 0 <= f x) ->
    0 <= fold_right Rplus 0 (map f l).
  Proof.
    induction l as [| a xs IH]; intro Hnn; simpl; [lra |].
    pose proof (Hnn a (or_introl eq_refl)).
    pose proof (IH (fun x Hx => Hnn x (or_intror Hx))). lra.
  Qed.

  Lemma fold_right_Rplus_plus : forall {A : Type} (f g : A -> R) (l : list A),
    fold_right Rplus 0 (map (fun x => f x + g x) l) =
    fold_right Rplus 0 (map f l) + fold_right Rplus 0 (map g l).
  Proof.
    induction l as [| a xs IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma fold_right_Rplus_scale_r : forall {A : Type} (c : R) (f : A -> R) (l : list A),
    fold_right Rplus 0 (map (fun x => f x * c) l) = fold_right Rplus 0 (map f l) * c.
  Proof.
    induction l as [| a xs IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma sum_over_tuples_le : forall {P : Type} (Lambda : list P) n f g,
    (forall Y, In Y (tuples_of_length Lambda n) -> f Y <= g Y) ->
    sum_over_tuples Lambda n f <= sum_over_tuples Lambda n g.
  Proof. intros P Lambda n f g Hle. unfold sum_over_tuples. apply fold_right_Rplus_le. exact Hle. Qed.

  Lemma sum_over_tuples_nonneg : forall {P : Type} (Lambda : list P) n f,
    (forall Y, In Y (tuples_of_length Lambda n) -> 0 <= f Y) ->
    0 <= sum_over_tuples Lambda n f.
  Proof. intros P Lambda n f Hnn. unfold sum_over_tuples. apply fold_right_Rplus_nonneg. exact Hnn. Qed.

  Lemma sum_over_tuples_scale : forall {P : Type} (Lambda : list P) n c f,
    sum_over_tuples Lambda n (fun Y => c * f Y) = c * sum_over_tuples Lambda n f.
  Proof. intros P Lambda n c f. unfold sum_over_tuples. apply fold_right_Rplus_scale. Qed.

  Lemma sum_over_tuples_plus : forall {P : Type} (Lambda : list P) n f g,
    sum_over_tuples Lambda n (fun Y => f Y + g Y) =
    sum_over_tuples Lambda n f + sum_over_tuples Lambda n g.
  Proof. intros P Lambda n f g. unfold sum_over_tuples. apply fold_right_Rplus_plus. Qed.

  Lemma prod_weight_nonneg : forall {P : Type} (wt : P -> R) (X : list P),
    (forall p, 0 <= wt p) -> 0 <= prod_weight wt X.
  Proof.
    intros P wt X Hnn. induction X as [| x xs IH].
    - unfold prod_weight, prod_list; simpl; lra.
    - unfold prod_weight, prod_list in *; simpl. apply Rmult_le_pos; [apply Hnn | exact IH].
  Qed.

  Lemma Rabs_prod_weight : forall {P : Type} (w : P -> R) (X : list P),
    Rabs (prod_weight w X) = prod_weight (fun p => Rabs (w p)) X.
  Proof.
    intros P w X. induction X as [| x xs IH].
    - unfold prod_weight, prod_list; simpl. apply Rabs_R1.
    - unfold prod_weight, prod_list in *; simpl. rewrite Rabs_mult, IH. reflexivity.
  Qed.

  Lemma prod_weight_mul : forall {P : Type} (f g : P -> R) (X : list P),
    prod_weight (fun p => f p * g p) X = prod_weight f X * prod_weight g X.
  Proof.
    intros P f g X. induction X as [| x xs IH]; unfold prod_weight, prod_list in *; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma prod_weight_exp : forall {P : Type} (d : P -> R) (X : list P),
    prod_weight (fun p => exp (d p)) X = exp (fold_right Rplus 0 (map d X)).
  Proof.
    intros P d X. induction X as [| x xs IH]; unfold prod_weight, prod_list in *; simpl.
    - rewrite exp_0. reflexivity.
    - rewrite IH, exp_plus. reflexivity.
  Qed.

  (* =======================================================================
     2. Mask-Splitting Factorization & Binomial Counting
     ======================================================================= *)

  Lemma prod_weight_mask_split : forall {P : Type} (wt : P -> R) mask (Y : list P),
    length mask = length Y ->
    prod_weight wt Y = prod_weight wt (select_true mask Y) * prod_weight wt (select_false mask Y).
  Proof.
    intros P wt. induction mask as [| [|] m' IH]; intros [| y ys] Hlen;
      simpl in *; try discriminate.
    - unfold prod_weight, prod_list; simpl; ring.
    - unfold prod_weight, prod_list in *; simpl.
      rewrite (IH ys ltac:(lia)). ring.
    - unfold prod_weight, prod_list in *; simpl.
      rewrite (IH ys ltac:(lia)). ring.
  Qed.

  Lemma sum_over_tuples_mask_split : forall {P : Type} (Lambda : list P) mask (f g : list P -> R),
    sum_over_tuples Lambda (length mask) (fun Y => f (select_true mask Y) * g (select_false mask Y)) =
    sum_over_tuples Lambda (count_true mask) f *
    sum_over_tuples Lambda (length mask - count_true mask) g.
  Proof.
    intros P Lambda. induction mask as [| [|] m' IH]; intros f g.
    - simpl. rewrite !sum_over_tuples_0. reflexivity.
    - cbn [length count_true].
      replace (S (length m') - S (count_true m'))%nat with (length m' - count_true m')%nat by lia.
      rewrite sum_over_tuples_S.
      transitivity (fold_right Rplus 0
        (map (fun p => sum_over_tuples Lambda (count_true m') (fun Z => f (p :: Z)) *
                       sum_over_tuples Lambda (length m' - count_true m') g) Lambda)).
      + apply fold_right_Rplus_ext. intros p _.
        exact (IH (fun Z => f (p :: Z)) g).
      + rewrite fold_right_Rplus_scale_r. rewrite <- sum_over_tuples_S. reflexivity.
    - cbn [length count_true].
      pose proof (count_true_le m').
      replace (S (length m') - count_true m')%nat with (S (length m' - count_true m')) by lia.
      rewrite sum_over_tuples_S.
      transitivity (fold_right Rplus 0
        (map (fun p => sum_over_tuples Lambda (count_true m') f *
                       sum_over_tuples Lambda (length m' - count_true m') (fun W => g (p :: W))) Lambda)).
      + apply fold_right_Rplus_ext. intros p _.
        exact (IH f (fun W => g (p :: W))).
      + rewrite fold_right_Rplus_scale. rewrite <- sum_over_tuples_S. reflexivity.
  Qed.

  Fixpoint binomial (n r : nat) : nat :=
    match n, r with
    | _, 0%nat => 1%nat
    | 0%nat, S _ => 0%nat
    | S n', S r' => (binomial n' r' + binomial n' (S r'))%nat
    end.

  Lemma count_masks_with_true : forall n r,
    length (filter (fun m => Nat.eqb (count_true m) r) (all_masks n)) = binomial n r.
  Proof.
    induction n as [| n' IH]; intro r; simpl.
    - destruct r; reflexivity.
    - rewrite filter_app, app_length.
      assert (H1 : filter (fun m => Nat.eqb (count_true m) r) (map (cons true) (all_masks n')) =
                   match r with
                   | 0%nat => []
                   | S r' => map (cons true) (filter (fun m => Nat.eqb (count_true m) r') (all_masks n'))
                   end).
      { clear IH. destruct r as [| r'].
        - induction (all_masks n') as [| m ms IHm]; simpl; [reflexivity | exact IHm].
        - induction (all_masks n') as [| m ms IHm]; simpl; [reflexivity |].
          destruct (Nat.eqb (count_true m) r'); simpl; [f_equal |]; exact IHm. }
      assert (H2 : filter (fun m => Nat.eqb (count_true m) r) (map (cons false) (all_masks n')) =
                   map (cons false) (filter (fun m => Nat.eqb (count_true m) r) (all_masks n'))).
      { clear IH H1. induction (all_masks n') as [| m ms IHm]; simpl; [reflexivity |].
        destruct (Nat.eqb (count_true m) r); simpl; [f_equal |]; exact IHm. }
      rewrite H1, H2, map_length, IH.
      destruct r as [| r']; [simpl; destruct n'; reflexivity |].
      rewrite map_length, IH. simpl. lia.
  Qed.

  Lemma binomial_fact : forall n r,
    (r <= n)%nat ->
    INR (binomial n r) * INR (fact r) * INR (fact (n - r)) = INR (fact n).
  Proof.
    induction n as [| n' IH]; intros r Hr.
    - assert (r = 0%nat) by lia. subst. simpl. ring.
    - destruct r as [| r'].
      + simpl. ring.
      + destruct (Nat.eq_dec r' n') as [-> | Hne].
        * assert (Hz : forall k j, (k < j)%nat -> binomial k j = 0%nat).
          { clear. induction k as [| k' IHk]; intros [| j'] Hlt; simpl; try lia; try reflexivity.
            rewrite (IHk j' ltac:(lia)), (IHk (S j') ltac:(lia)). reflexivity. }
          assert (Hb : binomial (S n') (S n') = 1%nat).
          { clear - Hz. induction n' as [| m IH]; [reflexivity |].
            change (binomial (S (S m)) (S (S m))) with (binomial (S m) (S m) + binomial (S m) (S (S m)))%nat.
            rewrite IH, (Hz (S m) (S (S m)) ltac:(lia)). lia. }
          rewrite Hb, Nat.sub_diag. simpl fact. simpl INR. ring.
        * simpl binomial. rewrite plus_INR.
          assert (H1 := IH r' ltac:(lia)).
          assert (H2 := IH (S r') ltac:(lia)).
          assert (Hf1 : INR (fact (S r')) = INR (S r') * INR (fact r')).
          { change (fact (S r')) with (S r' * fact r')%nat. rewrite mult_INR. reflexivity. }
          assert (Hf2 : INR (fact (n' - r')) = INR (n' - r') * INR (fact (n' - S r'))).
          { replace (n' - r')%nat with (S (n' - S r')) at 1 by lia.
            change (fact (S (n' - S r'))) with (S (n' - S r') * fact (n' - S r'))%nat.
            rewrite mult_INR. f_equal. f_equal. lia. }
          assert (Hf3 : INR (fact (S n')) = INR (S n') * INR (fact n')).
          { change (fact (S n')) with (S n' * fact n')%nat. rewrite mult_INR. reflexivity. }
          replace (S n' - S r')%nat with (n' - r')%nat by lia.
          assert (Hsum_n : INR (S r') + INR (n' - r') = INR (S n')).
          { rewrite <- plus_INR. f_equal. lia. }
          rewrite Hf3, <- Hsum_n.
          replace ((INR (binomial n' r') + INR (binomial n' (S r'))) * INR (fact (S r')) * INR (fact (n' - r')))
             with (INR (S r') * (INR (binomial n' r') * INR (fact r') * INR (fact (n' - r'))) +
                   INR (n' - r') * (INR (binomial n' (S r')) * INR (fact (S r')) * INR (fact (n' - S r'))))
            by (rewrite Hf1, Hf2; ring).
          rewrite H1, H2. ring.
  Qed.

  (* =======================================================================
     3. Swap-to-Front Permutation Invariance of Tuples, Ursell, and Trees
     ======================================================================= *)

  Fixpoint set_nth {A : Type} (i : nat) (v : A) (l : list A) : list A :=
    match i, l with
    | 0%nat, _ :: xs => v :: xs
    | S i', x :: xs => x :: set_nth i' v xs
    | _, [] => []
    end.

  Definition swap0_list {A : Type} (idx : nat) (l : list A) : list A :=
    match idx, l with
    | 0%nat, _ => l
    | S _, [] => []
    | S idx', a :: xs =>
        match nth_error xs idx' with
        | Some b => b :: set_nth idx' a xs
        | None => a :: xs
        end
    end.

  Lemma set_nth_length : forall {A : Type} i (v : A) l, length (set_nth i v l) = length l.
  Proof. induction i; intros v [| a xs]; simpl; auto. Qed.

  Lemma set_nth_nth_error_eq : forall {A : Type} i (v : A) l,
    (i < length l)%nat -> nth_error (set_nth i v l) i = Some v.
  Proof.
    induction i as [| i' IH]; intros v [| a xs] Hi; simpl in *; try lia; try reflexivity.
    apply IH; lia.
  Qed.

  Lemma set_nth_nth_error_ne : forall {A : Type} i j (v : A) l,
    j <> i -> nth_error (set_nth i v l) j = nth_error l j.
  Proof.
    induction i as [| i' IH]; intros [| j'] v [| a xs] Hne; simpl in *; try congruence; try reflexivity.
    apply IH; lia.
  Qed.

  Lemma swap0_list_length : forall {A : Type} idx (l : list A),
    length (swap0_list idx l) = length l.
  Proof.
    intros A [| idx'] [| a xs]; simpl; try reflexivity.
    destruct (nth_error xs idx'); simpl; [rewrite set_nth_length |]; reflexivity.
  Qed.

  Lemma swap0_list_nth_error : forall {A : Type} idx (l : list A) j,
    (idx < length l)%nat ->
    nth_error (swap0_list idx l) j =
    nth_error l (if Nat.eqb j 0%nat then idx else if Nat.eqb j idx then 0%nat else j).
  Proof.
    intros A [| idx'] [| a xs] j Hidx; simpl in *; try lia.
    - destruct (Nat.eqb_spec j 0%nat) as [-> | Hne]; reflexivity.
    - assert (Hex : exists b, nth_error xs idx' = Some b).
      { destruct (nth_error xs idx') eqn:E; [exists a0; reflexivity |].
        apply nth_error_None in E. lia. }
      destruct Hex as [b Hb]. rewrite Hb.
      destruct j as [| j']; simpl.
      + symmetry; exact Hb.
      + destruct (Nat.eqb_spec j' idx') as [-> | Hne]; simpl nth_error.
        * apply set_nth_nth_error_eq; lia.
        * apply set_nth_nth_error_ne; exact Hne.
  Qed.

  Lemma prod_weight_set_nth : forall {P : Type} (wt : P -> R) idx v b l,
    nth_error l idx = Some b ->
    wt b * prod_weight wt (set_nth idx v l) = wt v * prod_weight wt l.
  Proof.
    intros P wt. induction idx as [| i' IH]; intros v b [| a xs] Hb; simpl in *; try discriminate.
    - inversion Hb; subst. unfold prod_weight, prod_list; simpl; ring.
    - unfold prod_weight, prod_list in *; simpl.
      specialize (IH v b xs Hb).
      replace (wt b * (wt a * fold_right Rmult 1 (map wt (set_nth i' v xs))))
         with (wt a * (wt b * fold_right Rmult 1 (map wt (set_nth i' v xs)))) by ring.
      rewrite IH. ring.
  Qed.

  Lemma prod_weight_swap0 : forall {P : Type} (wt : P -> R) idx (l : list P),
    prod_weight wt (swap0_list idx l) = prod_weight wt l.
  Proof.
    intros P wt [| idx'] [| a xs]; simpl; try reflexivity.
    destruct (nth_error xs idx') as [b |] eqn:Hb; [| reflexivity].
    unfold prod_weight, prod_list; simpl.
    apply prod_weight_set_nth. exact Hb.
  Qed.

  (* Tuple-sum invariance under swap0_list *)
  Lemma sum_over_tuples_swap0 : forall {P : Type} (Lambda : list P) n idx (f : list P -> R),
    sum_over_tuples Lambda n (fun Y => f (swap0_list idx Y)) = sum_over_tuples Lambda n f.
  Proof.
    intros P Lambda n idx. revert n.
    induction idx as [| idx' IH]; intros n f.
    - apply sum_over_tuples_ext; intros Y _; reflexivity.
    - destruct n as [| [| n']].
      + rewrite !sum_over_tuples_0. reflexivity.
      + rewrite !sum_over_tuples_S. apply fold_right_Rplus_ext. intros p _.
        rewrite !sum_over_tuples_0. simpl. destruct idx'; reflexivity.
      + (* Swap (0, S idx') in p :: q :: rest:
           if idx' = 0: directly swap p and q via fold_right_Rplus_swap.
           if idx' = S m: swap(0,1), then swap(0, S m) in tail, then swap(0,1). *)
        destruct idx' as [| m].
        * rewrite !sum_over_tuples_S.
          transitivity (fold_right Rplus 0 (map (fun p =>
            fold_right Rplus 0 (map (fun q =>
              sum_over_tuples Lambda n' (fun rest => f (q :: p :: rest))) Lambda)) Lambda)).
          -- apply fold_right_Rplus_ext; intros p _. rewrite sum_over_tuples_S.
             apply fold_right_Rplus_ext; intros q _. reflexivity.
          -- rewrite fold_right_Rplus_swap.
             apply fold_right_Rplus_ext; intros q _. rewrite sum_over_tuples_S.
             apply fold_right_Rplus_ext; intros p _. reflexivity.
        * (* Use swap01 -> tail swap0(S m) -> swap01 *)
          assert (Hswap01 : forall g,
            sum_over_tuples Lambda (S (S n')) (fun Y => g (swap0_list 1%nat Y)) =
            sum_over_tuples Lambda (S (S n')) g).
          { intro g. rewrite !sum_over_tuples_S.
            transitivity (fold_right Rplus 0 (map (fun p =>
              fold_right Rplus 0 (map (fun q =>
                sum_over_tuples Lambda n' (fun rest => g (q :: p :: rest))) Lambda)) Lambda)).
            - apply fold_right_Rplus_ext; intros p _. rewrite sum_over_tuples_S.
              apply fold_right_Rplus_ext; intros q _. reflexivity.
            - rewrite fold_right_Rplus_swap.
              apply fold_right_Rplus_ext; intros q _. rewrite sum_over_tuples_S.
              apply fold_right_Rplus_ext; intros p _. reflexivity. }
          assert (Hdecomp : forall (p q : P) (rest : list P),
            swap0_list (S (S m)) (p :: q :: rest) =
            swap0_list 1%nat (q :: swap0_list (S m) (p :: rest))).
          { intros p q rest. simpl. destruct (nth_error rest m) as [b |]; reflexivity. }
          transitivity (sum_over_tuples Lambda (S (S n'))
            (fun Y => f (swap0_list 1%nat (match Y with
              | p :: q :: rest => q :: swap0_list (S m) (p :: rest)
              | _ => Y end)))).
          { apply sum_over_tuples_ext. intros Y HY.
            pose proof (tuples_of_length_len Lambda _ Y HY) as Hlen.
            destruct Y as [| p [| q rest]]; simpl in Hlen; try lia.
            rewrite Hdecomp. reflexivity. }
          (* First undo outer swap0_list 1 on the inner list *)
          rewrite !sum_over_tuples_S.
          transitivity (fold_right Rplus 0 (map (fun p =>
            fold_right Rplus 0 (map (fun q =>
              sum_over_tuples Lambda n' (fun rest =>
                f (swap0_list 1%nat (q :: swap0_list (S m) (p :: rest))))) Lambda)) Lambda)).
          { apply fold_right_Rplus_ext; intros p _. rewrite sum_over_tuples_S. reflexivity. }
          rewrite fold_right_Rplus_swap.
          transitivity (fold_right Rplus 0 (map (fun q =>
            sum_over_tuples Lambda (S n') (fun Z =>
              f (swap0_list 1%nat (q :: swap0_list (S m) Z)))) Lambda)).
          { apply fold_right_Rplus_ext; intros q _. rewrite sum_over_tuples_S. reflexivity. }
          transitivity (fold_right Rplus 0 (map (fun q =>
            sum_over_tuples Lambda (S n') (fun Z =>
              f (swap0_list 1%nat (q :: Z)))) Lambda)).
          { apply fold_right_Rplus_ext; intros q _.
            exact (IH (S n') (fun Z => f (swap0_list 1%nat (q :: Z)))). }
          transitivity (fold_right Rplus 0 (map (fun q =>
            fold_right Rplus 0 (map (fun p =>
              sum_over_tuples Lambda n' (fun rest => f (p :: q :: rest))) Lambda)) Lambda)).
          { apply fold_right_Rplus_ext; intros q _. rewrite sum_over_tuples_S. reflexivity. }
          rewrite fold_right_Rplus_swap.
          apply fold_right_Rplus_ext; intros p _. rewrite sum_over_tuples_S. reflexivity.
  Qed.

  (* Graph isomorphism invariance of ursell_fn and tree_count under swap0_list *)
  Lemma ursell_and_trees_swap0 : forall {P : Type} (ob : P -> P -> bool) idx (X : list P),
    (forall x y, ob x y = ob y x) ->
    (idx < length X)%nat ->
    ursell_fn ob (swap0_list idx X) = ursell_fn ob X /\
    tree_count ob (swap0_list idx X) = tree_count ob X.
  Proof.
    intros P ob idx X Hsym Hidx.
    set (n := length X).
    set (sigma := fun j : nat => if Nat.eqb j 0%nat then idx else if Nat.eqb j idx then 0%nat else j).
    assert (Hs : forall x, (x < n)%nat -> (sigma x < n)%nat).
    { intros x Hx. unfold sigma. destruct (Nat.eqb_spec x 0%nat); [lia |].
      destruct (Nat.eqb_spec x idx); lia. }
    assert (Hinv : forall x, (x < n)%nat -> sigma (sigma x) = x).
    { intros x Hx. unfold sigma.
      destruct (Nat.eqb_spec x 0%nat) as [-> | Hx0].
      - destruct (Nat.eqb_spec idx 0%nat); [congruence |]. rewrite Nat.eqb_refl. reflexivity.
      - destruct (Nat.eqb_spec x idx) as [-> | Hxi].
        + reflexivity.
        + destruct (Nat.eqb_spec x 0%nat); [congruence |].
          destruct (Nat.eqb_spec x idx); [congruence | reflexivity]. }
    assert (Hmap_gen : forall A B : list P,
      length A = n -> length B = n ->
      (forall j, nth_error A j = nth_error B (sigma j)) ->
      forall e, In e (graph_edges ob A) -> In (map_edge sigma e) (graph_edges ob B)).
    { intros A B HA HB Hnth [u v] Hin.
      apply graph_edges_in in Hin. destruct Hin as [Huv [Hvn [x [y [Hx [Hy Hob]]]]]].
      rewrite HA in Hvn.
      assert (Hsu_ne : sigma u <> sigma v).
      { intro Heq. assert (u = v) by (rewrite <- (Hinv u ltac:(lia)), <- (Hinv v Hvn), Heq; reflexivity). lia. }
      unfold map_edge, mk_edge; simpl.
      destruct (Nat.ltb_spec (sigma u) (sigma v)).
      - apply graph_edges_in. rewrite HB. repeat split; [lia | apply Hs; exact Hvn |].
        exists x, y. rewrite <- !Hnth. repeat split; assumption.
      - apply graph_edges_in. rewrite HB. repeat split; [lia | apply Hs; lia |].
        exists y, x. rewrite <- !Hnth, Hsym. repeat split; assumption. }
    unfold ursell_fn, tree_count.
    rewrite swap0_list_length. fold n.
    apply (graph_iso_ursell_and_trees n sigma sigma
             (graph_edges ob (swap0_list idx X)) (graph_edges ob X)).
    - unfold n. rewrite <- (swap0_list_length idx X) at 1. apply graph_edges_wf.
    - apply graph_edges_wf.
    - exact Hs.
    - exact Hs.
    - exact Hinv.
    - exact Hinv.
    - apply (Hmap_gen (swap0_list idx X) X (swap0_list_length idx X) eq_refl).
      intro j. exact (swap0_list_nth_error idx X j Hidx).
    - apply (Hmap_gen X (swap0_list idx X) eq_refl (swap0_list_length idx X)).
      intro j.
      destruct (lt_dec j n) as [Hj | Hge].
      + rewrite (swap0_list_nth_error idx X (sigma j) Hidx).
        fold (sigma (sigma j)). rewrite (Hinv j Hj). reflexivity.
      + assert (Hsj : (n <= sigma j)%nat).
        { unfold sigma. destruct (Nat.eqb_spec j 0%nat); [lia |].
          destruct (Nat.eqb_spec j idx); lia. }
        rewrite (proj2 (nth_error_None X j) ltac:(lia)).
        rewrite (proj2 (nth_error_None (swap0_list idx X) (sigma j)) ltac:(rewrite swap0_list_length; lia)).
        reflexivity.
  Qed.

  (* =======================================================================
     4. Exact Tree-Sum Recurrence & Kotecky-Preiss Tree-Sum Bound
     ======================================================================= *)

  Definition tree_sum_order {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (wt : P -> R) (k : nat) (p0 : P) : R :=
    (/ INR (fact k)) *
    sum_over_tuples Lambda k (fun Y => INR (tree_count ob (p0 :: Y)) * prod_weight wt Y).

  Lemma tree_sum_order_0 : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) wt (p0 : P),
    tree_sum_order ob Lambda wt 0%nat p0 = 1.
  Proof.
    intros P ob Lambda wt p0. unfold tree_sum_order.
    rewrite sum_over_tuples_0.
    unfold tree_count, spanning_trees, graph_edges, prod_weight, prod_list. simpl.
    field.
  Qed.

  Lemma tree_sum_order_nonneg : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) wt k (p0 : P),
    (forall q, 0 <= wt q) -> 0 <= tree_sum_order ob Lambda wt k p0.
  Proof.
    intros P ob Lambda wt k p0 Hnn. unfold tree_sum_order.
    apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, fact_pos_R |].
    apply sum_over_tuples_nonneg. intros Y _.
    apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hnn].
  Qed.

  Lemma valid_roots_length_sum : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y_A : list P),
    INR (length (valid_roots ob p0 Y_A)) =
    fold_right Rplus 0 (map (fun idx =>
      match nth_error Y_A idx with
      | Some q => if ob p0 q then 1 else 0
      | None => 0
      end) (seq 0%nat (length Y_A))).
  Proof.
    intros P ob p0 Y_A. unfold valid_roots.
    set (f := fun idx => match nth_error Y_A idx with Some q => ob p0 q | None => false end).
    assert (Hgen : forall l,
      INR (length (filter f l)) = fold_right Rplus 0 (map (fun idx => if f idx then 1 else 0) l)).
    { induction l as [| a xs IH]; simpl; [reflexivity |].
      destruct (f a); simpl length; [rewrite S_INR, IH; ring | rewrite IH; ring]. }
    rewrite Hgen. apply fold_right_Rplus_ext. intros idx _.
    unfold f. destruct (nth_error Y_A idx) as [q |]; [destruct (ob p0 q); reflexivity | reflexivity].
  Qed.

  (* Key symmetry step: summing valid_roots count * tree_count * prod_weight over Lambda^s *)
  Lemma sum_valid_roots_trees : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (wt : P -> R) (s : nat) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (1 <= s)%nat ->
    sum_over_tuples Lambda s (fun Y_A =>
      INR (length (valid_roots ob p0 Y_A)) * INR (tree_count ob Y_A) * prod_weight wt Y_A) =
    INR s * sum_overlap_Lambda ob Lambda p0 (fun q =>
      wt q * sum_over_tuples Lambda (s - 1)%nat (fun Z =>
        INR (tree_count ob (q :: Z)) * prod_weight wt Z)).
  Proof.
    intros P ob Lambda wt s p0 Hsym Hs.
    destruct s as [| s']; [lia |].
    replace (S s' - 1)%nat with s' by lia.
    transitivity (sum_over_tuples Lambda (S s') (fun Y_A =>
      fold_right Rplus 0 (map (fun idx =>
        (match nth_error Y_A idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
        INR (tree_count ob Y_A) * prod_weight wt Y_A) (seq 0%nat (S s'))))).
    { apply sum_over_tuples_ext. intros Y_A HY.
      rewrite (valid_roots_length_sum ob p0 Y_A).
      rewrite (tuples_of_length_len Lambda (S s') Y_A HY).
      rewrite <- !fold_right_Rplus_scale_r.
      apply fold_right_Rplus_ext; intros idx _; ring. }
    unfold sum_over_tuples at 1. rewrite fold_right_Rplus_swap.
    transitivity (fold_right Rplus 0 (map (fun _ =>
      sum_overlap_Lambda ob Lambda p0 (fun q =>
        wt q * sum_over_tuples Lambda s' (fun Z =>
          INR (tree_count ob (q :: Z)) * prod_weight wt Z))) (seq 0%nat (S s')))).
    { apply fold_right_Rplus_ext. intros idx Hidx. apply in_seq in Hidx.
      change (fold_right Rplus 0 (map (fun Y_A =>
        (match nth_error Y_A idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
        INR (tree_count ob Y_A) * prod_weight wt Y_A) (tuples_of_length Lambda (S s'))))
      with (sum_over_tuples Lambda (S s') (fun Y_A =>
        (match nth_error Y_A idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
        INR (tree_count ob Y_A) * prod_weight wt Y_A)).
      rewrite <- (sum_over_tuples_swap0 Lambda (S s') idx).
      transitivity (sum_over_tuples Lambda (S s') (fun Y_A =>
        (match nth_error Y_A 0%nat with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
        INR (tree_count ob Y_A) * prod_weight wt Y_A)).
      - apply sum_over_tuples_ext. intros Y_A HY.
        pose proof (tuples_of_length_len Lambda (S s') Y_A HY) as Hlen.
        destruct (ursell_and_trees_swap0 ob idx Y_A Hsym ltac:(lia)) as [_ Htr].
        rewrite Htr, prod_weight_swap0.
        rewrite (swap0_list_nth_error idx Y_A idx ltac:(lia)).
        destruct (Nat.eqb_spec idx 0%nat) as [-> | Hne]; [reflexivity |].
        rewrite Nat.eqb_refl. reflexivity.
      - rewrite sum_over_tuples_S. unfold sum_overlap_Lambda.
        apply fold_right_Rplus_ext. intros q _.
        destruct (ob p0 q) eqn:Hpq.
        + rewrite <- sum_over_tuples_scale.
          apply sum_over_tuples_ext. intros Z _.
          unfold prod_weight, prod_list; cbn [nth_error map fold_right]; rewrite Hpq; ring.
        + transitivity (sum_over_tuples Lambda s' (fun _ => 0)).
          * apply sum_over_tuples_ext. intros Z _. cbn [nth_error]; rewrite Hpq; ring.
          * unfold sum_over_tuples. apply fold_right_Rplus_0. }
    transitivity (fold_right Rplus 0 (map (fun _ => 1) (seq 0%nat (S s'))) *
      sum_overlap_Lambda ob Lambda p0 (fun q =>
        wt q * sum_over_tuples Lambda s' (fun Z =>
          INR (tree_count ob (q :: Z)) * prod_weight wt Z))).
    - rewrite <- fold_right_Rplus_scale_r.
      apply fold_right_Rplus_ext; intros _ _; ring.
    - rewrite fold_right_Rplus_const1, seq_length. reflexivity.
  Qed.

  (* Helper: partition sum over all_masks n by count_true = r (r = 0..n) *)
  Lemma sum_over_all_masks_by_count : forall n (F : nat -> R),
    fold_right Rplus 0 (map (fun m => F (count_true m)) (all_masks n)) =
    sum_f_R0 (fun r => INR (binomial n r) * F r) n.
  Proof.
    intros n F.
    assert (Hpart : forall (l : list (list bool)),
      (forall m, In m l -> (count_true m <= n)%nat) ->
      fold_right Rplus 0 (map (fun m => F (count_true m)) l) =
      sum_f_R0 (fun r => INR (length (filter (fun m => Nat.eqb (count_true m) r) l)) * F r) n).
    { induction l as [| m ms IH]; intro Hle.
      - simpl. symmetry. transitivity (sum_f_R0 (fun _ => 0) n); [| apply sum_f_R0_zero].
        apply sum_f_R0_ext; intros r _; ring.
      - simpl map; simpl fold_right.
        rewrite (IH (fun x Hx => Hle x (or_intror Hx))).
        pose proof (Hle m (or_introl eq_refl)) as Hm.
        assert (Hdelta :
          F (count_true m) =
          sum_f_R0 (fun r => (if Nat.eqb (count_true m) r then 1 else 0) * F r) n).
        { assert (Hgen : forall N c, (c <= N)%nat ->
            sum_f_R0 (fun r => (if Nat.eqb c r then 1 else 0) * F r) N = F c).
          { induction N as [| N' IHN]; intros c Hc; simpl.
            - assert (c = 0%nat) by lia. subst. simpl. ring.
            - destruct (Nat.eqb_spec c (S N')) as [-> | Hne].
              + assert (Hz : sum_f_R0 (fun r => (if Nat.eqb (S N') r then 1 else 0) * F r) N' = 0).
                { transitivity (sum_f_R0 (fun _ => 0) N'); [| apply sum_f_R0_zero].
                  apply sum_f_R0_ext. intros r Hr. destruct (Nat.eqb_spec (S N') r); [lia | ring]. }
                rewrite Hz. ring.
              + rewrite (IHN c ltac:(lia)). ring. }
          symmetry; apply Hgen; exact Hm. }
        rewrite Hdelta at 1. rewrite <- sum_f_R0_plus.
        apply sum_f_R0_ext. intros r _.
        simpl filter. destruct (Nat.eqb (count_true m) r); simpl length; [rewrite S_INR; ring | ring]. }
    rewrite Hpart.
    - apply sum_f_R0_ext. intros r _. rewrite count_masks_with_true. reflexivity.
    - intros m Hm. apply all_masks_in in Hm. pose proof (count_true_le m). lia.
  Qed.

  (* Exact combinatorial tree-sum recurrence! *)
  Theorem tree_sum_order_recurrence : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (wt : P -> R) (k : nat) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (1 <= k)%nat ->
    INR k * tree_sum_order ob Lambda wt k p0 =
    sum_f_R0 (fun j =>
      INR (S j) *
      sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt j q) *
      tree_sum_order ob Lambda wt (k - S j)%nat p0) (k - 1)%nat.
  Proof.
    intros P ob Lambda wt k p0 Hsym Hk.
    destruct k as [| k']; [lia |].
    replace (S k' - 1)%nat with k' by lia.
    unfold tree_sum_order at 1.
    (* Step 1: Apply tree_count_decomp inside sum_over_tuples *)
    assert (Hdecomp :
      sum_over_tuples Lambda (S k') (fun Y => INR (tree_count ob (p0 :: Y)) * prod_weight wt Y) =
      fold_right Rplus 0 (map (fun mask =>
        sum_over_tuples Lambda (S k') (fun Y =>
          (INR (length (valid_roots ob p0 (select_true mask Y))) *
           INR (tree_count ob (select_true mask Y)) * prod_weight wt (select_true mask Y)) *
          (INR (tree_count ob (p0 :: select_false mask Y)) * prod_weight wt (select_false mask Y))))
        (masks_head_true (S k')))).
    { unfold sum_over_tuples at 1.
      transitivity (fold_right Rplus 0 (map (fun Y =>
        fold_right Rplus 0 (map (fun mask =>
          (INR (length (valid_roots ob p0 (select_true mask Y))) *
           INR (tree_count ob (select_true mask Y)) * prod_weight wt (select_true mask Y)) *
          (INR (tree_count ob (p0 :: select_false mask Y)) * prod_weight wt (select_false mask Y)))
          (masks_head_true (S k')))) (tuples_of_length Lambda (S k')))).
      - apply fold_right_Rplus_ext. intros Y HY.
        pose proof (tuples_of_length_len Lambda (S k') Y HY) as HlenY.
        rewrite (tree_count_decomp ob p0 Y ltac:(lia)).
        rewrite HlenY.
        assert (Hnat_sum : forall {A : Type} (f : A -> nat) (l : list A),
          INR (fold_right Nat.add 0%nat (map f l)) = fold_right Rplus 0 (map (fun x => INR (f x)) l)).
        { induction l as [| a xs IH]; simpl; [reflexivity | rewrite plus_INR, IH; reflexivity]. }
        rewrite Hnat_sum, <- fold_right_Rplus_scale_r.
        apply fold_right_Rplus_ext. intros mask Hmask.
        apply masks_head_true_in in Hmask; [| lia]. destruct Hmask as [Hmlen _].
        rewrite !mult_INR.
        rewrite (prod_weight_mask_split wt mask Y ltac:(lia)). ring.
      - rewrite fold_right_Rplus_swap. reflexivity. }
    rewrite Hdecomp.
    (* Step 2: Factor each mask sum using sum_over_tuples_mask_split and sum_valid_roots_trees *)
    assert (Hmask_val : forall mask, In mask (masks_head_true (S k')) ->
      sum_over_tuples Lambda (S k') (fun Y =>
        (INR (length (valid_roots ob p0 (select_true mask Y))) *
         INR (tree_count ob (select_true mask Y)) * prod_weight wt (select_true mask Y)) *
        (INR (tree_count ob (p0 :: select_false mask Y)) * prod_weight wt (select_false mask Y))) =
      INR (count_true mask) *
      INR (fact (count_true mask - 1)) * INR (fact (S k' - count_true mask)) *
      sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt (count_true mask - 1) q) *
      tree_sum_order ob Lambda wt (S k' - count_true mask) p0).
    { intros mask Hmask. apply masks_head_true_in in Hmask; [| lia].
      destruct Hmask as [Hmlen Hm0].
      assert (Hcpos : (1 <= count_true mask)%nat).
      { destruct mask as [| [|] m']; simpl in *; try discriminate; lia. }
      rewrite <- Hmlen at 1.
      rewrite (sum_over_tuples_mask_split Lambda mask
        (fun YA => INR (length (valid_roots ob p0 YA)) * INR (tree_count ob YA) * prod_weight wt YA)
        (fun YB => INR (tree_count ob (p0 :: YB)) * prod_weight wt YB)).
      rewrite (sum_valid_roots_trees ob Lambda wt (count_true mask) p0 Hsym Hcpos).
      rewrite Hmlen.
      unfold tree_sum_order.
      assert (Hov_scale :
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q *
          sum_over_tuples Lambda (count_true mask - 1)%nat (fun Z => INR (tree_count ob (q :: Z)) * prod_weight wt Z)) =
        INR (fact (count_true mask - 1)) *
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q *
          (/ INR (fact (count_true mask - 1)) *
           sum_over_tuples Lambda (count_true mask - 1)%nat (fun Z => INR (tree_count ob (q :: Z)) * prod_weight wt Z)))).
      { unfold sum_overlap_Lambda. rewrite <- fold_right_Rplus_scale.
        apply fold_right_Rplus_ext. intros q _.
        destruct (ob p0 q); [| ring].
        assert (Hne : INR (fact (count_true mask - 1)) <> 0) by (apply not_0_INR, fact_neq_0).
        field; exact Hne. }
      rewrite Hov_scale.
      assert (Hne2 : INR (fact (S k' - count_true mask)) <> 0) by (apply not_0_INR, fact_neq_0).
      field; exact Hne2. }
    rewrite (fold_right_Rplus_ext _ _ (masks_head_true (S k')) Hmask_val).
    (* Step 3: Reindex masks_head_true (S k') = map (cons true) (all_masks k') by count_true m' = j *)
    unfold masks_head_true. rewrite map_map.
    set (F := fun j =>
      INR (S j) * INR (fact j) * INR (fact (k' - j)) *
      sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt j q) *
      tree_sum_order ob Lambda wt (k' - j) p0).
    transitivity (INR (S k') * (/ INR (fact (S k')) *
      fold_right Rplus 0 (map (fun m' => F (count_true m')) (all_masks k')))).
    { f_equal. f_equal. apply fold_right_Rplus_ext. intros m' _.
      unfold F. simpl count_true.
      replace (S (count_true m') - 1)%nat with (count_true m') by lia.
      replace (S k' - S (count_true m'))%nat with (k' - count_true m')%nat by lia.
      reflexivity. }
    rewrite (sum_over_all_masks_by_count k' F). unfold F.
    rewrite <- Rmult_assoc, <- sum_f_R0_scale.
    apply sum_f_R0_ext. intros j Hj.
    replace (S k' - S j)%nat with (k' - j)%nat by lia.
    pose proof (binomial_fact k' j Hj) as Hbf.
    assert (HfactS : INR (fact (S k')) = INR (S k') * INR (fact k')).
    { change (fact (S k')) with (S k' * fact k')%nat. rewrite mult_INR. reflexivity. }
    assert (Hne1 : INR (S k') <> 0) by (apply not_0_INR; lia).
    assert (Hne2 : INR (fact k') <> 0) by (apply not_0_INR, fact_neq_0).
    rewrite HfactS.
    replace (INR (S k') * / (INR (S k') * INR (fact k')) *
             (INR (binomial k' j) *
              (INR (S j) * INR (fact j) * INR (fact (k' - j)) *
               sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt j q) *
               tree_sum_order ob Lambda wt (k' - j) p0)))
       with ((INR (S k') * / (INR (S k') * INR (fact k'))) *
             (INR (binomial k' j) * INR (fact j) * INR (fact (k' - j))) *
             (INR (S j) *
              sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt j q) *
              tree_sum_order ob Lambda wt (k' - j) p0)) by ring.
    rewrite Hbf. field. split; assumption.
  Qed.

  (* Truncated rooted tree sum up to order N *)
  Definition tree_sum_upto {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (wt : P -> R) (N : nat) (p0 : P) : R :=
    sum_f_R0 (fun k => tree_sum_order ob Lambda wt k p0) N.

  (* Kotecky-Preiss single-polymer condition at a polymer p *)
  Definition kp_at {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p : P) : Prop :=
    sum_overlap_Lambda ob Lambda p (fun q => Rabs (w q) * exp (a q + d q)) <= a p.

  (* MAIN TREE-SUM BOUND BY INDUCTION ON N (zero analytic assumptions!) *)
  Theorem kp_tree_sum_bound_Lambda : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R),
    (forall x y, ob x y = ob y x) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
    forall N p, In p Lambda ->
      tree_sum_upto ob Lambda (fun q => Rabs (w q) * exp (d q)) N p <= exp (a p).
  Proof.
    intros P ob Lambda w a d Hsym Ha_nn Hkp.
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hwt_nn : forall q, 0 <= wt q).
    { intro q. unfold wt. apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]. }
    induction N as [| N' IH]; intros p Hp.
    - unfold tree_sum_upto; simpl. rewrite tree_sum_order_0.
      rewrite <- exp_0. destruct (Rle_lt_or_eq_dec 0 (a p) (Ha_nn p Hp)) as [Hlt | Heq].
      + left; apply exp_increasing; exact Hlt.
      + rewrite <- Heq; lra.
    - unfold tree_sum_upto.
      set (u := fun s => match s with
        | 0%nat => 0
        | S j => sum_overlap_Lambda ob Lambda p (fun q => wt q * tree_sum_order ob Lambda wt j q)
        end).
      eapply Rle_trans.
      { apply (exp_recurrence_sum_bound (fun k => tree_sum_order ob Lambda wt k p) u (S N')).
        - apply tree_sum_order_0.
        - intros s Hs. destruct s as [| j]; [lia |]. unfold u, sum_overlap_Lambda.
          apply fold_right_Rplus_nonneg. intros q _.
          destruct (ob p q); [| lra].
          apply Rmult_le_pos; [apply Hwt_nn | apply tree_sum_order_nonneg; exact Hwt_nn].
        - intros k Hk.
          rewrite (tree_sum_order_recurrence ob Lambda wt k p Hsym ltac:(lia)).
          apply sum_f_R0_ext. intros j Hj. reflexivity. }
      (* Now simplify sum_{j=0}^{N'} u (S j) = sum_overlap_Lambda (wt q * tree_sum_upto N' q) *)
      assert (Hsum_u :
        sum_f_R0 (fun j => u (S j)) N' =
        sum_overlap_Lambda ob Lambda p (fun q => wt q * tree_sum_upto ob Lambda wt N' q)).
      { unfold u, sum_overlap_Lambda, tree_sum_upto.
        assert (Hswap : forall M (f : nat -> P -> R),
          sum_f_R0 (fun j => fold_right Rplus 0 (map (f j) Lambda)) M =
          fold_right Rplus 0 (map (fun q => sum_f_R0 (fun j => f j q) M) Lambda)).
        { induction M as [| M' IHM]; intro f; [simpl; reflexivity |].
          simpl sum_f_R0. rewrite (IHM f), <- fold_right_Rplus_plus.
          apply fold_right_Rplus_ext; intros q _; reflexivity. }
        rewrite Hswap. apply fold_right_Rplus_ext. intros q _.
        destruct (ob p q).
        - rewrite sum_f_R0_scale. reflexivity.
        - apply sum_f_R0_zero. }
      rewrite Hsum_u.
      assert (Hexp_arg :
        sum_overlap_Lambda ob Lambda p (fun q => wt q * tree_sum_upto ob Lambda wt N' q) <= a p).
      { eapply Rle_trans; [| exact (Hkp p Hp)].
        unfold sum_overlap_Lambda. apply fold_right_Rplus_le. intros q Hq.
        destruct (ob p q); [| lra].
        unfold wt.
        replace (Rabs (w q) * exp (a q + d q)) with (Rabs (w q) * exp (d q) * exp (a q))
          by (rewrite exp_plus; ring).
        apply Rmult_le_compat_l; [apply Hwt_nn | exact (IH q Hq)]. }
      destruct (Rle_lt_or_eq_dec _ _ Hexp_arg) as [Hlt | Heq].
      + left; apply exp_increasing; exact Hlt.
      + rewrite Heq; lra.
  Qed.

  (* Extension to ANY root p0 : P (even p0 not in Lambda) satisfying kp_at p0 *)
  Theorem kp_tree_sum_bound : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (0 <= a p0) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a d p0 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
    forall N,
      tree_sum_upto ob Lambda (fun q => Rabs (w q) * exp (d q)) N p0 <= exp (a p0).
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N.
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hwt_nn : forall q, 0 <= wt q)
      by (intro q; unfold wt; apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]).
    destruct N as [| N'].
    - unfold tree_sum_upto; simpl. rewrite tree_sum_order_0.
      rewrite <- exp_0. destruct (Rle_lt_or_eq_dec 0 (a p0) Ha0) as [Hlt | Heq];
        [left; apply exp_increasing; exact Hlt | rewrite <- Heq; lra].
    - unfold tree_sum_upto.
      set (u := fun s => match s with
        | 0%nat => 0
        | S j => sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt j q)
        end).
      eapply Rle_trans.
      { apply (exp_recurrence_sum_bound (fun k => tree_sum_order ob Lambda wt k p0) u (S N')).
        - apply tree_sum_order_0.
        - intros s Hs. destruct s as [| j]; [lia |]. unfold u, sum_overlap_Lambda.
          apply fold_right_Rplus_nonneg. intros q _.
          destruct (ob p0 q); [| lra].
          apply Rmult_le_pos; [apply Hwt_nn | apply tree_sum_order_nonneg; exact Hwt_nn].
        - intros k Hk.
          rewrite (tree_sum_order_recurrence ob Lambda wt k p0 Hsym ltac:(lia)).
          apply sum_f_R0_ext; intros j _; reflexivity. }
      assert (Hsum_u :
        sum_f_R0 (fun j => u (S j)) N' =
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_upto ob Lambda wt N' q)).
      { unfold u, sum_overlap_Lambda, tree_sum_upto.
        assert (Hswap : forall M (f : nat -> P -> R),
          sum_f_R0 (fun j => fold_right Rplus 0 (map (f j) Lambda)) M =
          fold_right Rplus 0 (map (fun q => sum_f_R0 (fun j => f j q) M) Lambda)).
        { induction M as [| M' IHM]; intro f; [simpl; reflexivity |].
          simpl sum_f_R0. rewrite (IHM f), <- fold_right_Rplus_plus.
          apply fold_right_Rplus_ext; intros q _; reflexivity. }
        rewrite Hswap. apply fold_right_Rplus_ext. intros q _.
        destruct (ob p0 q); [rewrite sum_f_R0_scale; reflexivity | apply sum_f_R0_zero]. }
      rewrite Hsum_u.
      assert (Hexp_arg :
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_upto ob Lambda wt N' q) <= a p0).
      { eapply Rle_trans; [| exact Hkp0].
        unfold sum_overlap_Lambda. apply fold_right_Rplus_le. intros q Hq.
        destruct (ob p0 q); [| lra].
        unfold wt.
        replace (Rabs (w q) * exp (a q + d q)) with (Rabs (w q) * exp (d q) * exp (a q))
          by (rewrite exp_plus; ring).
        apply Rmult_le_compat_l; [apply Hwt_nn |].
        exact (kp_tree_sum_bound_Lambda ob Lambda w a d Hsym Ha_nn Hkp N' q Hq). }
      destruct (Rle_lt_or_eq_dec _ _ Hexp_arg) as [Hlt | Heq];
        [left; apply exp_increasing; exact Hlt | rewrite Heq; lra].
  Qed.

  (* =======================================================================
     5. Main Kotecky-Preiss Pinned Bounds & Exponential Decay (Zero Analytic Assumptions!)
     ======================================================================= *)

  (* 5a-1: Root-pinned Ursell exponential-moment bound *)
  Theorem kp_root_pinned_bound : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (0 <= a p0) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a d p0 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
    forall N,
      root_series Lambda N p0 (fun X =>
        Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp (d q)) (tl X))
      <= exp (a p0).
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N.
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hwt_nn : forall q, 0 <= wt q)
      by (intro q; unfold wt; apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]).
    eapply Rle_trans; [| exact (kp_tree_sum_bound ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N)].
    unfold tree_sum_upto.
    induction N as [| N' IH].
    - simpl. unfold tree_sum_order.
      apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R |].
      apply sum_over_tuples_le. intros Y _.
      apply Rmult_le_compat_r; [apply prod_weight_nonneg; exact Hwt_nn |].
      apply penrose_tree_graph_bound.
    - simpl. apply Rplus_le_compat; [exact IH |].
      unfold tree_sum_order.
      apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R |].
      apply sum_over_tuples_le. intros Y _.
      apply Rmult_le_compat_r; [apply prod_weight_nonneg; exact Hwt_nn |].
      apply penrose_tree_graph_bound.
  Qed.

  (* Helper: union bound on existsb (ob p0) X -> sum_{i < n} [ob p0 (nth i X)] *)
  Lemma existsb_le_sum_indices : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (X : list P),
    (if existsb (ob p0) X then 1 else 0) <=
    fold_right Rplus 0 (map (fun i =>
      match nth_error X i with Some q => if ob p0 q then 1 else 0 | None => 0 end)
      (seq 0%nat (length X))).
  Proof.
    intros P ob p0 X.
    assert (Hnn : forall i, 0 <= match nth_error X i with Some q => if ob p0 q then 1 else 0 | None => 0 end).
    { intro i. destruct (nth_error X i) as [q |]; [destruct (ob p0 q); lra | lra]. }
    destruct (existsb (ob p0) X) eqn:Hex.
    - apply existsb_exists in Hex. destruct Hex as [q [Hq Hob]].
      destruct (In_nth_error X q Hq) as [idx Hidx].
      assert (Hidx_lt : (idx < length X)%nat) by (apply nth_error_Some; congruence).
      assert (Hge : forall l, In idx l ->
        (match nth_error X idx with Some q' => if ob p0 q' then 1 else 0 | None => 0 end) <=
        fold_right Rplus 0 (map (fun i =>
          match nth_error X i with Some q' => if ob p0 q' then 1 else 0 | None => 0 end) l)).
      { induction l as [| a xs IH]; intro Hin; simpl in *; [contradiction |].
        destruct Hin as [-> | Hin].
        - pose proof (fold_right_Rplus_nonneg (fun i =>
            match nth_error X i with Some q' => if ob p0 q' then 1 else 0 | None => 0 end) xs (fun x _ => Hnn x)).
          lra.
        - pose proof (Hnn a). pose proof (IH Hin). lra. }
      specialize (Hge (seq 0%nat (length X)) (proj2 (in_seq (length X) 0%nat idx) ltac:(lia))).
      rewrite Hidx, Hob in Hge. exact Hge.
    - apply fold_right_Rplus_nonneg. intros i _. apply Hnn.
  Qed.

  (* 5a-2: 1-pinned overlap Ursell exponential-moment bound (Kotecky-Preiss Theorem 1) *)
  Theorem kp_overlap_pinned_bound : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (0 <= a p0) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a d p0 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
    forall N_max,
      kp_series Lambda N_max (fun X =>
        if existsb (ob p0) X
        then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp (d q)) X
        else 0) <= a p0.
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N_max.
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hwt_nn : forall q, 0 <= wt q)
      by (intro q; unfold wt; apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]).
    destruct N_max as [| N'].
    - simpl. exact Ha0.
    - (* Step 1: Bound each order n = S k by sum_{q in Lambda, ob p0 q} wt q * tree_sum_order k q *)
      assert (Horder : forall k,
        (/ INR (fact (S k))) *
        sum_over_tuples Lambda (S k) (fun X =>
          if existsb (ob p0) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0) <=
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt k q)).
      { intro k.
        assert (H1 :
          sum_over_tuples Lambda (S k) (fun X =>
            if existsb (ob p0) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0) <=
          sum_over_tuples Lambda (S k) (fun X =>
            fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k))))).
        { apply sum_over_tuples_le. intros X HX.
          pose proof (tuples_of_length_len Lambda (S k) X HX) as HlenX.
          eapply Rle_trans.
          - assert (Hrew : (if existsb (ob p0) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0) =
                           (if existsb (ob p0) X then 1 else 0) * (Rabs (ursell_fn ob X) * prod_weight wt X))
              by (destruct (existsb (ob p0) X); ring).
            rewrite Hrew.
            apply Rmult_le_compat_l; [destruct (existsb (ob p0) X); lra |].
            apply Rmult_le_compat_r; [apply prod_weight_nonneg; exact Hwt_nn |].
            apply penrose_tree_graph_bound.
          - replace (fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k))))
            with (fold_right Rplus 0 (map (fun idx =>
              match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) (seq 0%nat (S k))) *
              (INR (tree_count ob X) * prod_weight wt X)).
            + apply Rmult_le_compat_r.
              * apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hwt_nn].
              * rewrite <- HlenX. apply existsb_le_sum_indices.
            + rewrite <- fold_right_Rplus_scale_r.
              apply fold_right_Rplus_ext; intros idx _; ring. }
        eapply Rle_trans; [apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R | exact H1] |].
        (* Use valid_roots_length_sum + sum_valid_roots_trees! *)
        assert (Heq_vr :
          sum_over_tuples Lambda (S k) (fun X =>
            fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k)))) =
          sum_over_tuples Lambda (S k) (fun X =>
            INR (length (valid_roots ob p0 X)) * INR (tree_count ob X) * prod_weight wt X)).
        { apply sum_over_tuples_ext. intros X HX.
          rewrite (valid_roots_length_sum ob p0 X), (tuples_of_length_len Lambda (S k) X HX).
          rewrite <- !fold_right_Rplus_scale_r. apply fold_right_Rplus_ext; intros idx _; ring. }
        rewrite Heq_vr.
        rewrite (sum_valid_roots_trees ob Lambda wt (S k) p0 Hsym ltac:(lia)).
        replace (S k - 1)%nat with k by lia.
        unfold sum_overlap_Lambda, tree_sum_order.
        rewrite <- !fold_right_Rplus_scale.
        apply fold_right_Rplus_le. intros q _.
        destruct (ob p0 q); [| lra].
        assert (HfactS : INR (fact (S k)) = INR (S k) * INR (fact k)).
        { change (fact (S k)) with (S k * fact k)%nat. rewrite mult_INR. reflexivity. }
        assert (Hne1 : INR (S k) <> 0) by (apply not_0_INR; lia).
        assert (Hne2 : INR (fact k) <> 0) by (apply not_0_INR, fact_neq_0).
        rewrite HfactS. right. field. split; assumption. }
      (* Step 2: Sum over k = 0..N' *)
      assert (Hkp_le :
        kp_series Lambda (S N') (fun X =>
          if existsb (ob p0) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0) <=
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_upto ob Lambda wt N' q)).
      { clear - Horder. induction N' as [| M IH].
        - cbn [kp_series]. rewrite Rplus_0_l.
          eapply Rle_trans; [exact (Horder 0%nat) |].
          unfold tree_sum_upto; simpl. lra.
        - cbn [kp_series].
          eapply Rle_trans; [apply Rplus_le_compat; [exact IH | exact (Horder (S M))] |].
          unfold sum_overlap_Lambda, tree_sum_upto.
          rewrite <- fold_right_Rplus_plus.
          apply fold_right_Rplus_le. intros q _.
          destruct (ob p0 q); [simpl sum_f_R0; lra | lra]. }
      eapply Rle_trans; [exact Hkp_le |].
      eapply Rle_trans; [| exact Hkp0].
      unfold sum_overlap_Lambda. apply fold_right_Rplus_le. intros q Hq.
      destruct (ob p0 q); [| lra].
      unfold wt.
      replace (Rabs (w q) * exp (a q + d q)) with (Rabs (w q) * exp (d q) * exp (a q))
        by (rewrite exp_plus; ring).
      apply Rmult_le_compat_l; [apply Hwt_nn |].
      exact (kp_tree_sum_bound_Lambda ob Lambda w a d Hsym Ha_nn Hkp N' q Hq).
  Qed.

  (* =======================================================================
     6. Metric Distance Bound for Connected Tuples & Correlator Decay
     ======================================================================= *)

  Lemma reachable_k_dist_bound : forall {P : Type} (ob : P -> P -> bool) (dist : P -> P -> R)
    (X : list P) k u v x y,
    (forall p, dist p p = 0) ->
    (forall p q r, dist p r <= dist p q + dist q r) ->
    (forall p q, ob p q = true -> dist p q <= 1) ->
    (forall p q, ob p q = ob q p) ->
    reachable_k (graph_edges ob X) k u v ->
    nth_error X u = Some x ->
    nth_error X v = Some y ->
    dist x y <= INR k.
  Proof.
    intros P ob dist X k u v x y Hrefl Htri Hob_dist Hsym Hrk.
    revert x y. induction Hrk; intros x y Hx Hy.
    - rewrite Hx in Hy. inversion Hy; subst y. rewrite Hrefl. apply pos_INR.
    - pose proof (graph_edges_wf ob X) as [_ Hfor].
      assert (Hedge_dist : forall a b, nth_error X u = Some a -> nth_error X v = Some b -> dist a b <= 1).
      { intros a b Ha Hb. destruct H as [Hin | Hin]; apply graph_edges_in in Hin;
          destruct Hin as [_ [_ [p1 [p2 [Hp1 [Hp2 Hob]]]]]].
        - rewrite Ha in Hp1; rewrite Hb in Hp2; inversion Hp1; inversion Hp2; subst.
          apply Hob_dist; exact Hob.
        - rewrite Hb in Hp1; rewrite Ha in Hp2; inversion Hp1; inversion Hp2; subst.
          apply Hob_dist; rewrite Hsym; exact Hob. }
      pose proof (wf_has_edge_lt (length X) (graph_edges ob X) u v Hfor H) as [_ [Hvlt _]].
      destruct (nth_error X v) as [z |] eqn:Hz; [| apply nth_error_None in Hz; lia].
      pose proof (Hedge_dist x z Hx eq_refl) as H1.
      pose proof (IHHrk z y eq_refl Hy) as H2.
      pose proof (Htri x z y) as H3.
      rewrite S_INR. lra.
  Qed.

  Lemma connected_overlap_dist_bound : forall {P : Type} (ob : P -> P -> bool)
    (dist : P -> P -> R) (size : P -> R) (X : list P) (p1 p2 : P),
    (forall p, dist p p = 0) ->
    (forall p q r, dist p r <= dist p q + dist q r) ->
    (forall p q, ob p q = true -> dist p q <= 1) ->
    (forall p q, ob p q = ob q p) ->
    (forall p, 1 <= size p) ->
    is_connectedb (length X) (graph_edges ob X) = true ->
    existsb (ob p1) X = true ->
    existsb (ob p2) X = true ->
    dist p1 p2 <= fold_right Rplus 0 (map size X) + 1.
  Proof.
    intros P ob dist size X p1 p2 Hrefl Htri Hob_dist Hsym Hsize Hconn Hex1 Hex2.
    apply existsb_exists in Hex1; destruct Hex1 as [q1 [Hq1 Hob1]].
    apply existsb_exists in Hex2; destruct Hex2 as [q2 [Hq2 Hob2]].
    destruct (In_nth_error X q1 Hq1) as [i1 Hi1].
    destruct (In_nth_error X q2 Hq2) as [i2 Hi2].
    assert (Hi1_lt : (i1 < length X)%nat) by (apply nth_error_Some; congruence).
    assert (Hi2_lt : (i2 < length X)%nat) by (apply nth_error_Some; congruence).
    pose proof (graph_edges_wf ob X) as [_ Hfor].
    apply (is_connectedb_iff _ _ Hfor) in Hconn. destruct Hconn as [Hlen_pos Hreach].
    assert (Hr12 : reachable (graph_edges ob X) i1 i2).
    { eapply reachable_trans; [apply reachable_sym; apply Hreach; exact Hi1_lt | apply Hreach; exact Hi2_lt]. }
    pose proof (reachable_bounded_length (length X) (graph_edges ob X) i1 i2 Hfor Hi1_lt Hr12) as Hrk.
    pose proof (reachable_k_dist_bound ob dist X (length X - 1)%nat i1 i2 q1 q2
                  Hrefl Htri Hob_dist Hsym Hrk Hi1 Hi2) as Hd12.
    pose proof (Hob_dist p1 q1 Hob1) as Hd1.
    pose proof (Hob_dist q2 p2 (eq_trans (Hsym q2 p2) Hob2)) as Hd2.
    pose proof (Htri p1 q1 p2) as Ht1.
    pose proof (Htri q1 q2 p2) as Ht2.
    assert (Hsize_sum : INR (length X) <= fold_right Rplus 0 (map size X)).
    { clear - Hsize. induction X as [| a xs IH]; [simpl; lra |].
      cbn [length map fold_right]. rewrite S_INR. pose proof (Hsize a). lra. }
    assert (Hsub : INR (length X - 1) = INR (length X) - 1).
    { destruct (length X) as [| m]; [lia |].
      replace (S m - 1)%nat with m by lia. rewrite S_INR. ring. }
    lra.
  Qed.

  (* 5b: UNCONDITIONAL EXPONENTIAL DECAY OF THE GENUINE URSELL CORRELATOR FROM KP ALONE! *)
  Theorem kp_correlator_exponential_decay : forall {P : Type} (ob : P -> P -> bool)
    (Lambda : list P) (w a size : P -> R) (dist : P -> P -> R) (c : R) (p1 p2 : P),
    (forall x y, ob x y = ob y x) ->
    (forall p, dist p p = 0) ->
    (forall p q r, dist p r <= dist p q + dist q r) ->
    (forall p q, ob p q = true -> dist p q <= 1) ->
    (forall p, 1 <= size p) ->
    0 < c ->
    0 <= a p1 ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a (fun q => c * size q) p1 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a (fun q => c * size q) p) ->
    forall N_max,
      Rabs (ursell_correlator ob Lambda N_max w p1 p2) <=
      a p1 * exp c * exp (- c * dist p1 p2).
  Proof.
    intros P ob Lambda w a size dist c p1 p2 Hsym Hrefl Htri Hob_dist Hsize Hc Ha1 Ha_nn Hkp1 Hkp N_max.
    set (d := fun q => c * size q).
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hstep :
      Rabs (ursell_correlator ob Lambda N_max w p1 p2) <=
      exp c * exp (- c * dist p1 p2) *
      kp_series Lambda N_max (fun X =>
        if existsb (ob p1) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0)).
    { unfold ursell_correlator. induction N_max as [| N' IH].
      - simpl. rewrite Rabs_R0. lra.
      - cbn [kp_series].
        eapply Rle_trans; [apply Rabs_triang |].
        rewrite Rmult_plus_distr_l.
        apply Rplus_le_compat; [exact IH |].
        rewrite Rabs_mult.
        assert (Hinv_pos : 0 < / INR (fact (S N'))) by (apply Rinv_0_lt_compat, fact_pos_R).
        rewrite (Rabs_right (/ INR (fact (S N'))) ltac:(lra)).
        replace (exp c * exp (- c * dist p1 p2) *
                 (/ INR (fact (S N')) *
                  sum_over_tuples Lambda (S N') (fun X =>
                    if existsb (ob p1) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0)))
           with (/ INR (fact (S N')) *
                 sum_over_tuples Lambda (S N') (fun X =>
                   exp c * exp (- c * dist p1 p2) *
                   (if existsb (ob p1) X then Rabs (ursell_fn ob X) * prod_weight wt X else 0)))
          by (rewrite sum_over_tuples_scale; ring).
        apply Rmult_le_compat_l; [lra |].
        unfold sum_over_tuples. apply Rabs_fold_right_Rplus_le.
        intros X HX.
        destruct (existsb (ob p1) X) eqn:Hex1; [| simpl; rewrite Rabs_R0; lra].
        destruct (existsb (ob p2) X) eqn:Hex2; simpl.
        + destruct (Req_dec (ursell_fn ob X) 0) as [Hz | Hnz].
          * rewrite Hz, Rmult_0_l, Rabs_R0. lra.
          * pose proof (ursell_nonzero_connected ob X Hnz) as Hconn.
            pose proof (connected_overlap_dist_bound ob dist size X p1 p2
                          Hrefl Htri Hob_dist Hsym Hsize Hconn Hex1 Hex2) as Hdist.
            rewrite Rabs_mult, Rabs_prod_weight.
            unfold wt. rewrite prod_weight_mul, prod_weight_exp.
            replace (exp c * exp (- c * dist p1 p2) *
                     (Rabs (ursell_fn ob X) *
                      (prod_weight (fun p => Rabs (w p)) X * exp (fold_right Rplus 0 (map d X)))))
               with ((Rabs (ursell_fn ob X) * prod_weight (fun p => Rabs (w p)) X) *
                     (exp c * exp (- c * dist p1 p2) * exp (fold_right Rplus 0 (map d X)))) by ring.
            rewrite <- (Rmult_1_r (Rabs (ursell_fn ob X) * prod_weight (fun p => Rabs (w p)) X)) at 1.
            apply Rmult_le_compat_l.
            { apply Rmult_le_pos; [apply Rabs_pos | apply prod_weight_nonneg; intro q; apply Rabs_pos]. }
            rewrite <- !exp_plus, <- exp_0.
            assert (Hsum_d : fold_right Rplus 0 (map d X) = c * fold_right Rplus 0 (map size X)).
            { unfold d. rewrite <- fold_right_Rplus_scale. reflexivity. }
            rewrite Hsum_d.
            assert (Hge0 : 0 <= c + - c * dist p1 p2 + c * fold_right Rplus 0 (map size X)).
            { nra. }
            destruct (Rle_lt_or_eq_dec _ _ Hge0) as [Hlt | Heq];
              [left; apply exp_increasing; exact Hlt | rewrite <- Heq; lra].
        + rewrite Rabs_R0.
          apply Rmult_le_pos; [apply Rmult_le_pos; left; apply exp_pos |].
          apply Rmult_le_pos; [apply Rabs_pos | apply prod_weight_nonneg; intro q; unfold wt; apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]]. }
    eapply Rle_trans; [exact Hstep |].
    replace (a p1 * exp c * exp (- c * dist p1 p2))
       with (exp c * exp (- c * dist p1 p2) * a p1) by ring.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; left; apply exp_pos |].
    exact (kp_overlap_pinned_bound ob Lambda w a d p1 Hsym Ha1 Ha_nn Hkp1 Hkp N_max).
  Qed.

End KoteckyPreiss.
