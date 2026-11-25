(* =========================================================================
   rg/product_measure.v

   Elementary facts about the finite product a-priori measure of
   rg/dup_clustering.v (the configuration sum `csum`: every variable of a
   list E ranges independently over a finite list `vals` of values):

     - linearity, monotonicity and sup bounds, where the integrand only has
       to be controlled on configurations all of whose values satisfy a
       predicate `good` that holds on `vals`;
     - independence: the sum of a product of two functions that depend on
       disjoint sets of variables factorizes;
     - symmetry: if a map sigma permutes `vals` (in the sense that it
       preserves every sum over `vals`), then applying sigma to the value of
       ONE variable of E does not change a configuration sum;
     - the expansion of prod (x + y) over the ordered splittings of a list.

   Depends ONLY on Coq stdlib + rg.dup_clustering.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
From rg Require Import dup_clustering.
Import ListNotations.
Import DupClustering.
Open Scope R_scope.

Module ProductMeasure.

  (* =======================================================================
     1. Finite sums and products over lists
     ======================================================================= *)

  Lemma rsum_const : forall {A : Type} (l : list A) (c : R),
    rsum l (fun _ => c) = INR (length l) * c.
  Proof.
    intros A l c. induction l as [| a l IH].
    - rewrite rsum_nil. cbn [length INR]. ring.
    - rewrite rsum_cons, IH. cbn [length]. rewrite S_INR. ring.
  Qed.

  Lemma rsum_perm : forall {A : Type} (l l' : list A) (f : A -> R),
    Permutation l l' -> rsum l f = rsum l' f.
  Proof.
    intros A l l' f H. induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2].
    - reflexivity.
    - rewrite !rsum_cons, IH. reflexivity.
    - rewrite !rsum_cons. ring.
    - rewrite IH1. exact IH2.
  Qed.

  Lemma rprod_abs : forall {A : Type} (l : list A) (f : A -> R),
    Rabs (rprod l f) = rprod l (fun x => Rabs (f x)).
  Proof.
    intros A l f. induction l as [| a l IH].
    - rewrite !rprod_nil. apply Rabs_R1.
    - rewrite !rprod_cons, Rabs_mult, IH. reflexivity.
  Qed.

  Lemma rprod_ge_1 : forall {A : Type} (l : list A) (f : A -> R),
    (forall x, In x l -> 1 <= f x) -> 1 <= rprod l f.
  Proof.
    intros A l f H. induction l as [| a l IH].
    - rewrite rprod_nil. apply Rle_refl.
    - rewrite rprod_cons.
      assert (Ha : 1 <= f a) by (apply H; left; reflexivity).
      assert (Hl : 1 <= rprod l f) by (apply IH; intros x Hx; apply H; right; exact Hx).
      replace 1 with (1 * 1) by ring. apply Rmult_le_compat; lra.
  Qed.

  (* removing factors >= 1 can only decrease a product *)
  Lemma rprod_filter_le : forall {A : Type} (f : A -> bool) (g : A -> R) (l : list A),
    (forall x, In x l -> 1 <= g x) -> rprod (filter f l) g <= rprod l g.
  Proof.
    intros A f g l H. induction l as [| a l IH].
    - cbn [filter]. apply Rle_refl.
    - assert (Ha : 1 <= g a) by (apply H; left; reflexivity).
      assert (IH' : rprod (filter f l) g <= rprod l g)
        by (apply IH; intros x Hx; apply H; right; exact Hx).
      assert (H1 : 1 <= rprod (filter f l) g).
      { apply rprod_ge_1. intros x Hx. apply filter_In in Hx. apply H. right. tauto. }
      cbn [filter]. destruct (f a); rewrite !rprod_cons.
      + apply Rmult_le_compat_l; lra.
      + apply Rle_trans with (rprod l g); [exact IH' |].
        rewrite <- (Rmult_1_l (rprod l g)) at 1.
        apply Rmult_le_compat_r; lra.
  Qed.

  (* ordered splittings of a list into two complementary sublists *)
  Fixpoint splits {A : Type} (l : list A) : list (list A * list A) :=
    match l with
    | [] => [([], [])]
    | a :: l' =>
        map (fun P => (fst P, a :: snd P)) (splits l') ++
        map (fun P => (a :: fst P, snd P)) (splits l')
    end.

  Lemma splits_spec : forall {A : Type} (l : list A) (P : list A * list A),
    In P (splits l) ->
    incl (fst P) l /\ incl (snd P) l /\ (length (fst P) + length (snd P) = length l)%nat.
  Proof.
    intros A l. induction l as [| a l IH]; intros P HP.
    - cbn [splits] in HP. destruct HP as [<- | []]. cbn [fst snd length].
      split; [intros x [] | split; [intros x [] | reflexivity]].
    - cbn [splits] in HP. apply in_app_or in HP.
      destruct HP as [HP | HP]; apply in_map_iff in HP; destruct HP as [Q [<- HQ]];
        destruct (IH Q HQ) as [H1 [H2 H3]]; cbn [fst snd length].
      + split; [| split].
        * intros x Hx. right. exact (H1 x Hx).
        * intros x [<- | Hx]; [left; reflexivity | right; exact (H2 x Hx)].
        * lia.
      + split; [| split].
        * intros x [<- | Hx]; [left; reflexivity | right; exact (H1 x Hx)].
        * intros x Hx. right. exact (H2 x Hx).
        * lia.
  Qed.

  (* prod (x + y) = sum over splittings (R, R') of prod_R y * prod_R' x *)
  Lemma rprod_plus_splits : forall {A : Type} (l : list A) (x y : A -> R),
    rprod l (fun b => x b + y b) =
    rsum (splits l) (fun P => rprod (fst P) y * rprod (snd P) x).
  Proof.
    intros A l x y. induction l as [| a l IH].
    - cbn [splits]. rewrite rsum_cons, rsum_nil. cbn [fst snd]. rewrite !rprod_nil. ring.
    - cbn [splits]. rewrite rsum_app, !rsum_map, rprod_cons, IH.
      transitivity
        (x a * rsum (splits l) (fun P => rprod (fst P) y * rprod (snd P) x)
         + y a * rsum (splits l) (fun P => rprod (fst P) y * rprod (snd P) x));
        [ring |].
      rewrite <- !rsum_scal. f_equal; apply rsum_ext; intros P _; cbn [fst snd];
        rewrite rprod_cons; ring.
  Qed.

  (* =======================================================================
     2. Configuration sums
     ======================================================================= *)

  Section PM.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable vals : list V.

    Local Notation Cfg := (cfg L V).
    Local Notation Upd := (upd L V eqbL).
    Local Notation Csum := (csum L V eqbL vals).

    Lemma eqbL_refl : forall e, eqbL e e = true.
    Proof. intro e. apply eqbL_spec. reflexivity. Qed.

    Lemma eqbL_neq : forall e e', e <> e' -> eqbL e e' = false.
    Proof.
      intros e e' H. destruct (eqbL e e') eqn:He; [| reflexivity].
      apply eqbL_spec in He. contradiction.
    Qed.

    Lemma upd_same : forall (U : Cfg) e v, Upd U e v e = v.
    Proof. intros U e v. unfold upd. rewrite eqbL_refl. reflexivity. Qed.

    Lemma upd_other : forall (U : Cfg) e e' v, e' <> e -> Upd U e v e' = U e'.
    Proof. intros U e e' v H. unfold upd. rewrite (eqbL_neq e' e H). reflexivity. Qed.

    Lemma upd_twice : forall (U : Cfg) e v w, Upd (Upd U e v) e w = Upd U e w.
    Proof.
      intros U e v w. apply functional_extensionality. intro x. unfold upd.
      destruct (eqbL x e); reflexivity.
    Qed.

    Lemma upd_comm : forall (U : Cfg) e e' v w, e <> e' ->
      Upd (Upd U e v) e' w = Upd (Upd U e' w) e v.
    Proof.
      intros U e e' v w Hne. apply functional_extensionality. intro x. unfold upd.
      destruct (eqbL x e') eqn:H1, (eqbL x e) eqn:H2; try reflexivity.
      exfalso. apply Hne. apply eqbL_spec in H1. apply eqbL_spec in H2. congruence.
    Qed.

    (* ---------- linearity and bounds ---------- *)

    Lemma csum_rsum : forall {X : Type} (l : list X) E (F : X -> Cfg -> R) U,
      Csum E (fun A => rsum l (fun x => F x A)) U = rsum l (fun x => Csum E (F x) U).
    Proof.
      intros X l E. induction E as [| e E IH]; intros F U; [reflexivity |].
      cbn [csum].
      rewrite (rsum_swap l vals (fun x v => Csum E (F x) (Upd U e v))).
      apply rsum_ext. intros v _. apply IH.
    Qed.

    Lemma csum_const : forall E c U,
      Csum E (fun _ => c) U = c * INR (length vals) ^ length E.
    Proof.
      induction E as [| e E IH]; intros c U.
      - cbn [csum length pow]. ring.
      - cbn [csum length pow].
        rewrite (rsum_ext vals (fun v => Csum E (fun _ => c) (Upd U e v))
                   (fun _ => c * INR (length vals) ^ length E)).
        + rewrite rsum_const. ring.
        + intros v _. apply IH.
    Qed.

    Lemma csum_abs : forall E F U, Rabs (Csum E F U) <= Csum E (fun A => Rabs (F A)) U.
    Proof.
      induction E as [| e E IH]; intros F U; [apply Rle_refl |].
      cbn [csum]. eapply Rle_trans; [apply rsum_abs |].
      apply rsum_le. intros v _. apply IH.
    Qed.

    (* ---------- integrands controlled on "good" configurations ---------- *)

    Variable good : V -> Prop.
    Hypothesis vals_good : forall v, In v vals -> good v.

    Definition gcfg (A : Cfg) : Prop := forall e, good (A e).

    Lemma gcfg_upd : forall (A : Cfg) e v, gcfg A -> In v vals -> gcfg (Upd A e v).
    Proof.
      intros A e v HA Hv x. unfold upd.
      destruct (eqbL x e); [apply vals_good; exact Hv | apply HA].
    Qed.

    Lemma csum_ext_good : forall E F G, (forall A, gcfg A -> F A = G A) ->
      forall U, gcfg U -> Csum E F U = Csum E G U.
    Proof.
      induction E as [| e E IH]; intros F G H U HU; [apply H; exact HU |].
      cbn [csum]. apply rsum_ext. intros v Hv. apply IH; [exact H |].
      apply gcfg_upd; assumption.
    Qed.

    Lemma csum_le_good : forall E F G, (forall A, gcfg A -> F A <= G A) ->
      forall U, gcfg U -> Csum E F U <= Csum E G U.
    Proof.
      induction E as [| e E IH]; intros F G H U HU; [apply H; exact HU |].
      cbn [csum]. apply rsum_le. intros v Hv. apply IH; [exact H |].
      apply gcfg_upd; assumption.
    Qed.

    Lemma csum_bound_good : forall E F M, (forall A, gcfg A -> Rabs (F A) <= M) ->
      forall U, gcfg U -> Rabs (Csum E F U) <= M * INR (length vals) ^ length E.
    Proof.
      intros E F M H U HU. eapply Rle_trans; [apply csum_abs |].
      rewrite <- (csum_const E M U). apply csum_le_good; [exact H | exact HU].
    Qed.

    (* ---------- independence ---------- *)

    (* F only depends on the variables listed in S *)
    Definition local_on (S : list L) (F : Cfg -> R) : Prop :=
      forall A A', (forall e, In e S -> A e = A' e) -> F A = F A'.

    Lemma csum_upd_out : forall S F, local_on S F -> forall e, ~ In e S ->
      forall E v U, Csum E F (Upd U e v) = Csum E F U.
    Proof.
      intros S F HF e He E. induction E as [| e' E IH]; intros v U.
      - cbn [csum]. apply HF. intros x Hx. apply upd_other.
        intro Heq. subst x. contradiction.
      - cbn [csum]. apply rsum_ext. intros v' _.
        destruct (eqbL e e') eqn:Hee.
        + apply eqbL_spec in Hee. subst e'. rewrite upd_twice. reflexivity.
        + assert (Hne : e <> e').
          { intro Heq. subst e'. rewrite eqbL_refl in Hee. discriminate. }
          rewrite (upd_comm U e e' v v' Hne). apply IH.
    Qed.

    Lemma csum_indep_step : forall S2 F G, local_on S2 G -> forall e, ~ In e S2 ->
      forall E U,
      (forall U', Csum E (fun A => F A * G A) U' * INR (length vals) ^ length E
                  = Csum E F U' * Csum E G U') ->
      Csum (e :: E) (fun A => F A * G A) U * INR (length vals) ^ length (e :: E)
      = Csum (e :: E) F U * Csum (e :: E) G U.
    Proof.
      intros S2 F G HG e He2 E U IH.
      cbn [csum length pow].
      rewrite (rsum_ext vals (fun v => Csum E G (Upd U e v)) (fun _ => Csum E G U)).
      2: { intros v _. apply (csum_upd_out S2 G HG e He2). }
      rewrite rsum_const.
      transitivity
        (INR (length vals) *
         rsum vals (fun v => Csum E (fun A => F A * G A) (Upd U e v)
                             * INR (length vals) ^ length E)).
      { rewrite rsum_scal_r. ring. }
      rewrite (rsum_ext vals
                 (fun v => Csum E (fun A => F A * G A) (Upd U e v)
                           * INR (length vals) ^ length E)
                 (fun v => Csum E F (Upd U e v) * Csum E G U)).
      2: { intros v _. rewrite IH. rewrite (csum_upd_out S2 G HG e He2). reflexivity. }
      rewrite rsum_scal_r. ring.
    Qed.

    (* the sum of a product of functions of disjoint sets of variables factorizes *)
    Lemma csum_indep : forall S1 S2 F G, local_on S1 F -> local_on S2 G ->
      (forall e, In e S1 -> In e S2 -> False) ->
      forall E U,
      Csum E (fun A => F A * G A) U * INR (length vals) ^ length E
      = Csum E F U * Csum E G U.
    Proof.
      intros S1 S2 F G HF HG Hdis E. induction E as [| e E IH]; intro U.
      - cbn [csum length pow]. ring.
      - destruct (memb eqbL e S1) eqn:Hm.
        + apply (memb_In eqbL eqbL_spec) in Hm.
          assert (He2 : ~ In e S2) by (intro H2; exact (Hdis e Hm H2)).
          exact (csum_indep_step S2 F G HG e He2 E U IH).
        + apply (memb_false eqbL eqbL_spec) in Hm.
          assert (IH' : forall U',
                    Csum E (fun A => G A * F A) U' * INR (length vals) ^ length E
                    = Csum E G U' * Csum E F U').
          { intro U'. rewrite (csum_ext L V eqbL vals E (fun A => G A * F A)
                                 (fun A => F A * G A)) by (intro A; ring).
            rewrite IH. ring. }
          pose proof (csum_indep_step S1 G F HF e Hm E U IH') as H.
          rewrite (csum_ext L V eqbL vals (e :: E) (fun A => F A * G A)
                     (fun A => G A * F A)) by (intro A; ring).
          rewrite H. ring.
    Qed.

    (* ---------- applying a symmetry of `vals` to one variable ---------- *)

    Variable sigma : V -> V.
    Hypothesis sigma_sum : forall h : V -> R,
      rsum vals (fun v => h (sigma v)) = rsum vals h.

    Definition flip (e : L) (A : Cfg) : Cfg := Upd A e (sigma (A e)).

    Lemma csum_push_upd : forall E e w F U, ~ In e E ->
      Csum E (fun A => F (Upd A e w)) U = Csum E F (Upd U e w).
    Proof.
      induction E as [| e' E IH]; intros e w F U Hn; [reflexivity |].
      cbn [csum]. apply rsum_ext. intros v _.
      assert (Hne : e' <> e) by (intro Heq; apply Hn; left; exact Heq).
      rewrite IH by (intro Hin; apply Hn; right; exact Hin).
      rewrite (upd_comm U e' e v w Hne). reflexivity.
    Qed.

    Lemma csum_val_out : forall E e (K : V -> Cfg -> R) U, ~ In e E ->
      Csum E (fun A => K (A e) A) U = Csum E (K (U e)) U.
    Proof.
      induction E as [| e' E IH]; intros e K U Hn; [reflexivity |].
      cbn [csum]. apply rsum_ext. intros v _.
      rewrite IH by (intro Hin; apply Hn; right; exact Hin).
      rewrite upd_other; [reflexivity |].
      intro Heq. apply Hn. left. symmetry. exact Heq.
    Qed.

    Lemma csum_flip : forall E e F U, NoDup E -> In e E ->
      Csum E (fun A => F (flip e A)) U = Csum E F U.
    Proof.
      induction E as [| e' E IH]; intros e F U Hnd Hin; [contradiction |].
      inversion Hnd as [| x l Hnotin Hnd']; subst.
      cbn [csum].
      destruct (eqbL e e') eqn:Hee.
      - apply eqbL_spec in Hee. subst e'.
        rewrite <- (sigma_sum (fun v => Csum E F (Upd U e v))).
        apply rsum_ext. intros v _. unfold flip.
        etransitivity;
          [exact (csum_val_out E e (fun w A => F (Upd A e (sigma w))) (Upd U e v) Hnotin) |].
        cbv beta. rewrite upd_same.
        rewrite (csum_push_upd E e (sigma v) F (Upd U e v) Hnotin).
        rewrite upd_twice. reflexivity.
      - assert (Hne : e <> e').
        { intro Heq. subst e'. rewrite eqbL_refl in Hee. discriminate. }
        apply rsum_ext. intros v _. apply IH; [exact Hnd' |].
        destruct Hin as [Heq | Hin]; [exfalso; apply Hne; symmetry; exact Heq | exact Hin].
    Qed.

  End PM.

End ProductMeasure.
