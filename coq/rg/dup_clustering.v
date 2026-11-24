(* =========================================================================
   rg/dup_clustering.v

   Abstract strong-coupling (high-temperature) clustering theorem for finite
   lattice systems with a product a-priori measure, by the duplicate-system
   ("two independent copies") expansion.

   Setting.
     - variables indexed by a type L, each taking values in the finite list
       `vals : list V` (uniform a-priori counting measure),
     - local factors indexed by `Lam : list B`; the factor b has weight
       phi b (U) > 0 depending only on U restricted to `supp b`,
     - Gibbs weight  W(U) = prod_{b in Lam} phi b (U),
     - observables f, g supported on the link lists Sf, Sg.

   Hypothesis (small oscillation of every factor on the doubled system):
       m <= phi b (A) * phi b (A')
       phi b (A) * phi b (A') - m <= eps * (phi b (A) * phi b (A')).

   Conclusion (`dup_clustering`):
       |<f g> - <f><g>| <= (Df * Dg / 2) * sum_{k = 0}^{|Lam|} reach k Sf,
     where Df, Dg bound the oscillations of f, g and `reach k Sf` is the
     eps^k-weighted number of chains b_1, ..., b_k of factors of Lam with
     Sf ~ b_1 ~ b_2 ~ ... ~ b_k ~ Sg (consecutive supports intersect).

   Proof idea.  2 Z^2 (<fg> - <f><g>) is the sum over pairs (A, A') of
   (f A - f A')(g A - g A') W(A) W(A').  Writing each doubled factor as
   m + (phi phi' - m) and expanding the product over Lam gives a sum over
   subsets R of Lam.  If R contains no chain from Sf to Sg, exchanging
   A <-> A' on the links reachable from Sf through R is a weight-preserving
   involution that flips the sign of f A - f A' and fixes g A - g A', so
   the term vanishes.  The remaining terms are bounded by a union bound over
   duplicate-free chains.

   Depends ONLY on the Coq standard library.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope R_scope.

Module DupClustering.

  (* =======================================================================
     1. Finite sums and products over lists
     ======================================================================= *)

  Definition rsum {A : Type} (l : list A) (f : A -> R) : R :=
    fold_right Rplus 0 (map f l).

  Definition rprod {A : Type} (l : list A) (f : A -> R) : R :=
    fold_right Rmult 1 (map f l).

  Lemma rsum_nil : forall {A : Type} (f : A -> R), rsum [] f = 0.
  Proof. reflexivity. Qed.

  Lemma rsum_cons : forall {A : Type} (a : A) (l : list A) (f : A -> R),
    rsum (a :: l) f = f a + rsum l f.
  Proof. reflexivity. Qed.

  Lemma rsum_app : forall {A : Type} (l1 l2 : list A) (f : A -> R),
    rsum (l1 ++ l2) f = rsum l1 f + rsum l2 f.
  Proof.
    intros A l1 l2 f. unfold rsum. induction l1 as [| a l1 IH]; simpl.
    - lra.
    - rewrite IH. lra.
  Qed.

  Lemma rsum_ext : forall {A : Type} (l : list A) (f g : A -> R),
    (forall x, In x l -> f x = g x) -> rsum l f = rsum l g.
  Proof.
    intros A l f g H. unfold rsum. induction l as [| a l IH]; simpl; [reflexivity |].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
    intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rsum_plus : forall {A : Type} (l : list A) (f g : A -> R),
    rsum l (fun x => f x + g x) = rsum l f + rsum l g.
  Proof.
    intros A l f g. unfold rsum. induction l as [| a l IH]; simpl; [lra | rewrite IH; lra].
  Qed.

  Lemma rsum_scal : forall {A : Type} (l : list A) (c : R) (f : A -> R),
    rsum l (fun x => c * f x) = c * rsum l f.
  Proof.
    intros A l c f. unfold rsum. induction l as [| a l IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma rsum_scal_r : forall {A : Type} (l : list A) (c : R) (f : A -> R),
    rsum l (fun x => f x * c) = rsum l f * c.
  Proof.
    intros A l c f. unfold rsum. induction l as [| a l IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma rsum_le : forall {A : Type} (l : list A) (f g : A -> R),
    (forall x, In x l -> f x <= g x) -> rsum l f <= rsum l g.
  Proof.
    intros A l f g H. unfold rsum. induction l as [| a l IH]; simpl; [lra |].
    apply Rplus_le_compat.
    - apply H. left. reflexivity.
    - apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rsum_nonneg : forall {A : Type} (l : list A) (f : A -> R),
    (forall x, In x l -> 0 <= f x) -> 0 <= rsum l f.
  Proof.
    intros A l f H. unfold rsum. induction l as [| a l IH]; simpl; [lra |].
    apply Rplus_le_le_0_compat.
    - apply H. left. reflexivity.
    - apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rsum_zero : forall {A : Type} (l : list A) (f : A -> R),
    (forall x, In x l -> f x = 0) -> rsum l f = 0.
  Proof.
    intros A l f H. unfold rsum. induction l as [| a l IH]; simpl; [reflexivity |].
    rewrite (H a (or_introl eq_refl)), IH; [lra |].
    intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rsum_abs : forall {A : Type} (l : list A) (f : A -> R),
    Rabs (rsum l f) <= rsum l (fun x => Rabs (f x)).
  Proof.
    intros A l f. unfold rsum. induction l as [| a l IH]; simpl.
    - rewrite Rabs_R0. lra.
    - eapply Rle_trans; [apply Rabs_triang |]. lra.
  Qed.

  Lemma rsum_swap : forall {A B : Type} (l1 : list A) (l2 : list B) (f : A -> B -> R),
    rsum l1 (fun a => rsum l2 (fun b => f a b)) =
    rsum l2 (fun b => rsum l1 (fun a => f a b)).
  Proof.
    intros A B l1 l2 f. induction l1 as [| a l1 IH].
    - rewrite rsum_nil. symmetry. apply rsum_zero. intros b _. apply rsum_nil.
    - rewrite rsum_cons, IH, <- rsum_plus. apply rsum_ext. intros b _.
      rewrite rsum_cons. reflexivity.
  Qed.

  Lemma rsum_mult : forall {A B : Type} (l1 : list A) (l2 : list B) (f : A -> R) (g : B -> R),
    rsum l1 f * rsum l2 g = rsum l1 (fun a => rsum l2 (fun b => f a * g b)).
  Proof.
    intros A B l1 l2 f g. induction l1 as [| a l1 IH].
    - rewrite !rsum_nil. ring.
    - rewrite !rsum_cons, <- IH, rsum_scal. ring.
  Qed.

  Lemma rsum_ge_term : forall {A : Type} (l : list A) (f : A -> R) (a : A),
    (forall x, In x l -> 0 <= f x) -> In a l -> f a <= rsum l f.
  Proof.
    intros A l f a Hnn Hin. induction l as [| b l IH]; [contradiction |].
    rewrite rsum_cons.
    assert (Hb : 0 <= f b) by (apply Hnn; left; reflexivity).
    assert (Hl : 0 <= rsum l f) by (apply rsum_nonneg; intros x Hx; apply Hnn; right; exact Hx).
    destruct Hin as [-> | Hin]; [lra |].
    assert (f a <= rsum l f) by (apply IH; [intros x Hx; apply Hnn; right; exact Hx | exact Hin]).
    lra.
  Qed.

  Lemma rsum_flat_map : forall {A B : Type} (h : A -> list B) (l : list A) (f : B -> R),
    rsum (flat_map h l) f = rsum l (fun a => rsum (h a) f).
  Proof.
    intros A B h l f. induction l as [| a l IH]; [reflexivity |].
    cbn [flat_map]. rewrite rsum_app, rsum_cons, IH. reflexivity.
  Qed.

  Lemma rsum_map : forall {A B : Type} (h : A -> B) (l : list A) (f : B -> R),
    rsum (map h l) f = rsum l (fun a => f (h a)).
  Proof. intros A B h l f. unfold rsum. rewrite map_map. reflexivity. Qed.

  Lemma rsum_filter : forall {A : Type} (P : A -> bool) (l : list A) (f : A -> R),
    rsum (filter P l) f = rsum l (fun x => if P x then f x else 0).
  Proof.
    intros A P l f. unfold rsum. induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (P a); simpl; rewrite IH; lra.
  Qed.

  Lemma rsum_pos : forall {A : Type} (l : list A) (f : A -> R),
    l <> [] -> (forall x, In x l -> 0 < f x) -> 0 < rsum l f.
  Proof.
    intros A l f Hne Hpos. destruct l as [| a l]; [congruence |].
    rewrite rsum_cons.
    assert (Ha : 0 < f a) by (apply Hpos; left; reflexivity).
    assert (Hl : 0 <= rsum l f).
    { apply rsum_nonneg. intros x Hx. left. apply Hpos. right. exact Hx. }
    lra.
  Qed.

  Lemma rsum_indicator_const : forall {A : Type} (P : A -> bool) (c : R) (l : list A),
    rsum l (fun x => if P x then c else 0) = INR (length (filter P l)) * c.
  Proof.
    intros A P c l. unfold rsum. induction l as [| a l IH]; simpl; [ring |].
    destruct (P a).
    - cbn [length]. rewrite S_INR, IH. ring.
    - rewrite IH. ring.
  Qed.

  Lemma rprod_nil : forall {A : Type} (f : A -> R), rprod [] f = 1.
  Proof. reflexivity. Qed.

  Lemma rprod_cons : forall {A : Type} (a : A) (l : list A) (f : A -> R),
    rprod (a :: l) f = f a * rprod l f.
  Proof. reflexivity. Qed.

  Lemma rprod_app : forall {A : Type} (l1 l2 : list A) (f : A -> R),
    rprod (l1 ++ l2) f = rprod l1 f * rprod l2 f.
  Proof.
    intros A l1 l2 f. unfold rprod. induction l1 as [| a l1 IH]; simpl.
    - ring.
    - rewrite IH. ring.
  Qed.

  Lemma rprod_ext : forall {A : Type} (l : list A) (f g : A -> R),
    (forall x, In x l -> f x = g x) -> rprod l f = rprod l g.
  Proof.
    intros A l f g H. unfold rprod. induction l as [| a l IH]; simpl; [reflexivity |].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
    intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rprod_mult : forall {A : Type} (l : list A) (f g : A -> R),
    rprod l (fun x => f x * g x) = rprod l f * rprod l g.
  Proof.
    intros A l f g. unfold rprod. induction l as [| a l IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma rprod_nonneg : forall {A : Type} (l : list A) (f : A -> R),
    (forall x, In x l -> 0 <= f x) -> 0 <= rprod l f.
  Proof.
    intros A l f H. unfold rprod. induction l as [| a l IH]; simpl; [lra |].
    apply Rmult_le_pos.
    - apply H. left. reflexivity.
    - apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rprod_pos : forall {A : Type} (l : list A) (f : A -> R),
    (forall x, In x l -> 0 < f x) -> 0 < rprod l f.
  Proof.
    intros A l f H. unfold rprod. induction l as [| a l IH]; simpl; [lra |].
    apply Rmult_lt_0_compat.
    - apply H. left. reflexivity.
    - apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rprod_le : forall {A : Type} (l : list A) (f g : A -> R),
    (forall x, In x l -> 0 <= f x <= g x) -> rprod l f <= rprod l g.
  Proof.
    intros A l f g H. induction l as [| a l IH].
    - rewrite !rprod_nil. lra.
    - rewrite !rprod_cons.
      destruct (H a (or_introl eq_refl)) as [H0 H1].
      apply Rmult_le_compat.
      + exact H0.
      + apply rprod_nonneg. intros x Hx. apply (H x). right. exact Hx.
      + exact H1.
      + apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma rprod_indicator_pow : forall {A : Type} (P : A -> bool) (c : R) (l : list A),
    rprod l (fun x => if P x then c else 1) = c ^ length (filter P l).
  Proof.
    intros A P c l. unfold rprod. induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (P a); simpl; rewrite IH; ring.
  Qed.

  Lemma rprod_const : forall {A : Type} (c : R) (l : list A),
    rprod l (fun _ => c) = c ^ length l.
  Proof.
    intros A c l. unfold rprod. induction l as [| a l IH]; simpl; [reflexivity | rewrite IH; ring].
  Qed.

  Global Arguments rsum : simpl never.
  Global Arguments rprod : simpl never.

  (* =======================================================================
     2. Sublists (subsets), boolean membership, and the product expansion
     ======================================================================= *)

  Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
    match l with
    | [] => [[]]
    | x :: xs => sublists xs ++ map (cons x) (sublists xs)
    end.

  Lemma sublists_incl : forall {A : Type} (l S : list A),
    In S (sublists l) -> incl S l.
  Proof.
    intros A l. induction l as [| a l IH]; intros S HS; simpl in HS.
    - destruct HS as [<- | []]. intros x Hx. exact Hx.
    - apply in_app_or in HS. destruct HS as [HS | HS].
      + intros x Hx. right. exact (IH S HS x Hx).
      + apply in_map_iff in HS. destruct HS as [S' [<- HS']].
        intros x [<- | Hx]; [left; reflexivity | right; exact (IH S' HS' x Hx)].
  Qed.

  (* prod (1 + y) = sum over sublists of prod y  (no duplicate-freeness needed) *)
  Lemma rprod_one_plus : forall {A : Type} (l : list A) (y : A -> R),
    rprod l (fun b => 1 + y b) = rsum (sublists l) (fun S => rprod S y).
  Proof.
    intros A l y. induction l as [| a l IH].
    - cbn [sublists]. rewrite rsum_cons, rsum_nil, !rprod_nil. lra.
    - cbn [sublists]. rewrite rsum_app, rsum_map, rprod_cons, IH.
      transitivity (rsum (sublists l) (fun S => rprod S y)
                    + y a * rsum (sublists l) (fun S => rprod S y)); [ring |].
      rewrite <- rsum_scal. f_equal.
  Qed.

  Lemma NoDup_app_l : forall {A : Type} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
  Proof.
    intros A l1 l2. induction l1 as [| a l1 IH]; intro H; [constructor |].
    simpl in H. inversion H as [| a' l' Hnin Hnd]; subst.
    constructor.
    - intro Hin. apply Hnin. apply in_or_app. left. exact Hin.
    - apply IH. exact Hnd.
  Qed.

  Lemma NoDup_snoc : forall {A : Type} (l : list A) (b : A),
    NoDup l -> ~ In b l -> NoDup (l ++ [b]).
  Proof.
    intros A l b. induction l as [| a l IH]; intros Hnd Hnin; simpl.
    - constructor; [intros [] | constructor].
    - inversion Hnd as [| a' l' Hna Hnd']; subst. constructor.
      + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]].
        * contradiction.
        * apply Hnin. left. symmetry. exact Heq.
      + apply IH; [exact Hnd' |]. intro Hin. apply Hnin. right. exact Hin.
  Qed.

  Lemma NoDup_prefix_snoc : forall {A : Type} (o1 o2 : list A) (b : A),
    NoDup (o1 ++ b :: o2) -> NoDup (o1 ++ [b]).
  Proof.
    intros A o1 o2 b H. apply NoDup_remove in H. destruct H as [H1 H2].
    apply NoDup_snoc.
    - exact (NoDup_app_l o1 o2 H1).
    - intro Hin. apply H2. apply in_or_app. left. exact Hin.
  Qed.

  Section Mem.
    Context {A : Type} (eqb : A -> A -> bool).
    Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

    Definition memb (x : A) (l : list A) : bool := existsb (eqb x) l.

    Lemma memb_In : forall x l, memb x l = true <-> In x l.
    Proof.
      intros x l. unfold memb. rewrite existsb_exists. split.
      - intros [y [Hy He]]. apply eqb_spec in He. subst y. exact Hy.
      - intro Hx. exists x. split; [exact Hx | apply eqb_spec; reflexivity].
    Qed.

    Lemma memb_false : forall x l, memb x l = false <-> ~ In x l.
    Proof.
      intros x l. rewrite <- memb_In. destruct (memb x l); split; intro H.
      - discriminate.
      - exfalso. apply H. reflexivity.
      - discriminate.
      - reflexivity.
    Qed.

    Fixpoint nodupb (l : list A) : bool :=
      match l with
      | [] => true
      | x :: xs => negb (memb x xs) && nodupb xs
      end.

    Lemma nodupb_NoDup : forall l, nodupb l = true <-> NoDup l.
    Proof.
      induction l as [| a l IH]; simpl.
      - split; [intros _; constructor | reflexivity].
      - rewrite andb_true_iff, negb_true_iff, memb_false, IH. split.
        + intros [H1 H2]. constructor; assumption.
        + intro H. inversion H; subst. split; assumption.
    Qed.

    (* prod_{b in l} (x b + y b) = sum_{R <= l} prod_{b in l} [b in R ? y b : x b] *)
    Lemma prod_expand : forall (l : list A) (x y : A -> R),
      NoDup l ->
      rprod l (fun b => x b + y b) =
      rsum (sublists l) (fun R => rprod l (fun b => if memb b R then y b else x b)).
    Proof.
      induction l as [| a l IH]; intros x y Hnd.
      - cbn [sublists]. rewrite rsum_cons, rsum_nil, !rprod_nil. lra.
      - inversion Hnd as [| a' l' Hnotin Hnd']; subst.
        cbn [sublists]. rewrite rsum_app, rsum_map, rprod_cons, (IH x y Hnd').
        transitivity
          (x a * rsum (sublists l) (fun R => rprod l (fun b => if memb b R then y b else x b))
           + y a * rsum (sublists l) (fun R => rprod l (fun b => if memb b R then y b else x b)));
          [ring |].
        rewrite <- !rsum_scal. f_equal.
        + apply rsum_ext. intros R HR. rewrite rprod_cons.
          assert (Hma : memb a R = false).
          { apply memb_false. intro Hin. apply Hnotin. exact (sublists_incl l R HR a Hin). }
          rewrite Hma. reflexivity.
        + apply rsum_ext. intros R HR. rewrite rprod_cons.
          assert (Hma : memb a (a :: R) = true) by (apply memb_In; left; reflexivity).
          rewrite Hma. f_equal.
          apply rprod_ext. intros b Hb.
          assert (Hne : eqb b a = false).
          { destruct (eqb b a) eqn:Heq; [| reflexivity].
            apply eqb_spec in Heq. subst b. contradiction. }
          unfold memb. cbn [existsb]. rewrite Hne. reflexivity.
    Qed.

    Lemma filter_memb_length : forall (om l : list A),
      NoDup om -> NoDup l -> incl om l ->
      length (filter (fun b => memb b om) l) = length om.
    Proof.
      intros om l Hom Hl Hincl. apply Nat.le_antisymm.
      - apply NoDup_incl_length; [apply NoDup_filter; exact Hl |].
        intros b Hb. apply filter_In in Hb. destruct Hb as [_ Hb]. apply memb_In. exact Hb.
      - apply NoDup_incl_length; [exact Hom |].
        intros b Hb. apply filter_In. split; [apply Hincl; exact Hb | apply memb_In; exact Hb].
    Qed.
  End Mem.

  (* =======================================================================
     3. Configuration sums: single system and duplicated system
     ======================================================================= *)

  Section Sums.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable vals : list V.

    Definition cfg : Type := L -> V.

    Definition upd (U : cfg) (e : L) (v : V) : cfg :=
      fun e' => if eqbL e' e then v else U e'.

    (* Sum of F over all re-assignments of U on the links of E. *)
    Fixpoint csum (E : list L) (F : cfg -> R) (U : cfg) : R :=
      match E with
      | [] => F U
      | e :: E' => rsum vals (fun v => csum E' F (upd U e v))
      end.

    (* Sum of F over all re-assignments of the pair (U, U') on E. *)
    Fixpoint dsum (E : list L) (F : cfg -> cfg -> R) (U U' : cfg) : R :=
      match E with
      | [] => F U U'
      | e :: E' =>
          rsum vals (fun v => rsum vals (fun v' => dsum E' F (upd U e v) (upd U' e v')))
      end.

    Lemma csum_ext : forall E F G, (forall A, F A = G A) ->
      forall U, csum E F U = csum E G U.
    Proof.
      induction E as [| e E IH]; intros F G H U; simpl; [apply H |].
      apply rsum_ext. intros v _. apply IH. exact H.
    Qed.

    Lemma csum_plus : forall E F G U,
      csum E (fun A => F A + G A) U = csum E F U + csum E G U.
    Proof.
      induction E as [| e E IH]; intros F G U; simpl; [reflexivity |].
      rewrite <- rsum_plus. apply rsum_ext. intros v _. apply IH.
    Qed.

    Lemma csum_scal : forall E c F U,
      csum E (fun A => c * F A) U = c * csum E F U.
    Proof.
      induction E as [| e E IH]; intros c F U; simpl; [reflexivity |].
      rewrite <- rsum_scal. apply rsum_ext. intros v _. apply IH.
    Qed.

    Lemma csum_pos : forall E F, vals <> [] -> (forall A, 0 < F A) ->
      forall U, 0 < csum E F U.
    Proof.
      induction E as [| e E IH]; intros F Hne HF U; simpl; [apply HF |].
      apply rsum_pos; [exact Hne |]. intros v _. apply IH; assumption.
    Qed.

    Lemma dsum_ext : forall E F G, (forall A B, F A B = G A B) ->
      forall U U', dsum E F U U' = dsum E G U U'.
    Proof.
      induction E as [| e E IH]; intros F G H U U'; simpl; [apply H |].
      apply rsum_ext. intros v _. apply rsum_ext. intros v' _. apply IH. exact H.
    Qed.

    Lemma dsum_plus : forall E F G U U',
      dsum E (fun A B => F A B + G A B) U U' = dsum E F U U' + dsum E G U U'.
    Proof.
      induction E as [| e E IH]; intros F G U U'; simpl; [reflexivity |].
      rewrite <- rsum_plus. apply rsum_ext. intros v _.
      rewrite <- rsum_plus. apply rsum_ext. intros v' _. apply IH.
    Qed.

    Lemma dsum_scal : forall E c F U U',
      dsum E (fun A B => c * F A B) U U' = c * dsum E F U U'.
    Proof.
      induction E as [| e E IH]; intros c F U U'; simpl; [reflexivity |].
      rewrite <- rsum_scal. apply rsum_ext. intros v _.
      rewrite <- rsum_scal. apply rsum_ext. intros v' _. apply IH.
    Qed.

    Lemma dsum_le : forall E F G, (forall A B, F A B <= G A B) ->
      forall U U', dsum E F U U' <= dsum E G U U'.
    Proof.
      induction E as [| e E IH]; intros F G H U U'; simpl; [apply H |].
      apply rsum_le. intros v _. apply rsum_le. intros v' _. apply IH. exact H.
    Qed.

    Lemma dsum_nonneg : forall E F, (forall A B, 0 <= F A B) ->
      forall U U', 0 <= dsum E F U U'.
    Proof.
      induction E as [| e E IH]; intros F H U U'; simpl; [apply H |].
      apply rsum_nonneg. intros v _. apply rsum_nonneg. intros v' _. apply IH. exact H.
    Qed.

    Lemma dsum_abs : forall E F U U',
      Rabs (dsum E F U U') <= dsum E (fun A B => Rabs (F A B)) U U'.
    Proof.
      induction E as [| e E IH]; intros F U U'; simpl; [apply Rle_refl |].
      eapply Rle_trans; [apply rsum_abs |]. apply rsum_le. intros v _.
      eapply Rle_trans; [apply rsum_abs |]. apply rsum_le. intros v' _. apply IH.
    Qed.

    Lemma dsum_zero : forall E U U', dsum E (fun _ _ => 0) U U' = 0.
    Proof.
      induction E as [| e E IH]; intros U U'; simpl; [reflexivity |].
      apply rsum_zero. intros v _. apply rsum_zero. intros v' _. apply IH.
    Qed.

    Lemma dsum_rsum : forall {X : Type} (l : list X) E (F : X -> cfg -> cfg -> R) U U',
      dsum E (fun A B => rsum l (fun x => F x A B)) U U' =
      rsum l (fun x => dsum E (F x) U U').
    Proof.
      intros X l E F U U'. induction l as [| x l IH].
      - rewrite rsum_nil. apply dsum_zero.
      - rewrite rsum_cons, <- IH, <- dsum_plus. apply dsum_ext. intros A B.
        exact (rsum_cons x l (fun y => F y A B)).
    Qed.

    Lemma dsum_prod : forall E F G U U',
      dsum E (fun A B => F A * G B) U U' = csum E F U * csum E G U'.
    Proof.
      induction E as [| e E IH]; intros F G U U'; simpl; [reflexivity |].
      rewrite rsum_mult. apply rsum_ext. intros v _. apply rsum_ext. intros v' _. apply IH.
    Qed.

    Lemma dsum_prod4 : forall E F1 G1 F2 G2 F3 G3 F4 G4 U U',
      dsum E (fun A B => F1 A * G1 B + F2 A * G2 B - F3 A * G3 B - F4 A * G4 B) U U' =
      csum E F1 U * csum E G1 U' + csum E F2 U * csum E G2 U'
      - csum E F3 U * csum E G3 U' - csum E F4 U * csum E G4 U'.
    Proof.
      intros E F1 G1 F2 G2 F3 G3 F4 G4 U U'.
      rewrite <- (dsum_prod E F1 G1 U U'), <- (dsum_prod E F2 G2 U U'),
              <- (dsum_prod E F3 G3 U U'), <- (dsum_prod E F4 G4 U U').
      transitivity
        (dsum E (fun A B => F1 A * G1 B) U U' +
         (dsum E (fun A B => F2 A * G2 B) U U' +
          ((-1) * dsum E (fun A B => F3 A * G3 B) U U' +
           (-1) * dsum E (fun A B => F4 A * G4 B) U U'))); [| ring].
      rewrite <- !dsum_scal, <- !dsum_plus. apply dsum_ext. intros A B. ring.
    Qed.

    (* Exchange of the two copies on the links selected by inK. *)
    Definition sw1 (inK : L -> bool) (A B : cfg) : cfg :=
      fun e => if inK e then B e else A e.
    Definition sw2 (inK : L -> bool) (A B : cfg) : cfg :=
      fun e => if inK e then A e else B e.

    Lemma sw1_upd : forall inK A B e v v',
      sw1 inK (upd A e v) (upd B e v') = upd (sw1 inK A B) e (if inK e then v' else v).
    Proof.
      intros inK A B e v v'. apply functional_extensionality. intro e0.
      unfold sw1, upd. destruct (eqbL e0 e) eqn:He.
      - apply eqbL_spec in He. subst e0. destruct (inK e); reflexivity.
      - destruct (inK e0); reflexivity.
    Qed.

    Lemma sw2_upd : forall inK A B e v v',
      sw2 inK (upd A e v) (upd B e v') = upd (sw2 inK A B) e (if inK e then v else v').
    Proof.
      intros inK A B e v v'. apply functional_extensionality. intro e0.
      unfold sw2, upd. destruct (eqbL e0 e) eqn:He.
      - apply eqbL_spec in He. subst e0. destruct (inK e); reflexivity.
      - destruct (inK e0); reflexivity.
    Qed.

    Lemma dsum_swap : forall inK E F U U',
      dsum E (fun A B => F (sw1 inK A B) (sw2 inK A B)) U U' =
      dsum E F (sw1 inK U U') (sw2 inK U U').
    Proof.
      intros inK E F. induction E as [| e E IH]; intros U U'; simpl; [reflexivity |].
      destruct (inK e) eqn:HK.
      - rewrite rsum_swap. apply rsum_ext. intros v _. apply rsum_ext. intros v' _.
        rewrite IH, sw1_upd, sw2_upd, HK. reflexivity.
      - apply rsum_ext. intros v _. apply rsum_ext. intros v' _.
        rewrite IH, sw1_upd, sw2_upd, HK. reflexivity.
    Qed.

    Lemma dsum_swap_same : forall inK E F U,
      dsum E (fun A B => F (sw1 inK A B) (sw2 inK A B)) U U = dsum E F U U.
    Proof.
      intros inK E F U. rewrite dsum_swap.
      assert (H1 : sw1 inK U U = U).
      { apply functional_extensionality. intro e. unfold sw1. destruct (inK e); reflexivity. }
      assert (H2 : sw2 inK U U = U).
      { apply functional_extensionality. intro e. unfold sw2. destruct (inK e); reflexivity. }
      rewrite H1, H2. reflexivity.
    Qed.
  End Sums.

  (* =======================================================================
     4. The model, chains of factors, and the clustering theorem
     ======================================================================= *)

  Section Model.
    Variables (L V B : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable eqbB : B -> B -> bool.
    Hypothesis eqbB_spec : forall x y, eqbB x y = true <-> x = y.
    Variable vals : list V.
    Variable supp : B -> list L.
    Variable phi : B -> cfg L V -> R.
    Variable Lam : list B.
    Variable E : list L.
    Variable U0 : cfg L V.
    Variables f g : cfg L V -> R.
    Variables Sf Sg : list L.
    Variables m eps Df Dg : R.

    Hypothesis Lam_nodup : NoDup Lam.
    Hypothesis vals_nonempty : vals <> [].
    Hypothesis phi_local : forall b A A', In b Lam ->
      (forall e, In e (supp b) -> A e = A' e) -> phi b A = phi b A'.
    Hypothesis phi_pos : forall b A, In b Lam -> 0 < phi b A.
    Hypothesis m_pos : 0 < m.
    Hypothesis eps_nonneg : 0 <= eps.
    Hypothesis phi_osc_lo : forall b A A', In b Lam -> m <= phi b A * phi b A'.
    Hypothesis phi_osc_hi : forall b A A', In b Lam ->
      phi b A * phi b A' - m <= eps * (phi b A * phi b A').
    Hypothesis f_local : forall A A', (forall e, In e Sf -> A e = A' e) -> f A = f A'.
    Hypothesis g_local : forall A A', (forall e, In e Sg -> A e = A' e) -> g A = g A'.
    Hypothesis f_osc : forall A A', Rabs (f A - f A') <= Df.
    Hypothesis g_osc : forall A A', Rabs (g A - g A') <= Dg.

    Local Notation Cfg := (cfg L V).
    Local Notation Csum := (csum L V eqbL vals).
    Local Notation Dsum := (dsum L V eqbL vals).

    (* ---------- tuples and candidate chains ---------- *)

    Fixpoint tuples (l : list B) (n : nat) : list (list B) :=
      match n with
      | O => [[]]
      | S n' => flat_map (fun p => map (cons p) (tuples l n')) l
      end.

    Lemma tuples_In : forall l n om,
      In om (tuples l n) <-> (length om = n /\ incl om l).
    Proof.
      intros l n. induction n as [| n IH]; intro om; simpl.
      - split.
        + intros [<- | []]. split; [reflexivity | intros x []].
        + intros [Hlen _]. destruct om; [left; reflexivity | discriminate].
      - rewrite in_flat_map. split.
        + intros [p [Hp Hin]]. apply in_map_iff in Hin. destruct Hin as [om' [<- Hom']].
          apply IH in Hom'. destruct Hom' as [Hlen Hincl]. split; [simpl; lia |].
          intros x [<- | Hx]; [exact Hp | apply Hincl; exact Hx].
        + intros [Hlen Hincl]. destruct om as [| p om']; [discriminate |].
          exists p. split; [apply Hincl; left; reflexivity |].
          apply in_map. apply IH. split; [simpl in Hlen; lia |].
          intros x Hx. apply Hincl. right. exact Hx.
    Qed.

    Definition cand (R : list B) : list (list B) :=
      flat_map (tuples R) (seq 0 (S (length R))).

    Lemma cand_In : forall R om,
      In om (cand R) <-> (incl om R /\ (length om <= length R)%nat).
    Proof.
      intros R om. unfold cand. rewrite in_flat_map. split.
      - intros [k [Hk Hin]]. apply in_seq in Hk. apply tuples_In in Hin.
        destruct Hin as [Hlen Hincl]. split; [exact Hincl | lia].
      - intros [Hincl Hlen]. exists (length om). split; [apply in_seq; lia |].
        apply tuples_In. split; [reflexivity | exact Hincl].
    Qed.

    (* ---------- chains ---------- *)

    Definition touchb (S1 S2 : list L) : bool :=
      existsb (fun e => memb eqbL e S2) S1.

    Lemma touchb_true : forall S1 S2,
      touchb S1 S2 = true <-> exists e, In e S1 /\ In e S2.
    Proof.
      intros S1 S2. unfold touchb. rewrite existsb_exists. split.
      - intros [e [H1 H2]]. exists e. split; [exact H1 |].
        apply (memb_In eqbL eqbL_spec). exact H2.
      - intros [e [H1 H2]]. exists e. split; [exact H1 |].
        apply (memb_In eqbL eqbL_spec). exact H2.
    Qed.

    Lemma touchb_single : forall S e, touchb S [e] = true <-> In e S.
    Proof.
      intros S e. rewrite touchb_true. split.
      - intros [e' [H1 [<- | []]]]. exact H1.
      - intro H. exists e. split; [exact H | left; reflexivity].
    Qed.

    (* chainf S [b1; ...; bk]: S ~ b1 ~ b2 ~ ... ~ bk (consecutive supports meet) *)
    Fixpoint chainf (S : list L) (om : list B) : bool :=
      match om with
      | [] => true
      | b :: rest => touchb S (supp b) && chainf (supp b) rest
      end.

    (* support of the last factor of the chain (or the seed S if it is empty) *)
    Fixpoint endS (S : list L) (om : list B) : list L :=
      match om with
      | [] => S
      | b :: rest => endS (supp b) rest
      end.

    Lemma chainf_app : forall o1 o2 S,
      chainf S (o1 ++ o2) = chainf S o1 && chainf (endS S o1) o2.
    Proof.
      induction o1 as [| b o1 IH]; intros o2 S; simpl; [reflexivity |].
      rewrite IH, andb_assoc. reflexivity.
    Qed.

    Lemma endS_app : forall o1 o2 S, endS S (o1 ++ o2) = endS (endS S o1) o2.
    Proof.
      induction o1 as [| b o1 IH]; intros o2 S; simpl; [reflexivity | apply IH].
    Qed.

    Lemma chain_extend : forall (R om : list B) (b : B),
      NoDup om -> incl om R -> chainf Sf om = true -> In b R ->
      touchb (endS Sf om) (supp b) = true ->
      exists om', NoDup om' /\ incl om' R /\ chainf Sf om' = true /\ endS Sf om' = supp b.
    Proof.
      intros R om b Hnd Hincl Hch HbR Htouch.
      destruct (memb eqbB b om) eqn:Hmem.
      - apply (memb_In eqbB eqbB_spec) in Hmem. apply in_split in Hmem.
        destruct Hmem as [o1 [o2 Heq]]. subst om.
        exists (o1 ++ [b]). split; [exact (NoDup_prefix_snoc o1 o2 b Hnd) |]. split.
        + intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [Heq | []]].
          * apply Hincl. apply in_or_app. left. exact Hx.
          * subst x. exact HbR.
        + rewrite chainf_app in Hch. cbn [chainf] in Hch.
          apply andb_true_iff in Hch. destruct Hch as [Hc1 Hc2].
          apply andb_true_iff in Hc2. destruct Hc2 as [Ht _].
          split.
          * rewrite chainf_app. cbn [chainf]. rewrite Hc1, Ht. reflexivity.
          * rewrite endS_app. reflexivity.
      - apply (memb_false eqbB eqbB_spec) in Hmem.
        exists (om ++ [b]). split; [exact (NoDup_snoc om b Hnd Hmem) |]. split.
        + intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [Heq | []]].
          * apply Hincl. exact Hx.
          * subst x. exact HbR.
        + split.
          * rewrite chainf_app. cbn [chainf]. rewrite Hch, Htouch. reflexivity.
          * rewrite endS_app. reflexivity.
    Qed.

    (* duplicate-free chain from Sf whose last support meets the target T *)
    Definition goodchain (T : list L) (om : list B) : bool :=
      nodupb eqbB om && chainf Sf om && touchb (endS Sf om) T.

    Definition has_chain_to (R : list B) (T : list L) : bool :=
      existsb (goodchain T) (cand R).

    Lemma has_chain_to_true : forall R T,
      has_chain_to R T = true <->
      exists om, NoDup om /\ incl om R /\ chainf Sf om = true /\
                 touchb (endS Sf om) T = true.
    Proof.
      intros R T. unfold has_chain_to. rewrite existsb_exists. split.
      - intros [om [Hin Hg]]. unfold goodchain in Hg.
        apply andb_true_iff in Hg. destruct Hg as [Hg Ht].
        apply andb_true_iff in Hg. destruct Hg as [Hn Hc].
        apply (nodupb_NoDup eqbB eqbB_spec) in Hn.
        apply cand_In in Hin. destruct Hin as [Hincl _].
        exists om. split; [exact Hn |]. split; [exact Hincl |]. split; assumption.
      - intros [om [Hn [Hincl [Hc Ht]]]]. exists om. split.
        + apply cand_In. split; [exact Hincl |]. apply NoDup_incl_length; assumption.
        + unfold goodchain. rewrite Hc, Ht.
          rewrite (proj2 (nodupb_NoDup eqbB eqbB_spec om) Hn). reflexivity.
    Qed.

    (* links reachable from Sf through the factors of R *)
    Definition inK (R : list B) (e : L) : bool := has_chain_to R [e].

    Lemma inK_seed : forall R e, In e Sf -> inK R e = true.
    Proof.
      intros R e He. apply has_chain_to_true. exists [].
      split; [constructor |]. split; [intros x [] |]. split; [reflexivity |].
      cbn [endS]. apply touchb_single. exact He.
    Qed.

    Lemma inK_block : forall R b e, In b R -> In e (supp b) -> inK R e = true ->
      forall e', In e' (supp b) -> inK R e' = true.
    Proof.
      intros R b e HbR He HK e' He'.
      apply has_chain_to_true in HK. destruct HK as [om [Hn [Hincl [Hc Ht]]]].
      apply touchb_single in Ht.
      assert (Htouch : touchb (endS Sf om) (supp b) = true).
      { apply touchb_true. exists e. split; assumption. }
      destruct (chain_extend R om b Hn Hincl Hc HbR Htouch) as [om' [Hn' [Hincl' [Hc' Hend']]]].
      apply has_chain_to_true. exists om'.
      split; [exact Hn' |]. split; [exact Hincl' |]. split; [exact Hc' |].
      rewrite Hend'. apply touchb_single. exact He'.
    Qed.

    Lemma inK_target : forall R e, has_chain_to R Sg = false -> In e Sg -> inK R e = false.
    Proof.
      intros R e Hno He. destruct (inK R e) eqn:HK; [| reflexivity].
      apply has_chain_to_true in HK. destruct HK as [om [Hn [Hincl [Hc Ht]]]].
      apply touchb_single in Ht.
      assert (Hyes : has_chain_to R Sg = true).
      { apply has_chain_to_true. exists om.
        split; [exact Hn |]. split; [exact Hincl |]. split; [exact Hc |].
        apply touchb_true. exists e. split; assumption. }
      congruence.
    Qed.

    (* ---------- weights ---------- *)

    Definition W (A : Cfg) : R := rprod Lam (fun b => phi b A).
    Definition psi (b : B) (A A' : Cfg) : R := phi b A * phi b A'.
    Definition wR (Rs : list B) (A A' : Cfg) : R :=
      rprod Lam (fun b => if memb eqbB b Rs then psi b A A' - m else m).
    Definition wR2 (om Rs : list B) (A A' : Cfg) : R :=
      rprod Lam (fun b => if memb eqbB b Rs then psi b A A' - m
                          else if memb eqbB b om then 0 else m).
    Definition F0 (A A' : Cfg) : R := (f A - f A') * (g A - g A').

    Definition Zf : R := Csum E W U0.
    Definition Nf (F : Cfg -> R) : R := Csum E (fun A => F A * W A) U0.

    Lemma W_pos : forall A, 0 < W A.
    Proof. intro A. unfold W. apply rprod_pos. intros b Hb. apply phi_pos. exact Hb. Qed.

    Lemma Zf_pos : 0 < Zf.
    Proof. unfold Zf. apply csum_pos; [exact vals_nonempty | exact W_pos]. Qed.

    Lemma WW_expand : forall A A',
      W A * W A' = rsum (sublists Lam) (fun R => wR R A A').
    Proof.
      intros A A'.
      transitivity (rprod Lam (fun b => m + (psi b A A' - m))).
      - unfold W. rewrite <- rprod_mult. apply rprod_ext. intros b _. unfold psi. ring.
      - exact (prod_expand eqbB eqbB_spec Lam (fun _ => m) (fun b => psi b A A' - m) Lam_nodup).
    Qed.

    Lemma cov_dup :
      2 * (Zf * Nf (fun A => f A * g A) - Nf f * Nf g) =
      Dsum E (fun A A' => F0 A A' * (W A * W A')) U0 U0.
    Proof.
      unfold Zf, Nf.
      set (Ffg := fun A : Cfg => f A * g A * W A).
      set (Ff := fun A : Cfg => f A * W A).
      set (Fg := fun A : Cfg => g A * W A).
      transitivity (Csum E Ffg U0 * Csum E W U0 + Csum E W U0 * Csum E Ffg U0
                    - Csum E Ff U0 * Csum E Fg U0 - Csum E Fg U0 * Csum E Ff U0).
      - ring.
      - rewrite <- (dsum_prod4 L V eqbL vals E Ffg W W Ffg Ff Fg Fg Ff U0 U0).
        apply dsum_ext. intros A A'. unfold F0, Ffg, Ff, Fg. ring.
    Qed.

    Lemma psi_ge_m : forall b A A', In b Lam -> 0 <= psi b A A' - m.
    Proof.
      intros b A A' Hb. pose proof (phi_osc_lo b A A' Hb) as H. unfold psi. lra.
    Qed.

    Lemma wR_nonneg : forall R A A', 0 <= wR R A A'.
    Proof.
      intros R A A'. unfold wR. apply rprod_nonneg. intros b Hb.
      destruct (memb eqbB b R); [apply psi_ge_m; exact Hb | lra].
    Qed.

    Lemma wR2_nonneg : forall om R A A', 0 <= wR2 om R A A'.
    Proof.
      intros om R A A'. unfold wR2. apply rprod_nonneg. intros b Hb.
      destruct (memb eqbB b R); [apply psi_ge_m; exact Hb |].
      destruct (memb eqbB b om); lra.
    Qed.

    Lemma DfDg_nonneg : 0 <= Df * Dg.
    Proof.
      pose proof (f_osc U0 U0) as Hf. pose proof (g_osc U0 U0) as Hg.
      pose proof (Rabs_pos (f U0 - f U0)) as Hf0.
      pose proof (Rabs_pos (g U0 - g U0)) as Hg0.
      apply Rmult_le_pos; lra.
    Qed.

    Lemma F0_bound : forall A A', Rabs (F0 A A') <= Df * Dg.
    Proof.
      intros A A'. unfold F0. rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos; [apply f_osc | apply g_osc].
    Qed.

    (* ---------- vanishing of the terms without a connecting chain ---------- *)

    Lemma vanish : forall R, incl R Lam -> has_chain_to R Sg = false ->
      Dsum E (fun A A' => F0 A A' * wR R A A') U0 U0 = 0.
    Proof.
      intros R HR Hno.
      set (K := inK R).
      set (F := fun A A' : Cfg => F0 A A' * wR R A A').
      assert (Hflip : forall A A',
        F (sw1 L V K A A') (sw2 L V K A A') = (-1) * F A A').
      { intros A A'. unfold F, F0.
        assert (Hf1 : f (sw1 L V K A A') = f A').
        { apply f_local. intros e He. unfold sw1, K. rewrite (inK_seed R e He). reflexivity. }
        assert (Hf2 : f (sw2 L V K A A') = f A).
        { apply f_local. intros e He. unfold sw2, K. rewrite (inK_seed R e He). reflexivity. }
        assert (Hg1 : g (sw1 L V K A A') = g A).
        { apply g_local. intros e He. unfold sw1, K.
          rewrite (inK_target R e Hno He). reflexivity. }
        assert (Hg2 : g (sw2 L V K A A') = g A').
        { apply g_local. intros e He. unfold sw2, K.
          rewrite (inK_target R e Hno He). reflexivity. }
        assert (Hw : wR R (sw1 L V K A A') (sw2 L V K A A') = wR R A A').
        { unfold wR. apply rprod_ext. intros b Hb.
          destruct (memb eqbB b R) eqn:Hm; [| reflexivity].
          apply (memb_In eqbB eqbB_spec) in Hm.
          assert (Hpsi : psi b (sw1 L V K A A') (sw2 L V K A A') = psi b A A').
          { unfold psi. destruct (existsb K (supp b)) eqn:Hex.
            - apply existsb_exists in Hex. destruct Hex as [e [He HKe]].
              assert (Hall : forall e', In e' (supp b) -> K e' = true).
              { intros e' He'. exact (inK_block R b e Hm He HKe e' He'). }
              assert (H1 : phi b (sw1 L V K A A') = phi b A').
              { apply phi_local; [exact Hb |]. intros e' He'. unfold sw1.
                rewrite (Hall e' He'). reflexivity. }
              assert (H2 : phi b (sw2 L V K A A') = phi b A).
              { apply phi_local; [exact Hb |]. intros e' He'. unfold sw2.
                rewrite (Hall e' He'). reflexivity. }
              rewrite H1, H2. ring.
            - assert (Hall : forall e', In e' (supp b) -> K e' = false).
              { intros e' He'. destruct (K e') eqn:HKe'; [| reflexivity].
                assert (Hyes : existsb K (supp b) = true).
                { apply existsb_exists. exists e'. split; assumption. }
                congruence. }
              assert (H1 : phi b (sw1 L V K A A') = phi b A).
              { apply phi_local; [exact Hb |]. intros e' He'. unfold sw1.
                rewrite (Hall e' He'). reflexivity. }
              assert (H2 : phi b (sw2 L V K A A') = phi b A').
              { apply phi_local; [exact Hb |]. intros e' He'. unfold sw2.
                rewrite (Hall e' He'). reflexivity. }
              rewrite H1, H2. reflexivity. }
          rewrite Hpsi. reflexivity. }
        rewrite Hf1, Hf2, Hg1, Hg2, Hw. ring. }
      pose proof (dsum_swap_same L V eqbL eqbL_spec vals K E F U0) as Hsw.
      assert (Hneg :
        Dsum E (fun A A' => F (sw1 L V K A A') (sw2 L V K A A')) U0 U0 =
        (-1) * Dsum E F U0 U0).
      { rewrite <- dsum_scal. apply dsum_ext. intros A A'. apply Hflip. }
      rewrite Hneg in Hsw. lra.
    Qed.

    (* ---------- union bound over duplicate-free connecting chains ---------- *)

    Definition Chains : list (list B) := filter (goodchain Sg) (cand Lam).

    Lemma Chains_In : forall om, In om Chains -> NoDup om /\ incl om Lam.
    Proof.
      intros om Hom. unfold Chains in Hom. apply filter_In in Hom.
      destruct Hom as [Hc Hg]. apply cand_In in Hc. destruct Hc as [Hincl _].
      unfold goodchain in Hg.
      apply andb_true_iff in Hg. destruct Hg as [Hg _].
      apply andb_true_iff in Hg. destruct Hg as [Hn _].
      apply (nodupb_NoDup eqbB eqbB_spec) in Hn. split; assumption.
    Qed.

    Lemma term_bound : forall R, In R (sublists Lam) ->
      Rabs (Dsum E (fun A A' => F0 A A' * wR R A A') U0 U0)
      <= Df * Dg * Dsum E (fun A A' => rsum Chains (fun om => wR2 om R A A')) U0 U0.
    Proof.
      intros R HR. pose proof (sublists_incl Lam R HR) as Hincl.
      pose proof DfDg_nonneg as HDnn.
      assert (Hrnn : 0 <= Dsum E (fun A A' => rsum Chains (fun om => wR2 om R A A')) U0 U0).
      { apply dsum_nonneg. intros A A'. apply rsum_nonneg. intros om _. apply wR2_nonneg. }
      destruct (has_chain_to R Sg) eqn:Hc.
      - apply has_chain_to_true in Hc. destruct Hc as [om [Hn [Hio [Hch Ht]]]].
        assert (HomL : incl om Lam).
        { intros x Hx. apply Hincl. apply Hio. exact Hx. }
        assert (HomC : In om Chains).
        { unfold Chains. apply filter_In. split.
          - apply cand_In. split; [exact HomL |]. apply NoDup_incl_length; assumption.
          - unfold goodchain. rewrite Hch, Ht.
            rewrite (proj2 (nodupb_NoDup eqbB eqbB_spec om) Hn). reflexivity. }
        eapply Rle_trans; [apply dsum_abs |].
        rewrite <- dsum_scal. apply dsum_le. intros A A'.
        rewrite Rabs_mult.
        rewrite (Rabs_right (wR R A A')); [| apply Rle_ge; apply wR_nonneg].
        apply Rmult_le_compat; [apply Rabs_pos | apply wR_nonneg | apply F0_bound |].
        assert (Heq : wR R A A' = wR2 om R A A').
        { unfold wR, wR2. apply rprod_ext. intros b _.
          destruct (memb eqbB b R) eqn:Hm; [reflexivity |].
          assert (Hmo : memb eqbB b om = false).
          { apply (memb_false eqbB eqbB_spec). intro Hin.
            apply (memb_false eqbB eqbB_spec) in Hm. apply Hm. apply Hio. exact Hin. }
          rewrite Hmo. reflexivity. }
        rewrite Heq.
        apply (rsum_ge_term Chains (fun om' => wR2 om' R A A') om); [| exact HomC].
        intros x _. apply wR2_nonneg.
      - rewrite (vanish R Hincl Hc), Rabs_R0. apply Rmult_le_pos; assumption.
    Qed.

    Lemma chain_weight_bound : forall om A A', In om Chains ->
      rsum (sublists Lam) (fun R => wR2 om R A A') <= eps ^ length om * (W A * W A').
    Proof.
      intros om A A' Hom. destruct (Chains_In om Hom) as [Hn Hincl].
      assert (Hexp : rsum (sublists Lam) (fun R => wR2 om R A A') =
                     rprod Lam (fun b => (if memb eqbB b om then 0 else m) + (psi b A A' - m))).
      { symmetry.
        exact (prod_expand eqbB eqbB_spec Lam
                 (fun b => if memb eqbB b om then 0 else m)
                 (fun b => psi b A A' - m) Lam_nodup). }
      rewrite Hexp.
      apply Rle_trans with
        (rprod Lam (fun b => (if memb eqbB b om then eps else 1) * psi b A A')).
      - apply rprod_le. intros b Hb.
        pose proof (phi_osc_lo b A A' Hb) as Hlo.
        pose proof (phi_osc_hi b A A' Hb) as Hhi.
        fold (psi b A A') in Hlo, Hhi.
        destruct (memb eqbB b om); lra.
      - rewrite rprod_mult, rprod_indicator_pow.
        rewrite (filter_memb_length eqbB eqbB_spec om Lam Hn Lam_nodup Hincl).
        apply Req_le. f_equal. unfold W. rewrite <- rprod_mult. reflexivity.
    Qed.

    Lemma cov_bound :
      Rabs (2 * (Zf * Nf (fun A => f A * g A) - Nf f * Nf g))
      <= Df * Dg * rsum Chains (fun om => eps ^ length om) * (Zf * Zf).
    Proof.
      rewrite cov_dup.
      rewrite (dsum_ext L V eqbL vals E
                 (fun A A' => F0 A A' * (W A * W A'))
                 (fun A A' => rsum (sublists Lam) (fun R => F0 A A' * wR R A A'))).
      2: { intros A A'. rewrite WW_expand, <- rsum_scal. reflexivity. }
      rewrite (dsum_rsum L V eqbL vals (sublists Lam) E
                 (fun R A A' => F0 A A' * wR R A A') U0 U0).
      eapply Rle_trans; [apply rsum_abs |].
      apply Rle_trans with
        (rsum (sublists Lam) (fun R =>
           Df * Dg * Dsum E (fun A A' => rsum Chains (fun om => wR2 om R A A')) U0 U0)).
      { apply rsum_le. intros R HR. apply (term_bound R HR). }
      rewrite rsum_scal.
      rewrite <- (dsum_rsum L V eqbL vals (sublists Lam) E
                    (fun R A A' => rsum Chains (fun om => wR2 om R A A')) U0 U0).
      rewrite !Rmult_assoc. apply Rmult_le_compat_l; [apply Rle_trans with (Rabs (f U0 - f U0)); [apply Rabs_pos | apply f_osc] |].
      apply Rmult_le_compat_l; [apply Rle_trans with (Rabs (g U0 - g U0)); [apply Rabs_pos | apply g_osc] |].
      apply Rle_trans with
        (Dsum E (fun A A' => rsum Chains (fun om => eps ^ length om) * (W A * W A')) U0 U0).
      - apply dsum_le. intros A A'. rewrite rsum_swap, <- rsum_scal_r.
        apply rsum_le. intros om Hom. apply chain_weight_bound. exact Hom.
      - rewrite dsum_scal, dsum_prod. apply Rle_refl.
    Qed.

    (* ---------- chains are counted by the transfer recursion `reach` ---------- *)

    (* reach k S = sum over chains S ~ b1 ~ ... ~ bk ~ Sg in Lam of eps^k *)
    Fixpoint reach (k : nat) (S : list L) : R :=
      match k with
      | O => if touchb S Sg then 1 else 0
      | S k' => rsum Lam (fun b => if touchb S (supp b) then eps * reach k' (supp b) else 0)
      end.

    Definition conn (S : list L) (om : list B) : bool :=
      chainf S om && touchb (endS S om) Sg.

    Lemma tuples_reach : forall k S,
      rsum (tuples Lam k) (fun om => if conn S om then eps ^ length om else 0) = reach k S.
    Proof.
      induction k as [| k IH]; intro S.
      - cbn [tuples]. rewrite rsum_cons, rsum_nil. unfold conn. cbn [chainf endS length reach].
        cbn [andb pow]. destruct (touchb S Sg); lra.
      - cbn [tuples]. rewrite rsum_flat_map. cbn [reach]. apply rsum_ext. intros p _.
        rewrite rsum_map.
        destruct (touchb S (supp p)) eqn:Ht.
        + rewrite <- IH, <- rsum_scal. apply rsum_ext. intros om _.
          unfold conn. cbn [chainf endS length]. rewrite Ht. cbn [andb].
          destruct (chainf (supp p) om && touchb (endS (supp p) om) Sg); cbn [pow]; ring.
        + apply rsum_zero. intros om _. unfold conn. cbn [chainf]. rewrite Ht. reflexivity.
    Qed.

    Lemma chains_le_reach :
      rsum Chains (fun om => eps ^ length om)
      <= rsum (seq 0 (S (length Lam))) (fun k => reach k Sf).
    Proof.
      unfold Chains. rewrite rsum_filter.
      apply Rle_trans with
        (rsum (cand Lam) (fun om => if conn Sf om then eps ^ length om else 0)).
      - apply rsum_le. intros om _. unfold goodchain, conn.
        destruct (nodupb eqbB om); cbn [andb].
        + apply Rle_refl.
        + destruct (chainf Sf om && touchb (endS Sf om) Sg);
            [apply pow_le; exact eps_nonneg | apply Rle_refl].
      - unfold cand. rewrite rsum_flat_map. apply Req_le.
        apply rsum_ext. intros k _. apply tuples_reach.
    Qed.

    (* ---------- main theorem ---------- *)

    Theorem dup_clustering :
      Rabs (Nf (fun A => f A * g A) / Zf - (Nf f / Zf) * (Nf g / Zf))
      <= Df * Dg / 2 * rsum (seq 0 (S (length Lam))) (fun k => reach k Sf).
    Proof.
      pose proof Zf_pos as HZ.
      pose proof cov_bound as Hcb.
      pose proof chains_le_reach as Hcr.
      pose proof DfDg_nonneg as HD.
      set (Sr := rsum (seq 0 (S (length Lam))) (fun k => reach k Sf)) in *.
      set (Sc := rsum Chains (fun om => eps ^ length om)) in *.
      set (X := Zf * Nf (fun A => f A * g A) - Nf f * Nf g) in *.
      assert (HZZ : 0 < Zf * Zf) by (apply Rmult_lt_0_compat; assumption).
      replace (Nf (fun A => f A * g A) / Zf - Nf f / Zf * (Nf g / Zf))
        with (X * / (Zf * Zf)).
      2: { unfold X. field. lra. }
      rewrite Rabs_mult.
      rewrite (Rabs_right (/ (Zf * Zf))).
      2: { apply Rle_ge. left. apply Rinv_0_lt_compat. exact HZZ. }
      rewrite Rabs_mult in Hcb. rewrite (Rabs_right 2) in Hcb by lra.
      assert (H1 : Df * Dg * Sc * (Zf * Zf) <= Df * Dg * Sr * (Zf * Zf)).
      { apply Rmult_le_compat_r; [lra |]. apply Rmult_le_compat_l; assumption. }
      assert (Hx : Rabs X <= Df * Dg / 2 * Sr * (Zf * Zf)) by lra.
      apply Rmult_le_reg_r with (Zf * Zf); [exact HZZ |].
      rewrite Rmult_assoc, Rinv_l; [| lra]. lra.
    Qed.

  End Model.

End DupClustering.
