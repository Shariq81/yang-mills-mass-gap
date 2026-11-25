(* =========================================================================
   rg/product_measure_perm.v

   The finite product a-priori measure of rg/dup_clustering.v does not depend
   on the order in which the variables are summed, and variables on which
   the integrand does not depend contribute a trivial factor:

     - `csum_app`:  the sum over E1 ++ E2 is the iterated sum;
     - `csum_perm`: a configuration sum is invariant under permutations of
       the list of variables (Fubini for finite sums);
     - `csum_local_const`: summing a function over variables it does not
       depend on multiplies it by |vals|^(number of variables);
     - `csum_extra`: if E0 is a duplicate-free sublist (as a set) of the
       duplicate-free list E and F does not depend on the variables of E
       outside E0, the sum over E is |vals|^(|E| - |E0|) times the sum
       over E0.

   Depends ONLY on Coq stdlib + rg.dup_clustering + rg.product_measure.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import dup_clustering product_measure.
Import ListNotations.
Import DupClustering.
Open Scope R_scope.

Module ProductMeasurePerm.

  Lemma nodup_app : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
  Proof.
    intros A l1 l2 H1 H2 Hdis. induction l1 as [| a l1 IH]; [exact H2 |].
    inversion H1 as [| a' l' Hna Hnd]; subst. cbn [app]. constructor.
    - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [contradiction |].
      exact (Hdis a (or_introl eq_refl) Hin).
    - apply IH; [exact Hnd |]. intros x Hx. apply Hdis. right. exact Hx.
  Qed.

  Section PP.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable vals : list V.

    Local Notation Cfg := (cfg L V).
    Local Notation Upd := (upd L V eqbL).
    Local Notation Csum := (csum L V eqbL vals).

    Lemma csum_app : forall E1 E2 (F : Cfg -> R) U,
      Csum (E1 ++ E2) F U = Csum E1 (fun A => Csum E2 F A) U.
    Proof.
      induction E1 as [| e E1 IH]; intros E2 F U; [reflexivity |].
      cbn [app csum]. apply rsum_ext. intros v _. apply IH.
    Qed.

    Lemma csum_perm : forall E E', Permutation E E' ->
      forall (F : Cfg -> R) U, Csum E F U = Csum E' F U.
    Proof.
      intros E E' H.
      induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros F U.
      - reflexivity.
      - cbn [csum]. apply rsum_ext. intros v _. apply IH.
      - cbn [csum]. destruct (eqbL x y) eqn:Hxy.
        + apply eqbL_spec in Hxy. subst y. reflexivity.
        + assert (Hne : y <> x).
          { intro Heq. subst y.
            rewrite (ProductMeasure.eqbL_refl L eqbL eqbL_spec x) in Hxy. discriminate. }
          rewrite (rsum_swap vals vals (fun v w => Csum l F (Upd (Upd U y v) x w))).
          apply rsum_ext. intros w _. apply rsum_ext. intros v _.
          rewrite (ProductMeasure.upd_comm L V eqbL eqbL_spec U y x v w Hne). reflexivity.
      - rewrite IH1. apply IH2.
    Qed.

    Lemma csum_local_const : forall S (F : Cfg -> R), ProductMeasure.local_on L V S F ->
      forall X, (forall e, In e X -> ~ In e S) ->
      forall U, Csum X F U = INR (length vals) ^ length X * F U.
    Proof.
      intros S F HF X. induction X as [| e X IH]; intros HX U.
      - cbn [csum length pow]. ring.
      - cbn [csum length pow].
        rewrite (rsum_ext vals (fun v => Csum X F (Upd U e v))
                   (fun _ => INR (length vals) ^ length X * F U)).
        + rewrite ProductMeasure.rsum_const. ring.
        + intros v _. rewrite IH by (intros e' He'; apply HX; right; exact He').
          apply Rmult_eq_compat_l. apply HF. intros x Hx.
          apply (ProductMeasure.upd_other L V eqbL eqbL_spec).
          intro Heq. subst x. exact (HX e (or_introl eq_refl) Hx).
    Qed.

    Lemma csum_extra : forall S (F : Cfg -> R), ProductMeasure.local_on L V S F ->
      forall E0 E, NoDup E0 -> NoDup E -> incl E0 E ->
      (forall e, In e E -> ~ In e E0 -> ~ In e S) ->
      forall U, Csum E F U = INR (length vals) ^ (length E - length E0) * Csum E0 F U.
    Proof.
      intros S F HF E0 E H0 HE Hincl Hout U.
      set (X := filter (fun e => negb (memb eqbL e E0)) E).
      assert (HXin : forall e, In e X <-> In e E /\ ~ In e E0).
      { intro e. unfold X. rewrite filter_In, negb_true_iff.
        rewrite (memb_false eqbL eqbL_spec). reflexivity. }
      assert (Hperm : Permutation E (E0 ++ X)).
      { apply NoDup_Permutation; [exact HE | |].
        - apply nodup_app; [exact H0 | apply NoDup_filter; exact HE |].
          intros a Ha HaX. apply HXin in HaX. destruct HaX as [_ Hn]. contradiction.
        - intro e. rewrite in_app_iff, HXin. split.
          + intro He. destruct (memb eqbL e E0) eqn:Hm.
            * left. apply (memb_In eqbL eqbL_spec). exact Hm.
            * right. split; [exact He |]. apply (memb_false eqbL eqbL_spec). exact Hm.
          + intros [He | [He _]]; [apply Hincl; exact He | exact He]. }
      assert (Hlen : (length E - length E0 = length X)%nat).
      { pose proof (Permutation_length Hperm) as Hl. rewrite app_length in Hl. lia. }
      rewrite Hlen, (csum_perm E (E0 ++ X) Hperm), csum_app.
      rewrite (csum_ext L V eqbL vals E0 (fun A => Csum X F A)
                 (fun A => INR (length vals) ^ length X * F A)).
      - apply csum_scal.
      - intro A. apply (csum_local_const S F HF).
        intros e He. apply HXin in He. destruct He as [HeE HeN]. exact (Hout e HeE HeN).
    Qed.

  End PP.

End ProductMeasurePerm.
