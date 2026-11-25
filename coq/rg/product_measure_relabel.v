(* =========================================================================
   rg/product_measure_relabel.v

   Symmetries of the finite product a-priori measure of rg/dup_clustering.v
   and the abstract reflection-positivity identity.

     - `csum_local_base`: a configuration sum of a function that only
       depends on the variables of S depends on the base configuration only
       through the variables of S that are not summed;
     - `csum_factor_out`: a factor that does not depend on the summed
       variables can be pulled out of a configuration sum;
     - `csum_relabel`: change of variables.  For a bijection phi of the
       variables (with inverse psi) and maps sigma l of the values that
       preserve every sum over `vals`, the pulled-back configuration
       (pull A)(l) = sigma l (A (phi l)) satisfies
         sum_{A on E} F (pull A) = sum_{B on psi(E)} F (B);
     - `csum_reflection_identity`: if the summed variables split into a
       fixed part E0, a part Ep and its mirror image Em (phi maps Em onto
       Ep), then for X depending only on E0 ++ Ep and W0 only on E0,

         sum_{E0 ++ Ep ++ Em} W0 (A) X (A) X (pull A)
           = sum_{E0} W0 (A0) * (sum_{Ep} X)(A0)^2,

       which is non-negative when W0 is (`csum_reflection_positive`).

   Depends ONLY on Coq stdlib + rg.dup_clustering + rg.product_measure
   + rg.product_measure_perm.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
From rg Require Import dup_clustering product_measure product_measure_perm.
Import ListNotations.
Import DupClustering.
Open Scope R_scope.

Module ProductMeasureRelabel.

  Section RL.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable vals : list V.

    Local Notation Cfg := (cfg L V).
    Local Notation Upd := (upd L V eqbL).
    Local Notation Csum := (csum L V eqbL vals).
    Local Notation LocalOn := (ProductMeasure.local_on L V).

    Lemma csum_nonneg : forall E (F : Cfg -> R), (forall A, 0 <= F A) ->
      forall U, 0 <= Csum E F U.
    Proof.
      induction E as [| e E IH]; intros F HF U; cbn [csum]; [apply HF |].
      apply rsum_nonneg. intros v _. apply IH. exact HF.
    Qed.

    (* the base configuration only matters on the variables that are not summed *)
    Lemma csum_local_base : forall S (F : Cfg -> R), LocalOn S F ->
      forall E (A A' : Cfg),
      (forall e, In e S -> ~ In e E -> A e = A' e) -> Csum E F A = Csum E F A'.
    Proof.
      intros S F HF E. induction E as [| e E IH]; intros A A' H.
      - cbn [csum]. apply HF. intros x Hx. apply H; [exact Hx | intros []].
      - cbn [csum]. apply rsum_ext. intros v _. apply IH.
        intros x Hx Hn. unfold upd. destruct (eqbL x e) eqn:Hxe; [reflexivity |].
        apply H; [exact Hx |]. intros [Heq | Hin]; [| exact (Hn Hin)].
        subst x. rewrite (ProductMeasure.eqbL_refl L eqbL eqbL_spec e) in Hxe. discriminate.
    Qed.

    (* a factor that does not depend on the summed variables can be pulled out *)
    Lemma csum_factor_out : forall S (K : Cfg -> R), LocalOn S K ->
      forall E, (forall e, In e E -> ~ In e S) ->
      forall (Y : Cfg -> R) A, Csum E (fun B => K B * Y B) A = K A * Csum E Y A.
    Proof.
      intros S K HK E. induction E as [| e E IH]; intros HE Y A.
      - reflexivity.
      - cbn [csum].
        rewrite (rsum_ext vals (fun v => Csum E (fun B => K B * Y B) (Upd A e v))
                   (fun v => K A * Csum E Y (Upd A e v))).
        + apply rsum_scal.
        + intros v _. rewrite IH by (intros e' He'; apply HE; right; exact He').
          apply Rmult_eq_compat_r. apply HK. intros x Hx.
          apply (ProductMeasure.upd_other L V eqbL eqbL_spec).
          intro Heq. subst x. exact (HE e (or_introl eq_refl) Hx).
    Qed.

    (* ---------- change of variables ---------- *)

    Variables phi psi : L -> L.
    Hypothesis psi_phi : forall l, psi (phi l) = l.
    Hypothesis phi_psi : forall l, phi (psi l) = l.
    Variable sigma : L -> V -> V.
    Hypothesis sigma_sum : forall l (h : V -> R),
      rsum vals (fun v => h (sigma l v)) = rsum vals h.

    Definition pull (A : Cfg) : Cfg := fun l => sigma l (A (phi l)).

    Lemma pull_upd : forall (A : Cfg) e v,
      pull (Upd A e v) = Upd (pull A) (psi e) (sigma (psi e) v).
    Proof.
      intros A e v. apply functional_extensionality. intro l. unfold pull, upd.
      destruct (eqbL (phi l) e) eqn:H1.
      - apply eqbL_spec in H1. subst e. rewrite psi_phi.
        rewrite (ProductMeasure.eqbL_refl L eqbL eqbL_spec l). reflexivity.
      - destruct (eqbL l (psi e)) eqn:H2; [| reflexivity].
        apply eqbL_spec in H2. subst l. rewrite phi_psi in H1.
        rewrite (ProductMeasure.eqbL_refl L eqbL eqbL_spec e) in H1. discriminate.
    Qed.

    Theorem csum_relabel : forall E (F : Cfg -> R) U,
      Csum E (fun A => F (pull A)) U = Csum (map psi E) F (pull U).
    Proof.
      induction E as [| e E IH]; intros F U; [reflexivity |].
      cbn [map csum].
      rewrite <- (sigma_sum (psi e) (fun w => Csum (map psi E) F (Upd (pull U) (psi e) w))).
      apply rsum_ext. intros v _. rewrite IH, pull_upd. reflexivity.
    Qed.

    (* ---------- reflection positivity ---------- *)

    Section RP.
      Variables E0 Ep Em : list L.
      Hypothesis E0_fixed : forall l, In l E0 -> phi l = l /\ (forall v, sigma l v = v).
      Hypothesis Em_Ep : Permutation (map psi Em) Ep.
      Hypothesis dis_0p : forall l, In l E0 -> ~ In l Ep.
      Hypothesis dis_0m : forall l, In l E0 -> ~ In l Em.
      Hypothesis dis_pm : forall l, In l Ep -> ~ In l Em.
      Variables W0 X : Cfg -> R.
      Hypothesis W0_local : LocalOn E0 W0.
      Hypothesis X_local : LocalOn (E0 ++ Ep) X.

      (* the mirror image of a variable of E0 ++ Ep lies in E0 ++ Em *)
      Lemma phi_pos : forall l, In l (E0 ++ Ep) -> In (phi l) (E0 ++ Em).
      Proof.
        intros l Hl. apply in_app_or in Hl. apply in_or_app. destruct Hl as [Hl | Hl].
        - left. rewrite (proj1 (E0_fixed l Hl)). exact Hl.
        - right. pose proof (Permutation_in l (Permutation_sym Em_Ep) Hl) as Hm.
          apply in_map_iff in Hm. destruct Hm as [m [Hm1 Hm2]]. subst l.
          rewrite phi_psi. exact Hm2.
      Qed.

      Lemma Xpull_local : LocalOn (E0 ++ Em) (fun A => X (pull A)).
      Proof.
        intros A A' H. apply X_local. intros l Hl. unfold pull.
        rewrite (H (phi l) (phi_pos l Hl)). reflexivity.
      Qed.

      (* the sum over the mirror variables, as a function of the base configuration *)
      Lemma mirror_sum : forall A0 : Cfg,
        Csum Em (fun A => X (pull A)) A0 = Csum Ep X A0.
      Proof.
        intro A0. rewrite csum_relabel.
        rewrite (ProductMeasurePerm.csum_perm L V eqbL eqbL_spec vals (map psi Em) Ep Em_Ep).
        apply (csum_local_base (E0 ++ Ep) X X_local).
        intros e He Hn. apply in_app_or in He. destruct He as [He | He]; [| contradiction].
        unfold pull. destruct (E0_fixed e He) as [H1 H2]. rewrite H1, H2. reflexivity.
      Qed.

      Lemma mirror_sum_local : LocalOn E0 (fun A => Csum Em (fun B => X (pull B)) A).
      Proof.
        intros A A' H. apply (csum_local_base (E0 ++ Em) _ Xpull_local).
        intros e He Hn. apply in_app_or in He. destruct He as [He | He]; [| contradiction].
        apply H. exact He.
      Qed.

      Theorem csum_reflection_identity : forall U : Cfg,
        Csum (E0 ++ Ep ++ Em) (fun A => W0 A * (X A * X (pull A))) U =
        Csum E0 (fun A0 => W0 A0 * (Csum Ep X A0 * Csum Ep X A0)) U.
      Proof.
        intro U.
        rewrite (ProductMeasurePerm.csum_app L V eqbL vals E0 (Ep ++ Em)).
        apply csum_ext. intro A0.
        rewrite (ProductMeasurePerm.csum_app L V eqbL vals Ep Em).
        (* the sum over Em *)
        assert (HK : LocalOn (E0 ++ Ep) (fun B => W0 B * X B)).
        { intros A A' H. rewrite (X_local A A' H).
          rewrite (W0_local A A'); [reflexivity |].
          intros e He. apply H. apply in_or_app. left. exact He. }
        assert (HdisM : forall e, In e Em -> ~ In e (E0 ++ Ep)).
        { intros e He Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          - exact (dis_0m e Hin He).
          - exact (dis_pm e Hin He). }
        rewrite (csum_ext L V eqbL vals Ep
                   (fun A1 => Csum Em (fun A => W0 A * (X A * X (pull A))) A1)
                   (fun A1 => (W0 A1 * Csum Em (fun B => X (pull B)) A1) * X A1)).
        2: { intro A1.
             rewrite (csum_ext L V eqbL vals Em
                        (fun A => W0 A * (X A * X (pull A)))
                        (fun A => (W0 A * X A) * X (pull A))) by (intro A; ring).
             rewrite (csum_factor_out (E0 ++ Ep) (fun B => W0 B * X B) HK Em HdisM
                        (fun B => X (pull B)) A1).
             ring. }
        (* the sum over Ep *)
        assert (HK' : LocalOn E0 (fun B => W0 B * Csum Em (fun C => X (pull C)) B)).
        { intros A A' H. rewrite (W0_local A A' H), (mirror_sum_local A A' H). reflexivity. }
        assert (HdisP : forall e, In e Ep -> ~ In e E0).
        { intros e He Hin. exact (dis_0p e Hin He). }
        rewrite (csum_factor_out E0 (fun B => W0 B * Csum Em (fun C => X (pull C)) B)
                   HK' Ep HdisP X A0).
        rewrite mirror_sum. ring.
      Qed.

      Corollary csum_reflection_positive : (forall A, 0 <= W0 A) ->
        forall U : Cfg, 0 <= Csum (E0 ++ Ep ++ Em) (fun A => W0 A * (X A * X (pull A))) U.
      Proof.
        intros HW U. rewrite csum_reflection_identity.
        apply csum_nonneg. intro A0.
        apply Rmult_le_pos; [apply HW |].
        pose proof (Rle_0_sqr (Csum Ep X A0)) as Hs. unfold Rsqr in Hs. exact Hs.
      Qed.
    End RP.

  End RL.

End ProductMeasureRelabel.
