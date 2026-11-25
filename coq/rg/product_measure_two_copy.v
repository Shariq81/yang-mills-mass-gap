(* =========================================================================
   rg/product_measure_two_copy.v

   The two-copy identity behind reflection positivity with respect to a
   hyperplane that cuts links.

   Setting: a finite product a-priori measure; the summed variables split
   into the cut variables Ec, the variables Ep on the positive side and
   their mirror images Em (a relabeling phi with fibre maps sigma that
   preserve the a-priori sums maps Em onto Ep, `pull` being the induced
   map of configurations).  Let X depend only on Ep and let K2 (U, U') be a
   kernel that depends on each argument only through Ec ++ Ep.  For a
   configuration w put  merge w V = w on Ec, V elsewhere.  Then

     sum_{w on Ec}  sum_{U on Ec ++ Ep ++ Em}
         X (U) * X (pull U) * K2 (U, merge w (pull U))
       =  sum_{U on Ec ++ Ep}  sum_{U' on Ec ++ Ep}  X (U) * X (U') * K2 (U, U'):

   the mirror half of the configuration, completed by an independent copy w
   of the cut variables, is a second independent copy of the positive half.
   The right-hand side is non-negative when K2 is a positive kernel
   (rg/positive_kernel.v).

   Depends ONLY on Coq stdlib + rg.dup_clustering + rg.product_measure
   + rg.product_measure_perm + rg.product_measure_relabel.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import dup_clustering product_measure product_measure_perm.
From rg Require Import product_measure_relabel.
Import ListNotations.
Import DupClustering.
Open Scope R_scope.

Module ProductMeasureTwoCopy.

  Section TC.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable vals : list V.

    Local Notation Cfg := (cfg L V).
    Local Notation Upd := (upd L V eqbL).
    Local Notation Csum := (csum L V eqbL vals).
    Local Notation LocalOn := (ProductMeasure.local_on L V).

    (* inside a sum over E, only configurations that agree with the base
       outside E occur *)
    Lemma csum_ext_base : forall E (F G : Cfg -> R) (U : Cfg),
      (forall A, (forall l, ~ In l E -> A l = U l) -> F A = G A) ->
      Csum E F U = Csum E G U.
    Proof.
      induction E as [| e E IH]; intros F G U H.
      - cbn [csum]. apply H. intros l _. reflexivity.
      - cbn [csum]. apply rsum_ext. intros v _. apply IH.
        intros A HA. apply H. intros l Hl.
        rewrite (HA l) by (intro K; apply Hl; right; exact K).
        unfold upd. destruct (eqbL l e) eqn:Hle; [| reflexivity].
        apply eqbL_spec in Hle. subst l. exfalso. apply Hl. left. reflexivity.
    Qed.

    (* sums over two independent configurations commute *)
    Lemma csum_swap2 : forall E E' (F : Cfg -> Cfg -> R) (W0 U0 : Cfg),
      Csum E (fun w => Csum E' (fun U => F w U) U0) W0 =
      Csum E' (fun U => Csum E (fun w => F w U) W0) U0.
    Proof.
      induction E as [| e E IH]; intros E' F W0 U0.
      - reflexivity.
      - cbn [csum].
        rewrite (rsum_ext vals
                   (fun v => Csum E (fun w => Csum E' (fun U => F w U) U0) (Upd W0 e v))
                   (fun v => Csum E' (fun U => Csum E (fun w => F w U) (Upd W0 e v)) U0))
          by (intros v _; apply IH).
        symmetry.
        exact (ProductMeasure.csum_rsum L V eqbL vals vals E'
                 (fun v U => Csum E (fun w => F w U) (Upd W0 e v)) U0).
    Qed.

    Variables phi psi : L -> L.
    Hypothesis psi_phi : forall l, psi (phi l) = l.
    Hypothesis phi_psi : forall l, phi (psi l) = l.
    Variable sigma : L -> V -> V.
    Hypothesis sigma_sum : forall l (h : V -> R),
      rsum vals (fun v => h (sigma l v)) = rsum vals h.

    Local Notation pull := (ProductMeasureRelabel.pull L V phi sigma).

    Variables Ec Ep Em : list L.
    Hypothesis Em_Ep : Permutation (map psi Em) Ep.
    Hypothesis Ec_Ep : forall l, In l Ec -> ~ In l Ep.
    Hypothesis Ec_Em : forall l, In l Ec -> ~ In l Em.
    Hypothesis Ep_Em : forall l, In l Ep -> ~ In l Em.

    Variable X : Cfg -> R.
    Hypothesis X_loc : LocalOn Ep X.

    Variable K2 : Cfg -> Cfg -> R.
    Hypothesis K2_loc1 : forall U U' Z : Cfg,
      (forall l, In l (Ec ++ Ep) -> U l = U' l) -> K2 U Z = K2 U' Z.
    Hypothesis K2_loc2 : forall U Z Z' : Cfg,
      (forall l, In l (Ec ++ Ep) -> Z l = Z' l) -> K2 U Z = K2 U Z'.

    Variable inC : L -> bool.
    Hypothesis inC_spec : forall l, inC l = true <-> In l Ec.

    Definition merge (w A : Cfg) : Cfg := fun l => if inC l then w l else A l.

    Lemma half_sum : forall (w U0 : Cfg),
      Csum ((Ec ++ Ep) ++ Em)
        (fun U => X U * X (pull U) * K2 U (merge w (pull U))) U0 =
      Csum (Ec ++ Ep) (fun U => X U * Csum Ep (fun A => X A * K2 U A) w) U0.
    Proof.
      intros w U0.
      rewrite (ProductMeasurePerm.csum_app L V eqbL vals (Ec ++ Ep) Em).
      apply csum_ext. intro U.
      (* the factors that live on Ec ++ Ep are constant under the sum over Em *)
      transitivity (Csum Em (fun U2 => X U * (X (pull U2) * K2 U (merge w (pull U2)))) U).
      { apply csum_ext_base. intros A HA.
        rewrite (X_loc A U), (K2_loc1 A U (merge w (pull A))).
        - ring.
        - intros l Hl. apply HA. intro HlEm. apply in_app_or in Hl.
          destruct Hl as [Hl | Hl]; [exact (Ec_Em l Hl HlEm) | exact (Ep_Em l Hl HlEm)].
        - intros l Hl. apply HA. exact (Ep_Em l Hl). }
      rewrite (csum_scal L V eqbL vals Em (X U)
                 (fun U2 => X (pull U2) * K2 U (merge w (pull U2))) U).
      apply Rmult_eq_compat_l.
      (* the mirror variables become a second copy of the variables Ep *)
      set (H := fun A : Cfg => X A * K2 U (merge w A)).
      assert (HlocH : LocalOn Ep H).
      { intros A A' HAA. unfold H.
        rewrite (X_loc A A' HAA), (K2_loc2 U (merge w A) (merge w A')); [reflexivity |].
        intros l Hl. unfold merge. destruct (inC l) eqn:E; [reflexivity |].
        apply HAA. apply in_app_or in Hl. destruct Hl as [Hl | Hl]; [| exact Hl].
        apply (proj2 (inC_spec l)) in Hl. congruence. }
      transitivity (Csum (map psi Em) H (pull U)).
      { exact (ProductMeasureRelabel.csum_relabel L V eqbL eqbL_spec vals phi psi
                 psi_phi phi_psi sigma sigma_sum Em H U). }
      rewrite (ProductMeasurePerm.csum_perm L V eqbL eqbL_spec vals (map psi Em) Ep Em_Ep).
      transitivity (Csum Ep H w).
      { apply (ProductMeasureRelabel.csum_local_base L V eqbL eqbL_spec vals Ep H HlocH
                 Ep (pull U) w).
        intros e He Hne. contradiction. }
      apply csum_ext_base. intros A HA. unfold H. apply Rmult_eq_compat_l.
      apply K2_loc2. intros l Hl. unfold merge. destruct (inC l) eqn:E; [| reflexivity].
      symmetry. apply HA. apply (proj1 (inC_spec l)) in E. exact (Ec_Ep l E).
    Qed.

    Theorem two_copy_identity : forall (U0 W0 : Cfg),
      Csum Ec (fun w =>
                 Csum ((Ec ++ Ep) ++ Em)
                   (fun U => X U * X (pull U) * K2 U (merge w (pull U))) U0) W0 =
      Csum (Ec ++ Ep)
        (fun U => Csum (Ec ++ Ep) (fun U' => X U * X U' * K2 U U') W0) U0.
    Proof.
      intros U0 W0.
      rewrite (csum_ext L V eqbL vals Ec _
                 (fun w => Csum (Ec ++ Ep)
                             (fun U => X U * Csum Ep (fun A => X A * K2 U A) w) U0))
        by (intro w; apply half_sum).
      rewrite (csum_swap2 Ec (Ec ++ Ep)
                 (fun w U => X U * Csum Ep (fun A => X A * K2 U A) w) W0 U0).
      apply csum_ext. intro U.
      rewrite (csum_scal L V eqbL vals Ec (X U)
                 (fun w => Csum Ep (fun A => X A * K2 U A) w) W0).
      rewrite <- (ProductMeasurePerm.csum_app L V eqbL vals Ec Ep
                    (fun A => X A * K2 U A) W0).
      rewrite <- (csum_scal L V eqbL vals (Ec ++ Ep) (X U) (fun A => X A * K2 U A) W0).
      apply csum_ext. intro U'. ring.
    Qed.
  End TC.

End ProductMeasureTwoCopy.
