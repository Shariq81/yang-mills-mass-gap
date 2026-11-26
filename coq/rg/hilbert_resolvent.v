(* =========================================================================
   rg/hilbert_resolvent.v

   Resolvents of bounded symmetric operators on a complete form space
   (a real Hilbert space modulo its null vectors, as in
   `rg/hilbert_completion.v`: no quotient, no vector-space axioms, only a
   symmetric bilinear positive semidefinite form and completeness).

   Contents:
     1. weak limits;
     2. the Neumann series: if K is symmetric and || K x || <= q || x ||
        with q < 1, then 1 - K has a symmetric inverse of norm <= 1/(1-q);
     3. the resolvent of a symmetric operator with 0 <= A <= c:
        A - lam is invertible for lam > c and for lam < 0;
     4. an isolated simple eigenvalue: if A Om = Om, (Om, Om) = 1 and
        A <= c on the orthogonal complement of Om, then A - lam is
        invertible for every lam > c different from 1, and A - 1 is not
        invertible.

   All identities between vectors are weak identities
   (B u z = B w z for every z), which is the same as u - w being null.

   ZERO `Axiom`, `Parameter`, `Admitted`.  The limit of the Neumann series
   is selected with `ClassicalEpsilon.constructive_indefinite_description`.
   ========================================================================= *)

From Coq Require Import Reals Lra Lia Psatz ClassicalEpsilon.
Require Import rg.hilbert_completion.

Open Scope R_scope.

Module HilbertResolvent.

  Import HilbertCompletion.

  (* every Cauchy sequence converges *)
  Definition complete {E : Type} (add : E -> E -> E) (scal : R -> E -> E)
      (B : E -> E -> R) : Prop :=
    forall X : nat -> E,
      (forall eps : R, 0 < eps -> exists N : nat, forall p q : nat,
         (N <= p)%nat -> (N <= q)%nat ->
         B (sub add scal (X p) (X q)) (sub add scal (X p) (X q)) < eps) ->
      exists y : E, forall eps : R, 0 < eps -> exists N : nat, forall n : nat,
        (N <= n)%nat ->
        B (sub add scal (X n) y) (sub add scal (X n) y) < eps.

  Lemma cv_shift : forall (a : nat -> R) (l : R),
    Un_cv a l -> Un_cv (fun n => a (S n)) l.
  Proof.
    intros a l H eps He. destruct (H eps He) as [N HN]. exists N.
    intros n Hn. apply HN. unfold ge in *. lia.
  Qed.

  Lemma geo_aux : forall q D X : R, D = 1 + q * D ->
    X + 2 * (q * D * X) + q * q * (D * D * X) = D * D * X.
  Proof.
    intros q D X H.
    assert (E : D * D = (1 + q * D) * (1 + q * D)) by (rewrite <- H; reflexivity).
    transitivity ((1 + q * D) * (1 + q * D) * X); [ring |].
    rewrite <- E. reflexivity.
  Qed.

  Lemma sq_le_cancel : forall L W : R, 0 <= W -> L * L <= W * L -> L <= W.
  Proof.
    intros L W HW H. destruct (Rle_or_lt L W) as [Hle | Hlt]; [exact Hle | exfalso].
    assert (HL : 0 < L) by lra.
    pose proof (Rmult_lt_compat_r L W L HL Hlt) as Hc. lra.
  Qed.

  Section Space.
    Context {E : Type} {add : E -> E -> E} {scal : R -> E -> E} {B : E -> E -> R}.
    Hypothesis HF : form_axioms add scal B.

    Local Notation "x -- y" := (sub add scal x y) (at level 40, left associativity).

    (* =====================================================================
       1. Weak limits
       ===================================================================== *)

    Definition lim_of (X : nat -> E) (y : E) : Prop :=
      forall eps : R, 0 < eps -> exists N : nat, forall n : nat, (N <= n)%nat ->
        B (X n -- y) (X n -- y) < eps.

    Lemma lim_weak : forall (X : nat -> E) (y z : E),
      lim_of X y -> Un_cv (fun n => B (X n) z) (B y z).
    Proof.
      intros X y z HL eps He.
      pose proof (B_pos HF z) as HM.
      assert (Hd : 0 < eps * eps / (B z z + 1)).
      { apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; exact He | lra]. }
      destruct (HL _ Hd) as [N HN].
      exists N. intros n Hn. unfold R_dist.
      rewrite <- (B_sub HF (X n) y z).
      pose proof (cs HF (X n -- y) z) as Hcs.
      pose proof (HN n Hn) as Hq.
      pose proof (B_pos HF (X n -- y)) as Hp.
      assert (Hlt : B (X n -- y) z * B (X n -- y) z < eps * eps).
      { apply Rle_lt_trans with (B (X n -- y) (X n -- y) * B z z); [exact Hcs |].
        apply Rle_lt_trans with (eps * eps / (B z z + 1) * B z z).
        - apply Rmult_le_compat_r; [exact HM | lra].
        - assert (E1 : eps * eps / (B z z + 1) * (B z z + 1) = eps * eps)
            by (field; lra).
          assert (E2 : eps * eps / (B z z + 1) * B z z
                       = eps * eps / (B z z + 1) * (B z z + 1)
                         - eps * eps / (B z z + 1)) by ring.
          rewrite E2, E1. lra. }
      assert (Ha : Rabs (B (X n -- y) z) < Rabs eps)
        by (apply Rsqr_lt_abs_0; unfold Rsqr; exact Hlt).
      rewrite (Rabs_pos_eq eps) in Ha by lra. exact Ha.
    Qed.

    (* =====================================================================
       2. The Neumann series
       ===================================================================== *)

    Section Neumann.
      Hypothesis HC : complete add scal B.
      Variable K : E -> E.
      Hypothesis K_sym : forall x y, B (K x) y = B x (K y).
      Variable q : R.
      Hypothesis Hq0 : 0 <= q.
      Hypothesis Hq1 : q < 1.
      Hypothesis K_bd : forall x, B (K x) (K x) <= q * q * B x x.

      (* partial sums:  ps n x = x + K x + ... + K^(n-1) x *)
      Fixpoint ps (n : nat) (x : E) : E :=
        match n with
        | O => scal 0 x
        | S n' => add x (K (ps n' x))
        end.

      Let D : R := / (1 - q).

      Lemma D_pos : 0 < D.
      Proof. unfold D. apply Rinv_0_lt_compat. lra. Qed.

      Lemma D_eq : D = 1 + q * D.
      Proof. unfold D. field. lra. Qed.

      Lemma ps_0 : forall x z, B (ps 0 x) z = 0.
      Proof. intros x z. cbn [ps]. rewrite (B_scal HF 0 x z). ring. Qed.

      Lemma ps_S : forall n x z, B (ps (S n) x) z = B x z + B (ps n x) (K z).
      Proof.
        intros n x z. cbn [ps]. rewrite (B_add HF x (K (ps n x)) z), (K_sym (ps n x) z).
        reflexivity.
      Qed.

      Lemma ps_comm : forall n y z, B (ps n (K y)) z = B (K (ps n y)) z.
      Proof.
        induction n as [| n IH]; intros y z.
        - rewrite ps_0, (K_sym (ps 0 y) z), ps_0. reflexivity.
        - rewrite (ps_S n (K y) z), (IH y (K z)).
          rewrite (K_sym (ps (S n) y) z), (ps_S n y (K z)).
          rewrite (K_sym y z), (K_sym (ps n y) (K z)). reflexivity.
      Qed.

      Lemma ps_sym : forall n x y, B (ps n x) y = B x (ps n y).
      Proof.
        induction n as [| n IH]; intros x y.
        - rewrite ps_0, (B_sym HF x (ps 0 y)), ps_0. reflexivity.
        - rewrite (ps_S n x y), (IH x (K y)).
          rewrite (B_sym HF x (ps (S n) y)), (ps_S n y x).
          rewrite (B_sym HF x (ps n (K y))), (ps_comm n y x).
          rewrite (K_sym (ps n y) x), (B_sym HF y x). reflexivity.
      Qed.

      Lemma ps_bd : forall n x, B (ps n x) (ps n x) <= D * D * B x x.
      Proof.
        pose proof D_pos as HD.
        induction n as [| n IH]; intro x.
        - rewrite ps_0. apply Rmult_le_pos; [nra | apply (B_pos HF)].
        - cbn [ps].
          rewrite (Q_add HF x (K (ps n x))).
          pose proof (K_bd (ps n x)) as H1.
          pose proof (IH x) as H2.
          pose proof (B_pos HF x) as P1.
          pose proof (B_pos HF (ps n x)) as P2.
          pose proof (B_pos HF (K (ps n x))) as P3.
          pose proof (cs HF x (K (ps n x))) as Hcs.
          assert (H3 : B (K (ps n x)) (K (ps n x)) <= q * q * (D * D * B x x)).
          { apply Rle_trans with (q * q * B (ps n x) (ps n x)); [exact H1 |].
            apply Rmult_le_compat_l; [nra | exact H2]. }
          assert (H4 : Rabs (B x (K (ps n x))) <= q * D * B x x).
          { apply sq_abs_le.
            - apply Rmult_le_pos; [apply Rmult_le_pos; lra | exact P1].
            - apply Rle_trans with (B x x * B (K (ps n x)) (K (ps n x))); [exact Hcs |].
              apply Rle_trans with (B x x * (q * q * (D * D * B x x))).
              + apply Rmult_le_compat_l; [exact P1 | exact H3].
              + right. ring. }
          pose proof (Rle_abs (B x (K (ps n x)))) as H5.
          rewrite <- (geo_aux q D (B x x) D_eq). lra.
      Qed.

      Lemma ps_step : forall n m x z,
        B (ps (S (n + m)) x -- ps (S n) x) z = B (K (ps (n + m) x -- ps n x)) z.
      Proof.
        intros n m x z.
        rewrite <- (A_sub_weak HF K K_sym (ps (n + m) x) (ps n x) z).
        rewrite (B_sub HF (ps (S (n + m)) x) (ps (S n) x) z).
        rewrite (B_sub HF (K (ps (n + m) x)) (K (ps n x)) z).
        cbn [ps].
        rewrite (B_add HF x (K (ps (n + m) x)) z), (B_add HF x (K (ps n x)) z). ring.
      Qed.

      Lemma ps_diff : forall n m x,
        B (ps (n + m) x -- ps n x) (ps (n + m) x -- ps n x)
        <= (q * q) ^ n * (D * D * B x x).
      Proof.
        induction n as [| n IH]; intros m x.
        - rewrite (Q_sub HF (ps (0 + m) x) (ps 0 x)).
          rewrite (B_sym HF (ps (0 + m) x) (ps 0 x)), ps_0, ps_0.
          pose proof (ps_bd (0 + m) x) as H. simpl pow. lra.
        - change (S n + m)%nat with (S (n + m)).
          rewrite (Q_weak HF _ _ (ps_step n m x)).
          apply Rle_trans with (q * q * B (ps (n + m) x -- ps n x) (ps (n + m) x -- ps n x)).
          + apply K_bd.
          + change ((q * q) ^ S n) with (q * q * (q * q) ^ n).
            replace (q * q * (q * q) ^ n * (D * D * B x x))
              with (q * q * ((q * q) ^ n * (D * D * B x x))) by ring.
            apply Rmult_le_compat_l; [nra | apply IH].
      Qed.

      Lemma ps_cauchy : forall x eps, 0 < eps ->
        exists N : nat, forall p r : nat, (N <= p)%nat -> (N <= r)%nat ->
          B (ps p x -- ps r x) (ps p x -- ps r x) < eps.
      Proof.
        intros x eps He.
        pose proof D_pos as HD.
        pose proof (B_pos HF x) as P1.
        set (W := D * D * B x x).
        assert (HW : 0 <= W) by (unfold W; apply Rmult_le_pos; [nra | exact P1]).
        assert (Hy : 0 < eps / (W + 1)) by (apply Rdiv_lt_0_compat; lra).
        assert (Hqq : Rabs (q * q) < 1).
        { rewrite Rabs_pos_eq by nra. nra. }
        destruct (pow_lt_1_zero (q * q) Hqq (eps / (W + 1)) Hy) as [N HN].
        assert (Hmain : forall n m, (N <= n)%nat ->
                  B (ps (n + m) x -- ps n x) (ps (n + m) x -- ps n x) < eps).
        { intros n m Hn.
          apply Rle_lt_trans with ((q * q) ^ n * W); [apply ps_diff |].
          assert (Hn' : (n >= N)%nat) by (unfold ge; exact Hn).
          pose proof (HN n Hn') as Hp.
          pose proof (Rle_abs ((q * q) ^ n)) as Hp2.
          apply Rle_lt_trans with (eps / (W + 1) * W).
          - apply Rmult_le_compat_r; [exact HW | lra].
          - assert (E1 : eps / (W + 1) * (W + 1) = eps) by (field; lra).
            assert (E2 : eps / (W + 1) * W
                         = eps / (W + 1) * (W + 1) - eps / (W + 1)) by ring.
            rewrite E2, E1. lra. }
        exists N. intros p r Hp Hr.
        destruct (Nat.le_ge_cases r p) as [Hle | Hle].
        - replace p with (r + (p - r))%nat by lia. apply Hmain. exact Hr.
        - rewrite (Q_sub_sym HF (ps p x) (ps r x)).
          replace r with (p + (r - p))%nat by lia. apply Hmain. exact Hp.
      Qed.

      Definition S_ex (x : E) : { y : E | lim_of (fun n => ps n x) y } :=
        constructive_indefinite_description _ (HC (fun n => ps n x) (ps_cauchy x)).

      Definition Sx (x : E) : E := proj1_sig (S_ex x).

      Lemma S_cv : forall x z, Un_cv (fun n => B (ps n x) z) (B (Sx x) z).
      Proof.
        intros x z. exact (lim_weak (fun n => ps n x) (Sx x) z (proj2_sig (S_ex x))).
      Qed.

      Lemma S_sym : forall x y, B (Sx x) y = B x (Sx y).
      Proof.
        intros x y. rewrite (B_sym HF x (Sx y)).
        apply (UL_sequence (fun n => B (ps n x) y)); [apply S_cv |].
        apply (cv_ext (fun n => B (ps n y) x)); [| apply S_cv].
        intro n. rewrite (ps_sym n x y). apply (B_sym HF).
      Qed.

      (* (1 - K) S = 1, weakly *)
      Lemma S_eq : forall x z, B (Sx x) z - B (Sx x) (K z) = B x z.
      Proof.
        intros x z.
        assert (H1 : Un_cv (fun n => B (ps (S n) x) z) (B (Sx x) z))
          by (exact (cv_shift _ _ (S_cv x z))).
        assert (H2 : Un_cv (fun n => B (ps (S n) x) z) (B x z + B (Sx x) (K z))).
        { apply (cv_ext (fun n => B x z + B (ps n x) (K z))).
          - intro n. symmetry. apply ps_S.
          - exact (CV_plus _ _ _ _ (cv_const (B x z)) (S_cv x (K z))). }
        rewrite (UL_sequence _ _ _ H1 H2). ring.
      Qed.

      Lemma S_bd : forall x, B (Sx x) (Sx x) <= D * D * B x x.
      Proof.
        intro x.
        pose proof D_pos as HD.
        pose proof (B_pos HF x) as P1.
        pose proof (B_pos HF (Sx x)) as P2.
        set (W := D * D * B x x).
        assert (HW : 0 <= W) by (unfold W; apply Rmult_le_pos; [nra | exact P1]).
        apply sq_le_cancel; [exact HW |].
        pose proof (S_cv x (Sx x)) as Hcv.
        pose proof (CV_mult _ _ _ _ Hcv Hcv) as Hcv2. cbv beta in Hcv2.
        apply (cv_le_from _ _ _ 0%nat Hcv2).
        intros n _.
        apply Rle_trans with (B (ps n x) (ps n x) * B (Sx x) (Sx x)); [apply (cs HF) |].
        apply Rmult_le_compat_r; [exact P2 | apply ps_bd].
      Qed.

      Lemma neumann :
        exists S : E -> E,
          (forall x y, B (S x) y = B x (S y)) /\
          (forall x z, B (S x) z - B (S x) (K z) = B x z) /\
          (forall x, B (S x) (S x) <= / (1 - q) * / (1 - q) * B x x).
      Proof.
        exists Sx. split; [exact S_sym |]. split; [exact S_eq | exact S_bd].
      Qed.
    End Neumann.

    (* =====================================================================
       3. Resolvent of a symmetric operator with 0 <= A <= c
       ===================================================================== *)

    (* a symmetric operator with 0 <= (x, A x) <= c (x, x) has norm <= c *)
    Lemma form_to_norm : forall (A : E -> E) (c : R),
      (forall x y, B (A x) y = B x (A y)) ->
      (forall x, 0 <= B x (A x)) ->
      0 <= c ->
      (forall x, B x (A x) <= c * B x x) ->
      forall x, B (A x) (A x) <= c * c * B x x.
    Proof.
      intros A c A_sym A_pos Hc0 Hle x.
      pose proof (cs (A_form HF A A_sym A_pos) (A x) x) as Hcs. cbv beta in Hcs.
      pose proof (Hle x) as H1. pose proof (Hle (A x)) as H2.
      pose proof (A_pos x) as P1. pose proof (A_pos (A x)) as P2.
      pose proof (B_pos HF x) as P3. pose proof (B_pos HF (A x)) as P4.
      assert (Hprod : B (A x) (A (A x)) * B x (A x) <= (c * B (A x) (A x)) * (c * B x x))
        by (apply Rmult_le_compat; assumption).
      apply sq_le_cancel.
      - apply Rmult_le_pos; [apply Rmult_le_pos; exact Hc0 | exact P3].
      - lra.
    Qed.

    Section Resolvent.
      Hypothesis HC : complete add scal B.

      (* lam above the norm *)
      Lemma resolvent_above : forall (A : E -> E) (c lam : R),
        (forall x y, B (A x) y = B x (A y)) ->
        0 <= c ->
        (forall x, B (A x) (A x) <= c * c * B x x) ->
        c < lam ->
        exists G : E -> E,
          (forall x y, B (G x) y = B x (G y)) /\
          (forall x z, B (A (G x)) z - lam * B (G x) z = B x z) /\
          (forall x, B (G x) (G x) <= / (lam - c) * / (lam - c) * B x x).
      Proof.
        intros A c lam A_sym Hc0 A_bd Hlam.
        assert (Hl0 : 0 < lam) by lra.
        assert (Hil : 0 < / lam) by (apply Rinv_0_lt_compat; exact Hl0).
        set (K := fun x : E => scal (/ lam) (A x)).
        set (q := c * / lam).
        assert (K_sym : forall x y, B (K x) y = B x (K y)).
        { intros x y. unfold K.
          rewrite (B_scal HF (/ lam) (A x) y), (B_scal_r HF (/ lam) (A y) x), (A_sym x y).
          reflexivity. }
        assert (Hq0 : 0 <= q) by (unfold q; apply Rmult_le_pos; lra).
        assert (Hq1 : q < 1).
        { unfold q. apply Rmult_lt_reg_r with lam; [exact Hl0 |].
          rewrite Rmult_assoc, Rinv_l by lra. lra. }
        assert (K_bd : forall x, B (K x) (K x) <= q * q * B x x).
        { intro x. unfold K, q. rewrite (Q_scal HF (/ lam) (A x)).
          replace (c * / lam * (c * / lam) * B x x)
            with (/ lam * / lam * (c * c * B x x)) by ring.
          apply Rmult_le_compat_l; [nra | apply A_bd]. }
        destruct (neumann HC K K_sym q Hq0 Hq1 K_bd) as (S & S_sym & S_eq & S_bd).
        exists (fun x => scal (- / lam) (S x)).
        split; [| split].
        - intros x y.
          rewrite (B_scal HF (- / lam) (S x) y), (B_scal_r HF (- / lam) (S y) x), (S_sym x y).
          reflexivity.
        - intros x z.
          rewrite (A_sym (scal (- / lam) (S x)) z).
          rewrite (B_scal HF (- / lam) (S x) (A z)), (B_scal HF (- / lam) (S x) z).
          pose proof (S_eq x z) as H. unfold K in H.
          rewrite (B_scal_r HF (/ lam) (A z) (S x)) in H.
          rewrite <- H. field. lra.
        - intro x. rewrite (Q_scal HF (- / lam) (S x)).
          pose proof (S_bd x) as H.
          pose proof (B_pos HF (S x)) as P1.
          assert (E1 : / (lam - c) = / lam * / (1 - q)).
          { unfold q. field. split; lra. }
          rewrite E1.
          replace (/ lam * / (1 - q) * (/ lam * / (1 - q)) * B x x)
            with (/ lam * / lam * (/ (1 - q) * / (1 - q) * B x x)) by ring.
          replace (- / lam * - / lam * B (S x) (S x))
            with (/ lam * / lam * B (S x) (S x)) by ring.
          apply Rmult_le_compat_l; [nra | exact H].
      Qed.

      (* lam > c for 0 <= A <= c *)
      Lemma resolvent_form_above : forall (A : E -> E) (c lam : R),
        (forall x y, B (A x) y = B x (A y)) ->
        (forall x, 0 <= B x (A x)) ->
        0 <= c ->
        (forall x, B x (A x) <= c * B x x) ->
        c < lam ->
        exists G : E -> E,
          (forall x y, B (G x) y = B x (G y)) /\
          (forall x z, B (A (G x)) z - lam * B (G x) z = B x z) /\
          (forall x, B (G x) (G x) <= / (lam - c) * / (lam - c) * B x x).
      Proof.
        intros A c lam A_sym A_pos Hc0 Hle Hlam.
        exact (resolvent_above A c lam A_sym Hc0
                 (form_to_norm A c A_sym A_pos Hc0 Hle) Hlam).
      Qed.

      (* lam < 0 for 0 <= A <= c *)
      Lemma resolvent_below : forall (A : E -> E) (c lam : R),
        (forall x y, B (A x) y = B x (A y)) ->
        (forall x, 0 <= B x (A x)) ->
        0 <= c ->
        (forall x, B x (A x) <= c * B x x) ->
        lam < 0 ->
        exists G : E -> E,
          (forall x y, B (G x) y = B x (G y)) /\
          (forall x z, B (A (G x)) z - lam * B (G x) z = B x z) /\
          (forall x, B (G x) (G x) <= / (- lam) * / (- lam) * B x x).
      Proof.
        intros A c lam A_sym A_pos Hc0 Hle Hlam.
        set (A' := fun x : E => scal c x -- A x).
        assert (A'_sym : forall x y, B (A' x) y = B x (A' y)).
        { intros x y. unfold A'.
          rewrite (B_sub HF (scal c x) (A x) y), (B_sub_r HF (scal c y) (A y) x).
          rewrite (B_scal HF c x y), (B_scal_r HF c y x), (A_sym x y). reflexivity. }
        assert (A'_val : forall x, B x (A' x) = c * B x x - B x (A x)).
        { intro x. unfold A'.
          rewrite (B_sub_r HF (scal c x) (A x) x), (B_scal_r HF c x x). reflexivity. }
        assert (A'_pos : forall x, 0 <= B x (A' x)).
        { intro x. rewrite A'_val. pose proof (Hle x). lra. }
        assert (A'_le : forall x, B x (A' x) <= c * B x x).
        { intro x. rewrite A'_val. pose proof (A_pos x). lra. }
        assert (Hl' : c < c - lam) by lra.
        destruct (resolvent_form_above A' c (c - lam) A'_sym A'_pos Hc0 A'_le Hl')
          as (G' & G'_sym & G'_eq & G'_bd).
        exists (fun x => scal (-1) (G' x)).
        split; [| split].
        - intros x y.
          rewrite (B_scal HF (-1) (G' x) y), (B_scal_r HF (-1) (G' y) x), (G'_sym x y).
          reflexivity.
        - intros x z.
          rewrite (A_sym (scal (-1) (G' x)) z).
          rewrite (B_scal HF (-1) (G' x) (A z)), (B_scal HF (-1) (G' x) z).
          pose proof (G'_eq x z) as H.
          rewrite (A'_sym (G' x) z) in H. unfold A' in H.
          rewrite (B_sub_r HF (scal c z) (A z) (G' x)), (B_scal_r HF c z (G' x)) in H.
          lra.
        - intro x. rewrite (Q_scal HF (-1) (G' x)).
          pose proof (G'_bd x) as H.
          replace (c - lam - c) with (- lam) in H by ring. lra.
      Qed.

      (* ===================================================================
         4. An isolated simple eigenvalue
         =================================================================== *)

      Section Gap.
        Variable A : E -> E.
        Hypothesis A_sym : forall x y, B (A x) y = B x (A y).
        Hypothesis A_pos : forall x, 0 <= B x (A x).
        Variable Om : E.
        Hypothesis Om_norm : B Om Om = 1.
        Hypothesis Om_fix : B (A Om -- Om) (A Om -- Om) = 0.
        Variable c : R.
        Hypothesis Hc0 : 0 <= c.
        Hypothesis Hgap : forall x, B x Om = 0 -> B x (A x) <= c * B x x.

        Lemma AOm_r : forall u, B u (A Om) = B u Om.
        Proof.
          intro u. rewrite (B_sym HF u (A Om)), (B_sym HF u Om).
          exact (null_weak_inv HF (A Om) Om Om_fix u).
        Qed.

        (* the operator with the vacuum projected out *)
        Definition Ared (x : E) : E := A x -- scal (B x Om) Om.

        Lemma Ared_sym : forall x y, B (Ared x) y = B x (Ared y).
        Proof.
          intros x y. unfold Ared.
          rewrite (B_sub HF (A x) (scal (B x Om) Om) y).
          rewrite (B_sub_r HF (A y) (scal (B y Om) Om) x).
          rewrite (B_scal HF (B x Om) Om y), (B_scal_r HF (B y Om) Om x).
          rewrite (A_sym x y), (B_sym HF Om y). ring.
        Qed.

        Lemma Ared_val : forall x, B x (Ared x) = B x (A x) - B x Om * B x Om.
        Proof.
          intro x. unfold Ared.
          rewrite (B_sub_r HF (A x) (scal (B x Om) Om) x), (B_scal_r HF (B x Om) Om x).
          reflexivity.
        Qed.

        (* the component orthogonal to the vacuum *)
        Lemma perp_facts : forall x,
          B (x -- scal (B x Om) Om) Om = 0 /\
          B (x -- scal (B x Om) Om) (A (x -- scal (B x Om) Om))
            = B x (A x) - B x Om * B x Om /\
          B (x -- scal (B x Om) Om) (x -- scal (B x Om) Om)
            = B x x - B x Om * B x Om.
        Proof.
          intro x.
          set (k := B x Om).
          set (y := x -- scal k Om).
          assert (Hy : B y Om = 0).
          { unfold y. rewrite (B_sub HF x (scal k Om) Om), (B_scal HF k Om Om), Om_norm.
            unfold k. ring. }
          split; [exact Hy |]. split.
          - (* B y (A y) = B x (A y) - k * B Om (A y), and B Om (A y) = B y Om = 0 *)
            assert (E1 : B Om (A y) = 0).
            { rewrite <- (A_sym Om y), (B_sym HF (A Om) y), (AOm_r y). exact Hy. }
            assert (E2 : B y (A y) = B x (A y)).
            { unfold y at 1. rewrite (B_sub HF x (scal k Om) (A y)), (B_scal HF k Om (A y)), E1.
              ring. }
            rewrite E2, <- (A_sym x y). unfold y.
            rewrite (B_sub_r HF x (scal k Om) (A x)), (B_scal_r HF k Om (A x)).
            rewrite (B_sym HF (A x) x), (A_sym x Om), (AOm_r x). reflexivity.
          - unfold y. rewrite (Q_sub HF x (scal k Om)), (B_scal_r HF k Om x), (Q_scal HF k Om),
              Om_norm. unfold k. ring.
        Qed.

        Lemma Ared_pos : forall x, 0 <= B x (Ared x).
        Proof.
          intro x. rewrite Ared_val.
          destruct (perp_facts x) as (_ & H2 & _). rewrite <- H2. apply A_pos.
        Qed.

        Lemma Ared_le : forall x, B x (Ared x) <= c * B x x.
        Proof.
          intro x. rewrite Ared_val.
          destruct (perp_facts x) as (H1 & H2 & H3).
          pose proof (Hgap _ H1) as H. rewrite H2, H3 in H.
          assert (0 <= c * (B x Om * B x Om)) by (apply Rmult_le_pos; [exact Hc0 | nra]).
          lra.
        Qed.

        Lemma Ared_Om : forall u, B (Ared u) Om = 0.
        Proof.
          intro u. unfold Ared.
          rewrite (B_sub HF (A u) (scal (B u Om) Om) Om), (B_scal HF (B u Om) Om Om), Om_norm.
          rewrite (A_sym u Om), (AOm_r u). ring.
        Qed.

        Lemma resolvent_gap : forall lam : R, c < lam -> lam <> 1 ->
          exists (G : E -> E) (C : R),
            (forall x y, B (G x) y = B x (G y)) /\
            (forall x z, B (A (G x)) z - lam * B (G x) z = B x z) /\
            (forall x, B (G x) (G x) <= C * B x x).
        Proof.
          intros lam Hlam Hl1.
          assert (Hl0 : 0 < lam) by lra.
          destruct (resolvent_form_above Ared c lam Ared_sym Ared_pos Hc0 Ared_le Hlam)
            as (G' & G'_sym & G'_eq & G'_bd).
          set (alpha := / (lam * (1 - lam))).
          assert (Ea : alpha * lam * (1 - lam) = 1).
          { unfold alpha. field. split; lra. }
          (* (G' x, Om) = - (x, Om) / lam *)
          assert (HG'Om : forall x, - lam * B (G' x) Om = B x Om).
          { intro x. pose proof (G'_eq x Om) as H. rewrite (Ared_Om (G' x)) in H. lra. }
          set (C' := / (lam - c) * / (lam - c)).
          exists (fun x => add (G' x) (scal (alpha * B x Om) Om)),
                 (2 * C' + 2 * (alpha * alpha)).
          split; [| split].
          - intros x y.
            rewrite (B_add HF (G' x) (scal (alpha * B x Om) Om) y).
            rewrite (B_add_r HF (G' y) (scal (alpha * B y Om) Om) x).
            rewrite (B_scal HF (alpha * B x Om) Om y), (B_scal_r HF (alpha * B y Om) Om x).
            rewrite (G'_sym x y), (B_sym HF Om y). ring.
          - intros x z.
            set (k := B x Om).
            rewrite (A_sym (add (G' x) (scal (alpha * k) Om)) z).
            rewrite (B_add HF (G' x) (scal (alpha * k) Om) (A z)).
            rewrite (B_add HF (G' x) (scal (alpha * k) Om) z).
            rewrite (B_scal HF (alpha * k) Om (A z)), (B_scal HF (alpha * k) Om z).
            assert (E1 : B Om (A z) = B Om z).
            { rewrite <- (A_sym Om z). exact (null_weak_inv HF (A Om) Om Om_fix z). }
            rewrite E1.
            pose proof (G'_eq x z) as H.
            rewrite (Ared_sym (G' x) z) in H. unfold Ared in H.
            rewrite (B_sub_r HF (A z) (scal (B z Om) Om) (G' x)) in H.
            rewrite (B_scal_r HF (B z Om) Om (G' x)) in H.
            rewrite (B_sym HF z Om) in H.
            pose proof (HG'Om x) as Hk. fold k in Hk.
            set (g := B (G' x) Om) in *.
            set (oz := B Om z) in *.
            set (gT := B (G' x) (A z)) in *.
            set (gz := B (G' x) z) in *.
            rewrite <- Hk.
            replace (gT + alpha * (- lam * g) * oz - lam * (gz + alpha * (- lam * g) * oz))
              with (gT - oz * g - lam * gz + g * oz * (1 - alpha * lam * (1 - lam))) by ring.
            rewrite Ea. lra.
          - intro x.
            apply Rle_trans with (2 * B (G' x) (G' x)
                                  + 2 * B (scal (alpha * B x Om) Om) (scal (alpha * B x Om) Om)).
            + apply (Q_add2 HF).
            + rewrite (Q_scal HF (alpha * B x Om) Om), Om_norm.
              pose proof (G'_bd x) as H. fold C' in H.
              pose proof (cs HF x Om) as Hcs. rewrite Om_norm in Hcs.
              assert (Ha : 0 <= alpha * alpha) by nra.
              assert (H2 : alpha * alpha * (B x Om * B x Om) <= alpha * alpha * (B x x * 1))
                by (apply Rmult_le_compat_l; assumption).
              lra.
        Qed.

        (* A - 1 has no bounded left inverse: 1 is in the spectrum *)
        Lemma eigen_no_inverse : forall (G : E -> E) (C : R),
          (forall x, B (G x) (G x) <= C * B x x) ->
          B (G (A Om -- scal 1 Om) -- Om) (G (A Om -- scal 1 Om) -- Om) = 0 ->
          False.
        Proof.
          intros G C G_bd Hinv.
          set (a := A Om -- scal 1 Om) in *.
          assert (Ha : B a a = 0).
          { unfold a at 1. rewrite (B_sub HF (A Om) (scal 1 Om) a), (B_scal HF 1 Om a).
            rewrite (null_weak_inv HF (A Om) Om Om_fix a). ring. }
          pose proof (G_bd a) as H1. rewrite Ha, Rmult_0_r in H1.
          pose proof (B_pos HF (G a)) as P1.
          pose proof (Q_bound HF Om (G a)) as H2.
          rewrite (Q_sub_sym HF Om (G a)), Hinv, Om_norm in H2. lra.
        Qed.
      End Gap.
    End Resolvent.

    (* =====================================================================
       5. From the weak resolvent identity to a two-sided inverse
       ===================================================================== *)

    Lemma inverse_of_weak : forall (A G : E -> E) (lam : R),
      (forall x y, B (A x) y = B x (A y)) ->
      (forall x y, B (G x) y = B x (G y)) ->
      (forall x z, B (A (G x)) z - lam * B (G x) z = B x z) ->
      (forall x y, B (G (add x y) -- add (G x) (G y)) (G (add x y) -- add (G x) (G y)) = 0) /\
      (forall c x, B (G (scal c x) -- scal c (G x)) (G (scal c x) -- scal c (G x)) = 0) /\
      (forall x, B ((A (G x) -- scal lam (G x)) -- x) ((A (G x) -- scal lam (G x)) -- x) = 0) /\
      (forall x, B (G (A x -- scal lam x) -- x) (G (A x -- scal lam x) -- x) = 0).
    Proof.
      intros A G lam A_sym G_sym G_eq.
      split; [exact (A_add_null HF G G_sym) |].
      split; [exact (A_scal_null HF G G_sym) |].
      split.
      - intro x. apply (null_weak HF). intro z.
        rewrite (B_sub HF (A (G x)) (scal lam (G x)) z), (B_scal HF lam (G x) z).
        apply G_eq.
      - intro x. apply (null_weak HF). intro z.
        rewrite (G_sym (A x -- scal lam x) z).
        rewrite (B_sub HF (A x) (scal lam x) (G z)), (B_scal HF lam x (G z)).
        rewrite (A_sym x (G z)).
        rewrite (B_sym HF x (A (G z))), (B_sym HF x (G z)), (B_sym HF x z).
        apply G_eq.
    Qed.

  End Space.

End HilbertResolvent.
