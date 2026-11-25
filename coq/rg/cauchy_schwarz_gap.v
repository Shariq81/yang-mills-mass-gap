(* =========================================================================
   rg/cauchy_schwarz_gap.v

   Two elementary real-analysis facts behind the transfer-matrix mass gap.

   1. `quad_disc` (Cauchy-Schwarz from positivity): if
        a + 2 lam b + lam^2 c >= 0  for every real lam, and c >= 0,
      then  b^2 <= a c.

   2. `cs_gap` (iterated Cauchy-Schwarz).  Let a_j, j = 0, 1, 2, ..., be real
      numbers with
        a_0 >= 0,   a_{2j} >= 0,   a_j^2 <= a_0 a_{2j}        (for all j)
      (as for a_j = (psi, T^j psi) with T symmetric and the form positive
      semidefinite) and suppose |a_j| <= C rho^j for some constant C and
      some rho > 0.  Then the constant disappears:
        |a_k| <= rho^k a_0     for every k.
      Indeed a_k^{2^r} <= a_0^{2^r - 1} a_{k 2^r} <= a_0^{2^r - 1} C rho^{k 2^r}
      for every r >= 1, so (|a_k| / (rho^k a_0))^{2^r} <= C / a_0 is bounded
      in r, which forces |a_k| / (rho^k a_0) <= 1.

   Depends ONLY on the Coq standard library.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Arith Lia Lra Psatz.
Open Scope R_scope.

Module CauchySchwarzGap.

  (* =======================================================================
     1. Cauchy-Schwarz from positivity of a quadratic form
     ======================================================================= *)

  Lemma quad_disc : forall a b c : R,
    0 <= c ->
    (forall lam : R, 0 <= a + 2 * lam * b + lam * lam * c) ->
    b * b <= a * c.
  Proof.
    intros a b c Hc H.
    destruct (Req_dec c 0) as [Hc0 | Hc0].
    - subst c. destruct (Req_dec b 0) as [Hb0 | Hb0].
      + subst b. lra.
      + exfalso. specialize (H (- (a + 1) / (2 * b))).
        replace (a + 2 * (- (a + 1) / (2 * b)) * b
                 + - (a + 1) / (2 * b) * (- (a + 1) / (2 * b)) * 0)
          with (-1) in H by (field; exact Hb0).
        lra.
    - assert (Hcp : 0 < c) by lra.
      specialize (H (- b / c)).
      replace (a + 2 * (- b / c) * b + - b / c * (- b / c) * c)
        with ((a * c - b * b) / c) in H by (field; exact Hc0).
      assert (H1 : 0 <= (a * c - b * b) / c * c).
      { apply Rmult_le_pos; lra. }
      replace ((a * c - b * b) / c * c) with (a * c - b * b) in H1 by (field; exact Hc0).
      lra.
  Qed.

  (* =======================================================================
     2. Iterated Cauchy-Schwarz
     ======================================================================= *)

  Lemma pow2_pos : forall r : nat, (1 <= 2 ^ r)%nat.
  Proof.
    induction r as [| r IH]; [cbn; lia |]. rewrite Nat.pow_succ_r'. lia.
  Qed.

  Lemma pow2_ge : forall r : nat, (r <= 2 ^ r)%nat.
  Proof.
    induction r as [| r IH]; [cbn; lia |].
    rewrite Nat.pow_succ_r'. pose proof (pow2_pos r). lia.
  Qed.

  Lemma sqr_mono : forall x y : R, 0 <= x -> x <= y -> x * x <= y * y.
  Proof. intros x y Hx Hxy. apply Rmult_le_compat; lra. Qed.

  Section Gap.
    Variable a : nat -> R.
    Variables C rho : R.
    Hypothesis a0_nonneg : 0 <= a 0%nat.
    Hypothesis a_even_nonneg : forall j, 0 <= a (2 * j)%nat.
    Hypothesis a_cs : forall j, a j * a j <= a 0%nat * a (2 * j)%nat.
    Hypothesis rho_pos : 0 < rho.
    Hypothesis a_decay : forall j, Rabs (a j) <= C * rho ^ j.

    (* |a_k|^(2^(r+1)) <= a_0^(2^(r+1) - 1) * a_(k 2^(r+1)) *)
    Lemma cs_power : forall (k r : nat),
      Rabs (a k) ^ (2 ^ S r) <= a 0%nat ^ (2 ^ S r - 1) * a (k * 2 ^ S r)%nat.
    Proof.
      intros k r. induction r as [| r IH].
      - cbn [Nat.pow Nat.mul Nat.add Nat.sub pow].
        replace (k * 2)%nat with (2 * k)%nat by lia.
        rewrite !Rmult_1_r, <- Rabs_mult.
        rewrite Rabs_pos_eq; [apply a_cs |].
        pose proof (Rle_0_sqr (a k)) as Hs. unfold Rsqr in Hs. exact Hs.
      - set (N := (2 ^ S r)%nat) in *.
        assert (HN : (1 <= N)%nat) by apply pow2_pos.
        replace (2 ^ S (S r))%nat with (N * 2)%nat by (unfold N; rewrite (Nat.pow_succ_r' 2 (S r)); lia).
        replace (N * 2 - 1)%nat with ((N - 1) * 2 + 1)%nat by lia.
        replace (k * (N * 2))%nat with (2 * (k * N))%nat by lia.
        rewrite pow_mult, pow_add, pow_mult. cbn [pow]. rewrite !Rmult_1_r.
        set (x := Rabs (a k) ^ N) in *.
        set (y := a 0%nat ^ (N - 1)) in *.
        assert (Hx : 0 <= x) by (unfold x; apply pow_le; apply Rabs_pos).
        assert (Hy : 0 <= y) by (unfold y; apply pow_le; exact a0_nonneg).
        assert (HaK : 0 <= a (k * N)%nat).
        { replace (k * N)%nat with (2 * (k * 2 ^ r))%nat
            by (unfold N; rewrite (Nat.pow_succ_r' 2 r); lia).
          apply a_even_nonneg. }
        pose proof (sqr_mono x (y * a (k * N)%nat) Hx IH) as H1.
        pose proof (a_cs (k * N)%nat) as H2.
        assert (Hyy : 0 <= y * y) by (apply Rmult_le_pos; assumption).
        apply Rle_trans with (y * a (k * N)%nat * (y * a (k * N)%nat)); [exact H1 |].
        replace (y * a (k * N)%nat * (y * a (k * N)%nat))
          with (y * y * (a (k * N)%nat * a (k * N)%nat)) by ring.
        replace (y * y * a 0%nat * a (2 * (k * N))%nat)
          with (y * y * (a 0%nat * a (2 * (k * N))%nat)) by ring.
        apply Rmult_le_compat_l; assumption.
    Qed.

    Theorem cs_gap : forall k : nat, Rabs (a k) <= rho ^ k * a 0%nat.
    Proof.
      intro k.
      assert (Hrk : 0 < rho ^ k) by (apply pow_lt; exact rho_pos).
      destruct (Req_dec (a 0%nat) 0) as [Hz | Hnz].
      - (* a_0 = 0 forces a_k = 0 *)
        pose proof (a_cs k) as H. rewrite Hz, Rmult_0_l in H.
        assert (Hak : a k = 0) by nra.
        rewrite Hak, Rabs_R0, Hz. lra.
      - assert (Hp : 0 < a 0%nat) by lra.
        destruct (Rle_lt_dec (Rabs (a k)) (rho ^ k * a 0%nat)) as [Hle | Hgt];
          [exact Hle | exfalso].
        set (d := rho ^ k * a 0%nat) in *.
        assert (Hd : 0 < d) by (unfold d; apply Rmult_lt_0_compat; assumption).
        set (y := Rabs (a k) / d).
        assert (Hy1 : 1 < y).
        { unfold y. apply Rmult_lt_reg_r with d; [exact Hd |].
          unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
        assert (HC0 : 0 <= C).
        { pose proof (a_decay 0%nat) as H. cbn [pow] in H.
          pose proof (Rabs_pos (a 0%nat)). lra. }
        (* y^(2^(r+1)) <= C / a_0 for every r *)
        assert (Hbound : forall r, y ^ (2 ^ S r) <= C / a 0%nat).
        { intro r. set (N := (2 ^ S r)%nat).
          assert (HN : (1 <= N)%nat) by apply pow2_pos.
          pose proof (cs_power k r) as H1. fold N in H1.
          pose proof (a_decay (k * N)%nat) as H2.
          pose proof (Rle_abs (a (k * N)%nat)) as H3.
          assert (Hpow : 0 <= a 0%nat ^ (N - 1)) by (apply pow_le; lra).
          assert (H4 : Rabs (a k) ^ N <= a 0%nat ^ (N - 1) * (C * rho ^ (k * N))).
          { eapply Rle_trans; [exact H1 |]. apply Rmult_le_compat_l; [exact Hpow | lra]. }
          unfold y, Rdiv. rewrite Rpow_mult_distr, pow_inv.
          assert (HdN : d ^ N = rho ^ (k * N) * (a 0%nat ^ (N - 1) * a 0%nat)).
          { unfold d. rewrite Rpow_mult_distr, <- pow_mult.
            replace N with (N - 1 + 1)%nat at 2 by lia.
            rewrite pow_add. cbn [pow]. ring. }
          assert (HdNp : 0 < d ^ N) by (apply pow_lt; exact Hd).
          apply Rmult_le_reg_r with (d ^ N); [exact HdNp |].
          rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
          rewrite HdN. unfold Rdiv.
          replace (C * / a 0%nat * (rho ^ (k * N) * (a 0%nat ^ (N - 1) * a 0%nat)))
            with (a 0%nat ^ (N - 1) * (C * rho ^ (k * N))) by (field; exact Hnz).
          exact H4. }
        (* but y^n is unbounded *)
        assert (Hy : Rabs y > 1) by (rewrite Rabs_pos_eq; lra).
        destruct (Pow_x_infinity y Hy (C / a 0%nat + 1)) as [N0 HN0].
        pose proof (Hbound N0) as Hb.
        assert (Hge : (2 ^ S N0 >= N0)%nat).
        { pose proof (pow2_ge (S N0)). lia. }
        pose proof (HN0 (2 ^ S N0)%nat Hge) as Hinf.
        rewrite Rabs_pos_eq in Hinf by (apply pow_le; lra).
        lra.
    Qed.
  End Gap.

End CauchySchwarzGap.
