(* =========================================================================
   poly_exp_bound.v

   Elementary finite-polynomial exponential-generating-function lemma:
     If t(0) = 1, u(s) >= 0 (1 <= s <= N), and for all 1 <= k <= N:
       k * t(k) = sum_{s=1}^k s * u(s) * t(k - s),
     then:
       sum_{k=0}^N t(k) <= exp (sum_{s=1}^N u(s)).

   Uses ONLY finite polynomial arithmetic and Coq stdlib's definition of exp.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Arith List Lia Lra.
Import ListNotations.
Open Scope R_scope.

Module PolyExpBound.

  (* =======================================================================
     1. Helpers for sum_f_R0 and exp partial-sum lower bound
     ======================================================================= *)

  Lemma sum_f_R0_ext : forall f g N,
    (forall i, (i <= N)%nat -> f i = g i) ->
    sum_f_R0 f N = sum_f_R0 g N.
  Proof.
    intros f g N. induction N as [| N' IH]; intro Hext; simpl.
    - apply Hext; lia.
    - rewrite IH; [rewrite Hext; [reflexivity | lia] | intros i Hi; apply Hext; lia].
  Qed.

  Lemma sum_f_R0_le : forall f g N,
    (forall i, (i <= N)%nat -> f i <= g i) ->
    sum_f_R0 f N <= sum_f_R0 g N.
  Proof.
    intros f g N. induction N as [| N' IH]; intro Hle; simpl.
    - apply Hle; lia.
    - apply Rplus_le_compat; [apply IH; intros i Hi; apply Hle; lia | apply Hle; lia].
  Qed.

  Lemma sum_f_R0_nonneg : forall f N,
    (forall i, (i <= N)%nat -> 0 <= f i) ->
    0 <= sum_f_R0 f N.
  Proof.
    intros f N. induction N as [| N' IH]; intro Hnn; simpl.
    - apply Hnn; lia.
    - pose proof (IH (fun i Hi => Hnn i ltac:(lia))).
      pose proof (Hnn (S N') ltac:(lia)). lra.
  Qed.

  Lemma sum_f_R0_mono : forall f N M,
    (forall i, 0 <= f i) ->
    (N <= M)%nat ->
    sum_f_R0 f N <= sum_f_R0 f M.
  Proof.
    intros f N M Hnn Hle. induction Hle as [| M' Hle' IH].
    - lra.
    - simpl. specialize (Hnn (S M')). lra.
  Qed.

  Lemma sum_f_R0_scale : forall c f N,
    sum_f_R0 (fun i => c * f i) N = c * sum_f_R0 f N.
  Proof.
    intros c f N. induction N as [| N' IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma sum_f_R0_plus : forall f g N,
    sum_f_R0 (fun i => f i + g i) N = sum_f_R0 f N + sum_f_R0 g N.
  Proof.
    intros f g N. induction N as [| N' IH]; simpl; [ring | rewrite IH; ring].
  Qed.

  Lemma sum_f_R0_zero : forall N,
    sum_f_R0 (fun _ => 0) N = 0.
  Proof.
    induction N as [| N' IH]; simpl; [reflexivity | rewrite IH; ring].
  Qed.

  Lemma sum_f_R0_shift : forall f N,
    sum_f_R0 f (S N) = f 0%nat + sum_f_R0 (fun i => f (S i)) N.
  Proof.
    intros f N. induction N as [| N' IH].
    - simpl; ring.
    - change (sum_f_R0 f (S (S N'))) with (sum_f_R0 f (S N') + f (S (S N'))).
      change (sum_f_R0 (fun i => f (S i)) (S N'))
        with (sum_f_R0 (fun i => f (S i)) N' + f (S (S N'))).
      rewrite IH. ring.
  Qed.

  Lemma fact_pos_R : forall n, 0 < INR (fact n).
  Proof. intro n. apply lt_0_INR. pose proof (fact_neq_0 n). lia. Qed.

  Lemma exp_partial_sum_le : forall x N,
    0 <= x ->
    sum_f_R0 (fun i => / INR (fact i) * x ^ i) N <= exp x.
  Proof.
    intros x N Hx.
    assert (Hnn : forall i, 0 <= / INR (fact i) * x ^ i).
    { intro i. apply Rmult_le_pos.
      - left. apply Rinv_0_lt_compat. apply lt_0_INR. pose proof (fact_neq_0 i). lia.
      - apply pow_le. exact Hx. }
    destruct (Rle_lt_dec (sum_f_R0 (fun i => / INR (fact i) * x ^ i) N) (exp x)) as [Hle | Hgt];
      [exact Hle | exfalso].
    unfold exp in Hgt.
    destruct (exist_exp x) as [l Hl]; simpl in Hgt.
    unfold exp_in, infinite_sum in Hl.
    set (eps := (sum_f_R0 (fun i => / INR (fact i) * x ^ i) N - l) / 2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (Hl eps Heps) as [M HM].
    set (K := Nat.max N M).
    specialize (HM K (Nat.le_max_r N M)).
    unfold R_dist in HM.
    pose proof (sum_f_R0_mono _ N K Hnn (Nat.le_max_l N M)) as Hmono.
    apply Rabs_def2 in HM. unfold eps in HM. lra.
  Qed.

  (* =======================================================================
     2. Coefficient-Indexed Finite Polynomials (fun k : nat => R with degree bound)
     ======================================================================= *)

  (* Even simpler than list R: a polynomial is a pair (deg, coeff : nat -> R)
     with coeff k = 0 for k > deg! Wait: just a function (nat -> R) with
     separate degree-bound predicates is extraordinarily clean in Coq! *)

  Definition p_zero : nat -> R := fun _ => 0.
  Definition p_one  : nat -> R := fun k => match k with 0%nat => 1 | S _ => 0 end.
  Definition p_add (p q : nat -> R) : nat -> R := fun k => p k + q k.
  Definition p_scale (c : R) (p : nat -> R) : nat -> R := fun k => c * p k.
  Definition p_mul (p q : nat -> R) : nat -> R :=
    fun k => sum_f_R0 (fun j => p j * q (k - j)%nat) k.
  Definition p_deriv (p : nat -> R) : nat -> R :=
    fun k => INR (S k) * p (S k).

  Fixpoint p_pow (p : nat -> R) (m : nat) : nat -> R :=
    match m with
    | 0%nat => p_one
    | S m' => p_mul p (p_pow p m')
    end.

  Definition p_eq (p q : nat -> R) : Prop := forall k, p k = q k.

  Lemma p_mul_comm : forall p q k, p_mul p q k = p_mul q p k.
  Proof.
    intros p q k. unfold p_mul.
    (* Reverse index j -> k - j *)
    assert (Hrev : forall n (f : nat -> R),
      sum_f_R0 f n = sum_f_R0 (fun j => f (n - j)%nat) n).
    { induction n as [| n' IH]; intro f; [simpl; reflexivity |].
      rewrite (sum_f_R0_shift (fun j => f (S n' - j)%nat) n'). rewrite Nat.sub_0_r.
      change (sum_f_R0 f (S n')) with (sum_f_R0 f n' + f (S n')).
      rewrite (IH f).
      rewrite Rplus_comm. f_equal. }
    rewrite (Hrev k). apply sum_f_R0_ext. intros j Hj.
    replace (k - (k - j))%nat with j by lia. ring.
  Qed.

  Lemma p_mul_ext : forall p1 p2 q1 q2,
    p_eq p1 p2 -> p_eq q1 q2 -> p_eq (p_mul p1 q1) (p_mul p2 q2).
  Proof.
    intros p1 p2 q1 q2 Hp Hq k. unfold p_mul.
    apply sum_f_R0_ext. intros j _. rewrite Hp, Hq. reflexivity.
  Qed.

  Lemma p_mul_add_l : forall p1 p2 q k,
    p_mul (p_add p1 p2) q k = p_add (p_mul p1 q) (p_mul p2 q) k.
  Proof.
    intros p1 p2 q k. unfold p_mul, p_add.
    rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros j _. ring.
  Qed.

  Lemma p_mul_add_r : forall p q1 q2 k,
    p_mul p (p_add q1 q2) k = p_add (p_mul p q1) (p_mul p q2) k.
  Proof.
    intros p q1 q2 k. unfold p_mul, p_add.
    rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros j _. ring.
  Qed.

  Lemma p_mul_scale_l : forall c p q k,
    p_mul (p_scale c p) q k = p_scale c (p_mul p q) k.
  Proof.
    intros c p q k. unfold p_mul, p_scale.
    rewrite <- sum_f_R0_scale. apply sum_f_R0_ext. intros j _. ring.
  Qed.

  Lemma p_mul_scale_r : forall c p q k,
    p_mul p (p_scale c q) k = p_scale c (p_mul p q) k.
  Proof.
    intros c p q k. unfold p_mul, p_scale.
    rewrite <- sum_f_R0_scale. apply sum_f_R0_ext. intros j _. ring.
  Qed.

  Lemma p_mul_one_r : forall p k, p_mul p p_one k = p k.
  Proof.
    intros p k. unfold p_mul, p_one.
    destruct k as [| k']; [simpl; ring |].
    cbn [sum_f_R0]. rewrite Nat.sub_diag.
    assert (Hz : sum_f_R0 (fun j => p j * match (S k' - j)%nat with 0%nat => 1 | S _ => 0 end) k' = 0).
    { transitivity (sum_f_R0 (fun _ => 0) k'); [| apply sum_f_R0_zero].
      apply sum_f_R0_ext. intros j Hj.
      destruct (S k' - j)%nat eqn:Ed; [lia | ring]. }
    rewrite Hz. ring.
  Qed.

  Lemma p_mul_assoc : forall p q r k,
    p_mul (p_mul p q) r k = p_mul p (p_mul q r) k.
  Proof.
    intros p q r k. unfold p_mul.
    (* Double-sum identity: sum_{m=0}^k (sum_{i=0}^m p i * q (m-i)) * r (k-m)
       = sum_{i=0}^k p i * (sum_{j=0}^{k-i} q j * r (k-i-j)) *)
    assert (Hgen : forall n (F : nat -> nat -> R),
      sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) n =
      sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (n - i)%nat) n).
    { induction n as [| n' IH]; intro F; [simpl; reflexivity |].
      change (sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) (S n'))
        with (sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) n' +
              sum_f_R0 (fun i => F i (S n' - i)%nat) (S n')).
      rewrite (IH F).
      change (sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) (S n'))
        with (sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) n' +
              sum_f_R0 (fun j => F (S n') j) (S n' - S n')%nat).
      rewrite Nat.sub_diag.
      assert (Hsplit :
        sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) n' =
        sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (n' - i)%nat) n' +
        sum_f_R0 (fun i => F i (S n' - i)%nat) n').
      { rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros i Hi.
        replace (S n' - i)%nat with (S (n' - i)) by lia.
        simpl. reflexivity. }
      rewrite Hsplit.
      change (sum_f_R0 (fun i => F i (S n' - i)%nat) (S n'))
        with (sum_f_R0 (fun i => F i (S n' - i)%nat) n' + F (S n') (S n' - S n')%nat).
      rewrite Nat.sub_diag.
      change (sum_f_R0 (fun j => F (S n') j) 0%nat) with (F (S n') 0%nat). ring. }
    transitivity (sum_f_R0 (fun m => sum_f_R0 (fun i => p i * q (m - i)%nat * r (k - m)%nat) m) k).
    - apply sum_f_R0_ext. intros m _.
      rewrite Rmult_comm, <- sum_f_R0_scale.
      apply sum_f_R0_ext. intros i _. ring.
    - transitivity (sum_f_R0 (fun m => sum_f_R0 (fun i => (fun a b => p a * q b * r (k - (a + b))%nat) i (m - i)%nat) m) k).
      + apply sum_f_R0_ext. intros m Hm. apply sum_f_R0_ext. intros i Hi.
        replace (i + (m - i))%nat with m by lia. reflexivity.
      + rewrite (Hgen k (fun a b => p a * q b * r (k - (a + b))%nat)). apply sum_f_R0_ext. intros i Hi.
        rewrite <- sum_f_R0_scale. apply sum_f_R0_ext. intros j Hj.
        replace (k - (i + j))%nat with (k - i - j)%nat by lia. ring.
  Qed.

  (* Product rule for formal derivative *)
  Lemma p_deriv_mul : forall p q k,
    p_deriv (p_mul p q) k = p_add (p_mul (p_deriv p) q) (p_mul p (p_deriv q)) k.
  Proof.
    intros p q k. unfold p_deriv, p_mul, p_add.
    rewrite <- sum_f_R0_scale.
    assert (Hsplit :
      sum_f_R0 (fun j => INR (S k) * (p j * q (S k - j)%nat)) (S k) =
      sum_f_R0 (fun j => INR j * p j * q (S k - j)%nat) (S k) +
      sum_f_R0 (fun j => p j * (INR (S k - j) * q (S k - j)%nat)) (S k)).
    { rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros j Hj.
      assert (Hadd : INR (S k) = INR j + INR (S k - j)).
      { rewrite <- plus_INR. f_equal. lia. }
      rewrite Hadd. ring. }
    rewrite Hsplit. f_equal.
    - rewrite sum_f_R0_shift. simpl INR at 1. rewrite Rmult_0_l, Rmult_0_l, Rplus_0_l.
      apply sum_f_R0_ext. intros j Hj.
      replace (S k - S j)%nat with (k - j)%nat by lia. ring.
    - change (sum_f_R0 (fun j => p j * (INR (S k - j) * q (S k - j)%nat)) (S k))
        with (sum_f_R0 (fun j => p j * (INR (S k - j) * q (S k - j)%nat)) k +
              p (S k) * (INR (S k - S k) * q (S k - S k)%nat)).
      rewrite Nat.sub_diag. change (INR 0%nat) with 0.
      rewrite Rmult_0_l, Rmult_0_r, Rplus_0_r.
      apply sum_f_R0_ext. intros j Hj.
      replace (S k - j)%nat with (S (k - j)) by lia. ring.
  Qed.

  (* Power rule: (p^m)' = m * p' * p^{m-1} *)
  Lemma p_deriv_pow : forall p m k,
    p_deriv (p_pow p (S m)) k = p_scale (INR (S m)) (p_mul (p_deriv p) (p_pow p m)) k.
  Proof.
    intros p m. induction m as [| m' IH]; intro k.
    - simpl p_pow.
      unfold p_scale. rewrite Rmult_1_l.
      assert (Heq : p_deriv (p_mul p p_one) k = p_deriv p k).
      { unfold p_deriv. rewrite p_mul_one_r. reflexivity. }
      rewrite Heq, p_mul_one_r. reflexivity.
    - change (p_pow p (S (S m'))) with (p_mul p (p_pow p (S m'))).
      rewrite p_deriv_mul. unfold p_add.
      assert (H2 : p_mul p (p_deriv (p_pow p (S m'))) k =
                   p_scale (INR (S m')) (p_mul (p_deriv p) (p_pow p (S m'))) k).
      { rewrite (p_mul_ext p p _ _ (fun _ => eq_refl) IH k).
        rewrite p_mul_scale_r. unfold p_scale. f_equal.
        rewrite <- p_mul_assoc.
        rewrite (p_mul_ext (p_mul p (p_deriv p)) (p_mul (p_deriv p) p) _ _
                   (p_mul_comm p (p_deriv p)) (fun _ => eq_refl) k).
        rewrite p_mul_assoc. reflexivity. }
      rewrite H2. unfold p_scale. rewrite (S_INR (S m')). ring.
  Qed.

  (* Low-degree vanishing: if p 0 = 0 then (p^m) j = 0 for all j < m *)
  Lemma p_pow_vanish : forall p m j,
    p 0%nat = 0 -> (j < m)%nat -> p_pow p m j = 0.
  Proof.
    intros p m. induction m as [| m' IH]; intros j Hp0 Hlt; [lia |].
    simpl p_pow. unfold p_mul.
    transitivity (sum_f_R0 (fun _ => 0) j); [| apply sum_f_R0_zero].
    apply sum_f_R0_ext. intros i Hi.
    destruct i as [| i'].
    - rewrite Hp0. ring.
    - rewrite (IH (j - S i')%nat Hp0 ltac:(lia)). ring.
  Qed.

  (* Truncated exponential series E_N = sum_{m=0}^N (1/m!) * p^m *)
  Definition p_exp_trunc (p : nat -> R) (N : nat) : nat -> R :=
    fun k => sum_f_R0 (fun m => / INR (fact m) * p_pow p m k) N.

  Lemma p_exp_trunc_0 : forall p N,
    p 0%nat = 0 -> p_exp_trunc p N 0%nat = 1.
  Proof.
    intros p N Hp0. unfold p_exp_trunc.
    destruct N as [| N'].
    - simpl. field.
    - rewrite sum_f_R0_shift.
      assert (Hz : sum_f_R0 (fun i => / INR (fact (S i)) * p_pow p (S i) 0%nat) N' = 0).
      { transitivity (sum_f_R0 (fun _ => 0) N'); [| apply sum_f_R0_zero].
        apply sum_f_R0_ext. intros i _. rewrite (p_pow_vanish p (S i) 0%nat Hp0 ltac:(lia)). ring. }
      rewrite Hz. simpl. field.
  Qed.

  Lemma p_exp_trunc_deriv : forall p N k,
    p_deriv (p_exp_trunc p (S N)) k = p_mul (p_deriv p) (p_exp_trunc p N) k.
  Proof.
    intros p N k. unfold p_deriv, p_exp_trunc, p_mul.
    rewrite <- sum_f_R0_scale.
    rewrite sum_f_R0_shift.
    change (p_pow p 0%nat (S k)) with 0.
    rewrite Rmult_0_r, Rmult_0_r, Rplus_0_l.
    assert (Hterm :
      sum_f_R0 (fun i => INR (S k) * (/ INR (fact (S i)) * p_pow p (S i) (S k))) N =
      sum_f_R0 (fun i => / INR (fact i) *
        sum_f_R0 (fun j => INR (S j) * p (S j) * p_pow p i (k - j)%nat) k) N).
    { apply sum_f_R0_ext. intros i _.
      assert (Hpow := p_deriv_pow p i k). unfold p_deriv, p_scale, p_mul in Hpow.
      replace (INR (S k) * (/ INR (fact (S i)) * p_pow p (S i) (S k)))
         with (/ INR (fact (S i)) * (INR (S k) * p_pow p (S i) (S k))) by ring.
      rewrite Hpow.
      assert (Hfact : INR (fact (S i)) = INR (S i) * INR (fact i)).
      { change (fact (S i)) with (S i * fact i)%nat. rewrite mult_INR. reflexivity. }
      rewrite Hfact.
      assert (Hne1 : INR (S i) <> 0) by (apply not_0_INR; lia).
      assert (Hne2 : INR (fact i) <> 0) by (apply not_0_INR; apply fact_neq_0).
      field. split; assumption. }
    rewrite Hterm.
    (* Swap finite sums over i = 0..N and j = 0..k *)
    assert (Hswap : forall A B (F : nat -> nat -> R),
      sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) B) A =
      sum_f_R0 (fun j => sum_f_R0 (fun i => F i j) A) B).
    { induction A as [| A' IHA]; intros B F; [simpl; reflexivity |].
      simpl sum_f_R0 at 1. rewrite (IHA B F).
      rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros j _. simpl. reflexivity. }
    transitivity (sum_f_R0 (fun i => sum_f_R0 (fun j =>
      / INR (fact i) * (INR (S j) * p (S j) * p_pow p i (k - j)%nat)) k) N).
    - apply sum_f_R0_ext. intros i _. rewrite sum_f_R0_scale. reflexivity.
    - rewrite Hswap. apply sum_f_R0_ext. intros j _.
      rewrite <- sum_f_R0_scale. apply sum_f_R0_ext. intros i _. ring.
  Qed.

  Lemma p_exp_trunc_recurrence : forall p N k,
    p 0%nat = 0 -> (1 <= k <= N)%nat ->
    INR k * p_exp_trunc p N k =
    sum_f_R0 (fun j => INR (S j) * p (S j) * p_exp_trunc p N (k - S j)%nat) (k - 1)%nat.
  Proof.
    intros p N k Hp0 Hk.
    destruct N as [| N']; [lia |].
    destruct k as [| k']; [lia |].
    replace (S k' - 1)%nat with k' by lia.
    change (INR (S k') * p_exp_trunc p (S N') (S k')) with (p_deriv (p_exp_trunc p (S N')) k').
    rewrite p_exp_trunc_deriv.
    unfold p_mul, p_deriv.
    apply sum_f_R0_ext. intros j Hj.
    replace (S k' - S j)%nat with (k' - j)%nat by lia.
    f_equal.
    (* p_exp_trunc p N' (k' - j) = p_exp_trunc p (S N') (k' - j) since k' - j < S N' *)
    unfold p_exp_trunc. cbn [sum_f_R0].
    rewrite (p_pow_vanish p (S N') (k' - j)%nat Hp0 ltac:(lia)). ring.
  Qed.

  (* =======================================================================
     3. Evaluation of Truncated Polynomials at z = 1 & Non-negativity
     ======================================================================= *)

  Lemma p_pow_nonneg : forall p m k,
    (forall i, 0 <= p i) -> 0 <= p_pow p m k.
  Proof.
    intros p m. induction m as [| m' IH]; intros k Hnn.
    - simpl. unfold p_one. destruct k; lra.
    - simpl. unfold p_mul. apply sum_f_R0_nonneg. intros j _.
      apply Rmult_le_pos; [apply Hnn | apply IH; exact Hnn].
  Qed.

  Lemma p_pow_support : forall p D m k,
    (forall i, (D < i)%nat -> p i = 0) ->
    (m * D < k)%nat ->
    p_pow p m k = 0.
  Proof.
    intros p D m. induction m as [| m' IH]; intros k Hsupp Hgt.
    - simpl. unfold p_one. destruct k; [lia | reflexivity].
    - simpl p_pow. unfold p_mul.
      transitivity (sum_f_R0 (fun _ => 0) k); [| apply sum_f_R0_zero].
      apply sum_f_R0_ext. intros j Hj.
      destruct (le_lt_dec j D) as [Hle | Hgtj].
      + rewrite (IH (k - j)%nat Hsupp ltac:(simpl in Hgt; lia)). ring.
      + rewrite (Hsupp j Hgtj). ring.
  Qed.

  Lemma p_mul_eval1 : forall p q Dp Dq,
    (forall i, (Dp < i)%nat -> p i = 0) ->
    (forall i, (Dq < i)%nat -> q i = 0) ->
    sum_f_R0 (p_mul p q) (Dp + Dq)%nat = sum_f_R0 p Dp * sum_f_R0 q Dq.
  Proof.
    intros p q Dp Dq Hp Hq.
    (* Same double-sum reindexing: sum_{m=0}^{Dp+Dq} sum_{i=0}^m p i * q (m-i)
       = sum_{i=0}^{Dp+Dq} p i * sum_{j=0}^{Dp+Dq-i} q j *)
    assert (Hgen : forall n (F : nat -> nat -> R),
      sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) n =
      sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (n - i)%nat) n).
    { induction n as [| n' IH]; intro F; [simpl; reflexivity |].
      change (sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) (S n'))
        with (sum_f_R0 (fun m => sum_f_R0 (fun i => F i (m - i)%nat) m) n' +
              sum_f_R0 (fun i => F i (S n' - i)%nat) (S n')).
      rewrite (IH F).
      change (sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) (S n'))
        with (sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) n' +
              sum_f_R0 (fun j => F (S n') j) (S n' - S n')%nat).
      rewrite Nat.sub_diag.
      assert (Hsplit :
        sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (S n' - i)%nat) n' =
        sum_f_R0 (fun i => sum_f_R0 (fun j => F i j) (n' - i)%nat) n' +
        sum_f_R0 (fun i => F i (S n' - i)%nat) n').
      { rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros i Hi.
        replace (S n' - i)%nat with (S (n' - i)) by lia.
        simpl. reflexivity. }
      rewrite Hsplit.
      change (sum_f_R0 (fun i => F i (S n' - i)%nat) (S n'))
        with (sum_f_R0 (fun i => F i (S n' - i)%nat) n' + F (S n') (S n' - S n')%nat).
      rewrite Nat.sub_diag.
      change (sum_f_R0 (fun j => F (S n') j) 0%nat) with (F (S n') 0%nat). ring. }
    assert (Htail : forall (f : nat -> R) A B,
      (A <= B)%nat -> (forall i, (A < i)%nat -> f i = 0) ->
      sum_f_R0 f B = sum_f_R0 f A).
    { intros f A B Hle Hf. induction Hle as [| B' Hle' IH]; [reflexivity |].
      simpl. rewrite IH, Hf; [ring | lia]. }
    unfold p_mul.
    rewrite (Hgen (Dp + Dq)%nat (fun i j => p i * q j)).
    rewrite (Htail (fun i => sum_f_R0 (fun j => p i * q j) (Dp + Dq - i)%nat) Dp (Dp + Dq)%nat ltac:(lia)).
    - transitivity (sum_f_R0 (fun i => p i * sum_f_R0 q Dq) Dp).
      + apply sum_f_R0_ext. intros i Hi.
        rewrite sum_f_R0_scale. f_equal.
        apply (Htail q Dq (Dp + Dq - i)%nat ltac:(lia) Hq).
      + rewrite Rmult_comm, <- sum_f_R0_scale.
        apply sum_f_R0_ext. intros i _. ring.
    - intros i Hi.
      transitivity (sum_f_R0 (fun _ => 0) (Dp + Dq - i)%nat); [| apply sum_f_R0_zero].
      apply sum_f_R0_ext. intros j _. rewrite (Hp i Hi). ring.
  Qed.

  Lemma p_pow_eval1 : forall p D m,
    (forall i, (D < i)%nat -> p i = 0) ->
    sum_f_R0 (p_pow p m) (m * D)%nat = (sum_f_R0 p D) ^ m.
  Proof.
    intros p D m Hp. induction m as [| m' IH].
    - simpl. unfold p_one. reflexivity.
    - change (S m' * D)%nat with (D + m' * D)%nat.
      simpl p_pow. simpl pow.
      rewrite (p_mul_eval1 p (p_pow p m') D (m' * D)%nat Hp (fun k Hk => p_pow_support p D m' k Hp Hk)).
      rewrite IH. reflexivity.
  Qed.

  (* =======================================================================
     4. Main Finite Recurrence -> Exponential Upper Bound Theorem
     ======================================================================= *)

  Theorem exp_recurrence_sum_bound : forall (t u : nat -> R) (N : nat),
    t 0%nat = 1 ->
    (forall s, (1 <= s <= N)%nat -> 0 <= u s) ->
    (forall k, (1 <= k <= N)%nat ->
      INR k * t k = sum_f_R0 (fun j => INR (S j) * u (S j) * t (k - S j)%nat) (k - 1)%nat) ->
    sum_f_R0 t N <=
      exp (match N with 0%nat => 0 | S N' => sum_f_R0 (fun j => u (S j)) N' end).
  Proof.
    intros t u N Ht0 Hu_nn Hrec.
    destruct N as [| N'].
    - simpl. rewrite Ht0, exp_0. lra.
    - (* Define truncated polynomial P with P 0 = 0, P s = u s for 1 <= s <= S N', 0 for s > S N' *)
      set (P := fun k : nat =>
        if Nat.eqb k 0 then 0
        else if Nat.leb k (S N') then u k else 0).
      assert (HP0 : P 0%nat = 0) by reflexivity.
      assert (HP_nn : forall k, 0 <= P k).
      { intro k. unfold P. destruct k as [| k']; [simpl; lra |].
        simpl Nat.eqb. destruct (Nat.leb_spec (S k') (S N')); [apply Hu_nn; lia | lra]. }
      assert (HP_supp : forall i, (S N' < i)%nat -> P i = 0).
      { intros i Hi. unfold P. destruct i; [lia |].
        simpl Nat.eqb. destruct (Nat.leb_spec (S i) (S N')); [lia | reflexivity]. }
      assert (HP_eq : forall s, (1 <= s <= S N')%nat -> P s = u s).
      { intros s Hs. unfold P. destruct s; [lia |].
        simpl Nat.eqb. destruct (Nat.leb_spec (S s) (S N')); [reflexivity | lia]. }
      (* Prove by strong induction that t k = p_exp_trunc P (S N') k for all k <= S N' *)
      assert (Ht_eq : forall k, (k <= S N')%nat -> t k = p_exp_trunc P (S N') k).
      { intro k. induction k as [k IH] using lt_wf_ind. intro Hk.
        destruct k as [| k'].
        - rewrite Ht0, (p_exp_trunc_0 P (S N') HP0). reflexivity.
        - assert (Hne : INR (S k') <> 0) by (apply not_0_INR; lia).
          assert (Hmul : INR (S k') * t (S k') = INR (S k') * p_exp_trunc P (S N') (S k')).
          { rewrite (Hrec (S k') ltac:(lia)).
            rewrite (p_exp_trunc_recurrence P (S N') (S k') HP0 ltac:(lia)).
            apply sum_f_R0_ext. intros j Hj.
            rewrite (HP_eq (S j) ltac:(lia)).
            rewrite (IH (S k' - S j)%nat ltac:(lia) ltac:(lia)).
            reflexivity. }
          apply Rmult_eq_reg_l with (r := INR (S k')); assumption. }
      (* Sum t k for k = 0 .. S N' <= sum_{k=0}^{(S N')*(S N')} p_exp_trunc P (S N') k *)
      rewrite (sum_f_R0_ext t (p_exp_trunc P (S N')) (S N') Ht_eq).
      set (M := (S N' * S N')%nat).
      assert (Hexp_nn : forall k, 0 <= p_exp_trunc P (S N') k).
      { intro k. unfold p_exp_trunc. apply sum_f_R0_nonneg. intros m _.
        apply Rmult_le_pos.
        - left. apply Rinv_0_lt_compat. apply lt_0_INR. pose proof (fact_neq_0 m). lia.
        - apply p_pow_nonneg. exact HP_nn. }
      eapply Rle_trans.
      { apply (sum_f_R0_mono (p_exp_trunc P (S N')) (S N') M Hexp_nn).
        unfold M. nia. }
      (* Swap finite sums over k = 0..M and m = 0..S N' *)
      assert (Hswap : forall A B (F : nat -> nat -> R),
        sum_f_R0 (fun k => sum_f_R0 (fun m => F k m) B) A =
        sum_f_R0 (fun m => sum_f_R0 (fun k => F k m) A) B).
      { induction A as [| A' IHA]; intros B F; [simpl; reflexivity |].
        simpl sum_f_R0 at 1. rewrite (IHA B F).
        rewrite <- sum_f_R0_plus. apply sum_f_R0_ext. intros m _. simpl. reflexivity. }
      unfold p_exp_trunc. rewrite Hswap.
      assert (Htail : forall (f : nat -> R) A B,
        (A <= B)%nat -> (forall i, (A < i)%nat -> f i = 0) ->
        sum_f_R0 f B = sum_f_R0 f A).
      { intros f A B Hle Hf. induction Hle as [| B' Hle' IH]; [reflexivity |].
        simpl. rewrite IH, Hf; [ring | lia]. }
      assert (Hsum_eq :
        sum_f_R0 (fun m => sum_f_R0 (fun k => / INR (fact m) * p_pow P m k) M) (S N') =
        sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 P (S N')) ^ m) (S N')).
      { apply sum_f_R0_ext. intros m Hm.
        rewrite sum_f_R0_scale. f_equal.
        rewrite (Htail (p_pow P m) (m * S N')%nat M ltac:(unfold M; nia) (fun k Hk => p_pow_support P (S N') m k HP_supp Hk)).
        exact (p_pow_eval1 P (S N') m HP_supp). }
      rewrite Hsum_eq.
      assert (HP_sum : sum_f_R0 P (S N') = sum_f_R0 (fun j => u (S j)) N').
      { rewrite sum_f_R0_shift, HP0, Rplus_0_l.
        apply sum_f_R0_ext. intros j Hj. apply HP_eq; lia. }
      rewrite HP_sum.
      apply exp_partial_sum_le.
      apply sum_f_R0_nonneg. intros j Hj. apply Hu_nn; lia.
  Qed.

End PolyExpBound.
