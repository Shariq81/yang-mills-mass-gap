(* =========================================================================
   rg/hilbert_completion.v

   Completion of a real vector space with a positive semidefinite symmetric
   bilinear form, and extension of symmetric contractions to the completion.

   No quotient is taken: the completion is the type of Cauchy sequences, and
   two of its elements are identified when their difference has norm zero.
   The space V is not even assumed to satisfy the vector-space axioms: only
   the form is assumed to be bilinear with respect to the two operations.

   Contents:
     1. limits of real sequences (helpers);
     2. form spaces: Cauchy-Schwarz and the quadratic inequalities;
     3. symmetric operators on a form space, spectral consequences of a gap;
     4. the completion: the type of Cauchy sequences, its form, completeness,
        density of the original space;
     5. extension of a symmetric contraction.

   ZERO `Axiom`, `Parameter`, `Admitted`.  The completeness proof uses
   `ClassicalEpsilon.constructive_indefinite_description` (countable choice
   of approximating vectors).
   ========================================================================= *)

From Coq Require Import Reals Lra Lia Psatz ClassicalEpsilon.

Open Scope R_scope.

Module HilbertCompletion.

  (* =======================================================================
     1. Limits of real sequences
     ======================================================================= *)

  Lemma cv_ext : forall (a b : nat -> R) (l : R),
    (forall n, a n = b n) -> Un_cv a l -> Un_cv b l.
  Proof.
    intros a b l E H eps He. destruct (H eps He) as [N HN]. exists N.
    intros n Hn. rewrite <- (E n). exact (HN n Hn).
  Qed.

  Lemma cv_const : forall c : R, Un_cv (fun _ => c) c.
  Proof.
    intros c eps He. exists 0%nat. intros n _. unfold R_dist.
    replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Lemma cv_le_from : forall (a : nat -> R) (l c : R) (N : nat),
    Un_cv a l -> (forall n, (N <= n)%nat -> a n <= c) -> l <= c.
  Proof.
    intros a l c N H Hle. destruct (Rle_or_lt l c) as [Hl | Hl]; [exact Hl | exfalso].
    assert (He : l - c > 0) by lra.
    destruct (H (l - c) He) as [N1 HN1].
    pose proof (HN1 (Nat.max N N1) (Nat.le_max_r N N1)) as H1.
    pose proof (Hle (Nat.max N N1) (Nat.le_max_l N N1)) as H2.
    unfold R_dist in H1. apply Rabs_def2 in H1. lra.
  Qed.

  Lemma cv_ge_from : forall (a : nat -> R) (l c : R) (N : nat),
    Un_cv a l -> (forall n, (N <= n)%nat -> c <= a n) -> c <= l.
  Proof.
    intros a l c N H Hle. destruct (Rle_or_lt c l) as [Hl | Hl]; [exact Hl | exfalso].
    assert (He : c - l > 0) by lra.
    destruct (H (c - l) He) as [N1 HN1].
    pose proof (HN1 (Nat.max N N1) (Nat.le_max_r N N1)) as H1.
    pose proof (Hle (Nat.max N N1) (Nat.le_max_l N N1)) as H2.
    unfold R_dist in H1. apply Rabs_def2 in H1. lra.
  Qed.

  Lemma cv_le : forall (a b : nat -> R) (la lb : R),
    Un_cv a la -> Un_cv b lb -> (forall n, a n <= b n) -> la <= lb.
  Proof.
    intros a b la lb Ha Hb Hle.
    pose proof (CV_minus b a lb la Hb Ha) as Hd.
    assert (H0 : 0 <= lb - la).
    { apply (cv_ge_from (fun n => b n - a n) (lb - la) 0 0%nat Hd).
      intros n _. pose proof (Hle n). lra. }
    lra.
  Qed.

  Lemma cv_scal : forall (a : nat -> R) (l c : R),
    Un_cv a l -> Un_cv (fun n => c * a n) (c * l).
  Proof. intros a l c H. exact (CV_mult (fun _ => c) a c l (cv_const c) H). Qed.

  Lemma inv_small : forall eps : R, 0 < eps ->
    exists N : nat, forall k, (N <= k)%nat -> / INR (S k) < eps.
  Proof.
    intros eps He. destruct (archimed_cor1 eps He) as [N [HN HN0]].
    exists N. intros k Hk. apply Rle_lt_trans with (/ INR N); [| exact HN].
    apply Rinv_le_contravar; [apply lt_0_INR; exact HN0 | apply le_INR; lia].
  Qed.

  Lemma sq_abs_le : forall a c : R, 0 <= c -> a * a <= c * c -> Rabs a <= c.
  Proof.
    intros a c Hc H. apply Rle_trans with (Rabs c).
    - apply Rsqr_le_abs_0. unfold Rsqr. exact H.
    - rewrite (Rabs_pos_eq c Hc). apply Rle_refl.
  Qed.

  (* =======================================================================
     2. Form spaces
     ======================================================================= *)

  Definition sub {E : Type} (add : E -> E -> E) (scal : R -> E -> E) (x y : E) : E :=
    add x (scal (-1) y).

  Definition form_axioms {E : Type} (add : E -> E -> E) (scal : R -> E -> E)
      (B : E -> E -> R) : Prop :=
    (forall x y, B x y = B y x) /\
    (forall x y z, B (add x y) z = B x z + B y z) /\
    (forall c x z, B (scal c x) z = c * B x z) /\
    (forall x, 0 <= B x x).

  Section Form.
    Context {E : Type} {add : E -> E -> E} {scal : R -> E -> E} {B : E -> E -> R}.
    Hypothesis HF : form_axioms add scal B.

    Local Notation "x -- y" := (sub add scal x y) (at level 40, left associativity).

    Lemma B_sym : forall x y, B x y = B y x.
    Proof. exact (proj1 HF). Qed.

    Lemma B_add : forall x y z, B (add x y) z = B x z + B y z.
    Proof. exact (proj1 (proj2 HF)). Qed.

    Lemma B_scal : forall c x z, B (scal c x) z = c * B x z.
    Proof. exact (proj1 (proj2 (proj2 HF))). Qed.

    Lemma B_pos : forall x, 0 <= B x x.
    Proof. exact (proj2 (proj2 (proj2 HF))). Qed.

    Lemma B_add_r : forall x y z, B z (add x y) = B z x + B z y.
    Proof.
      intros x y z. rewrite (B_sym z (add x y)), B_add, (B_sym x z), (B_sym y z).
      reflexivity.
    Qed.

    Lemma B_scal_r : forall c x z, B z (scal c x) = c * B z x.
    Proof. intros c x z. rewrite (B_sym z (scal c x)), B_scal, (B_sym x z). reflexivity. Qed.

    Lemma B_sub : forall x y z, B (x -- y) z = B x z - B y z.
    Proof. intros x y z. unfold sub. rewrite B_add, B_scal. ring. Qed.

    Lemma B_sub_r : forall x y z, B z (x -- y) = B z x - B z y.
    Proof. intros x y z. unfold sub. rewrite B_add_r, B_scal_r. ring. Qed.

    Lemma Q_sub : forall x y, B (x -- y) (x -- y) = B x x - 2 * B x y + B y y.
    Proof.
      intros x y. rewrite (B_sub x y (x -- y)), (B_sub_r x y x), (B_sub_r x y y),
                    (B_sym y x). ring.
    Qed.

    Lemma Q_self : forall x, B (x -- x) (x -- x) = 0.
    Proof. intro x. rewrite Q_sub. ring. Qed.

    Lemma Q_sub_sym : forall x y, B (x -- y) (x -- y) = B (y -- x) (y -- x).
    Proof. intros x y. rewrite (Q_sub x y), (Q_sub y x), (B_sym y x). ring. Qed.

    Lemma Q_scal : forall c x, B (scal c x) (scal c x) = c * c * B x x.
    Proof. intros c x. rewrite B_scal, B_scal_r. ring. Qed.

    Lemma Q_add : forall x y, B (add x y) (add x y) = B x x + 2 * B x y + B y y.
    Proof.
      intros x y. rewrite (B_add x y (add x y)), (B_add_r x y x), (B_add_r x y y),
                    (B_sym y x). ring.
    Qed.

    (* Cauchy-Schwarz *)
    Lemma cs : forall x y, B x y * B x y <= B x x * B y y.
    Proof.
      intros x y.
      assert (Hq : forall t : R, 0 <= B x x + 2 * t * B x y + t * t * B y y).
      { intro t. pose proof (B_pos (add x (scal t y))) as H.
        rewrite (Q_add x (scal t y)), (B_scal_r t y x), (Q_scal t y) in H. lra. }
      destruct (Req_dec (B y y) 0) as [Hy | Hy].
      - (* B y y = 0: then B x y = 0 *)
        rewrite Hy, Rmult_0_r.
        destruct (Req_dec (B x y) 0) as [Hxy | Hxy]; [rewrite Hxy; lra | exfalso].
        pose proof (Hq (- (B x x + 1) / (2 * B x y))) as H.
        rewrite Hy in H.
        assert (E1 : 2 * (- (B x x + 1) / (2 * B x y)) * B x y = - (B x x + 1))
          by (field; exact Hxy).
        rewrite E1 in H. lra.
      - pose proof (B_pos y) as Hy0.
        assert (Hy1 : 0 < B y y) by lra.
        pose proof (Hq (- B x y / B y y)) as H.
        assert (E1 : B x x + 2 * (- B x y / B y y) * B x y
                     + (- B x y / B y y) * (- B x y / B y y) * B y y
                     = (B x x * B y y - B x y * B x y) / B y y)
          by (field; exact Hy).
        rewrite E1 in H.
        assert (H2 : 0 <= (B x x * B y y - B x y * B x y) / B y y * B y y)
          by (apply Rmult_le_pos; lra).
        assert (E2 : (B x x * B y y - B x y * B x y) / B y y * B y y
                     = B x x * B y y - B x y * B x y) by (field; exact Hy).
        rewrite E2 in H2. lra.
    Qed.

    Lemma abs_bound : forall x y d M, 0 <= d -> 0 <= M ->
      B x x <= d * d -> B y y <= M * M -> Rabs (B x y) <= d * M.
    Proof.
      intros x y d M Hd HM Hx Hy.
      apply sq_abs_le; [apply Rmult_le_pos; assumption |].
      apply Rle_trans with (B x x * B y y); [apply cs |].
      replace (d * M * (d * M)) with ((d * d) * (M * M)) by ring.
      apply Rmult_le_compat; [apply B_pos | apply B_pos | exact Hx | exact Hy].
    Qed.

    Lemma Q_add2 : forall x y, B (add x y) (add x y) <= 2 * B x x + 2 * B y y.
    Proof.
      intros x y. pose proof (B_pos (x -- y)) as H. rewrite Q_sub in H.
      rewrite Q_add. lra.
    Qed.

    Lemma Q_bound : forall x y, B x x <= 2 * B (x -- y) (x -- y) + 2 * B y y.
    Proof.
      intros x y. pose proof (B_pos (x -- scal 2 y)) as H.
      rewrite (Q_sub x (scal 2 y)), (B_scal_r 2 y x), (Q_scal 2 y) in H.
      rewrite Q_sub. lra.
    Qed.

    Lemma Q_tri2 : forall x y z,
      B (x -- z) (x -- z) <= 2 * B (x -- y) (x -- y) + 2 * B (y -- z) (y -- z).
    Proof.
      intros x y z.
      pose proof (B_pos ((x -- y) -- (y -- z))) as H.
      rewrite (Q_sub (x -- y) (y -- z)) in H.
      rewrite (B_sub x y (y -- z)), (B_sub_r y z x), (B_sub_r y z y) in H.
      rewrite (Q_sub x y), (Q_sub y z) in H.
      rewrite (Q_sub x z), (Q_sub x y), (Q_sub y z). lra.
    Qed.

    Lemma Q_tri3 : forall a b c d,
      B (a -- d) (a -- d)
      <= 4 * (B (a -- b) (a -- b) + B (b -- c) (b -- c) + B (c -- d) (c -- d)).
    Proof.
      intros a b c d.
      pose proof (Q_tri2 a b d) as H1. pose proof (Q_tri2 b c d) as H2.
      pose proof (B_pos (a -- b)) as H3. lra.
    Qed.

    Lemma Q_addsub : forall a b c d,
      B (add a b -- add c d) (add a b -- add c d)
      <= 2 * B (a -- c) (a -- c) + 2 * B (b -- d) (b -- d).
    Proof.
      intros a b c d.
      pose proof (B_pos ((a -- c) -- (b -- d))) as H.
      rewrite (Q_sub (a -- c) (b -- d)) in H.
      rewrite (B_sub a c (b -- d)), (B_sub_r b d a), (B_sub_r b d c) in H.
      rewrite (Q_sub a c), (Q_sub b d) in H.
      rewrite (Q_sub (add a b) (add c d)), (Q_add a b), (Q_add c d).
      rewrite (B_add a b (add c d)), (B_add_r c d a), (B_add_r c d b).
      rewrite (Q_sub a c), (Q_sub b d).
      pose proof (B_sym c b) as S1. lra.
    Qed.

    Lemma Q_scalsub : forall c a b,
      B (scal c a -- scal c b) (scal c a -- scal c b) = c * c * B (a -- b) (a -- b).
    Proof.
      intros c a b. rewrite (Q_sub (scal c a) (scal c b)), (Q_sub a b).
      rewrite (Q_scal c a), (Q_scal c b), (B_scal c a (scal c b)), (B_scal_r c b a). ring.
    Qed.

    (* weak equality *)
    Lemma null_weak : forall u w, (forall z, B u z = B w z) -> B (u -- w) (u -- w) = 0.
    Proof. intros u w Hz. rewrite (B_sub u w (u -- w)), (Hz (u -- w)). ring. Qed.

    Lemma null_weak_inv : forall u w, B (u -- w) (u -- w) = 0 -> forall z, B u z = B w z.
    Proof.
      intros u w H z. pose proof (cs (u -- w) z) as Hc. rewrite H, Rmult_0_l in Hc.
      rewrite (B_sub u w z) in Hc.
      assert (B u z - B w z = 0) by nra. lra.
    Qed.

    Lemma Q_weak : forall u w, (forall z, B u z = B w z) -> B u u = B w w.
    Proof. intros u w Hz. rewrite (Hz u), (B_sym w u), (Hz w). reflexivity. Qed.

    Lemma null_Q : forall u w, B (u -- w) (u -- w) = 0 -> B u u = B w w.
    Proof. intros u w H. apply Q_weak. exact (null_weak_inv u w H). Qed.

    (* ---------- symmetric operators ---------- *)

    Section Op.
      Variable A : E -> E.
      Hypothesis A_sym : forall x y, B (A x) y = B x (A y).

      Lemma A_sub_weak : forall x y z, B (A x -- A y) z = B (A (x -- y)) z.
      Proof.
        intros x y z. rewrite (B_sub (A x) (A y) z), (A_sym x z), (A_sym y z),
                        (A_sym (x -- y) z), (B_sub x y (A z)). reflexivity.
      Qed.

      Lemma A_Q_sub : forall x y,
        B (A x -- A y) (A x -- A y) = B (A (x -- y)) (A (x -- y)).
      Proof. intros x y. apply Q_weak. intro z. apply A_sub_weak. Qed.

      Lemma A_add_null : forall x y,
        B (A (add x y) -- add (A x) (A y)) (A (add x y) -- add (A x) (A y)) = 0.
      Proof.
        intros x y. apply null_weak. intro z.
        rewrite (B_add (A x) (A y) z), (A_sym (add x y) z), (A_sym x z), (A_sym y z),
          (B_add x y (A z)). reflexivity.
      Qed.

      Lemma A_scal_null : forall c x,
        B (A (scal c x) -- scal c (A x)) (A (scal c x) -- scal c (A x)) = 0.
      Proof.
        intros c x. apply null_weak. intro z.
        rewrite (B_scal c (A x) z), (A_sym (scal c x) z), (A_sym x z),
          (B_scal c x (A z)). reflexivity.
      Qed.

      (* the form (x, A y) *)
      Lemma A_form : (forall x, 0 <= B x (A x)) ->
        form_axioms add scal (fun x y => B x (A y)).
      Proof.
        intro Hpos. split; [| split; [| split]].
        - intros x y. rewrite <- (A_sym x y). apply B_sym.
        - intros x y z. apply B_add.
        - intros c x z. apply B_scal.
        - exact Hpos.
      Qed.
    End Op.
  End Form.

  (* =======================================================================
     3. Vacuum and gap: consequences in a form space
     ======================================================================= *)

  Section Spectral.
    Context {E : Type} {add : E -> E -> E} {scal : R -> E -> E} {B : E -> E -> R}.
    Hypothesis HF : form_axioms add scal B.
    Variable A : E -> E.
    Hypothesis A_sym : forall x y, B (A x) y = B x (A y).
    Hypothesis A_pos : forall x, 0 <= B x (A x).
    Variable Om : E.
    Hypothesis Om_fix : B (sub add scal (A Om) Om) (sub add scal (A Om) Om) = 0.
    Variable c : R.
    Hypothesis Hc0 : 0 <= c.
    Hypothesis Hgap : forall x, B x Om = 0 -> B x (A x) <= c * B x x.

    Local Notation "x -- y" := (sub add scal x y) (at level 40, left associativity).

    Lemma A_orth : forall x, B x Om = 0 -> B (A x) Om = 0.
    Proof.
      intros x Hx. rewrite (A_sym x Om), (B_sym HF x (A Om)).
      rewrite (null_weak_inv HF (A Om) Om Om_fix x), (B_sym HF Om x). exact Hx.
    Qed.

    (* || A x ||^2 <= c^2 || x ||^2 on the orthogonal complement of Om *)
    Lemma norm_gap : forall x, B x Om = 0 -> B (A x) (A x) <= c * c * B x x.
    Proof.
      intros x Hx.
      pose proof (cs (A_form HF A A_sym A_pos) (A x) x) as Hcs. cbv beta in Hcs.
      pose proof (Hgap x Hx) as H1.
      pose proof (Hgap (A x) (A_orth x Hx)) as H2.
      pose proof (A_pos x) as P1. pose proof (A_pos (A x)) as P2.
      pose proof (B_pos HF x) as P3. pose proof (B_pos HF (A x)) as P4.
      set (n := B (A x) (A x)) in *.
      set (q := B x x) in *.
      assert (Hprod : B (A x) (A (A x)) * B x (A x) <= (c * n) * (c * q))
        by (apply Rmult_le_compat; assumption).
      assert (Hn : n * n <= n * (c * c * q)) by lra.
      destruct (Rle_or_lt n (c * c * q)) as [Hle | Hlt]; [exact Hle | exfalso].
      assert (Hcq : 0 <= c * c * q)
        by (apply Rmult_le_pos; [apply Rmult_le_pos; exact Hc0 | exact P3]).
      assert (Hn0 : 0 < n) by lra.
      pose proof (Rmult_lt_compat_l n (c * c * q) n Hn0 Hlt) as Hc'. lra.
    Qed.

    Lemma iter_orth : forall k x, B x Om = 0 -> B (Nat.iter k A x) Om = 0.
    Proof.
      induction k as [| k IH]; intros x Hx; [exact Hx |].
      cbn [Nat.iter]. apply A_orth. apply IH. exact Hx.
    Qed.

    Lemma iter_gap : forall k x, B x Om = 0 ->
      B (Nat.iter k A x) (Nat.iter k A x) <= (c * c) ^ k * B x x.
    Proof.
      induction k as [| k IH]; intros x Hx; [simpl; lra |].
      cbn [Nat.iter].
      apply Rle_trans with (c * c * B (Nat.iter k A x) (Nat.iter k A x)).
      - apply norm_gap. apply iter_orth. exact Hx.
      - change ((c * c) ^ S k) with (c * c * (c * c) ^ k).
        replace (c * c * (c * c) ^ k * B x x) with (c * c * ((c * c) ^ k * B x x)) by ring.
        apply Rmult_le_compat_l.
        + apply Rmult_le_pos; exact Hc0.
        + apply IH. exact Hx.
    Qed.

    (* uniqueness of the invariant vector *)
    Lemma vacuum_unique : c < 1 -> B Om Om = 1 ->
      forall x, B (A x -- x) (A x -- x) = 0 ->
        B (x -- scal (B x Om) Om) (x -- scal (B x Om) Om) = 0.
    Proof.
      intros Hc1 Hn x Hx.
      set (k := B x Om).
      set (y := x -- scal k Om).
      assert (Hy : B y Om = 0).
      { unfold y. rewrite (B_sub HF x (scal k Om) Om), (B_scal HF k Om Om), Hn.
        unfold k. ring. }
      assert (HAy : forall z, B (A y) z = B y z).
      { intro z. rewrite (A_sym y z). unfold y.
        rewrite (B_sub HF x (scal k Om) (A z)), (B_scal HF k Om (A z)).
        rewrite (B_sub HF x (scal k Om) z), (B_scal HF k Om z).
        rewrite <- (A_sym x z), <- (A_sym Om z).
        rewrite (null_weak_inv HF (A x) x Hx z), (null_weak_inv HF (A Om) Om Om_fix z).
        reflexivity. }
      pose proof (Hgap y Hy) as H1.
      rewrite (B_sym HF y (A y)), (HAy y) in H1.
      pose proof (B_pos HF y) as H2.
      assert (H3 : (1 - c) * B y y <= 0) by lra.
      assert (H4 : 0 <= (1 - c) * B y y) by (apply Rmult_le_pos; lra).
      assert (H5 : (1 - c) * B y y = 0) by lra.
      apply Rmult_integral in H5. destruct H5 as [H5 | H5]; [lra | exact H5].
    Qed.
  End Spectral.

  (* =======================================================================
     4. The completion
     ======================================================================= *)

  Section Completion.
    Context {V : Type} {vadd : V -> V -> V} {vscal : R -> V -> V} {BV : V -> V -> R}.
    Hypothesis HV : form_axioms vadd vscal BV.

    Local Notation vsub := (sub vadd vscal).

    Definition cauchy (x : nat -> V) : Prop :=
      forall eps : R, 0 < eps -> exists N : nat, forall p q : nat,
        (N <= p)%nat -> (N <= q)%nat ->
        BV (vsub (x p) (x q)) (vsub (x p) (x q)) < eps.

    (* the completion: Cauchy sequences *)
    Definition Hc : Type := { x : nat -> V | cauchy x }.

    Definition seq (x : Hc) : nat -> V := proj1_sig x.

    Lemma cauchy_bounded : forall x, cauchy x ->
      exists (N : nat) (M : R), 0 <= M /\ forall n, (N <= n)%nat -> BV (x n) (x n) <= M * M.
    Proof.
      intros x Hx. destruct (Hx 1 Rlt_0_1) as [N HN].
      pose proof (B_pos HV (x N)) as HxN.
      exists N, (2 + 2 * BV (x N) (x N)). split; [lra |].
      intros n Hn.
      pose proof (Q_bound HV (x n) (x N)) as H1.
      pose proof (HN n N Hn (Nat.le_refl N)) as H2.
      set (K := 2 + 2 * BV (x N) (x N)).
      assert (HK : 1 <= K) by (unfold K; lra).
      assert (HKK : K <= K * K) by nra.
      unfold K in *. lra.
    Qed.

    Lemma ip_cauchy : forall x y, cauchy x -> cauchy y ->
      Cauchy_crit (fun n => BV (x n) (y n)).
    Proof.
      intros x y Hx Hy eps He.
      destruct (cauchy_bounded x Hx) as [N1 [M1 [HM1 Hb1]]].
      destruct (cauchy_bounded y Hy) as [N2 [M2 [HM2 Hb2]]].
      set (M := M1 + M2 + 1).
      assert (HM : 0 < M) by (unfold M; lra).
      set (d := eps / (4 * M)).
      assert (Hd : 0 < d) by (unfold d; apply Rdiv_lt_0_compat; lra).
      assert (HdM : d * M = eps / 4) by (unfold d; field; lra).
      assert (Hdd : 0 < d * d) by (apply Rmult_lt_0_compat; exact Hd).
      destruct (Hx (d * d) Hdd) as [N3 HN3].
      destruct (Hy (d * d) Hdd) as [N4 HN4].
      exists (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)).
      intros n m Hn Hm. unfold R_dist.
      assert (Hn1 : (N1 <= n)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia. assert (Hn4 : (N4 <= n)%nat) by lia.
      assert (Hm1 : (N1 <= m)%nat) by lia. assert (Hm2 : (N2 <= m)%nat) by lia.
      assert (Hm3 : (N3 <= m)%nat) by lia. assert (Hm4 : (N4 <= m)%nat) by lia.
      assert (E : BV (x n) (y n) - BV (x m) (y m)
                  = BV (vsub (x n) (x m)) (y n) + BV (x m) (vsub (y n) (y m))).
      { rewrite (B_sub HV (x n) (x m) (y n)), (B_sub_r HV (y n) (y m) (x m)). ring. }
      rewrite E.
      assert (HMM1 : M1 * M1 <= M * M) by (unfold M; nra).
      assert (HMM2 : M2 * M2 <= M * M) by (unfold M; nra).
      assert (A1 : Rabs (BV (vsub (x n) (x m)) (y n)) <= d * M).
      { apply (abs_bound HV); [lra | lra | |].
        - apply Rlt_le. exact (HN3 n m Hn3 Hm3).
        - apply Rle_trans with (M2 * M2); [exact (Hb2 n Hn2) | exact HMM2]. }
      assert (A2 : Rabs (BV (x m) (vsub (y n) (y m))) <= M * d).
      { apply (abs_bound HV); [lra | lra | |].
        - apply Rle_trans with (M1 * M1); [exact (Hb1 m Hm1) | exact HMM1].
        - apply Rlt_le. exact (HN4 n m Hn4 Hm4). }
      eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
    Qed.

    Definition ip (x y : Hc) : R :=
      proj1_sig (R_complete (fun n => BV (seq x n) (seq y n))
                   (ip_cauchy (seq x) (seq y) (proj2_sig x) (proj2_sig y))).

    Lemma ip_cv : forall x y : Hc, Un_cv (fun n => BV (seq x n) (seq y n)) (ip x y).
    Proof.
      intros x y.
      exact (proj2_sig (R_complete (fun n => BV (seq x n) (seq y n))
                          (ip_cauchy (seq x) (seq y) (proj2_sig x) (proj2_sig y)))).
    Qed.

    Lemma ip_val : forall (x y : Hc) (l : R),
      Un_cv (fun n => BV (seq x n) (seq y n)) l -> ip x y = l.
    Proof. intros x y l H. exact (UL_sequence _ _ _ (ip_cv x y) H). Qed.

    (* ---------- operations ---------- *)

    Lemma cauchy_add : forall x y, cauchy x -> cauchy y ->
      cauchy (fun n => vadd (x n) (y n)).
    Proof.
      intros x y Hx Hy eps He.
      assert (He4 : 0 < eps / 4) by lra.
      destruct (Hx (eps / 4) He4) as [N1 HN1]. destruct (Hy (eps / 4) He4) as [N2 HN2].
      exists (Nat.max N1 N2). intros p q Hp Hq.
      assert (Hp1 : (N1 <= p)%nat) by lia. assert (Hp2 : (N2 <= p)%nat) by lia.
      assert (Hq1 : (N1 <= q)%nat) by lia. assert (Hq2 : (N2 <= q)%nat) by lia.
      pose proof (Q_addsub HV (x p) (y p) (x q) (y q)) as H.
      pose proof (HN1 p q Hp1 Hq1). pose proof (HN2 p q Hp2 Hq2). lra.
    Qed.

    Lemma cauchy_scal : forall c x, cauchy x -> cauchy (fun n => vscal c (x n)).
    Proof.
      intros c x Hx eps He.
      assert (Hc1 : 0 < c * c + 1) by nra.
      set (e := eps / (c * c + 1)).
      assert (He' : 0 < e) by (unfold e; apply Rdiv_lt_0_compat; assumption).
      assert (Ee : e * (c * c + 1) = eps) by (unfold e; field; lra).
      destruct (Hx e He') as [N HN]. exists N. intros p q Hp Hq.
      rewrite (Q_scalsub HV c (x p) (x q)).
      pose proof (HN p q Hp Hq) as H.
      pose proof (B_pos HV (vsub (x p) (x q))) as H0.
      assert (Hcc : 0 <= c * c) by nra.
      assert (H1 : c * c * BV (vsub (x p) (x q)) (vsub (x p) (x q)) <= c * c * e)
        by (apply Rmult_le_compat_l; lra).
      lra.
    Qed.

    Lemma cauchy_const : forall v : V, cauchy (fun _ => v).
    Proof.
      intros v eps He. exists 0%nat. intros p q _ _. rewrite (Q_self HV v). exact He.
    Qed.

    Definition hadd (x y : Hc) : Hc :=
      exist cauchy (fun n => vadd (seq x n) (seq y n))
        (cauchy_add (seq x) (seq y) (proj2_sig x) (proj2_sig y)).

    Definition hscal (c : R) (x : Hc) : Hc :=
      exist cauchy (fun n => vscal c (seq x n)) (cauchy_scal c (seq x) (proj2_sig x)).

    Definition emb (v : V) : Hc := exist cauchy (fun _ => v) (cauchy_const v).

    Local Notation hsub := (sub hadd hscal).

    Theorem H_form : form_axioms hadd hscal ip.
    Proof.
      split; [| split; [| split]].
      - intros x y. apply ip_val.
        apply (cv_ext (fun n => BV (seq y n) (seq x n))); [| apply ip_cv].
        intro n. apply (B_sym HV).
      - intros x y z. apply ip_val.
        apply (cv_ext (fun n => BV (seq x n) (seq z n) + BV (seq y n) (seq z n))).
        + intro n. symmetry. exact (B_add HV (seq x n) (seq y n) (seq z n)).
        + exact (CV_plus _ _ _ _ (ip_cv x z) (ip_cv y z)).
      - intros c x z. apply ip_val.
        apply (cv_ext (fun n => c * BV (seq x n) (seq z n))).
        + intro n. symmetry. exact (B_scal HV c (seq x n) (seq z n)).
        + exact (cv_scal _ _ c (ip_cv x z)).
      - intro x. apply (cv_ge_from (fun n => BV (seq x n) (seq x n)) (ip x x) 0 0%nat).
        + apply ip_cv.
        + intros n _. apply (B_pos HV).
    Qed.

    Lemma ip_emb : forall u v : V, ip (emb u) (emb v) = BV u v.
    Proof. intros u v. apply ip_val. exact (cv_const (BV u v)). Qed.

    (* || x - y ||^2 is the limit of || x_n - y_n ||^2 *)
    Lemma nrm_cv : forall x y : Hc,
      Un_cv (fun n => BV (vsub (seq x n) (seq y n)) (vsub (seq x n) (seq y n)))
            (ip (hsub x y) (hsub x y)).
    Proof. intros x y. exact (ip_cv (hsub x y) (hsub x y)). Qed.

    Lemma nrm_emb : forall u v : V,
      ip (hsub (emb u) (emb v)) (hsub (emb u) (emb v)) = BV (vsub u v) (vsub u v).
    Proof.
      intros u v.
      exact (UL_sequence _ _ _ (nrm_cv (emb u) (emb v))
               (cv_const (BV (vsub u v) (vsub u v)))).
    Qed.

    (* the original space is dense *)
    Theorem dense : forall (x : Hc) (eps : R), 0 < eps ->
      exists v : V, ip (hsub x (emb v)) (hsub x (emb v)) < eps.
    Proof.
      intros x eps He.
      assert (He2 : 0 < eps / 2) by lra.
      destruct (proj2_sig x (eps / 2) He2) as [N HN].
      exists (seq x N). apply Rle_lt_trans with (eps / 2); [| lra].
      apply (cv_le_from _ _ (eps / 2) N (nrm_cv x (emb (seq x N)))).
      intros n Hn. apply Rlt_le. exact (HN n N Hn (Nat.le_refl N)).
    Qed.

    (* completeness *)
    Theorem complete : forall X : nat -> Hc,
      (forall eps : R, 0 < eps -> exists N : nat, forall p q : nat,
         (N <= p)%nat -> (N <= q)%nat ->
         ip (hsub (X p) (X q)) (hsub (X p) (X q)) < eps) ->
      exists y : Hc, forall eps : R, 0 < eps -> exists N : nat, forall n : nat,
        (N <= n)%nat -> ip (hsub (X n) y) (hsub (X n) y) < eps.
    Proof.
      intros X HX.
      assert (Hch : forall k : nat,
                { v : V | ip (hsub (X k) (emb v)) (hsub (X k) (emb v)) < / INR (S k) }).
      { intro k. apply constructive_indefinite_description. apply dense.
        apply Rinv_0_lt_compat. apply lt_0_INR. lia. }
      set (v := fun k => proj1_sig (Hch k)).
      assert (Hv : forall k,
                ip (hsub (X k) (emb (v k))) (hsub (X k) (emb (v k))) < / INR (S k))
        by (intro k; exact (proj2_sig (Hch k))).
      assert (Hcau : cauchy v).
      { intros eps He.
        assert (He12 : 0 < eps / 12) by lra.
        destruct (inv_small (eps / 12) He12) as [N1 HN1].
        destruct (HX (eps / 12) He12) as [N2 HN2].
        exists (Nat.max N1 N2). intros p q Hp Hq.
        assert (Hp1 : (N1 <= p)%nat) by lia. assert (Hp2 : (N2 <= p)%nat) by lia.
        assert (Hq1 : (N1 <= q)%nat) by lia. assert (Hq2 : (N2 <= q)%nat) by lia.
        rewrite <- (nrm_emb (v p) (v q)).
        pose proof (Q_tri3 H_form (emb (v p)) (X p) (X q) (emb (v q))) as H.
        rewrite (Q_sub_sym H_form (emb (v p)) (X p)) in H.
        pose proof (Hv p) as H1. pose proof (HN1 p Hp1) as H1'.
        pose proof (Hv q) as H2. pose proof (HN1 q Hq1) as H2'.
        pose proof (HN2 p q Hp2 Hq2) as H3. lra. }
      exists (exist cauchy v Hcau).
      intros eps He.
      assert (He8 : 0 < eps / 8) by lra.
      destruct (inv_small (eps / 8) He8) as [N1 HN1].
      destruct (Hcau (eps / 8) He8) as [N2 HN2].
      exists (Nat.max N1 N2). intros n Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
      pose proof (Q_tri2 H_form (X n) (emb (v n)) (exist cauchy v Hcau)) as H.
      pose proof (Hv n) as H1. pose proof (HN1 n Hn1) as H1'.
      assert (H2 : ip (hsub (emb (v n)) (exist cauchy v Hcau))
                      (hsub (emb (v n)) (exist cauchy v Hcau)) <= eps / 8).
      { apply (cv_le_from _ _ (eps / 8) N2 (nrm_cv (emb (v n)) (exist cauchy v Hcau))).
        intros m Hm. apply Rlt_le. exact (HN2 n m Hn2 Hm). }
      lra.
    Qed.

    (* =====================================================================
       5. Extension of a symmetric contraction
       ===================================================================== *)

    Section Ext.
      Variable T0 : V -> V.
      Hypothesis T0_sym : forall u w, BV (T0 u) w = BV u (T0 w).
      Hypothesis T0_contr : forall u, BV (T0 u) (T0 u) <= BV u u.

      Lemma cauchy_T : forall x, cauchy x -> cauchy (fun n => T0 (x n)).
      Proof.
        intros x Hx eps He. destruct (Hx eps He) as [N HN]. exists N. intros p q Hp Hq.
        rewrite (A_Q_sub HV T0 T0_sym (x p) (x q)).
        apply Rle_lt_trans with (BV (vsub (x p) (x q)) (vsub (x p) (x q)));
          [apply T0_contr | exact (HN p q Hp Hq)].
      Qed.

      Definition Text (x : Hc) : Hc :=
        exist cauchy (fun n => T0 (seq x n)) (cauchy_T (seq x) (proj2_sig x)).

      Lemma Text_sym : forall x y, ip (Text x) y = ip x (Text y).
      Proof.
        intros x y. apply ip_val.
        apply (cv_ext (fun n => BV (seq x n) (T0 (seq y n)))).
        - intro n. symmetry. apply T0_sym.
        - exact (ip_cv x (Text y)).
      Qed.

      Lemma Text_contr : forall x, ip (Text x) (Text x) <= ip x x.
      Proof.
        intro x.
        apply (cv_le _ _ _ _ (ip_cv (Text x) (Text x)) (ip_cv x x)).
        intro n. apply T0_contr.
      Qed.

      Lemma Text_pos : (forall u, 0 <= BV u (T0 u)) -> forall x, 0 <= ip x (Text x).
      Proof.
        intros Hpos x.
        apply (cv_ge_from _ _ 0 0%nat (ip_cv x (Text x))). intros n _. apply Hpos.
      Qed.

      Lemma Text_emb : forall u : V,
        ip (hsub (Text (emb u)) (emb (T0 u))) (hsub (Text (emb u)) (emb (T0 u))) = 0.
      Proof.
        intro u.
        apply (UL_sequence _ _ _ (nrm_cv (Text (emb u)) (emb (T0 u)))).
        apply (cv_ext (fun _ => 0)); [| apply cv_const].
        intro n. symmetry. exact (Q_self HV (T0 u)).
      Qed.

      Lemma Text_gap : forall (om : V) (c : R),
        (forall u, BV u (T0 u) - BV u om * BV u om
                   <= c * (BV u u - BV u om * BV u om)) ->
        forall x, ip x (Text x) - ip x (emb om) * ip x (emb om)
                  <= c * (ip x x - ip x (emb om) * ip x (emb om)).
      Proof.
        intros om c Hgap x.
        pose proof (ip_cv x (Text x)) as C1. pose proof (ip_cv x (emb om)) as C2.
        pose proof (ip_cv x x) as C3.
        pose proof (CV_mult _ _ _ _ C2 C2) as C4.
        pose proof (CV_minus _ _ _ _ C1 C4) as C5.
        pose proof (cv_scal _ _ c (CV_minus _ _ _ _ C3 C4)) as C6.
        apply (cv_le _ _ _ _ C5 C6). intro n. apply Hgap.
      Qed.
    End Ext.
  End Completion.

End HilbertCompletion.
