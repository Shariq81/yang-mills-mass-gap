(* =========================================================================
   ym/su2_haar_poly.v

   Polynomials in the four coordinates of a quaternion, and the Haar
   integral (limit of the Hopf-grid averages) of the zonal kernels
       kap k x y = ((1 + <x, y>) / 2) ^ k.

     - polynomials as finite lists of monomials; closure under sums and
       products; polynomials are bounded and uniformly continuous on SU(2);
     - `poly_swap_inv`: the Haar integral of a polynomial is invariant
       under the exchange of the second and third coordinates (from the
       symmetry of the moments, ym/su2_haar_moments.v);
     - `kernel_const`: the Haar integral of x |-> kap k x y does not depend
       on the unit quaternion y (y is moved to 1 by rotations in coordinate
       planes, ym/su2_haar_orbit.v, under which the integral of the kernel
       is invariant: ym/su2_haar_torus.v and `poly_swap_inv`).

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import rg.dup_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_mean.
Require Import ym.su2_haar_moments.
Require Import ym.su2_haar_torus.
Require Import ym.su2_haar_orbit.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2HaarGrid SU2HaarMean.
Open Scope R_scope.

Module SU2HaarPoly.

  (* =======================================================================
     1. Polynomials
     ======================================================================= *)

  Definition term : Type := (R * (nat * nat * nat * nat))%type.

  Definition tval (t : term) (q : Quat) : R :=
    match t with (c, (a, b, e, d)) => c * mono a b e d q end.

  Definition pval (p : list term) (q : Quat) : R := rsum p (fun t => tval t q).

  Definition is_poly (f : Quat -> R) : Prop :=
    exists p : list term, forall q, f q = pval p q.

  Lemma pval_nil : forall q, pval [] q = 0.
  Proof. reflexivity. Qed.

  Lemma pval_cons : forall t p q, pval (t :: p) q = tval t q + pval p q.
  Proof. intros t p q. exact (rsum_cons t p (fun t0 => tval t0 q)). Qed.

  Lemma pval_app : forall p p' q, pval (p ++ p') q = pval p q + pval p' q.
  Proof. intros p p' q. exact (rsum_app p p' (fun t => tval t q)). Qed.

  Lemma mono_mul : forall a b c d a' b' c' d' q,
    mono a b c d q * mono a' b' c' d' q = mono (a + a') (b + b') (c + c') (d + d') q.
  Proof. intros. unfold mono. rewrite !pow_add. ring. Qed.

  Definition tmul (t t' : term) : term :=
    match t, t' with
    | (c, (a, b, e, d)), (c', (a', b', e', d')) =>
        (c * c', ((a + a')%nat, (b + b')%nat, (e + e')%nat, (d + d')%nat))
    end.

  Lemma tval_tmul : forall t t' q, tval (tmul t t') q = tval t q * tval t' q.
  Proof.
    intros [c [[[a b] e] d]] [c' [[[a' b'] e'] d']] q. cbn [tmul tval].
    rewrite <- mono_mul. ring.
  Qed.

  Definition pmul (p p' : list term) : list term :=
    flat_map (fun t => map (tmul t) p') p.

  Lemma pval_pmul : forall p p' q, pval (pmul p p') q = pval p q * pval p' q.
  Proof.
    intros p p' q. unfold pval, pmul. rewrite rsum_flat_map.
    rewrite (rsum_ext p _ (fun t => tval t q * rsum p' (fun t' => tval t' q))).
    - apply rsum_scal_r.
    - intros t _. rewrite rsum_map, <- rsum_scal. apply rsum_ext.
      intros t' _. apply tval_tmul.
  Qed.

  Lemma is_poly_ext : forall f f' : Quat -> R,
    (forall q, f q = f' q) -> is_poly f -> is_poly f'.
  Proof.
    intros f f' E [p Hp]. exists p. intro q. rewrite <- E. apply Hp.
  Qed.

  Lemma is_poly_const : forall c : R, is_poly (fun _ => c).
  Proof.
    intro c. exists [(c, (0%nat, 0%nat, 0%nat, 0%nat))]. intro q.
    rewrite pval_cons, pval_nil. unfold tval, mono. cbn [pow]. ring.
  Qed.

  Lemma is_poly_qr : is_poly qr.
  Proof.
    exists [(1, (1%nat, 0%nat, 0%nat, 0%nat))]. intro q.
    rewrite pval_cons, pval_nil. unfold tval, mono. cbn [pow]. ring.
  Qed.

  Lemma is_poly_qi : is_poly qi.
  Proof.
    exists [(1, (0%nat, 1%nat, 0%nat, 0%nat))]. intro q.
    rewrite pval_cons, pval_nil. unfold tval, mono. cbn [pow]. ring.
  Qed.

  Lemma is_poly_qj : is_poly qj.
  Proof.
    exists [(1, (0%nat, 0%nat, 1%nat, 0%nat))]. intro q.
    rewrite pval_cons, pval_nil. unfold tval, mono. cbn [pow]. ring.
  Qed.

  Lemma is_poly_qk : is_poly qk.
  Proof.
    exists [(1, (0%nat, 0%nat, 0%nat, 1%nat))]. intro q.
    rewrite pval_cons, pval_nil. unfold tval, mono. cbn [pow]. ring.
  Qed.

  Lemma is_poly_plus : forall f f' : Quat -> R,
    is_poly f -> is_poly f' -> is_poly (fun q => f q + f' q).
  Proof.
    intros f f' [p Hp] [p' Hp']. exists (p ++ p'). intro q.
    rewrite pval_app, Hp, Hp'. reflexivity.
  Qed.

  Lemma is_poly_mult : forall f f' : Quat -> R,
    is_poly f -> is_poly f' -> is_poly (fun q => f q * f' q).
  Proof.
    intros f f' [p Hp] [p' Hp']. exists (pmul p p'). intro q.
    rewrite pval_pmul, Hp, Hp'. reflexivity.
  Qed.

  Lemma is_poly_pow : forall (f : Quat -> R) k, is_poly f -> is_poly (fun q => f q ^ k).
  Proof.
    intros f k Hf. induction k as [| k IH].
    - exact (is_poly_const 1).
    - exact (is_poly_mult f (fun q => f q ^ k) Hf IH).
  Qed.

  Lemma pval_fn_bc : forall p, fn_bc (pval p).
  Proof.
    induction p as [| [c [[[a b] e] d]] p IH].
    - exact (fn_bc_const 0).
    - apply (fn_bc_ext (fun q => c * mono a b e d q + pval p q)).
      + intros q _. rewrite pval_cons. reflexivity.
      + apply fn_bc_plus; [| exact IH]. apply fn_bc_scal. apply fn_bc_mono.
  Qed.

  Lemma is_poly_fn_bc : forall f : Quat -> R, is_poly f -> fn_bc f.
  Proof.
    intros f [p Hp]. apply (fn_bc_ext (pval p)); [| apply pval_fn_bc].
    intros q _. symmetry. apply Hp.
  Qed.

  (* =======================================================================
     2. The zonal kernels
     ======================================================================= *)

  Definition kap (k : nat) (x y : Quat) : R := ((1 + qdot x y) / 2) ^ k.

  Lemma kap_sym : forall k x y, kap k x y = kap k y x.
  Proof. intros k x y. unfold kap. rewrite (qdot_sym x y). reflexivity. Qed.

  Lemma kap_base_bounds : forall x y, su2_unit x -> su2_unit y ->
    0 <= (1 + qdot x y) / 2 <= 1.
  Proof. intros x y Hx Hy. pose proof (qdot_bounds x y Hx Hy). lra. Qed.

  Lemma kap_bounds : forall k x y, su2_unit x -> su2_unit y -> 0 <= kap k x y <= 1.
  Proof.
    intros k x y Hx Hy. destruct (kap_base_bounds x y Hx Hy) as [H0 H1].
    unfold kap. split; [apply pow_le; exact H0 |].
    apply Rle_trans with (1 ^ k); [apply pow_incr; split; assumption |].
    rewrite pow1. apply Rle_refl.
  Qed.

  Lemma kap_poly : forall k y, is_poly (fun x => kap k x y).
  Proof.
    intros k y. unfold kap. apply is_poly_pow.
    apply (is_poly_ext
             (fun x => / 2 * (1 + (qr y * qr x + (qi y * qi x
                                   + (qj y * qj x + qk y * qk x)))))).
    - intro x. unfold qdot. field.
    - apply is_poly_mult; [apply is_poly_const |].
      apply is_poly_plus; [apply is_poly_const |].
      apply is_poly_plus; [apply is_poly_mult; [apply is_poly_const | exact is_poly_qr] |].
      apply is_poly_plus; [apply is_poly_mult; [apply is_poly_const | exact is_poly_qi] |].
      apply is_poly_plus; [apply is_poly_mult; [apply is_poly_const | exact is_poly_qj] |].
      apply is_poly_mult; [apply is_poly_const | exact is_poly_qk].
  Qed.

  Lemma kap_fn_bc : forall k y, fn_bc (fun x => kap k x y).
  Proof. intros k y. apply is_poly_fn_bc. apply kap_poly. Qed.

  (* the adjoints of the elementary isometries *)
  Lemma qdot_rot01 : forall t x z, qdot x (rot01 t z) = qdot (rot01 (- t) x) z.
  Proof.
    intros t x z. unfold qdot, rot01. cbn [qr qi qj qk].
    rewrite cos_neg, sin_neg. ring.
  Qed.

  Lemma qdot_rot23 : forall t x z, qdot x (rot23 t z) = qdot (rot23 (- t) x) z.
  Proof.
    intros t x z. unfold qdot, rot23. cbn [qr qi qj qk].
    rewrite cos_neg, sin_neg. ring.
  Qed.

  Lemma qdot_swap12 : forall x z, qdot x (swap12 z) = qdot (swap12 x) z.
  Proof. intros x z. unfold qdot, swap12. cbn [qr qi qj qk]. ring. Qed.

  (* =======================================================================
     3. Invariance of the Haar integral of polynomials and of the kernels
     ======================================================================= *)

  Lemma mono_swap12 : forall a b c d q, mono a b c d (swap12 q) = mono a c b d q.
  Proof. intros. unfold mono, swap12. cbn [qr qi qj qk]. ring. Qed.

  Lemma poly_swap_lim : forall p : list term,
    exists v : R, haar_lim (pval p) v /\ haar_lim (fun q => pval p (swap12 q)) v.
  Proof.
    induction p as [| [c [[[a b] e] d]] p IH].
    - exists 0. split.
      + exact (haar_const 0).
      + exact (haar_const 0).
    - destruct IH as [v [H1 H2]].
      destruct (haar_exists (mono a b e d) (fn_bc_mono a b e d)) as [w Hw].
      destruct (haar_exists (mono a e b d) (fn_bc_mono a e b d)) as [w' Hw'].
      assert (E : w = w') by exact (SU2HaarMoments.moment_swap a b e d w w' Hw Hw').
      subst w'. exists (c * w + v). split.
      + apply (haar_ext (fun q => c * mono a b e d q + pval p q)).
        * intros q _. rewrite pval_cons. reflexivity.
        * apply haar_plus; [apply haar_scal; exact Hw | exact H1].
      + apply (haar_ext (fun q => c * mono a e b d q + pval p (swap12 q))).
        * intros q _. rewrite pval_cons. cbn [tval]. rewrite mono_swap12. reflexivity.
        * apply haar_plus; [apply haar_scal; exact Hw' | exact H2].
  Qed.

  Lemma poly_swap_inv : forall (f : Quat -> R) (v : R),
    is_poly f -> haar_lim f v -> haar_lim (fun q => f (swap12 q)) v.
  Proof.
    intros f v [p Hp] Hv. destruct (poly_swap_lim p) as [w [H1 H2]].
    assert (E : v = w).
    { apply (haar_unique (pval p)); [| exact H1].
      apply (haar_ext f); [intros q _; apply Hp | exact Hv]. }
    subst w. apply (haar_ext (fun q => pval p (swap12 q))); [| exact H2].
    intros q _. symmetry. apply Hp.
  Qed.

  Lemma kernel_step_rot01 : forall k t z v,
    haar_lim (fun x => kap k x z) v -> haar_lim (fun x => kap k x (rot01 t z)) v.
  Proof.
    intros k t z v H.
    apply (haar_ext (fun x => kap k (rot01 (- t) x) z)).
    - intros x _. unfold kap. rewrite qdot_rot01. reflexivity.
    - exact (SU2HaarTorus.haar_rot01 (- t) (fun x => kap k x z) v (kap_fn_bc k z) H).
  Qed.

  Lemma kernel_step_rot23 : forall k t z v,
    haar_lim (fun x => kap k x z) v -> haar_lim (fun x => kap k x (rot23 t z)) v.
  Proof.
    intros k t z v H.
    apply (haar_ext (fun x => kap k (rot23 (- t) x) z)).
    - intros x _. unfold kap. rewrite qdot_rot23. reflexivity.
    - exact (SU2HaarTorus.haar_rot23 (- t) (fun x => kap k x z) v (kap_fn_bc k z) H).
  Qed.

  Lemma kernel_step_swap : forall k z v,
    haar_lim (fun x => kap k x z) v -> haar_lim (fun x => kap k x (swap12 z)) v.
  Proof.
    intros k z v H.
    apply (haar_ext (fun x => kap k (swap12 x) z)).
    - intros x _. unfold kap. rewrite qdot_swap12. reflexivity.
    - exact (poly_swap_inv (fun x => kap k x z) v (kap_poly k z) H).
  Qed.

  (* the Haar integral of the kernel does not depend on its center *)
  Theorem kernel_const : forall (k : nat) (y : Quat) (v v0 : R),
    su2_unit y ->
    haar_lim (fun x => kap k x y) v ->
    haar_lim (fun x => kap k x qone) v0 ->
    v = v0.
  Proof.
    intros k y v v0 Hy Hv Hv0.
    destruct (SU2HaarOrbit.unit_orbit y Hy) as [t1 [t2 [t3 E]]].
    apply (haar_unique (fun x => kap k x y) v v0 Hv). rewrite E.
    apply kernel_step_rot01, kernel_step_rot23, kernel_step_swap, kernel_step_rot01.
    exact Hv0.
  Qed.

End SU2HaarPoly.
