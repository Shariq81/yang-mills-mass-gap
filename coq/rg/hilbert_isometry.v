(* =========================================================================
   rg/hilbert_isometry.v

   Maps that preserve the form of a complete form space (a real Hilbert
   space modulo its null vectors, as in `rg/hilbert_completion.v`).

     - joint continuity of the form;
     - a map that preserves the form is additive and homogeneous modulo
       null vectors;
     - two non-expansive maps that agree, modulo null vectors, on a dense
       family agree everywhere;
     - a map defined on a dense family that preserves the form extends to
       a form-preserving map of the whole space.

   Nothing in this file refers to a lattice or to a gauge group.

   ZERO `Axiom`, `Parameter`, `Admitted`.  Approximating sequences and
   limits are selected with
   `ClassicalEpsilon.constructive_indefinite_description`.
   ========================================================================= *)

From Coq Require Import Reals Lra Lia Psatz ClassicalEpsilon.
Require Import rg.hilbert_completion.
Require Import rg.hilbert_resolvent.

Open Scope R_scope.

Module HilbertIsometry.

  Import HilbertCompletion HilbertResolvent.

  Lemma zero_of_small : forall a : R,
    0 <= a -> (forall eps : R, 0 < eps -> a <= eps) -> a = 0.
  Proof.
    intros a Ha H. destruct (Rle_lt_or_eq_dec 0 a Ha) as [Hlt | He];
      [| symmetry; exact He].
    assert (Hh : 0 < a / 2) by lra. pose proof (H (a / 2) Hh). lra.
  Qed.

  Section Space.
    Context {E : Type} {add : E -> E -> E} {scal : R -> E -> E} {B : E -> E -> R}.
    Hypothesis HF : form_axioms add scal B.

    Local Notation "x -- y" := (sub add scal x y) (at level 40, left associativity).
    Local Notation lim := (@lim_of E add scal B).

    (* =====================================================================
       1. Null vectors and limits
       ===================================================================== *)

    Lemma null_sym : forall x y,
      B (x -- y) (x -- y) = 0 -> B (y -- x) (y -- x) = 0.
    Proof. intros x y H. rewrite (Q_sub_sym HF y x). exact H. Qed.

    Lemma null_trans : forall x y z,
      B (x -- y) (x -- y) = 0 -> B (y -- z) (y -- z) = 0 ->
      B (x -- z) (x -- z) = 0.
    Proof.
      intros x y z H1 H2. pose proof (Q_tri2 HF x y z) as H.
      pose proof (B_pos HF (x -- z)) as P. lra.
    Qed.

    Lemma lim_unique : forall (X : nat -> E) (y y' : E),
      lim X y -> lim X y' -> B (y -- y') (y -- y') = 0.
    Proof.
      intros X y y' H1 H2. apply zero_of_small; [apply (B_pos HF) |].
      intros eps He. assert (He4 : 0 < eps / 4) by lra.
      destruct (H1 _ He4) as [N1 HN1]. destruct (H2 _ He4) as [N2 HN2].
      pose proof (HN1 (Nat.max N1 N2) (Nat.le_max_l _ _)) as A1.
      pose proof (HN2 (Nat.max N1 N2) (Nat.le_max_r _ _)) as A2.
      pose proof (Q_tri2 HF y (X (Nat.max N1 N2)) y') as T.
      rewrite (Q_sub_sym HF y (X (Nat.max N1 N2))) in T. lra.
    Qed.

    (* joint continuity of the form *)
    Lemma B_cv : forall (X Y : nat -> E) (x y : E),
      lim X x -> lim Y y -> Un_cv (fun n => B (X n) (Y n)) (B x y).
    Proof.
      intros X Y x y HX HY.
      assert (H1 : Un_cv (fun n => B (X n -- x) (Y n -- y)) 0).
      { intros eps He. destruct (HX eps He) as [N1 HN1].
        destruct (HY eps He) as [N2 HN2].
        exists (Nat.max N1 N2). intros n Hn. unfold R_dist. rewrite Rminus_0_r.
        assert (Hn1 : (N1 <= n)%nat) by (unfold ge in Hn; lia).
        assert (Hn2 : (N2 <= n)%nat) by (unfold ge in Hn; lia).
        pose proof (HN1 n Hn1) as A1. pose proof (HN2 n Hn2) as A2.
        pose proof (B_pos HF (X n -- x)) as P1.
        pose proof (B_pos HF (Y n -- y)) as P2.
        pose proof (cs HF (X n -- x) (Y n -- y)) as Hcs.
        assert (Hlt : B (X n -- x) (Y n -- y) * B (X n -- x) (Y n -- y) < eps * eps).
        { apply Rle_lt_trans with (B (X n -- x) (X n -- x) * B (Y n -- y) (Y n -- y));
            [exact Hcs |].
          apply Rle_lt_trans with (eps * B (Y n -- y) (Y n -- y)).
          - apply Rmult_le_compat_r; [exact P2 | lra].
          - apply Rmult_lt_compat_l; [exact He | exact A2]. }
        assert (Ha : Rabs (B (X n -- x) (Y n -- y)) < Rabs eps)
          by (apply Rsqr_lt_abs_0; unfold Rsqr; exact Hlt).
        rewrite (Rabs_pos_eq eps) in Ha by lra. exact Ha. }
      pose proof (lim_weak HF X x y HX) as H2.
      pose proof (lim_weak HF Y y x HY) as H3.
      pose proof (CV_minus _ _ _ _ (CV_plus _ _ _ _ (CV_plus _ _ _ _ H1 H2) H3)
                    (cv_const (B x y))) as H4.
      assert (Elim : 0 + B x y + B y x - B x y = B x y)
        by (rewrite (B_sym HF y x); ring).
      rewrite Elim in H4.
      apply (cv_ext (fun n => B (X n -- x) (Y n -- y) + B (X n) y + B (Y n) x - B x y));
        [| exact H4].
      intro n.
      rewrite (B_sub HF (X n) x (Y n -- y)), (B_sub_r HF (Y n) y (X n)),
        (B_sub_r HF (Y n) y x), (B_sym HF (Y n) x).
      ring.
    Qed.

    (* =====================================================================
       2. Form-preserving maps are linear modulo null vectors
       ===================================================================== *)

    Section Iso.
      Variable F : E -> E.
      Hypothesis F_iso : forall x y, B (F x) (F y) = B x y.

      Lemma iso_Q_sub : forall x y,
        B (F x -- F y) (F x -- F y) = B (x -- y) (x -- y).
      Proof.
        intros x y. rewrite (Q_sub HF (F x) (F y)), (Q_sub HF x y), !F_iso.
        reflexivity.
      Qed.

      Lemma iso_null : forall x y,
        B (x -- y) (x -- y) = 0 -> B (F x -- F y) (F x -- F y) = 0.
      Proof. intros x y H. rewrite iso_Q_sub. exact H. Qed.

      Lemma iso_add : forall x y,
        B (F (add x y) -- add (F x) (F y)) (F (add x y) -- add (F x) (F y)) = 0.
      Proof.
        intros x y.
        rewrite (Q_sub HF (F (add x y)) (add (F x) (F y))),
          (Q_add HF (F x) (F y)), (B_add_r HF (F x) (F y) (F (add x y))), !F_iso.
        rewrite (Q_add HF x y), (B_add HF x y x), (B_add HF x y y), (B_sym HF y x).
        ring.
      Qed.

      Lemma iso_scal : forall c x,
        B (F (scal c x) -- scal c (F x)) (F (scal c x) -- scal c (F x)) = 0.
      Proof.
        intros c x.
        rewrite (Q_sub HF (F (scal c x)) (scal c (F x))),
          (B_scal_r HF c (F x) (F (scal c x))), (Q_scal HF c (F x)), !F_iso.
        rewrite (Q_scal HF c x), (B_scal HF c x x). ring.
      Qed.
    End Iso.

    (* =====================================================================
       3. A dense family
       ===================================================================== *)

    Section Dense.
      Variable V : Type.
      Variable e : V -> E.
      Hypothesis e_dense : forall (x : E) (eps : R), 0 < eps ->
        exists v : V, B (x -- e v) (x -- e v) < eps.

      (* two non-expansive maps that agree on the dense family agree *)
      Lemma agree_dense : forall A1 A2 : E -> E,
        (forall x y, B (A1 x -- A1 y) (A1 x -- A1 y) <= B (x -- y) (x -- y)) ->
        (forall x y, B (A2 x -- A2 y) (A2 x -- A2 y) <= B (x -- y) (x -- y)) ->
        (forall v, B (A1 (e v) -- A2 (e v)) (A1 (e v) -- A2 (e v)) = 0) ->
        forall x, B (A1 x -- A2 x) (A1 x -- A2 x) = 0.
      Proof.
        intros A1 A2 L1 L2 Hag x.
        apply zero_of_small; [apply (B_pos HF) |]. intros eps He.
        assert (He8 : 0 < eps / 8) by lra.
        destruct (e_dense x (eps / 8) He8) as [v Hv].
        pose proof (Q_tri3 HF (A1 x) (A1 (e v)) (A2 (e v)) (A2 x)) as T.
        pose proof (L1 x (e v)) as B1. pose proof (L2 (e v) x) as B2.
        rewrite (Q_sub_sym HF (e v) x) in B2.
        rewrite (Hag v) in T. lra.
      Qed.

      Lemma approx_ex : forall (x : E) (n : nat),
        exists v : V, B (x -- e v) (x -- e v) < / INR (S n).
      Proof.
        intros x n. apply e_dense. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
      Qed.

      Definition approx (x : E) (n : nat) : V :=
        proj1_sig (constructive_indefinite_description _ (approx_ex x n)).

      Lemma approx_spec : forall x n,
        B (x -- e (approx x n)) (x -- e (approx x n)) < / INR (S n).
      Proof.
        intros x n.
        exact (proj2_sig (constructive_indefinite_description _ (approx_ex x n))).
      Qed.

      Lemma approx_lim : forall (x : E) (eps : R), 0 < eps ->
        exists N : nat, forall n : nat, (N <= n)%nat ->
          B (e (approx x n) -- x) (e (approx x n) -- x) < eps.
      Proof.
        intros x eps He. destruct (inv_small eps He) as [N HN]. exists N.
        intros n Hn. rewrite (Q_sub_sym HF (e (approx x n)) x).
        apply Rlt_trans with (/ INR (S n)); [apply approx_spec | apply HN; exact Hn].
      Qed.

      (* ===================================================================
         4. Extension of a form-preserving map defined on the dense family
         =================================================================== *)

      Section Ext.
        Hypothesis HC : complete add scal B.
        Variable W0 : V -> E.
        Hypothesis W0_iso : forall u v, B (W0 u) (W0 v) = B (e u) (e v).

        Lemma W0_Q : forall u v,
          B (W0 u -- W0 v) (W0 u -- W0 v) = B (e u -- e v) (e u -- e v).
        Proof.
          intros u v. rewrite (Q_sub HF (W0 u) (W0 v)), (Q_sub HF (e u) (e v)), !W0_iso.
          reflexivity.
        Qed.

        Lemma W0_cauchy : forall (x : E) (eps : R), 0 < eps ->
          exists N : nat, forall p q : nat, (N <= p)%nat -> (N <= q)%nat ->
            B (W0 (approx x p) -- W0 (approx x q)) (W0 (approx x p) -- W0 (approx x q))
            < eps.
        Proof.
          intros x eps He. assert (He4 : 0 < eps / 4) by lra.
          destruct (approx_lim x (eps / 4) He4) as [N HN]. exists N. intros p q Hp Hq.
          rewrite W0_Q.
          pose proof (Q_tri2 HF (e (approx x p)) x (e (approx x q))) as T.
          pose proof (HN p Hp) as A1. pose proof (HN q Hq) as A2.
          rewrite (Q_sub_sym HF x (e (approx x q))) in T. lra.
        Qed.

        Lemma Wext_ex : forall x : E,
          exists y : E, forall eps : R, 0 < eps ->
            exists N : nat, forall n : nat, (N <= n)%nat ->
              B (W0 (approx x n) -- y) (W0 (approx x n) -- y) < eps.
        Proof. intro x. exact (HC (fun n => W0 (approx x n)) (W0_cauchy x)). Qed.

        Definition Wext (x : E) : E :=
          proj1_sig (constructive_indefinite_description _ (Wext_ex x)).

        Lemma Wext_lim : forall (x : E) (eps : R), 0 < eps ->
          exists N : nat, forall n : nat, (N <= n)%nat ->
            B (W0 (approx x n) -- Wext x) (W0 (approx x n) -- Wext x) < eps.
        Proof.
          intro x.
          exact (proj2_sig (constructive_indefinite_description _ (Wext_ex x))).
        Qed.

        Theorem Wext_iso : forall x y, B (Wext x) (Wext y) = B x y.
        Proof.
          intros x y.
          apply (UL_sequence (fun n => B (W0 (approx x n)) (W0 (approx y n)))).
          - exact (B_cv (fun n => W0 (approx x n)) (fun n => W0 (approx y n))
                     (Wext x) (Wext y) (Wext_lim x) (Wext_lim y)).
          - apply (cv_ext (fun n => B (e (approx x n)) (e (approx y n)))).
            + intro n. symmetry. apply W0_iso.
            + exact (B_cv (fun n => e (approx x n)) (fun n => e (approx y n))
                       x y (approx_lim x) (approx_lim y)).
        Qed.

        Theorem Wext_e : forall v : V,
          B (Wext (e v) -- W0 v) (Wext (e v) -- W0 v) = 0.
        Proof.
          intro v.
          apply (lim_unique (fun n => W0 (approx (e v) n)) (Wext (e v)) (W0 v)
                   (Wext_lim (e v))).
          intros eps He. destruct (approx_lim (e v) eps He) as [N HN]. exists N.
          intros n Hn. cbv beta. rewrite W0_Q. exact (HN n Hn).
        Qed.
      End Ext.
    End Dense.
  End Space.

End HilbertIsometry.
