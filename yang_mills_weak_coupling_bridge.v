From Coq Require Import Reals.
From Coq Require Import Lra.

Open Scope R_scope.

Module WeakCouplingBridge.

Parameter BetaPoint : Type.
Parameter beta_value : BetaPoint -> R.
Parameter gap : BetaPoint -> R.
Parameter same_phase : BetaPoint -> BetaPoint -> Prop.

Parameter C : R.
Hypothesis C_pos : C > 0.

Definition strong_threshold : R := / C.

Hypothesis strong_exists :
  exists b_strong : BetaPoint, beta_value b_strong < strong_threshold.

Hypothesis mass_gap_strong :
  forall b : BetaPoint, beta_value b < strong_threshold -> gap b > 0.

Hypothesis weak_coupling_gap :
  forall b : BetaPoint, beta_value b >= strong_threshold -> gap b > 0.

Theorem mass_gap_split_regimes :
  forall b : BetaPoint, gap b > 0.
Proof.
  intro b.
  destruct (Rlt_dec (beta_value b) strong_threshold) as [Hstrong | Hweak].
  - apply mass_gap_strong; exact Hstrong.
  - apply weak_coupling_gap; lra.
Qed.

Hypothesis no_phase_transition :
  forall b1 b2 : BetaPoint, same_phase b1 b2.

Hypothesis gap_phase_invariant :
  forall b1 b2 : BetaPoint, same_phase b1 b2 -> gap b1 > 0 -> gap b2 > 0.

Theorem mass_gap_all_beta_from_phase_connectivity :
  forall b : BetaPoint, gap b > 0.
Proof.
  intro b.
  destruct strong_exists as [b_strong Hb_strong].
  apply (gap_phase_invariant b_strong b).
  - apply no_phase_transition.
  - apply mass_gap_strong; exact Hb_strong.
Qed.

Hypothesis gap_monotone_nondecreasing :
  forall b1 b2 : BetaPoint, beta_value b1 <= beta_value b2 -> gap b1 <= gap b2.

Theorem weak_regime_dominates_strong_regime :
  forall b : BetaPoint,
    beta_value b >= strong_threshold ->
    exists b_strong : BetaPoint,
      beta_value b_strong < strong_threshold /\
      gap b >= gap b_strong /\
      gap b > 0.
Proof.
  intros b Hb.
  destruct strong_exists as [b_strong Hb_strong].
  exists b_strong.
  split; [exact Hb_strong |].
  split.
  - pose proof (gap_monotone_nondecreasing b_strong b) as Hmono.
    assert (Hle : beta_value b_strong <= beta_value b) by lra.
    specialize (Hmono Hle).
    lra.
  - apply mass_gap_split_regimes.
Qed.

End WeakCouplingBridge.
