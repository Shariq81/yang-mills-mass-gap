(* =========================================================================
   ym/su2_transfer_spectrum.v

   TARGET 14: the spectrum of the transfer operator of the 4D SU(2) Wilson
   lattice gauge theory at strong coupling on its Osterwalder-Schrader
   Hilbert space.

   The proof uses nothing about the lattice beyond the statement of
   Target 13: for ANY complete form space with a symmetric positive
   contraction T, a normalized invariant vector Omega and the form gap
       (x, T x) <= exp(- m) (x, x)      for x orthogonal to Omega,
   `rg/hilbert_resolvent.v` (Neumann series) gives a bounded inverse of
   T - lam for every lam < 0 and every lam > exp(- m) different from 1,
   and shows that T - 1 has none.

   ZERO `Axiom`, `Parameter`, `Admitted`.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.ChallengeSU2TransferSpectrum.
Require Import rg.hilbert_completion.
Require Import rg.hilbert_resolvent.
Require Import ym.su2_os_hilbert_space.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import ChallengeSU2HilbertSpace ChallengeSU2TransferSpectrum.
Import HilbertCompletion HilbertResolvent.

Open Scope R_scope.

Module SU2TransferSpectrum.

  (* The spectral statement in any Hilbert space (in the sense of the frozen
     definition `hs_hilbert_space`) with a transfer operator, a vacuum and a
     form gap. *)
  Section Abstract.
    Variable H : Type.
    Variable hadd : H -> H -> H.
    Variable hscal : R -> H -> H.
    Variable ip : H -> H -> R.
    Variable T : H -> H.
    Variable Om : H.
    Variable m : R.
    Hypothesis HH : hs_hilbert_space H hadd hscal ip.
    Hypothesis T_sym : forall x y : H, ip (T x) y = ip x (T y).
    Hypothesis T_pos : forall x : H, 0 <= ip x (T x).
    Hypothesis T_contr : forall x : H, ip (T x) (T x) <= ip x x.
    Hypothesis Om_norm : ip Om Om = 1.
    Hypothesis Om_fix : hs_null hadd hscal ip (T Om) Om.
    Hypothesis T_gap : forall x : H, ip x Om = 0 -> ip x (T x) <= exp (- m) * ip x x.

    Lemma HF : form_axioms hadd hscal ip.
    Proof.
      destruct HH as (h1 & h2 & h3 & h4 & _). unfold form_axioms.
      split; [exact h1 |]. split; [exact h2 |]. split; [exact h3 | exact h4].
    Qed.

    Lemma HC : complete hadd hscal ip.
    Proof. destruct HH as (_ & _ & _ & _ & h5). exact h5. Qed.

    (* T <= 1 as a quadratic form *)
    Lemma T_le1 : forall x : H, ip x (T x) <= 1 * ip x x.
    Proof.
      intro x.
      pose proof (cs HF x (T x)) as Hcs.
      pose proof (T_contr x) as H1. pose proof (T_pos x) as H2.
      pose proof (B_pos HF x) as P1. pose proof (B_pos HF (T x)) as P2.
      assert (Hsq : ip x (T x) * ip x (T x) <= ip x x * ip x x).
      { apply Rle_trans with (ip x x * ip (T x) (T x)); [exact Hcs |].
        apply Rmult_le_compat_l; assumption. }
      pose proof (sq_abs_le _ _ P1 Hsq) as Ha.
      pose proof (Rle_abs (ip x (T x))) as Hb. lra.
    Qed.

    (* from a symmetric weak resolvent to the frozen notion of inverse *)
    Lemma to_resolvent : forall (lam : R) (G : H -> H) (C : R),
      (forall x y, ip (G x) y = ip x (G y)) ->
      (forall x z, ip (T (G x)) z - lam * ip (G x) z = ip x z) ->
      (forall x, ip (G x) (G x) <= C * ip x x) ->
      hs_in_resolvent_set hadd hscal ip T lam.
    Proof.
      intros lam G C G_sym G_eq G_bd.
      destruct (inverse_of_weak HF T G lam T_sym G_sym G_eq) as (I1 & I2 & I3 & I4).
      exists G, C.
      split; [exact I1 |]. split; [exact I2 |]. split; [exact G_bd |].
      split; [exact I3 | exact I4].
    Qed.

    Lemma resolvent_negative : forall lam : R, lam < 0 ->
      hs_in_resolvent_set hadd hscal ip T lam.
    Proof.
      intros lam Hlam.
      destruct (resolvent_below HF HC T 1 lam T_sym T_pos Rle_0_1 T_le1 Hlam)
        as (G & G_sym & G_eq & G_bd).
      exact (to_resolvent lam G _ G_sym G_eq G_bd).
    Qed.

    Lemma resolvent_in_gap : forall lam : R, exp (- m) < lam -> lam <> 1 ->
      hs_in_resolvent_set hadd hscal ip T lam.
    Proof.
      intros lam Hlam Hl1.
      assert (Hc0 : 0 <= exp (- m)) by (left; apply exp_pos).
      destruct (resolvent_gap HF HC T T_sym T_pos Om Om_norm Om_fix (exp (- m)) Hc0 T_gap
                  lam Hlam Hl1) as (G & C & G_sym & G_eq & G_bd).
      exact (to_resolvent lam G C G_sym G_eq G_bd).
    Qed.

    Lemma one_in_spectrum : ~ hs_in_resolvent_set hadd hscal ip T 1.
    Proof.
      intros (G & C & _ & _ & G_bd & _ & G_inv).
      exact (eigen_no_inverse HF T Om Om_norm Om_fix G C G_bd (G_inv Om)).
    Qed.

    Theorem transfer_spectrum : su2_os_transfer_spectrum H hadd hscal ip T m.
    Proof.
      split; [exact resolvent_negative |].
      split; [exact resolvent_in_gap | exact one_in_spectrum].
    Qed.
  End Abstract.

  (* TARGET 14 *)
  Theorem su2_transfer_spectrum : Challenge_SU2Gauge4D_TransferSpectrum.
  Proof.
    intros beta mu Hmu Hb0 Hsmall Hb.
    destruct (SU2OSHilbertSpace.su2_os_hilbert_space beta mu Hmu Hb0 Hsmall Hb)
      as (H & hadd & hscal & ip & emb & T & HH & Hemb & HT & HV).
    exists H, hadd, hscal, ip, emb, T.
    split; [exact HH |]. split; [exact Hemb |]. split; [exact HT |]. split; [exact HV |].
    destruct HT as (_ & _ & T_sym & T_pos & T_contr & _).
    destruct HV as (Om_norm & Om_fix & T_gap & _).
    exact (transfer_spectrum H hadd hscal ip T (emb (fun _ => 1)) (mu / 2)
             HH T_sym T_pos T_contr Om_norm Om_fix T_gap).
  Qed.

End SU2TransferSpectrum.
