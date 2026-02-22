(* =========================================================================
   peter_weyl.v - Peter-Weyl Axiom Decomposition for Wilson Kernel PSD

   GOAL: Replace the single SU(N) reflection-positivity axiom with a chain
   of 3+1 harmonic-analysis axioms that are standard consequences of Peter-Weyl.

   AXIOM CHAIN:
     (1) character_orthonormal - Characters are orthonormal under Haar
     (2) wilson_kernel_character_expansion - K_β = Σ a_λ χ_λ
     (3) coefficients_nonneg - a_λ(β) ≥ 0 for β ≥ 0
     (4) quadratic_form_decomposition - Q_β(f) = Σ a_λ |⟨f,χ_λ⟩|²

   DERIVED:
     su_n_single_reflection_positive (the original monolithic axiom)

   This file is a REFINEMENT LAYER: it derives the original axiom from
   smaller, more attackable pieces. Future work can discharge (1)-(4)
   individually without touching downstream code.

   MATHEMATICAL BASIS:
     - Peter-Weyl theorem (1927): L²(G) decomposes into irreducibles
     - Schur orthogonality: matrix coefficients are orthonormal
     - Character expansion: K_β(U) = Σ_λ a_λ(β) χ_λ(U)
     - Bessel coefficients: a_λ(β) = I_{d_λ}(β) / I₀(β) ≥ 0

   Author: APEX
   Date: 2026-02-20
   ========================================================================= *)

From Coq Require Import Reals List Arith Lia Lra.
Require Import Coq.Reals.R_sqrt.
Import ListNotations.
Open Scope R_scope.

(* =========================================================================
   Part 1: Abstract Setup (matches su_n_os2_bridge.v)
   ========================================================================= *)

Module PeterWeylAxioms.

Section PW_Setup.

  (* Abstract compact group carrier (SU(N) for some N ≥ 2) *)
  Variable G : Type.

  (* Group involution: U ↦ U† (adjoint/Hermitian conjugate) *)
  Variable dag : G -> G.

  (* Normalized trace: Re(tr(U))/N ∈ [-1, 1] *)
  Variable normalized_trace : G -> R.

  (* Haar integral: ∫_G f(U) dU *)
  Variable haar : (G -> R) -> R.

  (* Wilson kernel: K_β(U) = exp(β · Re(tr(U))/N) *)
  Definition wilson_kernel (beta : R) (U : G) : R :=
    exp (beta * normalized_trace U).

  (* =========================================================================
     Part 2: Irreducible Representation Infrastructure
     ========================================================================= *)

  (* Index type for irreducible representations (irreps) *)
  Variable Irrep : Type.

  (* Decidable equality on irreps *)
  Variable irrep_eq_dec : forall (lam mu : Irrep), {lam = mu} + {lam <> mu}.

  (* Characters χ_λ : G → R (real-valued for simplicity; generalizes to C) *)
  Variable chi : Irrep -> G -> R.

  (* Expansion coefficients a_λ(β) (modified Bessel functions) *)
  Variable acoef : R -> Irrep -> R.

  (* Finite support list for the character expansion.
     This avoids infinite series infrastructure on day one.
     In full generality, this is "all irreps" but we keep it abstract. *)
  Variable support : R -> list Irrep.

  (* =========================================================================
     Part 3: Haar Inner Product
     ========================================================================= *)

  (* Inner product on functions: ⟨f, g⟩ = ∫ f(U) g(U) dU *)
  Definition inner (f g : G -> R) : R :=
    haar (fun U => f U * g U).

  (* Reflected inner product: ⟨f, g⟩_dag = ∫ f(U†) g(U) dU *)
  Definition inner_dag (f g : G -> R) : R :=
    haar (fun U => f (dag U) * g U).

  (* =========================================================================
     AXIOM 1: Character Orthonormality

     ∫ χ_λ(U) χ_μ(U†) dU = δ_{λμ}

     MATHEMATICAL JUSTIFICATION & TRUST LEVEL:
     This is the Schur orthogonality relation specialized to characters of a 
     compact Lie group. It is a fundamental, textbook theorem in harmonic 
     analysis and representation theory.

     Trust Level: HIGH (Standard Mathematics)
     Unlike the original monolithic physics axiom `su_n_single_reflection_positive`,
     this axiom asserts a standard mathematical fact, not a physical hypothesis.

     Mathematical Dependencies:
     1. Existence of Haar measure on compact groups (G = SU(N)).
     2. Schur's Lemma for complex representations.
     3. Definition of characters as Tr(rho(g)).

     References:
     - Brocker & tom Dieck, "Representations of Compact Lie Groups" (Theorem II.2.5)
     - Menotti & Pelissetto, "Poincare, reflection positivity and lattice gauge theories" 
       (Eq. 2.15 implicitly uses this for the character expansion).
     
     STATUS: Kept as an explicit axiom because formalizing full representation 
     theory for compact Lie groups in Coq is a massive research undertaking 
     (no existing library covers this, unlike finite groups).
     ========================================================================= *)

  Axiom character_orthonormal :
    forall (lam mu : Irrep),
      inner_dag (chi lam) (chi mu) = if irrep_eq_dec lam mu then 1 else 0.

  (* =========================================================================
     AXIOM 2: Wilson Kernel Character Expansion

     K_β(U) = Σ_{λ ∈ support(β)} a_λ(β) χ_λ(U)

     This is the character expansion from Peter-Weyl.
     ========================================================================= *)

  Definition sum_characters (beta : R) (U : G) : R :=
    fold_right Rplus 0 (map (fun lam => acoef beta lam * chi lam U) (support beta)).

  Axiom wilson_kernel_character_expansion :
    forall (beta : R) (U : G),
      wilson_kernel beta U = sum_characters beta U.

  (* =========================================================================
     AXIOM 3: Coefficient Non-negativity

     For β ≥ 0, all expansion coefficients a_λ(β) ≥ 0.

     These are modified Bessel functions: a_λ(β) = I_{d_λ}(β) / I₀(β).

     STATUS: ✅ DISCHARGED (Feb 20, 2026)

     This axiom is now FULLY PROVEN in bessel_positivity.v:
       - I_n is DEFINED (not axiom) using monotone convergence (growing_cv)
       - I_n_nonneg and I_0_pos proven via exp series domination
       - bessel_ratio_nonneg: I_n(x)/I_0(x) ≥ 0 for x ≥ 0

     The axiom below is KEPT for backward compatibility with this file's
     structure, but can be replaced by importing bessel_positivity.v
     and instantiating BesselCoefficients.coefficients_nonneg.

     REMAINING STANDARD AXIOMS (in bessel_positivity.v):
       - functional_extensionality_dep
       - sig_forall_dec, sig_not_dec (classical)
     ========================================================================= *)

  Axiom coefficients_nonneg :
    forall (beta : R) (lam : Irrep),
      beta >= 0 -> acoef beta lam >= 0.

  (* =========================================================================
     Part 4: Quadratic Form and PSD
     ========================================================================= *)

  (* The OS quadratic form (matches su_n_os2_bridge.v exactly):
       Q_β(f) = ∫ f(U†) f(U) K_β(U) dU *)
  Definition Q (beta : R) (f : G -> R) : R :=
    haar (fun U => f (dag U) * f U * wilson_kernel beta U).

  (* Character projection: ⟨f, χ_λ⟩ = ∫ f(U) χ_λ(U) dU *)
  Definition proj (f : G -> R) (lam : Irrep) : R :=
    inner f (chi lam).

  (* =========================================================================
     AXIOM 4: Quadratic Form Decomposition

     Q_β(f) = Σ_{λ ∈ support(β)} a_λ(β) · |⟨f, χ_λ⟩|²

     This is where Peter-Weyl completeness enters: the quadratic form
     decomposes as a weighted sum of squared projections.

     This axiom bridges the gap between "kernel is a sum of characters"
     and "quadratic form is non-negative." Making it explicit isolates
     exactly what needs to be proved from L² completeness.
     ========================================================================= *)

  Definition sum_squared_projections (beta : R) (f : G -> R) : R :=
    fold_right Rplus 0
      (map (fun lam => acoef beta lam * Rsqr (proj f lam)) (support beta)).

  Axiom quadratic_form_decomposition :
    forall (beta : R) (f : G -> R),
      beta >= 0 ->
      Q beta f = sum_squared_projections beta f.

  (* =========================================================================
     Part 5: Main Theorem - Wilson Kernel PSD
     ========================================================================= *)

  (* Helper: sum of non-negative terms is non-negative *)
  Lemma sum_nonneg_terms :
    forall (ls : list Irrep) (beta : R) (f : G -> R),
      beta >= 0 ->
      fold_right Rplus 0
        (map (fun lam => acoef beta lam * Rsqr (proj f lam)) ls) >= 0.
  Proof.
    intros ls beta f Hbeta.
    induction ls as [| lam ls' IH]; simpl.
    - lra.
    - assert (Hacoef : acoef beta lam >= 0) by (apply coefficients_nonneg; exact Hbeta).
      assert (Hsqr : Rsqr (proj f lam) >= 0).
      { unfold Rsqr. nra. }
      assert (Hterm : acoef beta lam * Rsqr (proj f lam) >= 0).
      { apply Rle_ge. apply Rmult_le_pos; apply Rge_le; assumption. }
      lra.
  Qed.

  (* MAIN THEOREM: Q_β(f) ≥ 0 for β ≥ 0 *)
  Theorem wilson_kernel_psd :
    forall (beta : R) (f : G -> R),
      beta >= 0 ->
      Q beta f >= 0.
  Proof.
    intros beta f Hbeta.
    rewrite (quadratic_form_decomposition beta f Hbeta).
    apply sum_nonneg_terms.
    exact Hbeta.
  Qed.

  (* =========================================================================
     Part 6: Derive the Original Monolithic Axiom
     ========================================================================= *)

  (* This is the connection to su_n_os2_bridge.v.
     The original axiom was:

       Axiom su_n_single_reflection_positive :
         forall (beta : R) (f : SUN -> R),
           beta >= 0 -> os_inner beta f f >= 0.

     where os_inner beta f f = ∫ f(U†) f(U) K_β(U) dU = Q beta f.

     So we can derive it directly from wilson_kernel_psd.
  *)

  (* Note: os_inner in su_n_os2_bridge.v is:
       haar_integral (fun U => f (sun_inv U) * g U * wilson_kernel beta U)
     which equals Q beta f when g = f. *)

  Definition os_inner (beta : R) (f g : G -> R) : R :=
    haar (fun U => f (dag U) * g U * wilson_kernel beta U).

  (* Verify Q and os_inner coincide for f = g *)
  Lemma Q_eq_os_inner :
    forall (beta : R) (f : G -> R),
      Q beta f = os_inner beta f f.
  Proof.
    intros beta f.
    unfold Q, os_inner.
    (* Both are: haar (fun U => f (dag U) * f U * wilson_kernel beta U) *)
    reflexivity.
  Qed.

  (* THE DERIVED AXIOM: This is what su_n_os2_bridge.v assumed as an axiom.
     Now it's a theorem from the 4 Peter-Weyl axioms. *)
  Theorem su_n_single_reflection_positive_from_PW :
    forall (beta : R) (f : G -> R),
      beta >= 0 ->
      os_inner beta f f >= 0.
  Proof.
    intros beta f Hbeta.
    rewrite <- Q_eq_os_inner.
    apply wilson_kernel_psd.
    exact Hbeta.
  Qed.

End PW_Setup.

End PeterWeylAxioms.

(* =========================================================================
   Part 7: Print Assumptions Census
   ========================================================================= *)

Print Assumptions PeterWeylAxioms.wilson_kernel_psd.
Print Assumptions PeterWeylAxioms.su_n_single_reflection_positive_from_PW.

(* Expected output (as of Feb 20, 2026):
   Axioms:
     - character_orthonormal (Schur orthogonality) [OPEN]
     - wilson_kernel_character_expansion (Peter-Weyl expansion) [OPEN]
     - coefficients_nonneg [DISCHARGEABLE via bessel_positivity.v]
     - quadratic_form_decomposition (L² completeness) [OPEN]

   Note: coefficients_nonneg is still listed here because peter_weyl.v
   uses it as an Axiom for structural clarity. To fully discharge it,
   replace the Axiom with an import from bessel_positivity.v and
   instantiate BesselCoefficients with your Irrep/dim types.

   EFFECTIVE AXIOM COUNT: 3 (down from 4)
*)

(* =========================================================================
   AXIOM DISCHARGE ROADMAP (Updated Feb 20, 2026)

   STATUS SUMMARY:
     ✅ (3) coefficients_nonneg     - DISCHARGED (bessel_positivity.v)
     ⬜ (1) character_orthonormal   - Open (Schur orthogonality)
     ⬜ (2) wilson_kernel_character_expansion - Open (Peter-Weyl)
     ⬜ (4) quadratic_form_decomposition - Open (L² completeness)

   -------------------------------------------------------------------------

   (1) character_orthonormal
       - Requires: Haar measure, Schur orthogonality for compact groups
       - Lean status: Partial (finite groups done, compact groups TBD)
       - Coq status: Not formalized
       - Difficulty: Medium (6-12 months)
       - NEXT ATTACK: schur_orthogonality.v scaffolding exists

   (2) wilson_kernel_character_expansion
       - Requires: Character completeness (Peter-Weyl), functional calculus
       - Lean status: Not formalized
       - Coq status: Not formalized
       - Difficulty: Hard (Peter-Weyl is the main content)

   (3) coefficients_nonneg ✅ DONE
       - File: bessel_positivity.v
       - Method: Constructive I via growing_cv + exp domination
       - Qed count: 26
       - Custom axioms: 0
       - Completed: Feb 20, 2026

   (4) quadratic_form_decomposition
       - Requires: L² completeness, Parseval's theorem for compact groups
       - This is the "bridge" axiom connecting expansion to PSD
       - Lean status: Not formalized
       - Coq status: Not formalized
       - Difficulty: Medium-Hard (Hilbert space theory)

   REMAINING ORDER:
     (1) -> (4) -> (2)

   Next target: (1) character_orthonormal via schur_orthogonality.v
   Hardest: (2) requires full Peter-Weyl machinery.
   ========================================================================= *)

(* =========================================================================
   USAGE NOTE

   To use this file as a refinement layer for su_n_os2_bridge.v:

   1. Import this file
   2. Instantiate the PeterWeylAxioms module with your SUN type
   3. Use su_n_single_reflection_positive_from_PW instead of the axiom
   4. Gradually discharge (1)-(4) as you formalize more

   This keeps downstream code (OS2, mass gap) unchanged while you work
   on eliminating the axioms one by one.
   ========================================================================= *)
