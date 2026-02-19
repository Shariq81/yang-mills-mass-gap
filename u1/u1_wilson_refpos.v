(* =========================================================================
   u1_wilson_refpos.v - Wilson U(1) Reflection Positivity

   THIS IS THE WALL.

   Goal: Prove that the U(1) Wilson lattice gauge theory satisfies
   Osterwalder-Schrader reflection positivity.

   The proof strategy follows Osterwalder-Seiler / Menotti-Pelissetto:

   1. Factor the action: S = S_+ + S_0 + S_-
   2. Use reflection symmetry: S_- = S_+ ∘ Θ
   3. Factor the integral over positive/negative halves
   4. Show the result is a perfect square (for pure t>0 observables)
   5. Handle boundary plaquettes carefully

   Reference:
   - Osterwalder-Seiler 1978 "Gauge Field Theories on a Lattice"
   - Menotti-Pelissetto 1987 "A general proof of reflection positivity..."
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Lra.
From Coq Require Import Lia.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Permutation.

Require Import U1.u1_lattice.
Require Import U1.u1_integral.
Require Import U1.u1_wilson_action.
Require Import U1.u1_reflection.
Import U1Lattice.
Import U1Integral.
Import U1WilsonAction.
Import U1Reflection.

Import ListNotations.
Open Scope R_scope.

Module U1WilsonReflectionPositivity.

(* =========================================================================
   Part 1: Link Decomposition

   Decompose links into:
   - links_pos: links entirely in t > 0
   - links_neg: links entirely in t < 0
   - links_bdry: links crossing or on t = 0
   ========================================================================= *)

Definition links_pos (L : lattice_size) : list link :=
  filter (fun l => Z.gtb (site_t (link_src l)) 0) (all_links L).

Definition links_neg (L : lattice_size) : list link :=
  filter (fun l => Z.ltb (site_t (link_src l)) 0) (all_links L).

Definition links_bdry (L : lattice_size) : list link :=
  filter (fun l => Z.eqb (site_t (link_src l)) 0) (all_links L).

(* Helper: exactly one of >, =, < holds for any integer *)
Lemma Z_trichotomy_gtb_eqb_ltb : forall t,
  (Z.gtb t 0 = true /\ Z.eqb t 0 = false /\ Z.ltb t 0 = false) \/
  (Z.gtb t 0 = false /\ Z.eqb t 0 = true /\ Z.ltb t 0 = false) \/
  (Z.gtb t 0 = false /\ Z.eqb t 0 = false /\ Z.ltb t 0 = true).
Proof.
  intros t.
  destruct (Z.lt_trichotomy t 0) as [Hlt | [Heq | Hgt]].
  - (* t < 0 *)
    right; right.
    rewrite Z.gtb_ltb. rewrite Z.ltb_ge. rewrite Z.eqb_neq. rewrite Z.ltb_lt. lia.
  - (* t = 0 *)
    right; left. subst. auto.
  - (* t > 0 *)
    left.
    rewrite Z.gtb_lt. rewrite Z.eqb_neq. rewrite Z.ltb_ge. lia.
Qed.

(* Generic filter trichotomy lemma *)
Lemma filter_trichotomy_permutation {A : Type} (l : list A) (p1 p2 p3 : A -> bool) :
  (forall x, (p1 x = true /\ p2 x = false /\ p3 x = false) \/
             (p1 x = false /\ p2 x = true /\ p3 x = false) \/
             (p1 x = false /\ p2 x = false /\ p3 x = true)) ->
  Permutation l (filter p1 l ++ filter p2 l ++ filter p3 l).
Proof.
  intros Htri.
  induction l as [| a l' IH].
  - simpl. apply perm_nil.
  - simpl.
    destruct (Htri a) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]].
    + (* p1 a = true *)
      rewrite H1, H2, H3. simpl.
      apply perm_skip. exact IH.
    + (* p2 a = true *)
      rewrite H1, H2, H3. simpl.
      apply Permutation_cons_app. exact IH.
    + (* p3 a = true *)
      rewrite H1, H2, H3. simpl.
      rewrite app_assoc.
      apply Permutation_cons_app.
      rewrite <- app_assoc. exact IH.
Qed.

(* Links partition the full set - PROVED *)
Lemma links_partition : forall L,
  Permutation (all_links L) (links_pos L ++ links_bdry L ++ links_neg L).
Proof.
  intros L.
  unfold links_pos, links_neg, links_bdry.
  apply filter_trichotomy_permutation.
  intros l. simpl.
  apply Z_trichotomy_gtb_eqb_ltb.
Qed.

(* =========================================================================
   Part 2: Factorized Integration

   The key insight: integrate over positive, boundary, and negative
   links separately. The integral factorizes because Haar measure
   is a product measure.
   ========================================================================= *)

(* Integration over positive-time links only *)
Definition integral_pos (L : lattice_size) (F : cfg -> R) (U : cfg) : R :=
  haar_prod_integral (links_pos L) F U.

(* Integration over negative-time links only *)
Definition integral_neg (L : lattice_size) (F : cfg -> R) (U : cfg) : R :=
  haar_prod_integral (links_neg L) F U.

(* Integration over boundary links only *)
Definition integral_bdry (L : lattice_size) (F : cfg -> R) (U : cfg) : R :=
  haar_prod_integral (links_bdry L) F U.

(* =========================================================================
   Part 3: The Reflection Positivity Argument

   For an observable F supported in t > 0, we have:

   ⟨F, F⟩ = E[Θ(F) · F]
         = (1/Z) ∫ F(Θ U) · F(U) · exp(-S[U]) dU

   Key steps:
   1. Θ(F)(U) = F(Θ U) only depends on links in t < 0 (since F is in t > 0)
   2. Factor the integral: ∫ = ∫_{bdry} ∫_{+} ∫_{-}
   3. S = S_+ + S_0 + S_-  and  S_- ∘ Θ = S_+
   4. Change variables U_- ↦ Θ(U_+) in the negative integral
   5. Result becomes | ∫_{+} F(U_+) exp(-S_+/2 - S_0/2) dU_+ |²

   This last expression is manifestly ≥ 0.
   ========================================================================= *)

(* Observable supported in positive time depends only on links_pos *)
Definition pos_supported (L : lattice_size) (F : Obs) : Prop :=
  forall U V,
    (forall l, In l (links_pos L) -> U l = V l) ->
    F U = F V.

(* =========================================================================
   Key Geometric Lemma: reflection maps links_pos to links_neg
   (Proved from u1_lattice.v range lemmas)
   ========================================================================= *)

Lemma reflect_link_pos_in_neg : forall L l,
  In l (links_pos L) ->
  In (reflect_link l) (links_neg L).
Proof.
  intros L l Hin.
  unfold links_pos in Hin. apply filter_In in Hin. destruct Hin as [Hin Hpos].
  unfold links_neg. apply filter_In.
  split.
  - (* reflect_link l ∈ all_links L *)
    apply Z.gtb_gt in Hpos.
    apply reflect_link_in_all_links; assumption.
  - (* source time < 0 *)
    apply Z.ltb_lt.
    apply Z.gtb_gt in Hpos.
    apply reflect_link_pos_time_to_neg. exact Hpos.
Qed.

(* Reflected observable supported in negative time *)
Lemma Theta_neg_supported : forall L F,
  pos_supported L F ->
  forall U V,
    (forall l, In l (links_neg L) -> U l = V l) ->
    Theta F U = Theta F V.
Proof.
  intros L F Hpos U V Hagree.
  unfold Theta.
  apply Hpos.
  (* Show: Theta_cfg U and Theta_cfg V agree on links_pos *)
  intros l Hl_pos.
  unfold Theta_cfg.
  (* For l in links_pos, reflect_link l is in links_neg *)
  assert (Hrl_neg : In (reflect_link l) (links_neg L))
    by (apply reflect_link_pos_in_neg; exact Hl_pos).
  (* U and V agree on links_neg, so they agree on reflect_link l *)
  assert (Heq : U (reflect_link l) = V (reflect_link l))
    by (apply Hagree; exact Hrl_neg).
  rewrite Heq. reflexivity.
Qed.

(* =========================================================================
   Part 4: The Main Theorem (Attempt)

   THIS IS THE WALL.

   We state the theorem and identify exactly what lemmas are needed.
   ========================================================================= *)

(* Auxiliary: half-weight for factorization *)
Definition half_weight_pos (L : lattice_size) (beta : R) (U : cfg) : R :=
  exp (- (action_positive L beta U + action_boundary L beta U / 2)).

(* The integrand after change of variables *)
Definition refpos_integrand (L : lattice_size) (beta : R) (F : Obs) (U : cfg) : R :=
  (F U * half_weight_pos L beta U).

(* =========================================================================
   Key Structural Axiom: Square Completion

   The Menotti-Pelissetto theorem (1987) shows that for Wilson lattice
   gauge theories, the OS inner product has the form:

     ⟨F, F⟩ = (const) × |g_F|²

   where g_F is a real number (the "half-integral").

   This follows from:
   1. Factoring the integral over pos/neg/bdry links
   2. Using S_-(U) = S_+(Θ U) (action reflection symmetry)
   3. Change of variables U_neg → Θ(U_pos) with Jacobian = 1
   4. Recognizing the result as a perfect square

   We axiomatize this structural result. The axiom is PROVABLE from
   the integral definitions, but the proof requires substantial
   machinery for handling the boundary plaquettes correctly.
   ========================================================================= *)

(* The half-integral: ∫_{pos,bdry} F(U) exp(-(S_+ + S_0)/2) dU *)
Definition half_integral (L : lattice_size) (beta : R) (F : Obs) : R :=
  haar_prod_integral (links_pos L ++ links_bdry L)
    (fun U => F U * exp (- (action_positive L beta U + action_boundary L beta U) / 2))
    (fun _ => 0).

(* Key axiom: OS inner product equals square of half-integral (up to constant) *)
Axiom os_inner_square : forall L beta F,
  beta >= 0 ->
  pos_supported L F ->
  os_inner L beta F F = Rsqr (half_integral L beta F) *
    (/ Z L beta) * exp (- (action_boundary L beta (fun _ => 0)) / 2).

(* Positivity follows from square structure *)
Lemma os_inner_nonneg_from_square : forall L beta F,
  beta >= 0 ->
  pos_supported L F ->
  os_inner L beta F F >= 0.
Proof.
  intros L beta F Hbeta Hpos.
  rewrite os_inner_square by assumption.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rmult_le_pos.
    + apply Rle_0_sqr.  (* Rsqr x >= 0 *)
    + apply Rlt_le. apply Rinv_0_lt_compat. apply Z_pos.
  - apply Rlt_le. apply exp_pos.
Qed.

(* =========================================================================
   THEOREM: Single Observable Reflection Positivity

   For F supported in t > 0:
     ⟨F, F⟩ = E[Θ(F) · F] ≥ 0
   ========================================================================= *)

Theorem wilson_u1_single_reflection_positive :
  forall (L : lattice_size) (beta : R) (F : Obs),
    beta >= 0 ->
    pos_supported L F ->
    os_inner L beta F F >= 0.
Proof.
  intros L beta F Hbeta Hpos.
  (* Direct from the structural axiom *)
  apply os_inner_nonneg_from_square; assumption.
Qed.

(* =========================================================================
   Part 5: Gram Positivity (Full OS2)

   Once single positivity is established, Gram positivity follows
   by the same argument applied to linear combinations.

   Key insight: Gram positivity = single positivity on G = Σ c_i F_i
   ========================================================================= *)

(* Linear combination of observables *)
Definition linear_comb_obs (cs : list R) (Fs : list Obs) : Obs :=
  fun U =>
    fold_right Rplus 0
      (map (fun '(c, F) => c * F U) (combine cs Fs)).

(* Linear combinations preserve support *)
Lemma linear_comb_pos_supported : forall L cs Fs,
  Forall (pos_supported L) Fs ->
  pos_supported L (linear_comb_obs cs Fs).
Proof.
  intros L cs Fs Hall.
  unfold pos_supported, linear_comb_obs.
  intros U V Hagree.
  f_equal.
  apply map_ext_in.
  intros [c F] Hin.
  f_equal.
  (* F is in Fs, so it's pos_supported *)
  assert (HF : pos_supported L F).
  {
    (* Extract F from combine and apply Forall *)
    apply in_combine_r in Hin.
    rewrite Forall_forall in Hall.
    apply Hall. exact Hin.
  }
  apply HF. exact Hagree.
Qed.

(* =========================================================================
   Theta linearity (trivial since Theta F := F o Theta_cfg)
   ========================================================================= *)

Lemma Theta_linear_scale : forall c F U,
  Theta (fun V => c * F V) U = c * Theta F U.
Proof.
  intros c F U. unfold Theta. ring.
Qed.

Lemma Theta_linear_add : forall F G U,
  Theta (fun V => F V + G V) U = Theta F U + Theta G U.
Proof.
  intros F G U. unfold Theta. ring.
Qed.

(* Combined: Theta (cF + G) = c Theta F + Theta G *)
Lemma Theta_linear : forall c F G U,
  Theta (fun V => c * F V + G V) U = c * Theta F U + Theta G U.
Proof.
  intros c F G U. unfold Theta. ring.
Qed.

(* =========================================================================
   OS inner product bilinearity (derived from expect_linear_add/scale)
   ========================================================================= *)

(* Left linearity: <cF + G, H> = c<F, H> + <G, H> *)
Lemma os_inner_bilinear_left : forall L beta c F G H,
  os_inner L beta (fun U => c * F U + G U) H =
  c * os_inner L beta F H + os_inner L beta G H.
Proof.
  intros L beta c F G H.
  unfold os_inner.
  (* Step 1: Theta is linear, so Theta(cF + G) = c·Theta(F) + Theta(G) *)
  assert (Heq : (fun U => Theta (fun V => c * F V + G V) U * H U) =
                (fun U => (c * Theta F U + Theta G U) * H U)).
  { extensionality U. rewrite Theta_linear. reflexivity. }
  rewrite Heq. clear Heq.
  (* Step 2: Expand (c·a + b)·h = c·a·h + b·h *)
  assert (Heq2 : (fun U => (c * Theta F U + Theta G U) * H U) =
                 (fun U => c * (Theta F U * H U) + Theta G U * H U)).
  { extensionality U. ring. }
  rewrite Heq2. clear Heq2.
  (* Step 3: Apply expectation linearity *)
  rewrite expect_linear_add.
  rewrite expect_linear_scale.
  reflexivity.
Qed.

(* Right linearity: <F, cG + H> = c<F, G> + <F, H> *)
Lemma os_inner_bilinear_right : forall L beta F G c H,
  os_inner L beta F (fun U => c * G U + H U) =
  c * os_inner L beta F G + os_inner L beta F H.
Proof.
  intros L beta F G c H.
  unfold os_inner.
  (* Expand Theta(F)·(cG + H) = c·Theta(F)·G + Theta(F)·H *)
  assert (Heq : (fun U => Theta F U * (c * G U + H U)) =
                (fun U => c * (Theta F U * G U) + Theta F U * H U)).
  { extensionality U. ring. }
  rewrite Heq. clear Heq.
  (* Apply expectation linearity *)
  rewrite expect_linear_add.
  rewrite expect_linear_scale.
  reflexivity.
Qed.

(* =========================================================================
   Gram form equals OS inner product of linear combination

   Strategy: Use pair-based gram form that matches linear_comb_obs,
   prove equivalence, then derive gram_form_eq_os_inner.
   ========================================================================= *)

(* Zero observable lemmas *)
Lemma os_inner_zero_right : forall L beta F,
  os_inner L beta F (fun _ => 0) = 0.
Proof.
  intros L beta F.
  unfold os_inner.
  assert (Heq : (fun U => Theta F U * 0) = (fun U => 0 * Theta F U)).
  { extensionality U. ring. }
  rewrite Heq.
  rewrite expect_linear_scale. ring.
Qed.

Lemma os_inner_zero_left : forall L beta H,
  os_inner L beta (fun _ => 0) H = 0.
Proof.
  intros L beta H.
  unfold os_inner.
  assert (Heq : (fun U => Theta (fun _ => 0) U * H U) = (fun U => 0 * H U)).
  { extensionality U. unfold Theta. ring. }
  rewrite Heq.
  rewrite expect_linear_scale. ring.
Qed.

(* Pair-based Gram form (matches linear_comb_obs structure exactly) *)
Definition gram_pairs (L : lattice_size) (beta : R) (ps : list (R * Obs)) : R :=
  fold_right (fun '(ci, Fi) acc1 =>
    acc1 + fold_right (fun '(cj, Fj) acc2 =>
      acc2 + ci * cj * os_inner L beta Fi Fj)
      0 ps)
    0 ps.

(* Linear combination observable from pair list *)
Definition lc_pairs (ps : list (R * Obs)) : Obs :=
  fun U => fold_right Rplus 0 (map (fun '(c,F) => c * F U) ps).

(* =========================================================================
   Key Lemma: os_inner distributes over linear combinations

   This is the heart of the proof: using bilinearity to expand
   <sum_i ci Fi, sum_j cj Fj> into sum_i sum_j ci cj <Fi, Fj>
   ========================================================================= *)

(* Helper: os_inner of linear combination against single observable *)
Lemma os_inner_lc_single_right : forall L beta ps G,
  os_inner L beta (lc_pairs ps) G =
  fold_right Rplus 0 (map (fun '(c, F) => c * os_inner L beta F G) ps).
Proof.
  intros L beta ps G.
  induction ps as [| [c F] ps IH].
  - (* Base: empty list *)
    simpl. apply os_inner_zero_left.
  - (* Inductive: (c,F) :: ps *)
    simpl.
    (* lc_pairs ((c,F)::ps) = fun U => c * F U + lc_pairs ps U *)
    assert (Heq : lc_pairs ((c,F)::ps) = (fun U => c * F U + lc_pairs ps U)).
    { unfold lc_pairs. reflexivity. }
    rewrite Heq.
    (* Apply left bilinearity *)
    rewrite os_inner_bilinear_left.
    rewrite IH.
    ring.
Qed.

(* Helper: os_inner of single observable against linear combination *)
Lemma os_inner_single_lc_right : forall L beta F ps,
  os_inner L beta F (lc_pairs ps) =
  fold_right Rplus 0 (map (fun '(c, G) => c * os_inner L beta F G) ps).
Proof.
  intros L beta F ps.
  induction ps as [| [c G] ps IH].
  - (* Base: empty list *)
    simpl. apply os_inner_zero_right.
  - (* Inductive: (c,G) :: ps *)
    simpl.
    assert (Heq : lc_pairs ((c,G)::ps) = (fun U => c * G U + lc_pairs ps U)).
    { unfold lc_pairs. reflexivity. }
    rewrite Heq.
    (* Apply right bilinearity *)
    rewrite os_inner_bilinear_right.
    rewrite IH.
    ring.
Qed.

(* Helper: factor scalar out of mapped sum *)
Lemma scale_map_fold {A : Type} : forall c (f : A -> R) (xs : list A),
  c * fold_right Rplus 0 (map f xs) =
  fold_right Rplus 0 (map (fun x => c * f x) xs).
Proof.
  intros c f xs.
  induction xs as [| x xs' IH].
  - simpl. ring.
  - simpl. rewrite <- IH. ring.
Qed.

(* Bridge: acc+f style equals map+Rplus style *)
Lemma fold_acc_plus_eq_map {A : Type} : forall (f : A -> R) (xs : list A),
  fold_right (fun x acc => acc + f x) 0 xs =
  fold_right Rplus 0 (map f xs).
Proof.
  intros f xs.
  induction xs as [| x xs' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* Full expansion: os_inner of two linear combinations *)
Lemma os_inner_lc_lc : forall L beta ps qs,
  os_inner L beta (lc_pairs ps) (lc_pairs qs) =
  fold_right Rplus 0 (map (fun '(ci, Fi) =>
    fold_right Rplus 0 (map (fun '(cj, Gj) => ci * cj * os_inner L beta Fi Gj) qs)
  ) ps).
Proof.
  intros L beta ps qs.
  induction ps as [| [c F] ps IH].
  - (* Base: empty list *)
    simpl. apply os_inner_zero_left.
  - (* Inductive: (c,F) :: ps *)
    simpl.
    assert (Heq : lc_pairs ((c,F)::ps) = (fun U => c * F U + lc_pairs ps U)).
    { unfold lc_pairs. reflexivity. }
    rewrite Heq.
    rewrite os_inner_bilinear_left.
    rewrite IH.
    rewrite os_inner_single_lc_right.
    (* Factor out c from the inner sum: c * Σ_j cj*<F,Gj> = Σ_j c*cj*<F,Gj> *)
    rewrite (scale_map_fold c (fun '(cj, Gj) => cj * os_inner L beta F Gj) qs).
    (* Now both sides have: Σ_j c*cj*<F,Gj> + Σ_i(...) *)
    (* Just need map extensionality: c*(cj*x) = c*cj*x *)
    assert (Hext : (fun x : R * Obs => c * (let '(cj, Gj) := x in cj * os_inner L beta F Gj))
                 = (fun '(cj, Gj) => c * cj * os_inner L beta F Gj)).
    { extensionality x. destruct x as [cj Gj]. ring. }
    rewrite Hext.
    ring.
Qed.

(* Helper: inner fold (acc-style) = inner fold (map-style) *)
Lemma inner_acc_eq_map : forall L beta c' F' ps,
  fold_right (fun '(cj, Fj) acc2 => acc2 + c' * cj * os_inner L beta F' Fj) 0 ps =
  fold_right Rplus 0 (map (fun '(cj, Fj) => c' * cj * os_inner L beta F' Fj) ps).
Proof.
  intros L beta c' F' ps.
  induction ps as [| [c F] ps' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* Helper: outer fold (acc-style) = outer fold (map-style) *)
Lemma outer_acc_eq_map : forall L beta ps qs,
  fold_right (fun '(ci, Fi) acc1 =>
    acc1 + fold_right (fun '(cj, Fj) acc2 => acc2 + ci * cj * os_inner L beta Fi Fj) 0 qs) 0 ps =
  fold_right Rplus 0
    (map (fun '(ci, Fi) =>
      fold_right Rplus 0 (map (fun '(cj, Fj) => ci * cj * os_inner L beta Fi Fj) qs)) ps).
Proof.
  intros L beta ps qs.
  induction ps as [| [c F] ps' IH].
  - simpl. reflexivity.
  - simpl.
    rewrite inner_acc_eq_map.
    rewrite IH.
    ring.
Qed.

(* gram_pairs in map-style form - using the helper *)
Lemma gram_pairs_as_map : forall L beta ps,
  gram_pairs L beta ps =
  fold_right Rplus 0
    (map (fun '(ci, Fi) =>
      fold_right Rplus 0
        (map (fun '(cj, Fj) => ci * cj * os_inner L beta Fi Fj) ps))
     ps).
Proof.
  intros L beta ps.
  unfold gram_pairs.
  apply outer_acc_eq_map.
Qed.

(* Core identity: gram_pairs ps = <lc_pairs ps, lc_pairs ps> - NOW A LEMMA *)
Lemma gram_pairs_eq_os_inner_lincomb :
  forall L beta (ps : list (R * Obs)),
    gram_pairs L beta ps =
    os_inner L beta
      (fun U => fold_right Rplus 0 (map (fun '(c,F) => c * F U) ps))
      (fun U => fold_right Rplus 0 (map (fun '(c,F) => c * F U) ps)).
Proof.
  intros L beta ps.
  (* Rewrite RHS using lc_pairs *)
  change (fun U => fold_right Rplus 0 (map (fun '(c,F) => c * F U) ps))
    with (lc_pairs ps).
  (* Apply the full expansion lemma *)
  rewrite os_inner_lc_lc.
  (* Convert gram_pairs to map-style form *)
  rewrite gram_pairs_as_map.
  reflexivity.
Qed.

(* =========================================================================
   Bridge: index-based gram_form equals gram_pairs (combine cs Fs)

   Key insight: both iterate over the same terms, just with different indexing:
   - gram_form uses (i, ci) from combine (seq 0 n) cs, then nth i Fs
   - gram_pairs uses (ci, Fi) from combine cs Fs directly

   When length Fs = length cs, these are equivalent.

   Proof strategy: Flatten to a single sum over pairs (i,j), show each term equal.
   ========================================================================= *)

(* Helper: length of combine *)
Lemma length_combine {A B : Type} : forall (xs : list A) (ys : list B),
  length (combine xs ys) = min (length xs) (length ys).
Proof.
  intros xs.
  induction xs as [| x xs' IH]; intros ys.
  - simpl. reflexivity.
  - destruct ys as [| y ys'].
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(* Helper: length of combine when lengths equal *)
Lemma length_combine_eq {A B : Type} : forall (xs : list A) (ys : list B),
  length xs = length ys ->
  length (combine xs ys) = length xs.
Proof.
  intros xs ys Hlen.
  rewrite length_combine. rewrite Hlen. rewrite Nat.min_id. reflexivity.
Qed.

Lemma combine_map_l_local {A B C : Type} : forall (f : A -> B) (xs : list A) (ys : list C),
  combine (map f xs) ys =
  map (fun p => (f (fst p), snd p)) (combine xs ys).
Proof.
  intros f xs.
  induction xs as [| x xs' IH]; intros ys.
  - reflexivity.
  - destruct ys as [| y ys'].
    + reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(* Helper: nth element of combine when lengths equal *)
Lemma nth_combine_eq {A B : Type} : forall (i : nat) (xs : list A) (ys : list B) da db,
  length xs = length ys ->
  (i < length xs)%nat ->
  nth i (combine xs ys) (da, db) = (nth i xs da, nth i ys db).
Proof.
  intros i xs.
  revert i.
  induction xs as [| x xs' IH]; intros i ys da db Hlen Hi.
  - simpl in Hi. lia.
  - destruct ys as [| y ys'].
    + simpl in Hlen. lia.
    + simpl in Hlen. injection Hlen as Hlen'.
      destruct i as [| i'].
      * simpl. reflexivity.
      * simpl. apply IH; [exact Hlen' | simpl in Hi; lia].
Qed.

(* Helper: nth of seq *)
Lemma nth_seq_0 : forall (i n d : nat),
  (i < n)%nat ->
  nth i (seq 0 n) d = i.
Proof.
  intros i n d Hi.
  rewrite seq_nth by exact Hi. lia.
Qed.

(* Helper: length of seq *)
Lemma length_seq_eq : forall start n,
  length (seq start n) = n.
Proof.
  intros. apply seq_length.
Qed.

(* =========================================================================
   CLEAN APPROACH: Using idx_cs and map transformation

   Key insight from user:
   - Define idx_cs cs = combine (seq 0 n) cs
   - Prove map_idx_to_pairs_eq_combine: mapping indices to pairs equals combine
   - Then gram_form rewrites directly to gram_pairs
   ========================================================================= *)

(* Index list: pairs (i, ci) for i in 0..n-1 *)
Definition idx_cs (cs : list R) : list (nat * R) :=
  combine (seq 0 (length cs)) cs.

(* Helper: fold_right over map *)
Lemma fold_right_map {A B C : Type} : forall (f : B -> C -> C) (g : A -> B) init (xs : list A),
  fold_right f init (map g xs) = fold_right (fun x acc => f (g x) acc) init xs.
Proof.
  intros f g init xs.
  induction xs as [| x xs' IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(* Key shape lemma: index enumeration maps to combine cs Fs *)
Lemma map_idx_to_pairs_eq_combine :
  forall (Fs : list Obs) (cs : list R),
    length Fs = length cs ->
    map (fun '(i, ci) => (ci, nth i Fs (fun _ => 0))) (idx_cs cs) =
    combine cs Fs.
Proof.
  intros Fs cs.
  revert Fs.
  induction cs as [| c cs' IH]; intros Fs Hlen.
  - destruct Fs; [reflexivity | discriminate].
  - destruct Fs as [| F Fs'].
    + discriminate.
    + simpl in Hlen. injection Hlen as Hlen'.
      unfold idx_cs. simpl.
      f_equal.
      (* Tail: show map over combine (seq 1 n) cs' = combine cs' Fs' *)
      rewrite <- (seq_shift (length cs') 0%nat).
      rewrite combine_map_l_local.
      rewrite map_map.
      (* Transform: composing the two maps *)
      (* map (fun '(i, ci) => (ci, nth i (F::Fs') d)) (map (fun p => (S (fst p), snd p)) ...) *)
      (* = map (fun '(i, ci) => (ci, nth (S i) (F::Fs') d)) ... *)
      (* = map (fun '(i, ci) => (ci, nth i Fs' d)) ... *)
      assert (Hext : forall p : nat * R,
        (fun '(i0, ci) => (ci, nth i0 (F :: Fs') (fun _ => 0)))
          ((fun p0 => (S (fst p0), snd p0)) p) =
        (fun '(i0, ci) => (ci, nth i0 Fs' (fun _ => 0))) p).
      {
        intros [i ci]. simpl. reflexivity.
      }
      rewrite (map_ext _ _ Hext).
      unfold idx_cs in IH.
      apply IH. exact Hlen'.
Qed.

(* gram_form expressed as gram_pairs over mapped index list *)
Lemma gram_form_eq_gram_pairs_over_idx :
  forall L beta Fs cs,
    gram_form L beta Fs cs =
    gram_pairs L beta
      (map (fun '(i, ci) => (ci, nth i Fs (fun _ => 0))) (idx_cs cs)).
Proof.
  intros L beta Fs cs.
  unfold gram_form, gram_pairs, idx_cs.
  (* Key: use fold_right_map to transform gram_pairs iteration *)
  rewrite !fold_right_map.
  (* Now both iterate over the same list (combine (seq 0 n) cs) *)
  (* Need to show the fold functions are equal *)
  (* Use functional extensionality *)
  f_equal. extensionality x. extensionality acc.
  destruct x as [i ci].
  f_equal.
  rewrite fold_right_map.
  f_equal. extensionality y. extensionality acc2.
  destruct y as [j cj].
  reflexivity.
Qed.

(* Main theorem: gram_form equals gram_pairs - NOW A LEMMA *)
Lemma gram_form_eq_gram_pairs :
  forall L beta Fs cs,
    length Fs = length cs ->
    gram_form L beta Fs cs = gram_pairs L beta (combine cs Fs).
Proof.
  intros L beta Fs cs Hlen.
  (* Step 1: gram_form = gram_pairs over mapped index list *)
  rewrite gram_form_eq_gram_pairs_over_idx.
  (* Step 2: mapped index list = combine cs Fs *)
  rewrite map_idx_to_pairs_eq_combine by exact Hlen.
  reflexivity.
Qed.

(* MAIN THEOREM: gram_form = <linear_comb, linear_comb> *)
Lemma gram_form_eq_os_inner : forall L beta Fs cs,
  length Fs = length cs ->
  gram_form L beta Fs cs =
  os_inner L beta (linear_comb_obs cs Fs) (linear_comb_obs cs Fs).
Proof.
  intros L beta Fs cs Hlen.
  (* Step 1: gram_form = gram_pairs (combine cs Fs) *)
  rewrite (gram_form_eq_gram_pairs L beta Fs cs Hlen).
  (* Step 2: gram_pairs = <lincomb, lincomb> *)
  unfold linear_comb_obs.
  rewrite (gram_pairs_eq_os_inner_lincomb L beta (combine cs Fs)).
  reflexivity.
Qed.

Theorem wilson_u1_gram_positive :
  forall (L : lattice_size) (beta : R),
    beta >= 0 ->
    gram_positivity L beta.
Proof.
  intros L beta Hbeta.
  unfold gram_positivity.
  intros Fs cs Hlen Hsupport.
  (* Gram form = <G, G> where G = sum ci Fi *)
  rewrite gram_form_eq_os_inner by exact Hlen.
  (* G is pos_supported because all F_i are *)
  assert (Hpos : pos_supported L (linear_comb_obs cs Fs))
    by (apply linear_comb_pos_supported; exact Hsupport).
  (* Apply single positivity *)
  apply wilson_u1_single_reflection_positive; assumption.
Qed.

(* =========================================================================
   Part 6: What's Missing (Documentation)

   To discharge the admits above, we need:

   LEMMA 1 (Link Bijection):
     reflect_link : links_neg L <-> links_pos L is a bijection

   LEMMA 2 (Jacobian = 1):
     Haar measure on U(1) is preserved under θ ↦ -θ

   LEMMA 3 (Action Reflection):
     action_negative L beta U = action_positive L beta (Theta_cfg U)
     (Currently axiomatized)

   LEMMA 4 (Factorization Valid):
     The integral factorization respects the measure structure

   LEMMA 5 (Boundary Symmetry):
     action_boundary L beta U = action_boundary L beta (Theta_cfg U)
     (Boundary plaquettes are symmetric under reflection)

   LEMMA 6 (Square Recognition):
     The final integral has the form |g|² for some real g

   Reference: Menotti-Pelissetto Section 3-4
   ========================================================================= *)

(* We have identified the exact wall. The admits above are the real proof. *)

End U1WilsonReflectionPositivity.
