(* =========================================================================
   u1_reflection.v - Time Reflection Operator Θ for U(1)

   The reflection operator acts on configurations by:
   1. Reflecting spatial coordinates: t -> -t
   2. Inverting link variables that cross the reflection plane

   For U(1), inversion means angle negation: θ -> -θ
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Lra.
From Coq Require Import Lia.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Permutation.

Require Import U1.u1_lattice.
Require Import U1.u1_integral.
Require Import U1.u1_wilson_action.
Import U1Lattice.
Import U1Integral.
Import U1WilsonAction.

Import ListNotations.
Open Scope R_scope.
(* Use Z explicitly where needed rather than opening Z_scope globally *)

Module U1Reflection.

(* =========================================================================
   Part 1: Time Reflection on Configurations

   For U(1) gauge theory, time reflection Θ acts on configurations as:
     (Θ U)(l) = ε(l) · U(Θ⁻¹ l)

   where:
   - Θ⁻¹ l is the reflected link
   - ε(l) = -1 for time-like links (that cross t=0), +1 for space-like

   This is because time-like links get their orientation reversed,
   and in U(1), reversing orientation means taking the inverse
   (conjugate), which is angle negation.
   ========================================================================= *)

(* Reflected configuration: the key definition *)
Definition Theta_cfg (U : cfg) : cfg :=
  fun l =>
    let lr := reflect_link l in
    if orientation_flipped l then
      (- (U lr))%R   (* time-like: conjugate = negate angle *)
    else
      U lr.      (* space-like: no conjugation *)

(* Key property: Θ is an involution on configurations *)
(* Proved in u1_lattice.v: reflect_link_involutive, orientation_flipped_reflect *)

Lemma Theta_cfg_involutive : forall U l,
  Theta_cfg (Theta_cfg U) l = U l.
Proof.
  intros U l.
  unfold Theta_cfg.
  rewrite U1Lattice.reflect_link_involutive.
  rewrite U1Lattice.orientation_flipped_reflect.
  destruct (orientation_flipped l); ring.
Qed.

(* =========================================================================
   Key Geometry Lemma: reflect_link maps positive-time to negative-time
   ========================================================================= *)

(* Filter characterization of link sets *)
Definition links_pos_pred (l : link) : bool :=
  Z.gtb (site_t (link_src l)) 0.

Definition links_neg_pred (l : link) : bool :=
  Z.ltb (site_t (link_src l)) 0.

(* The key mapping lemma: reflection takes pos-time links to neg-time links *)
Lemma reflect_link_pos_to_neg : forall l,
  links_pos_pred l = true ->
  links_neg_pred (reflect_link l) = true.
Proof.
  intros l Hpos.
  unfold links_pos_pred, links_neg_pred in *.
  apply Z.ltb_lt.
  apply U1Lattice.reflect_link_pos_time_to_neg.
  apply Z.gtb_gt. exact Hpos.
Qed.

(* Key LEMMA: reflection preserves lattice membership for pos-time links *)
(* Proved from symmetric time range in u1_lattice.v *)
Lemma reflect_link_in_lattice : forall L l,
  In l (all_links L) ->
  links_pos_pred l = true ->
  In (reflect_link l) (all_links L).
Proof.
  intros L l Hin Hpos.
  unfold links_pos_pred in Hpos.
  apply Z.gtb_gt in Hpos.
  apply U1Lattice.reflect_link_in_all_links; assumption.
Qed.

(* Theta_cfg agrees on pos links when U,V agree on neg links *)
Lemma Theta_cfg_agrees_pos_from_neg : forall L U V,
  (forall l, links_neg_pred l = true -> In l (all_links L) -> U l = V l) ->
  forall l, links_pos_pred l = true -> In l (all_links L) ->
    Theta_cfg U l = Theta_cfg V l.
Proof.
  intros L U V Hneg l Hpos Hin.
  unfold Theta_cfg.
  (* reflect_link l is in neg-time *)
  assert (Hrl_neg : links_neg_pred (reflect_link l) = true)
    by (apply reflect_link_pos_to_neg; exact Hpos).
  (* reflect_link l is in all_links L *)
  assert (Hrl_in : In (reflect_link l) (all_links L))
    by (apply reflect_link_in_lattice; assumption).
  (* U and V agree on reflect_link l *)
  assert (Heq : U (reflect_link l) = V (reflect_link l))
    by (apply Hneg; assumption).
  rewrite Heq. reflexivity.
Qed.

(* =========================================================================
   Part 2: Time Reflection on Observables

   (Θ F)(U) := F(Θ U)

   where Θ U means reflecting the configuration.
   ========================================================================= *)

Definition Theta (F : Obs) : Obs :=
  fun U => F (Theta_cfg U).

Lemma Theta_involutive : forall F U,
  Theta (Theta F) U = F U.
Proof.
  intros F U.
  unfold Theta.
  f_equal.
  apply functional_extensionality.
  intros l. apply Theta_cfg_involutive.
Qed.

(* =========================================================================
   Part 3: Observable Support (Positive Time)

   An observable is supported in positive time if it only depends
   on link angles in the t > 0 half-space.
   ========================================================================= *)

(* Observable depends only on a given set of links *)
Definition supported_on (ls : list link) (F : Obs) : Prop :=
  forall U V, agrees_on ls U V -> F U = F V.

(* Supported in positive time half-space *)
Definition support_pos (L : lattice_size) (F : Obs) : Prop :=
  supported_on (links_positive L) F.

(* Alternative characterization: F is constant under changes
   at links in t ≤ 0 *)

(* =========================================================================
   Part 4: OS Inner Product

   ⟨F, G⟩ := E[Θ(F) · G]

   This is the sesquilinear form that should be positive semi-definite
   for observables supported in positive time.
   ========================================================================= *)

Definition os_inner (L : lattice_size) (beta : R) (F G : Obs) : R :=
  expect L beta (fun U => (Theta F) U * G U).

(* =========================================================================
   Part 5: Key Theorem Target - Wilson Reflection Positivity

   For U(1) Wilson lattice gauge theory:

     ∀ F supported in t > 0: ⟨F, F⟩ ≥ 0

   More generally, Gram positivity:

     ∀ F_i supported in t > 0, ∀ c_i ∈ R:
       Σ_{i,j} c_i c_j ⟨F_i, F_j⟩ ≥ 0

   THIS IS THE WALL.
   ========================================================================= *)

(* Single observable positivity - the first wall *)
Definition single_reflection_pos (L : lattice_size) (beta : R) : Prop :=
  forall F : Obs,
    support_pos L F ->
    os_inner L beta F F >= 0.

(* Gram positivity - the full wall *)
Definition gram_form (L : lattice_size) (beta : R)
    (Fs : list Obs) (cs : list R) : R :=
  fold_right (fun '(i, ci) acc1 =>
    acc1 + fold_right (fun '(j, cj) acc2 =>
      acc2 + ci * cj * os_inner L beta (nth i Fs (fun _ => 0))
                                       (nth j Fs (fun _ => 0)))
      0 (combine (seq 0 (length cs)) cs))
    0 (combine (seq 0 (length cs)) cs).

Definition gram_positivity (L : lattice_size) (beta : R) : Prop :=
  forall (Fs : list Obs) (cs : list R),
    length Fs = length cs ->
    Forall (support_pos L) Fs ->
    gram_form L beta Fs cs >= 0.

(* =========================================================================
   Part 6: Key Lemma - Action Factorization Under Reflection

   The proof of reflection positivity for Wilson theory relies on:

   1. The Wilson action factorizes across the t=0 hyperplane:
      S[U] = S_+[U] + S_0[U] + S_-[U]

   2. S_-[U] = S_+[Θ U] (reflected action equals unreflected)

   3. Plaquettes crossing t=0 contribute symmetrically.

   This structural property is what makes the integrand a perfect
   square (up to the crossing terms).
   ========================================================================= *)

(* Plaquette time predicates are defined in u1_lattice.v:
   plaq_in_positive, plaq_in_negative *)

(* Plaquette crosses the t=0 hyperplane *)
Definition plaq_crosses_zero (L : lattice_size) (p : plaquette) : bool :=
  negb (plaq_in_positive p) && negb (plaq_in_negative L p).

(* Action contribution from positive-time plaquettes *)
Definition action_positive (L : lattice_size) (beta : R) (U : cfg) : R :=
  fold_right (fun p acc =>
    if plaq_in_positive p then plaq_action beta (theta_plaq U p) + acc
    else acc)
    0 (all_plaquettes L).

(* Action contribution from negative-time plaquettes *)
Definition action_negative (L : lattice_size) (beta : R) (U : cfg) : R :=
  fold_right (fun p acc =>
    if plaq_in_negative L p then plaq_action beta (theta_plaq U p) + acc
    else acc)
    0 (all_plaquettes L).

(* Action contribution from boundary plaquettes *)
Definition action_boundary (L : lattice_size) (beta : R) (U : cfg) : R :=
  fold_right (fun p acc =>
    if plaq_crosses_zero L p then plaq_action beta (theta_plaq U p) + acc
    else acc)
    0 (all_plaquettes L).

(* Plaquette trichotomy: exactly one predicate holds *)
Lemma plaq_trichotomy : forall L p,
  (plaq_in_positive p = true /\ plaq_crosses_zero L p = false /\ plaq_in_negative L p = false) \/
  (plaq_in_positive p = false /\ plaq_crosses_zero L p = true /\ plaq_in_negative L p = false) \/
  (plaq_in_positive p = false /\ plaq_crosses_zero L p = false /\ plaq_in_negative L p = true).
Proof.
  intros L p.
  destruct (plaq_in_positive p) eqn:Hbp;
  destruct (plaq_in_negative L p) eqn:Hbn.
  - exfalso.
    unfold plaq_in_positive in Hbp.
    unfold plaq_in_negative in Hbn.
    destruct (plaq_involves_time p);
    [apply Z.gtb_gt in Hbp; apply Z.ltb_lt in Hbn; lia
    |apply Z.gtb_gt in Hbp;
     apply andb_true_iff in Hbn as [Hlt Hgt];
     apply Z.ltb_lt in Hlt;
     apply Z.gtb_gt in Hgt; lia].
  - left. split; [reflexivity|]. split.
    + unfold plaq_crosses_zero. rewrite Hbp, Hbn. reflexivity.
    + reflexivity.
  - right. right. split; [reflexivity|]. split.
    + unfold plaq_crosses_zero. rewrite Hbp, Hbn. reflexivity.
    + reflexivity.
  - right. left. split; [reflexivity|]. split.
    + unfold plaq_crosses_zero. rewrite Hbp, Hbn. reflexivity.
    + reflexivity.
Qed.

(* Helper: fold_right with conditional distributes *)
Lemma fold_right_filter_split {A : Type} (l : list A) (f : A -> R) (p1 p2 p3 : A -> bool) :
  (forall x, (p1 x = true /\ p2 x = false /\ p3 x = false) \/
             (p1 x = false /\ p2 x = true /\ p3 x = false) \/
             (p1 x = false /\ p2 x = false /\ p3 x = true)) ->
  fold_right (fun x acc => f x + acc) 0 l =
  fold_right (fun x acc => if p1 x then f x + acc else acc) 0 l +
  fold_right (fun x acc => if p2 x then f x + acc else acc) 0 l +
  fold_right (fun x acc => if p3 x then f x + acc else acc) 0 l.
Proof.
  intros Htri.
  induction l as [| a l' IH].
  - simpl. ring.
  - simpl.
    destruct (Htri a) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]];
    rewrite H1, H2, H3; rewrite IH; ring.
Qed.

(* Factorization: S = S_+ + S_0 + S_- - PROVED *)
Lemma action_factorizes : forall L beta U,
  wilson_action L beta U =
  action_positive L beta U + action_boundary L beta U + action_negative L beta U.
Proof.
  intros L beta U.
  unfold wilson_action, action_positive, action_boundary, action_negative.
  apply fold_right_filter_split.
  apply plaq_trichotomy.
Qed.


(* -------------------------------------------------------------------------
   Plaquette-level reflection machinery (minimal, boundary-first)
   ------------------------------------------------------------------------- *)

Definition theta_edges (U : cfg) (es : list (link * bool)) : R :=
  fold_right (fun (x : link * bool) acc =>
    let (l, sgn) := x in
    acc + (if sgn then U l else - U l))
    0 es.

(* Reflect a boundary edge and toggle its orientation sign when time-like.
   This compensates exactly for conjugation in Theta_cfg on reflected links. *)
Definition reflect_edge_signed (e : link * bool) : (link * bool) :=
  let (l, sgn) := e in
  (reflect_link l, xorb sgn (orientation_flipped l)).

Definition reflect_boundary (es : list (link * bool)) : list (link * bool) :=
  map reflect_edge_signed es.

Lemma theta_edges_reflect_boundary : forall U es,
  theta_edges (Theta_cfg U) (reflect_boundary es) = theta_edges U es.
Proof.
  intros U es.
  induction es as [| [l sgn] es' IH].
  - reflexivity.
  - unfold reflect_boundary. simpl.
    change (theta_edges (Theta_cfg U) (map reflect_edge_signed es'))
      with (theta_edges (Theta_cfg U) (reflect_boundary es')).
    rewrite IH.
    unfold Theta_cfg.
    rewrite U1Lattice.orientation_flipped_reflect.
    rewrite U1Lattice.reflect_link_involutive.
    destruct sgn, (orientation_flipped l); simpl; ring.
Qed.

Lemma theta_plaq_reflect_boundary : forall U p,
  theta_edges (Theta_cfg U) (reflect_boundary (plaq_boundary p)) = theta_plaq U p.
Proof.
  intros U p.
  unfold theta_plaq.
  apply theta_edges_reflect_boundary.
Qed.

Lemma plaq_action_reflect_boundary : forall beta U p,
  plaq_action beta (theta_edges (Theta_cfg U) (reflect_boundary (plaq_boundary p)))
  = plaq_action beta (theta_plaq U p).
Proof.
  intros beta U p.
  unfold plaq_action.
  rewrite theta_plaq_reflect_boundary.
  reflexivity.
Qed.

(* =========================================================================
   Action Reflection Symmetry: S_-(U) = S_+(Θ U)

   This is the key structural lemma for reflection positivity.

   Strategy: Use Permutation instead of direct list equality.
   - reflect_plaq gives a bijection between neg and pos plaquettes
   - fold_right over Permutation-equivalent lists gives equal sums
   ========================================================================= *)

(* -------------------------------------------------------------------------
   Permutation Infrastructure
   ------------------------------------------------------------------------- *)

(* fold_right of Rplus is invariant under Permutation *)
Lemma fold_right_Rplus_perm : forall (xs ys : list R),
  Permutation xs ys ->
  fold_right Rplus 0 xs = fold_right Rplus 0 ys.
Proof.
  intros xs ys Hperm.
  induction Hperm.
  - reflexivity.
  - simpl. rewrite IHHperm. reflexivity.
  - simpl. ring.
  - rewrite IHHperm1, IHHperm2. reflexivity.
Qed.

(* map preserves Permutation *)
Lemma Permutation_map {A B : Type} (f : A -> B) (xs ys : list A) :
  Permutation xs ys -> Permutation (map f xs) (map f ys).
Proof.
  intros Hperm.
  induction Hperm; simpl.
  - constructor.
  - constructor. exact IHHperm.
  - apply perm_swap.
  - eapply perm_trans; eassumption.
Qed.

(* -------------------------------------------------------------------------
   NoDup and Filter Infrastructure
   ------------------------------------------------------------------------- *)

(* Positive-time plaquettes map back into the finite-volume enumeration. *)
Lemma reflect_plaq_lattice_closed_pos : forall L p,
  In p (all_plaquettes L) ->
  plaq_in_positive p = true ->
  In (reflect_plaq p) (all_plaquettes L).
Proof.
  intros L p Hin Hpos.
  pose proof (U1Lattice.In_all_plaquettes_fwd L p Hin) as Hsite.
  pose proof (U1Lattice.In_all_plaquettes_dir L p Hin) as Hdir.
  unfold plaq_in_positive in Hpos.
  apply Z.gtb_gt in Hpos.
  unfold reflect_plaq, plaq_involves_time.
  destruct p as [s mu nu]; simpl in *.
  destruct mu, nu; simpl in *;
    try (apply U1Lattice.In_all_plaquettes_bwd;
      [apply U1Lattice.reflect_shift_site_in_lattice; [exact Hsite | exact Hpos] | exact Hdir]);
    try (apply U1Lattice.In_all_plaquettes_bwd;
      [apply U1Lattice.reflect_site_in_lattice; [exact Hsite | exact Hpos] | exact Hdir]).
Qed.

(* Filter membership characterization *)
Lemma In_filter {A : Type} (f : A -> bool) (l : list A) (x : A) :
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  induction l as [| a l' IH]; simpl.
  - split; [intros [] | intros [[] _]].
  - destruct (f a) eqn:Hfa.
    + simpl. rewrite IH. split.
      * intros [Heq | [Hin Hfx]]; subst; auto.
      * intros [[Heq | Hin] Hfx]; subst; auto.
    + rewrite IH. split.
      * intros [Hin Hfx]. split; auto.
      * intros [[Heq | Hin] Hfx]; auto. subst. congruence.
Qed.

(* map membership *)
Lemma In_map_iff_explicit {A B : Type} (f : A -> B) (l : list A) (y : B) :
  In y (map f l) <-> exists x, In x l /\ f x = y.
Proof.
  split; intro Hy.
  - apply in_map_iff in Hy.
    destruct Hy as [x [Hfx Hin]].
    exists x. split; [exact Hin | exact Hfx].
  - destruct Hy as [x [Hin Hfx]].
    apply in_map_iff.
    exists x. split; [exact Hfx | exact Hin].
Qed.

(* -------------------------------------------------------------------------
   Key Permutation: filter neg P ~ map reflect_plaq (filter pos P)

   Proof strategy (count_occ approach, avoids slow NoDup_Permutation):
   - Use Permutation_count_occ: Permutation A B <-> forall x, count_occ x A = count_occ x B
   - Show counts equal using:
     1. count_occ over filter
     2. count_occ over map with involution (injectivity)
     3. Half-flip equivalence: neg p = pos (reflect p)
     4. Membership equivalence for negative plaquettes
   ------------------------------------------------------------------------- *)

(* Decidable equality for plaquettes *)
Lemma plaquette_eq_dec : forall (p q : plaquette), {p = q} + {p <> q}.
Proof.
  intros [[t1 x1 y1 z1] mu1 nu1] [[t2 x2 y2 z2] mu2 nu2].
  destruct (Z.eq_dec t1 t2); [subst | right; intro H; inversion H; lia].
  destruct (Z.eq_dec x1 x2); [subst | right; intro H; inversion H; lia].
  destruct (Z.eq_dec y1 y2); [subst | right; intro H; inversion H; lia].
  destruct (Z.eq_dec z1 z2); [subst | right; intro H; inversion H; lia].
  destruct (U1Lattice.direction_eq_dec mu1 mu2); [subst | right; intro H; inversion H; auto].
  destruct (U1Lattice.direction_eq_dec nu1 nu2); [subst | right; intro H; inversion H; auto].
  left. reflexivity.
Defined.

(* count_occ over filter: count equals original count if predicate holds, 0 otherwise *)
Lemma count_occ_filter_pred {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (pred : A -> bool) (x : A) (l : list A) :
  count_occ eq_dec (filter pred l) x =
  if pred x then count_occ eq_dec l x else O.
Proof.
  induction l as [| a l' IH]; simpl.
  - destruct (pred x); reflexivity.
  - destruct (pred a) eqn:Hpa; simpl.
    + destruct (eq_dec a x) as [<- | Hne].
      * rewrite Hpa, IH, Hpa. reflexivity.
      * rewrite IH. reflexivity.
    + destruct (eq_dec a x) as [<- | Hne].
      * rewrite Hpa, IH, Hpa. reflexivity.
      * rewrite IH. reflexivity.
Qed.

(* Injectivity from involution *)
Lemma reflect_plaq_injective : forall p q,
  reflect_plaq p = reflect_plaq q -> p = q.
Proof.
  intros p q H.
  rewrite <- (U1Lattice.reflect_plaq_involutive p).
  rewrite <- (U1Lattice.reflect_plaq_involutive q).
  rewrite H. reflexivity.
Qed.

(* count_occ of y in map f l equals count_occ of preimage in l, for involution *)
Lemma count_occ_map_involutive (y : plaquette) (l : list plaquette) :
  count_occ plaquette_eq_dec (map reflect_plaq l) y =
  count_occ plaquette_eq_dec l (reflect_plaq y).
Proof.
  induction l as [| a l' IH]; simpl.
  - reflexivity.
  - destruct (plaquette_eq_dec (reflect_plaq a) y) as [Heq | Hne].
    + (* reflect_plaq a = y, so a = reflect_plaq y *)
      assert (Ha : a = reflect_plaq y).
      { rewrite <- Heq. symmetry. apply U1Lattice.reflect_plaq_involutive. }
      rewrite Ha.
      destruct (plaquette_eq_dec (reflect_plaq y) (reflect_plaq y)) as [_ | Habs]; [| contradiction].
      rewrite IH. reflexivity.
    + (* reflect_plaq a <> y *)
      destruct (plaquette_eq_dec a (reflect_plaq y)) as [Heq2 | Hne2].
      * (* a = reflect_plaq y, so reflect_plaq a = y - contradiction *)
        exfalso. apply Hne.
        rewrite Heq2.
        apply U1Lattice.reflect_plaq_involutive.
      * rewrite IH. reflexivity.
Qed.

(* Membership equivalence for negative plaquettes *)
Lemma neg_plaq_membership_reflect : forall L p,
  plaq_in_negative L p = true ->
  In p (all_plaquettes L) <-> In (reflect_plaq p) (all_plaquettes L).
Proof.
  intros L p Hneg.
  split; intro Hin.
  - (* -> *) exact (U1Lattice.reflect_plaq_in_lattice L p Hin Hneg).
  - (* <- *)
    (* reflect_plaq p is in all, and pos (reflect_plaq p) = true by half_flip *)
    pose proof (U1Lattice.plaq_half_flip_neg_to_pos L p Hneg) as Hpos.
    (* Apply reflect_plaq_lattice_closed_pos to reflect_plaq p *)
    pose proof (reflect_plaq_lattice_closed_pos L (reflect_plaq p) Hin Hpos) as H.
    rewrite U1Lattice.reflect_plaq_involutive in H.
    exact H.
Qed.

(* Helper: positive plaquettes don't map to positive under reflect *)
Lemma reflect_pos_not_pos : forall L p,
  In p (all_plaquettes L) ->
  plaq_in_positive p = true ->
  plaq_in_positive (reflect_plaq p) = false.
Proof.
  intros L p Hin Hpos.
  (* Reflection of positive is negative, not positive *)
  pose proof (U1Lattice.plaq_half_flip_pos_to_neg L p Hin Hpos) as Hneg_refl.
  (* Show positive and negative are disjoint *)
  destruct (plaq_in_positive (reflect_plaq p)) eqn:Hpos_refl; [| reflexivity].
  (* If both positive and negative, contradiction *)
  exfalso.
  apply Z.gtb_gt in Hpos_refl.
  unfold plaq_in_negative in Hneg_refl.
  destruct p as [[t x y z] mu nu].
  unfold reflect_plaq, plaq_involves_time, plaq_in_positive in *.
  unfold reflect_site, shift_site in *. simpl in *.
  destruct mu, nu; simpl in *;
    try (apply Z.ltb_lt in Hneg_refl; lia);
    try (apply andb_prop in Hneg_refl; destruct Hneg_refl as [Hlt Hgt];
         apply Z.ltb_lt in Hlt; apply Z.gtb_gt in Hgt; lia).
Qed.

(* The core permutation lemma - NOW PROVED via count_occ *)
Lemma perm_filter_neg_map_pos : forall L,
  Permutation (filter (plaq_in_negative L) (all_plaquettes L))
              (map reflect_plaq (filter plaq_in_positive (all_plaquettes L))).
Proof.
  intro L.
  apply (proj2 (Permutation_count_occ plaquette_eq_dec _ _)).
  intro p.
  (* LHS: count_occ (filter neg all) p *)
  rewrite count_occ_filter_pred.
  (* RHS: count_occ (map reflect (filter pos all)) p *)
  rewrite count_occ_map_involutive.
  rewrite count_occ_filter_pred.

  (* Case analysis on whether p is negative *)
  destruct (plaq_in_negative L p) eqn:Hneg.

  - (* p is negative *)
    (* LHS = count_occ all p *)
    (* For RHS: reflect p is positive (by half_flip) *)
    pose proof (U1Lattice.plaq_half_flip_neg_to_pos L p Hneg) as Hpos_refl.
    rewrite Hpos_refl.
    (* RHS = count_occ all (reflect p) *)
    (* Need: count all p = count all (reflect p) *)
    (* Both = 1 if in lattice, both = 0 if not *)
    destruct (in_dec plaquette_eq_dec p (all_plaquettes L)) as [Hin | Hnotin].
    + (* p in lattice *)
      pose proof (neg_plaq_membership_reflect L p Hneg) as [Hfwd _].
      pose proof (Hfwd Hin) as Hrefl_in.
      assert (H1 : count_occ plaquette_eq_dec (all_plaquettes L) p = 1%nat).
      { apply NoDup_count_occ'; [apply U1Lattice.all_plaquettes_nodup | exact Hin]. }
      assert (H2 : count_occ plaquette_eq_dec (all_plaquettes L) (reflect_plaq p) = 1%nat).
      { apply NoDup_count_occ'; [apply U1Lattice.all_plaquettes_nodup | exact Hrefl_in]. }
      rewrite H1, H2. reflexivity.
    + (* p not in lattice - count is 0 *)
      assert (H1 : count_occ plaquette_eq_dec (all_plaquettes L) p = 0%nat).
      { apply count_occ_not_In. exact Hnotin. }
      assert (H2 : count_occ plaquette_eq_dec (all_plaquettes L) (reflect_plaq p) = 0%nat).
      {
        apply count_occ_not_In. intro Hrefl_in.
        apply Hnotin.
        apply (neg_plaq_membership_reflect L p Hneg).
        exact Hrefl_in.
      }
      rewrite H1, H2. reflexivity.

  - (* p is not negative *)
    (* LHS = 0 *)
    (* For RHS: need to show pos (reflect p) = false, so RHS = 0 too *)
    destruct (plaq_in_positive (reflect_plaq p)) eqn:Hpos_refl.
    + (* pos (reflect p) = true *)
      (* Then reflect (reflect p) = p is negative by half_flip *)
      (* But we assumed p is not negative - contradiction? No wait... *)
      (* We need: if pos (reflect p) = true and reflect p in lattice, then p = reflect (reflect p) is negative *)
      destruct (in_dec plaquette_eq_dec (reflect_plaq p) (all_plaquettes L)) as [Hrefl_in | Hrefl_notin].
      * (* reflect p in lattice, and positive *)
        pose proof (U1Lattice.plaq_half_flip_pos_to_neg L (reflect_plaq p) Hrefl_in Hpos_refl) as Hneg_p.
        rewrite U1Lattice.reflect_plaq_involutive in Hneg_p.
        (* Now we have neg p = true, contradicting Hneg = false *)
        congruence.
      * (* reflect p not in lattice *)
        assert (H2 : count_occ plaquette_eq_dec (all_plaquettes L) (reflect_plaq p) = 0%nat).
        { apply count_occ_not_In. exact Hrefl_notin. }
        rewrite H2. reflexivity.
    + (* pos (reflect p) = false *)
      (* Both sides are 0 *)
      reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Plaquette contribution under reflection

   Key: plaq_action(theta_plaq (Theta_cfg U) (reflect_plaq p))
      = plaq_action(theta_plaq U p)
   ------------------------------------------------------------------------- *)

(* Direct plaquette transport under Θ and reflect_plaq.
   Time-like plaquettes pick up a minus sign; purely spatial plaquettes do not. *)
Lemma theta_plaq_Theta_reflect : forall U p,
  theta_plaq (Theta_cfg U) (reflect_plaq p) =
  if plaq_involves_time p then - theta_plaq U p else theta_plaq U p.
Proof.
  intros U [[t x y z] mu nu].
  unfold theta_plaq, Theta_cfg, reflect_plaq, plaq_involves_time.
  destruct mu, nu; simpl;
  unfold reflect_link, reflect_site, shift_site, orientation_flipped; simpl;
  try rewrite shift_site_comm;
  repeat rewrite Z.opp_involutive;
  repeat match goal with
         | |- context [(- (- (?a + 1) + 1))%Z] =>
             replace (- (- (a + 1) + 1))%Z with a by lia
         | |- context [(- - (?a + 1))%Z] =>
             replace (- - (a + 1))%Z with (a + 1)%Z by lia
         end;
  lra.
Qed.

(* Contribution equivalence under reflection - negative plaquette version *)
Lemma plaq_contribution_reflect_neg : forall beta U p,
  plaq_action beta (theta_plaq U p) =
  plaq_action beta (theta_plaq (Theta_cfg U) (reflect_plaq p)).
Proof.
  intros beta U p.
  rewrite theta_plaq_Theta_reflect.
  unfold plaq_action.
  destruct (plaq_involves_time p).
  - rewrite cos_neg. ring.
  - ring.
Qed.

(* Contribution equivalence - positive plaquette version (via involution) *)
Lemma plaq_contribution_reflect_pos : forall beta U q,
  plaq_in_positive q = true ->
  plaq_action beta (theta_plaq U (reflect_plaq q)) =
  plaq_action beta (theta_plaq (Theta_cfg U) q).
Proof.
  intros beta U q _.
  rewrite (plaq_contribution_reflect_neg beta U (reflect_plaq q)).
  rewrite U1Lattice.reflect_plaq_involutive.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Main Theorem: Action Reflection Symmetry
   ------------------------------------------------------------------------- *)

(* Helper: rewrite fold_right with conditional to fold over filtered list *)
Lemma fold_right_cond_filter {A : Type} (l : list A) (f : A -> R) (pred : A -> bool) :
  fold_right (fun x acc => if pred x then f x + acc else acc) 0 l =
  fold_right (fun x acc => f x + acc) 0 (filter pred l).
Proof.
  induction l as [| a l' IH]; simpl.
  - reflexivity.
  - destruct (pred a) eqn:Hpa; simpl.
    + rewrite IH. reflexivity.
    + exact IH.
Qed.

(* Unfold fold_right with additions to map *)
Lemma fold_right_add_map {A : Type} (l : list A) (f : A -> R) :
  fold_right (fun x acc => f x + acc) 0 l = fold_right Rplus 0 (map f l).
Proof.
  induction l as [| a l' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Action reflection symmetry - PROVED via Permutation *)
Lemma action_reflection_symmetry : forall L beta U,
  action_negative L beta U = action_positive L beta (Theta_cfg U).
Proof.
  intros L beta U.
  set (P := all_plaquettes L).
  set (f_neg := fun p => plaq_action beta (theta_plaq U p)).
  set (f_pos := fun q => plaq_action beta (theta_plaq (Theta_cfg U) q)).

  unfold action_negative, action_positive.
  change
    (fold_right (fun p acc => if plaq_in_negative L p then f_neg p + acc else acc) 0 P =
     fold_right (fun p acc => if plaq_in_positive p then f_pos p + acc else acc) 0 P).

  rewrite (fold_right_cond_filter P f_neg (plaq_in_negative L)).
  rewrite (fold_right_cond_filter P f_pos plaq_in_positive).
  rewrite (fold_right_add_map (filter (plaq_in_negative L) P) f_neg).
  rewrite (fold_right_add_map (filter plaq_in_positive P) f_pos).

  rewrite (fold_right_Rplus_perm
            (map f_neg (filter (plaq_in_negative L) P))
            (map f_neg (map reflect_plaq (filter plaq_in_positive P)))).
  2: {
    apply Permutation_map.
    apply perm_filter_neg_map_pos.
  }
  rewrite map_map.
  f_equal.
  apply map_ext_in.
  intros q Hq.
  apply In_filter in Hq as [_ Hpos].
  unfold f_neg, f_pos.
  apply plaq_contribution_reflect_pos.
  exact Hpos.
Qed.

End U1Reflection.
