(* =========================================================================
   ym/z2_even_holonomy.v

   Elementary mod-2 facts about Z_2 holonomies, used by the minimal-area
   lemma and by the Wilson-loop area law (Target 7e):

     - `even_holonomy`: if every link of a list M occurs an even number of
       times in M, then the product of the link variables along M is +1 for
       EVERY configuration U (each link variable is squared away);
     - `allEven`: the boolean "every link occurs an even number of times"
       and its characterisation;
     - the holonomy along the concatenated boundaries of a list of
       plaquettes is the product of their plaquette variables.

   Depends ONLY on Coq stdlib + verification.Challenge
   + verification.ChallengeZ2Gauge + rg.dup_clustering
   + ym.z2_gauge_expansion + ym.z2_polymer_gas (link-counting lemmas).
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.

Import ListNotations.
Import Challenge ChallengeZ2Gauge.
Import DupClustering Z2GaugeExpansion Z2PolymerGas.
Open Scope R_scope.

Module Z2EvenHolonomy.

  (* =======================================================================
     1. Resetting links to +1 one at a time
     ======================================================================= *)

  Fixpoint reset (U : Z2Config) (K : list Link4D) : Z2Config :=
    match K with
    | [] => U
    | l :: K' => reset (z2_update U l false) K'
    end.

  Lemma link4D_eqb_refl : forall l, link4D_eqb l l = true.
  Proof. intro l. apply link4D_eqb_spec. reflexivity. Qed.

  Lemma link4D_eqb_neq : forall l l', l <> l' -> link4D_eqb l l' = false.
  Proof.
    intros l l' H. destruct (link4D_eqb l l') eqn:E; [| reflexivity].
    apply link4D_eqb_spec in E. contradiction.
  Qed.

  Lemma reset_notin : forall K U l, ~ In l K -> reset U K l = U l.
  Proof.
    induction K as [| l0 K IH]; intros U l Hn; [reflexivity |].
    cbn [reset]. rewrite IH.
    - unfold z2_update. rewrite link4D_eqb_neq; [reflexivity |].
      intro Heq. apply Hn. left. symmetry. exact Heq.
    - intro Hin. apply Hn. right. exact Hin.
  Qed.

  Lemma reset_in : forall K U l, In l K -> reset U K l = false.
  Proof.
    induction K as [| l0 K IH]; intros U l Hin; [contradiction |].
    cbn [reset].
    destruct (memb link4D_eqb l K) eqn:Hm.
    - apply IH. apply (memb_In link4D_eqb link4D_eqb_spec). exact Hm.
    - apply (memb_false link4D_eqb link4D_eqb_spec) in Hm.
      destruct Hin as [Heq | Hin]; [| contradiction].
      subst l0. rewrite (reset_notin K _ l Hm). unfold z2_update.
      rewrite link4D_eqb_refl. reflexivity.
  Qed.

  Lemma z2_sign_pm1 : forall b, z2_sign b = 1 \/ z2_sign b = -1.
  Proof. intros []; cbn [z2_sign]; [right | left]; reflexivity. Qed.

  Lemma pm1_pow_even : forall s n, (s = 1 \/ s = -1) -> Nat.even n = true -> s ^ n = 1.
  Proof.
    intros s n [Hs | Hs] He; subst s.
    - apply pow1.
    - rewrite pow_m1, He. reflexivity.
  Qed.

  Lemma holonomy_reset : forall K U M,
    (forall l, In l K -> Nat.even (link4D_count l M) = true) ->
    z2_holonomy (reset U K) M = z2_holonomy U M.
  Proof.
    induction K as [| l0 K IH]; intros U M HK; [reflexivity |].
    cbn [reset]. rewrite IH.
    - rewrite holonomy_update.
      rewrite (pm1_pow_even (z2_sign false * z2_sign (U l0)) (link4D_count l0 M)).
      + ring.
      + cbn [z2_sign]. destruct (z2_sign_pm1 (U l0)) as [H | H]; rewrite H;
          [left | right]; ring.
      + apply HK. left. reflexivity.
    - intros l Hl. apply HK. right. exact Hl.
  Qed.

  (* =======================================================================
     2. Even multiplicities force holonomy +1
     ======================================================================= *)

  Theorem even_holonomy : forall U M,
    (forall l, In l M -> Nat.even (link4D_count l M) = true) ->
    z2_holonomy U M = 1.
  Proof.
    intros U M H. rewrite <- (holonomy_reset M U M H).
    rewrite (holonomy_local (reset U M) (fun _ => false) M).
    - apply holonomy_base.
    - intros l Hl. apply reset_in. exact Hl.
  Qed.

  (* every link of M occurs an even number of times in M *)
  Definition allEven (M : list Link4D) : bool :=
    forallb (fun l => Nat.even (link4D_count l M)) M.

  Lemma allEven_iff : forall M,
    allEven M = true <-> forall l, Nat.even (link4D_count l M) = true.
  Proof.
    intro M. unfold allEven. rewrite forallb_forall. split.
    - intros H l. destruct (memb link4D_eqb l M) eqn:Hm.
      + apply (memb_In link4D_eqb link4D_eqb_spec) in Hm. exact (H l Hm).
      + apply (memb_false link4D_eqb link4D_eqb_spec) in Hm.
        rewrite (count_zero l M Hm). reflexivity.
    - intros H l _. exact (H l).
  Qed.

  Lemma allEven_holonomy : forall U M, allEven M = true -> z2_holonomy U M = 1.
  Proof.
    intros U M H. apply even_holonomy. intros l _. exact (proj1 (allEven_iff M) H l).
  Qed.

  (* =======================================================================
     3. Holonomy along the boundaries of a list of plaquettes
     ======================================================================= *)

  Lemma holonomy_flat_map : forall U (S : list Plaq4D),
    z2_holonomy U (flat_map plaq4D_links S) = rprod S (z2_plaq U).
  Proof.
    intros U S. induction S as [| p S IH].
    - reflexivity.
    - cbn [flat_map]. rewrite holonomy_app, IH, rprod_cons. reflexivity.
  Qed.

  (* a product of signs equal to -1 contains a factor -1 *)
  Lemma rprod_minus_one_exists : forall {A : Type} (f : A -> R) (l : list A),
    (forall x, In x l -> f x = 1 \/ f x = -1) ->
    rprod l f = -1 ->
    exists x, In x l /\ f x = -1.
  Proof.
    intros A f l. induction l as [| a l IH]; intros Hpm Hprod.
    - rewrite rprod_nil in Hprod. lra.
    - rewrite rprod_cons in Hprod.
      destruct (Hpm a (or_introl eq_refl)) as [Ha | Ha].
      + rewrite Ha in Hprod.
        destruct IH as [x [Hx Hfx]].
        * intros x Hx. apply Hpm. right. exact Hx.
        * lra.
        * exists x. split; [right; exact Hx | exact Hfx].
      + exists a. split; [left; reflexivity | exact Ha].
  Qed.

End Z2EvenHolonomy.
