Require Import List.
Require Import Arith.
Require Import Misc.
Require Import Psatz.
Require Import Star.

Definition reflc {A : Type} (R : A -> A -> Prop) x y := R x y \/ x = y.

Lemma star_1 {A : Type} (R : A -> A -> Prop) :
  forall x y, R x y -> star R x y.
Proof.
  intros x y H. econstructor; [eassumption|].
  constructor.
Qed.

Lemma reflc_star {A : Type} (R : A -> A -> Prop) :
  forall x y, reflc R x y -> star R x y.
Proof.
  intros x y [Hxy | <-]; [apply star_1; assumption|constructor].
Qed.

Definition union {A : Type} (R1 R2 : A -> A -> Prop) (x y : A) := R1 x y \/ R2 x y.

Definition compose {A : Type} (R1 R2 : A -> A -> Prop) (x y : A) := exists z, R1 x z /\ R2 z y.

Definition commuting_diamond {A : Type} (R1 R2 : A -> A -> Prop) :=
  forall x y z, R1 x y -> R2 x z -> exists w, R2 y w /\ R1 z w.

Definition strongly_commute {A : Type} (R1 R2 : A -> A -> Prop) :=
  forall x y z, R1 x y -> R2 x z -> exists w, reflc R2 y w /\ star R1 z w.

Definition commute {A : Type} (R1 R2 : A -> A -> Prop) := commuting_diamond (star R1) (star R2).

Definition diamond {A : Type} (R : A -> A -> Prop) := commuting_diamond R R.

Definition confluent {A : Type} (R : A -> A -> Prop) := diamond (star R).

Lemma commuting_diamond_symmetric {A : Type} (R1 R2 : A -> A -> Prop) :
  commuting_diamond R1 R2 -> commuting_diamond R2 R1.
Proof.
  intros H x y z H2 H1. destruct (H x z y H1 H2) as (w & Hw2 & Hw1).
  exists w. split; assumption.
Qed.

Lemma commute_symmetric {A : Type} (R1 R2 : A -> A -> Prop) :
  commute R1 R2 -> commute R2 R1.
Proof.
  intros. apply commuting_diamond_symmetric. assumption.
Qed.

Definition same_rel {A : Type} (R1 R2 : A -> A -> Prop) :=
  forall x y, R1 x y <-> R2 x y.

Lemma same_rel_refl {A : Type} (R : A -> A -> Prop) : same_rel R R.
Proof.
  intros x y. reflexivity.
Qed.

Lemma same_rel_star {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> same_rel (star R1) (star R2).
Proof.
  intros H x y.
  split; intros Hxy; eapply star_map_impl with (f := id); try eassumption; intros; apply H; assumption.
Qed.

Lemma same_rel_reflc {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> same_rel (reflc R1) (reflc R2).
Proof.
  intros H x y.
  split; intros [Hxy | ->]; try (right; reflexivity); left; apply H; assumption.
Qed.

Lemma commuting_diamond_ext {A : Type} (R1a R2a R1b R2b : A -> A -> Prop) :
    same_rel R1a R1b -> same_rel R2a R2b -> commuting_diamond R1a R2a <-> commuting_diamond R1b R2b.
Proof.
  intros Heq1 Heq2; split; intros H x y z Hxy Hxz.
  - apply Heq1 in Hxy. apply Heq2 in Hxz. destruct (H _ _ _ Hxy Hxz) as (w & Hyw & Hzw).
    exists w; split; [apply Heq2 | apply Heq1]; assumption.
  - apply Heq1 in Hxy; apply Heq2 in Hxz. destruct (H _ _ _ Hxy Hxz) as (w & Hyw & Hzw).
    exists w; split; [apply Heq2 | apply Heq1]; assumption.
Qed.

Lemma diamond_ext {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> diamond R1 <-> diamond R2.
Proof.
  intros Heq; apply commuting_diamond_ext; assumption.
Qed.

Lemma commute_ext {A : Type} (R1a R2a R1b R2b : A -> A -> Prop) :
  same_rel R1a R1b -> same_rel R2a R2b -> commute R1a R2a <-> commute R1b R2b.
Proof.
  intros Heq1 Heq2. apply commuting_diamond_ext; apply same_rel_star; assumption.
Qed.

Lemma confluent_ext {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> confluent R1 <-> confluent R2.
Proof.
  intros H; apply commute_ext; assumption.
Qed.

Lemma commuting_diamond_strongly_commutes {A : Type} (R1 R2 : A -> A -> Prop) :
  commuting_diamond R1 R2 -> strongly_commute R1 R2.
Proof.
  intros H x y z Hxy Hxz.
  destruct (H x y z Hxy Hxz) as (w & Hw2 & Hw1).
  exists w. split.
  - left. assumption.
  - apply star_1; assumption.
Qed.

Lemma strongly_commute_commutes {A : Type} (R1 R2 : A -> A -> Prop) :
  strongly_commute R1 R2 -> commute R1 R2.
Proof.
  intros H.
  assert (H1 : forall x y z, star R1 x y -> R2 x z -> exists w, reflc R2 y w /\ star R1 z w).
  - intros x y z Hxy; revert z. induction Hxy.
    + intros z Hxz. exists z. split; [left; assumption|constructor].
    + intros w Hw.
      destruct (H _ _ _ H0 Hw) as (t & [Hyt | <-] & Hwt).
      * destruct (IHHxy t Hyt) as (s & Hzs & Hts).
        exists s. split; [assumption|].
        eapply star_compose; eassumption.
      * exists z. split; [right; reflexivity|].
        eapply star_compose; eassumption.
  - intros x y z Hxy Hxz; revert y Hxy. induction Hxz; intros w Hxw.
    + exists w. split; [constructor|assumption].
    + destruct (H1 x w y Hxw H0) as (t & Hwt & Hyt).
      destruct (IHHxz t Hyt) as (s & Hts & Hzs).
      exists s. split; [|assumption].
      eapply star_compose; [|eassumption].
      apply reflc_star; assumption.
Qed.

Lemma commuting_diamond_commutes {A : Type} (R1 R2 : A -> A -> Prop) :
  commuting_diamond R1 R2 -> commute R1 R2.
Proof.
  intros H. apply strongly_commute_commutes, commuting_diamond_strongly_commutes, H.
Qed.

Lemma diamond_is_confluent {A : Type} (R : A -> A -> Prop) :
  diamond R -> confluent R.
Proof.
  apply commuting_diamond_commutes.
Qed.

Lemma between_star {A : Type} (R1 R2 : A -> A -> Prop) :
  (forall x y, R1 x y -> R2 x y) -> (forall x y, R2 x y -> star R1 x y) -> same_rel (star R1) (star R2).
Proof.
  intros H1 H2 x y. split; intros H.
  - eapply star_map_impl with (f := id); eassumption.
  - eapply star_star.
    eapply star_map_impl with (f := id); eassumption.
Qed.


Lemma commuting_confluent :
  forall {A : Type} (R1 R2 : A -> A -> Prop), confluent R1 -> confluent R2 -> commute R1 R2 -> confluent (union R1 R2).
Proof.
  intros A R1 R2 Hcf1 Hcf2 Hcomm.
  assert (H : diamond (compose (star R1) (star R2))).
  - intros x1 z1 x3 (y1 & Hxy1 & Hyz1) (x2 & Hx12 & Hx23).
    destruct (Hcf1 _ _ _ Hxy1 Hx12) as (y2 & Hy12 & Hxy2).
    destruct (Hcomm _ _ _ Hy12 Hyz1) as (z2 & Hyz2 & Hz12).
    destruct (Hcomm _ _ _ Hxy2 Hx23) as (y3 & Hy23 & Hxy3).
    destruct (Hcf2 _ _ _ Hy23 Hyz2) as (z3 & Hyz3 & Hz23).
    exists z3.
    split; [exists z2|exists y3]; split; assumption.
  - apply diamond_is_confluent in H.
    eapply diamond_ext; [|exact H]. apply between_star.
    + intros x y [H1 | H2]; [exists y|exists x]; split; econstructor; try eassumption; constructor.
    + intros x z (y & Hxy & Hyz).
      eapply star_compose; eapply star_map_impl with (f := id); try eassumption;
        intros u v Huv; [left|right]; assumption.
Qed.

