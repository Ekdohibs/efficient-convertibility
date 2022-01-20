Require Import List.
Require Import Arith.
Require Import Misc.
Require Import Psatz.

Definition curry {A B C : Type} (f : A * B -> C) x y := f (x, y).
Definition uncurry {A B C : Type} (f : A -> B -> C) '(x, y) := f x y.
Definition flip {A B C : Type} (f : A -> B -> C) x y := f y x.
Definition union {A B : Type} (R1 R2 : A -> B -> Prop) x y := R1 x y \/ R2 x y.
Definition compose {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) x y := exists z, R1 x z /\ R2 z y.

Definition same_rel {A B : Type} (R1 R2 : A -> B -> Prop) :=
  forall x y, R1 x y <-> R2 x y.

Lemma same_rel_refl {A : Type} (R : A -> A -> Prop) : same_rel R R.
Proof.
  intros x y. reflexivity.
Qed.

Lemma same_rel_sym {A B : Type} (R1 R2 : A -> B -> Prop) :
  same_rel R1 R2 -> same_rel R2 R1.
Proof.
  intros H x y; split; intros H1; apply H; assumption.
Qed.

Lemma same_rel_trans {A B : Type} (R1 R2 R3 : A -> B -> Prop) :
  same_rel R1 R2 -> same_rel R2 R3 -> same_rel R1 R3.
Proof.
  intros H1 H2 x y; split; intros H3; [apply H2, H1, H3|apply H1, H2, H3].
Qed.

Lemma flip_flip :
  forall (A B : Type) (R : A -> B -> Prop), same_rel (flip (flip R)) R.
Proof.
  intros A R x y. reflexivity.
Qed.


(* Reflexive closure *)

Definition reflc {A : Type} (R : A -> A -> Prop) x y := R x y \/ x = y.

Lemma same_rel_reflc {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> same_rel (reflc R1) (reflc R2).
Proof.
  intros H x y.
  split; intros [Hxy | ->]; try (right; reflexivity); left; apply H; assumption.
Qed.


(* Symmetric closure *)
Definition symc {A : Type} (R : A -> A -> Prop) := union R (flip R).

Lemma symc_sym {A : Type} (R : A -> A -> Prop) :
  forall x y, symc R x y -> symc R y x.
Proof.
  intros x y [H | H]; [right | left]; assumption.
Qed.


(* Transitive reflexive closure *)

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star R x x
| star_step : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_1 {A : Type} (R : A -> A -> Prop) :
  forall x y, R x y -> star R x y.
Proof.
  intros x y H. econstructor; [eassumption|].
  constructor.
Qed.

Lemma star_compose :
  forall (A : Type) (R : A -> A -> Prop) x y z, star R x y -> star R y z -> star R x z.
Proof.
  intros A R x y z H. induction H.
  - intros; assumption.
  - intros; econstructor; [eassumption | firstorder].
Qed.

Lemma star_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y, RA x y -> RB (f x) (f y)) -> forall x y, star RA x y -> star RB (f x) (f y).
Proof.
  intros A B RA RB f HR x y H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma star_impl :
  forall (A : Type) (R1 R2 : A -> A -> Prop),
    (forall x y, R1 x y -> R2 x y) -> forall x y, star R1 x y -> star R2 x y.
Proof.
  intros A R1 R2 H x y Hxy. eapply star_map_impl with (f := id); eassumption.
Qed.

Lemma same_rel_star {A : Type} (R1 R2 : A -> A -> Prop) :
  same_rel R1 R2 -> same_rel (star R1) (star R2).
Proof.
  intros H x y.
  split; intros Hxy; eapply star_impl; try eassumption; intros; apply H; assumption.
Qed.

Lemma flip_star :
  forall (A : Type) (R : A -> A -> Prop) x y, star (flip R) x y -> star R y x.
Proof.
  intros A R x y H. induction H.
  - apply star_refl.
  - eapply star_compose; [eassumption|]. apply star_1; assumption.
Qed.

Lemma flip_star_iff :
  forall (A : Type) (R : A -> A -> Prop), same_rel (star (flip R)) (flip (star R)).
Proof.
  intros A R x y; split; intros H.
  - apply flip_star. assumption.
  - eapply flip_star, same_rel_star; [|eassumption]. apply flip_flip.
Qed.

Lemma star_star :
  forall (A : Type) (R : A -> A -> Prop), forall x y, star (star R) x y -> star R x y.
Proof.
  intros A R x y H. induction H.
  - constructor.
  - eapply star_compose; eauto.
Qed.

Lemma star_induction_rev :
  forall {A : Type} (R : A -> A -> Prop) (P : A -> Prop) (x : A),
    P x -> (forall y z, P y -> R y z -> P z) -> (forall y, star R x y -> P y).
Proof.
  intros A R P x HPx HPind y Hy. revert HPx.
  induction Hy; firstorder.
Qed.

Lemma star_same :
  forall (A : Type) (R : A -> A -> Prop) t1 t2, t1 = t2 -> star R t1 t2.
Proof.
  intros A R t1 t2 ->. constructor.
Qed.

Lemma star_sym {A : Type} (R : A -> A -> Prop) (Hsym : forall x y, R x y -> R y x) :
  forall x y, star R x y -> star R y x.
Proof.
  intros x y H; induction H.
  - apply star_refl.
  - eapply star_compose; [eassumption|apply star_1, Hsym; assumption].
Qed.

Lemma reflc_star {A : Type} (R : A -> A -> Prop) :
  forall x y, reflc R x y -> star R x y.
Proof.
  intros x y [Hxy | <-]; [apply star_1; assumption|constructor].
Qed.

Lemma star_reflc {A : Type} (R : A -> A -> Prop) :
  same_rel (star R) (star (reflc R)).
Proof.
  intros x y. split; intros H.
  - eapply star_impl; [|eassumption].
    intros; left; assumption.
  - induction H.
    + constructor.
    + destruct H as [H | ->].
      * econstructor; eassumption.
      * assumption.
Qed.

(* Transitive closure *)

Inductive plus {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| plus_1 : forall x y, R x y -> plus R x y
| plus_S : forall x y z, R x y -> plus R y z -> plus R x z.

Lemma plus_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y, RA x y -> RB (f x) (f y)) -> forall x y, plus RA x y -> plus RB (f x) (f y).
Proof.
  intros A B RA RB f HR x y H. induction H.
  - apply plus_1; auto.
  - eapply plus_S; eauto.
Qed.

Lemma plus_impl :
  forall (A : Type) (R1 R2 : A -> A -> Prop),
    (forall x y, R1 x y -> R2 x y) -> forall x y, plus R1 x y -> plus R2 x y.
Proof.
  intros A R1 R2 H x y Hxy. eapply plus_map_impl with (f := id); eassumption.
Qed.

Lemma same_rel_plus :
  forall (A : Type) (R1 R2 : A -> A -> Prop), same_rel R1 R2 -> same_rel (plus R1) (plus R2).
Proof.
  intros A R1 R2 H x y. split; intros Hplus; eapply plus_impl; try eassumption; intros; apply H; assumption.
Qed.

Lemma plus_star :
  forall (A : Type) (R : A -> A -> Prop) x y, plus R x y -> star R x y.
Proof.
  intros A R x y H; induction H.
  - apply star_1. assumption.
  - econstructor; eassumption.
Qed.

Lemma plus_star_iff :
  forall (A : Type) (R : A -> A -> Prop), same_rel (plus R) (compose R (star R)).
Proof.
  intros A R x y; split; intros H.
  - inversion H; subst.
    + exists y; split; [assumption|apply star_refl].
    + exists y0. split; [assumption|apply plus_star; assumption].
  - destruct H as (z & Hxz & Hzy).
    revert x Hxz; induction Hzy; intros w Hw.
    + apply plus_1; assumption.
    + eapply plus_S; [eassumption|apply IHHzy; assumption].
Qed.

Lemma plus_compose_star_left :
  forall (A : Type) (R : A -> A -> Prop) x y z, star R x y -> plus R y z -> plus R x z.
Proof.
  intros A R x y z H1 H2; induction H1; [assumption|].
  econstructor; [eassumption|].
  apply IHstar; assumption.
Qed.

Lemma flip_plus :
  forall (A : Type) (R : A -> A -> Prop) x y, plus (flip R) x y -> plus R y x.
Proof.
  intros A R x y H. induction H.
  - apply plus_1. assumption.
  - eapply plus_compose_star_left; [eapply plus_star; eassumption|].
    apply plus_1. assumption.
Qed.

Lemma flip_plus_iff :
  forall (A : Type) (R : A -> A -> Prop), same_rel (plus (flip R)) (flip (plus R)).
Proof.
  intros A R x y; split; intros H.
  - apply flip_plus. assumption.
  - eapply flip_plus, same_rel_plus; [|eassumption]. apply flip_flip.
Qed.

Lemma plus_compose_star_right :
  forall (A : Type) (R : A -> A -> Prop) x y z, plus R x y -> star R y z -> plus R x z.
Proof.
  intros A R x y z H1 H2.
  apply flip_plus_iff.
  eapply plus_compose_star_left; [|apply flip_plus_iff; eassumption].
  apply flip_star in H2. eassumption.
Qed.


(* Transitive symmetric reflexive closure *)

Definition convertible {A : Type} (R : A -> A -> Prop) := star (symc R).

Lemma convertible_refl {A : Type} (R : A -> A -> Prop) x : convertible R x x.
Proof.
  intros; apply star_refl.
Qed.

Lemma convertible_sym {A : Type} (R : A -> A -> Prop) :
  forall x y, convertible R x y -> convertible R y x.
Proof.
  apply star_sym, symc_sym.
Qed.

Lemma common_reduce_convertible :
  forall (A : Type) (R : A -> A -> Prop) x y z, star R x z -> star R y z -> convertible R x y.
Proof.
  intros A R x y z Hxz Hyz.
  eapply star_compose.
  - eapply star_impl; [|eassumption]. intros; left; assumption.
  - eapply star_impl; [|apply flip_star_iff; eassumption]. intros; right; assumption.
Qed.



(* Confluence *)

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
  - eapply star_impl; eassumption.
  - eapply star_star.
    eapply star_impl; eassumption.
Qed.

Definition weak_diamond {A : Type} (R : A -> A -> Prop) :=
  forall x y z, R x y -> R x z -> y = z \/ (exists w, R y w /\ R z w).

Lemma weak_diamond_diamond_reflc {A : Type} (R : A -> A -> Prop) :
  weak_diamond R -> diamond (reflc R).
Proof.
  intros HD x y z [Hxy | <-] [Hxz | <-].
  - specialize (HD x y z Hxy Hxz).
    destruct HD as [-> | (w & Hyw & Hzw)].
    + exists z. split; right; reflexivity.
    + exists w. split; left; assumption.
  - exists y. split; [right; reflexivity|left; assumption].
  - exists z. split; [left; assumption|right; reflexivity].
  - exists x. split; right; reflexivity.
Qed.

Lemma weak_diamond_confluent {A : Type} (R : A -> A -> Prop) :
  weak_diamond R -> confluent R.
Proof.
  intros H.
  apply weak_diamond_diamond_reflc, diamond_is_confluent in H.
  eapply diamond_ext; [|eassumption].
  apply star_reflc.
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
      eapply star_compose; eapply star_impl; try eassumption;
        intros u v Huv; [left|right]; assumption.
Qed.


Lemma convertible_confluent_common_reduce :
  forall (A : Type) (R : A -> A -> Prop),
    confluent R -> forall x y, convertible R x y -> exists z, star R x z /\ star R y z.
Proof.
  intros A R Hconf x y Hconv. induction Hconv.
  - exists x. split; constructor.
  - destruct IHHconv as (w & Hyw & Hzw).
    destruct H as [Hxy | Hyx].
    + exists w. split; [|assumption]. econstructor; eassumption.
    + destruct (Hconf y x w) as (t & Hxt & Hwt).
      * apply star_1. assumption.
      * assumption.
      * exists t. split; [assumption|].
        eapply star_compose; eassumption.
Qed.


(* Rewriting one element of a list *)

Inductive step_one {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| step_one_step : forall x y L, R x y -> step_one R (x :: L) (y :: L)
| step_one_cons : forall x L1 L2, step_one R L1 L2 -> step_one R (x :: L1) (x :: L2).

Lemma step_one_decompose :
  forall (A : Type) (R : A -> A -> Prop) l1 l2, step_one R l1 l2 <-> exists l3 l4 x y, l1 = l3 ++ x :: l4 /\ l2 = l3 ++ y :: l4 /\ R x y.
Proof.
  intros A R l1 l2. split; intros H.
  - induction H.
    + exists nil, L, x, y. tauto.
    + destruct IHstep_one as (l3 & l4 & a & b & H1); exists (x :: l3), l4, a, b.
      simpl; intuition congruence.
  - destruct H as (l3 & l4 & x & y & -> & -> & H).
    induction l3; simpl; constructor; assumption.
Qed.

Lemma step_one_star :
  forall (A : Type) (R : A -> A -> Prop), same_rel (star (step_one R)) (Forall2 (star R)).
Proof.
  intros A R x y. split; intros H.
  - induction H.
    + apply Forall2_map_same, Forall_True. intros; apply star_refl.
    + enough (Forall2 (star R) x y).
      * apply Forall2_comm in H1.
        eapply Forall3_select23, Forall3_impl; [|eapply Forall3_from_Forall2; eassumption].
        intros ? ? ? [? ?]; eapply star_compose; simpl in *; eassumption.
      * clear H0 IHstar. induction H; constructor.
        -- apply star_1; assumption.
        -- apply Forall2_map_same, Forall_True. intros; apply star_refl.
        -- apply star_refl.
        -- assumption.
  - induction H.
    + apply star_refl.
    + eapply star_compose; [|eapply star_map_impl with (f := fun l => y :: l); [|eassumption]; intros; constructor; assumption].
      eapply star_map_impl with (f := fun x => x :: l); [|eassumption].
      intros; constructor; assumption.
Qed.

Lemma step_one_impl_transparent :
  forall (A : Type) (R1 R2 : A  -> A -> Prop) L1 L2, (forall x y, R1 x y -> R2 x y) -> step_one R1 L1 L2 -> step_one R2 L1 L2.
Proof.
  intros A R1 R2 L1 L2 H1 H2; induction H2; constructor; [|assumption].
  apply H1, H.
Defined.

Lemma step_one_impl_strong_transparent :
  forall (A : Type) (R1 R2 : A -> A -> Prop) L1 L2, (forall x y, R1 x y -> R2 x y) -> step_one R1 L1 L2 -> step_one (fun x y => R1 x y /\ R2 x y) L1 L2.
Proof.
  intros A R1 R2 L1 L2 H1 H2. eapply step_one_impl_transparent; [|eassumption].
  intros; split; [assumption|apply H1; assumption].
Defined.
