Section Ind1.

Context {A : Type}.
Context (G : (A -> Prop) -> (A -> Prop)).
Context (P : A -> Prop).

Implicit Types Q R : A -> Prop.

Definition is_ind1 :=
  (forall Q R, (forall x, Q x -> R x) -> forall x, G Q x -> G R x) /\ (forall Q, (forall x, G Q x -> Q x) -> forall x, P x -> Q x) /\ (forall x, G P x -> P x).

Hypothesis Hind : is_ind1.

Let is_positive := proj1 Hind.
Definition is_positive1 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved1 Q :=
  forall x, G (fun x => P x /\ Q x) x -> Q x.
Definition preserved_with_inv1 Q R :=
  forall x, G (fun x => P x /\ Q x /\ R x) x -> R x -> Q x.
Definition preserved_down1 Q :=
  forall x R, G (fun x => P x /\ R x) x -> Q x -> G (fun x => P x /\ Q x /\ R x) x.

Lemma preserved1_rec :
  forall Q, preserved1 Q -> forall x, P x -> Q x.
Proof.
  intros Q HQ.
  enough (H : forall x, P x -> P x /\ Q x) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv1_rec :
  forall Q R, preserved_down1 R -> preserved_with_inv1 Q R -> forall x, P x -> R x -> Q x.
Proof.
  intros Q R H1 H2. refine (preserved1_rec (fun x => R x -> Q x) _).
  intros x H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x => P x /\ R x /\ (R x -> Q x)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind1_inv :
  forall x, P x -> G P x.
Proof.
  apply preserved1_rec. intros x H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind1.

Ltac prove_ind1 :=
  unfold is_ind1;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x Hx; destruct Hx; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x Hx; constructor; assumption];
    intros Q HQ; fix H 2; intros x Hx;
    destruct Hx as [x1 Hx];
    apply (Hmap _ Q) in Hx; [apply HQ; assumption|assumption]
  end.


Section Ind2.

Context {A : Type}.
Context {B : A -> Type}.
Context (G : (forall x, B x -> Prop) -> (forall x, B x -> Prop)).
Context (P : forall x, B x -> Prop).

Implicit Types Q R : forall x, B x -> Prop.

Definition is_ind2 :=
  (forall Q R, (forall x y, Q x y -> R x y) -> forall x y, G Q x y -> G R x y) /\
  (forall Q, (forall x y, G Q x y -> Q x y) -> forall x y, P x y -> Q x y) /\
  (forall x y, G P x y -> P x y).

Hypothesis Hind : is_ind2.

Let is_positive := proj1 Hind.
Definition is_positive2 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved2 Q :=
  forall x y, G (fun x y => P x y /\ Q x y) x y -> Q x y.
Definition preserved_with_inv2 Q R :=
  forall x y, G (fun x y => P x y /\ Q x y /\ R x y) x y -> R x y -> Q x y.
Definition preserved_down2 Q :=
  forall x y R, G (fun x y => P x y /\ R x y) x y -> Q x y -> G (fun x y => P x y /\ Q x y /\ R x y) x y.

Lemma preserved2_rec :
  forall Q, preserved2 Q -> forall x y, P x y -> Q x y.
Proof.
  intros Q HQ.
  enough (H : forall x y, P x y -> P x y /\ Q x y) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv2_rec :
  forall Q R, preserved_down2 R -> preserved_with_inv2 Q R -> forall x y, P x y -> R x y -> Q x y.
Proof.
  intros Q R H1 H2. refine (preserved2_rec (fun x y => R x y -> Q x y) _).
  intros x y H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x y => P x y /\ R x y /\ (R x y -> Q x y)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind2_inv :
  forall x y, P x y -> G P x y.
Proof.
  apply preserved2_rec. intros x y H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind2.

Ltac prove_ind2 :=
  unfold is_ind2;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x y Hxy; destruct Hxy; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x y Hxy; constructor; assumption];
    intros Q HQ; fix H 3; intros x y Hxy;
    destruct Hxy as [x1 y1 Hxy];
    apply (Hmap _ Q) in Hxy; [apply HQ; assumption|assumption]
  end.


Section Ind3.

Context {A : Type}.
Context {B : A -> Type}.
Context {C : forall x, B x -> Type}.
Context (G : (forall x y, C x y -> Prop) -> (forall x y, C x y -> Prop)).
Context (P : forall x y, C x y -> Prop).

Implicit Types Q R : forall x y, C x y -> Prop.

Definition is_ind3 :=
  (forall Q R, (forall x y z, Q x y z -> R x y z) -> forall x y z, G Q x y z -> G R x y z) /\
  (forall Q, (forall x y z, G Q x y z -> Q x y z) -> forall x y z, P x y z -> Q x y z) /\
  (forall x y z, G P x y z -> P x y z).

Hypothesis Hind : is_ind3.

Let is_positive := proj1 Hind.
Definition is_positive3 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved3 Q :=
  forall x y z, G (fun x y z => P x y z /\ Q x y z) x y z -> Q x y z.
Definition preserved_with_inv3 Q R :=
  forall x y z, G (fun x y z => P x y z /\ Q x y z /\ R x y z) x y z -> R x y z -> Q x y z.
Definition preserved_down3 Q :=
  forall x y z R, G (fun x y z => P x y z /\ R x y z) x y z -> Q x y z -> G (fun x y z => P x y z /\ Q x y z /\ R x y z) x y z.

Lemma preserved3_rec :
  forall Q, preserved3 Q -> forall x y z, P x y z -> Q x y z.
Proof.
  intros Q HQ.
  enough (H : forall x y z, P x y z -> P x y z /\ Q x y z) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv3_rec :
  forall Q R, preserved_down3 R -> preserved_with_inv3 Q R -> forall x y z, P x y z -> R x y z -> Q x y z.
Proof.
  intros Q R H1 H2. refine (preserved3_rec (fun x y z => R x y z -> Q x y z) _).
  intros x y z H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x y z => P x y z /\ R x y z /\ (R x y z -> Q x y z)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind3_inv :
  forall x y z, P x y z -> G P x y z.
Proof.
  apply preserved3_rec. intros x y z H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind3.

Ltac prove_ind3 :=
  unfold is_ind3;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x y z Hxyz; destruct Hxyz; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x y z Hxyz; constructor; assumption];
    intros Q HQ; fix H 4; intros x y z Hxyz;
    destruct Hxyz as [x1 y1 z1 Hxyz];
    apply (Hmap _ Q) in Hxyz; [apply HQ; assumption|assumption]
  end.


Section Ind4.

Context {A : Type}.
Context {B : A -> Type}.
Context {C : forall x, B x -> Type}.
Context {D : forall x y, C x y -> Type}.
Context (G : (forall x y z, D x y z -> Prop) -> (forall x y z, D x y z -> Prop)).
Context (P : forall x y z, D x y z -> Prop).

Implicit Types Q R : forall x y z, D x y z -> Prop.

Definition is_ind4 :=
  (forall Q R, (forall x y z u, Q x y z u -> R x y z u) -> forall x y z u, G Q x y z u -> G R x y z u) /\
  (forall Q, (forall x y z u, G Q x y z u -> Q x y z u) -> forall x y z u, P x y z u -> Q x y z u) /\
  (forall x y z u, G P x y z u -> P x y z u).

Hypothesis Hind : is_ind4.

Let is_positive := proj1 Hind.
Definition is_positive4 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved4 Q :=
  forall x y z u, G (fun x y z u => P x y z u /\ Q x y z u) x y z u -> Q x y z u.
Definition preserved_with_inv4 Q R :=
  forall x y z u, G (fun x y z u => P x y z u /\ Q x y z u /\ R x y z u) x y z u -> R x y z u -> Q x y z u.
Definition preserved_down4 Q :=
  forall x y z u R, G (fun x y z u => P x y z u /\ R x y z u) x y z u -> Q x y z u -> G (fun x y z u => P x y z u /\ Q x y z u /\ R x y z u) x y z u.

Lemma preserved4_rec :
  forall Q, preserved4 Q -> forall x y z u, P x y z u -> Q x y z u.
Proof.
  intros Q HQ.
  enough (H : forall x y z u, P x y z u -> P x y z u /\ Q x y z u) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv4_rec :
  forall Q R, preserved_down4 R -> preserved_with_inv4 Q R -> forall x y z u, P x y z u -> R x y z u -> Q x y z u.
Proof.
  intros Q R H1 H2. refine (preserved4_rec (fun x y z u => R x y z u -> Q x y z u) _).
  intros x y z u H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x y z u => P x y z u /\ R x y z u /\ (R x y z u -> Q x y z u)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind4_inv :
  forall x y z u, P x y z u -> G P x y z u.
Proof.
  apply preserved4_rec. intros x y z u H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind4.

Ltac prove_ind4 :=
  unfold is_ind4;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x y z u Hxyzu; destruct Hxyzu; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x y z u Hxyzu; constructor; assumption];
    intros Q HQ; fix H 5; intros x y z u Hxyzu;
    destruct Hxyzu as [x1 y1 z1 u1 Hxyzu];
    apply (Hmap _ Q) in Hxyzu; [apply HQ; assumption|assumption]
  end.


Section Ind5.

Context {A : Type}.
Context {B : A -> Type}.
Context {C : forall x, B x -> Type}.
Context {D : forall x y, C x y -> Type}.
Context {E : forall x y z, D x y z -> Type}.
Context (G : (forall x y z u, E x y z u -> Prop) -> (forall x y z u, E x y z u -> Prop)).
Context (P : forall x y z u, E x y z u -> Prop).

Implicit Types Q R : forall x y z u, E x y z u -> Prop.

Definition is_ind5 :=
  (forall Q R, (forall x y z u v, Q x y z u v -> R x y z u v) -> forall x y z u v, G Q x y z u v -> G R x y z u v) /\
  (forall Q, (forall x y z u v, G Q x y z u v -> Q x y z u v) -> forall x y z u v, P x y z u v -> Q x y z u v) /\
  (forall x y z u v, G P x y z u v -> P x y z u v).

Hypothesis Hind : is_ind5.

Let is_positive := proj1 Hind.
Definition is_positive5 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved5 Q :=
  forall x y z u v, G (fun x y z u v => P x y z u v /\ Q x y z u v) x y z u v -> Q x y z u v.
Definition preserved_with_inv5 Q R :=
  forall x y z u v, G (fun x y z u v => P x y z u v /\ Q x y z u v /\ R x y z u v) x y z u v -> R x y z u v -> Q x y z u v.
Definition preserved_down5 Q :=
  forall x y z u v R, G (fun x y z u v => P x y z u v /\ R x y z u v) x y z u v -> Q x y z u v -> G (fun x y z u v => P x y z u v /\ Q x y z u v /\ R x y z u v) x y z u v.

Lemma preserved5_rec :
  forall Q, preserved5 Q -> forall x y z u v, P x y z u v -> Q x y z u v.
Proof.
  intros Q HQ.
  enough (H : forall x y z u v, P x y z u v -> P x y z u v /\ Q x y z u v) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv5_rec :
  forall Q R, preserved_down5 R -> preserved_with_inv5 Q R -> forall x y z u v, P x y z u v -> R x y z u v -> Q x y z u v.
Proof.
  intros Q R H1 H2. refine (preserved5_rec (fun x y z u v => R x y z u v -> Q x y z u v) _).
  intros x y z u v H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x y z u v => P x y z u v /\ R x y z u v /\ (R x y z u v -> Q x y z u v)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind5_inv :
  forall x y z u v, P x y z u v -> G P x y z u v.
Proof.
  apply preserved5_rec. intros x y z u v H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind5.

Ltac prove_ind5 :=
  unfold is_ind5;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x y z u v Hxyzuv; destruct Hxyzuv; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x y z u v Hxyzuv; constructor; assumption];
    intros Q HQ; fix H 6; intros x y z u v Hxyzuv;
    destruct Hxyzuv as [x1 y1 z1 u1 v1 Hxyzuv];
    apply (Hmap _ Q) in Hxyzuv; [apply HQ; assumption|assumption]
  end.


Section Ind6.

Context {A : Type}.
Context {B : A -> Type}.
Context {C : forall x, B x -> Type}.
Context {D : forall x y, C x y -> Type}.
Context {E : forall x y z, D x y z -> Type}.
Context {F : forall x y z u, E x y z u -> Type}.
Context (G : (forall x y z u v, F x y z u v -> Prop) -> (forall x y z u v, F x y z u v -> Prop)).
Context (P : forall x y z u v, F x y z u v -> Prop).

Implicit Types Q R : forall x y z u v, F x y z u v -> Prop.

Definition is_ind6 :=
  (forall Q R, (forall x y z u v w, Q x y z u v w -> R x y z u v w) -> forall x y z u v w, G Q x y z u v w -> G R x y z u v w) /\
  (forall Q, (forall x y z u v w, G Q x y z u v w -> Q x y z u v w) -> forall x y z u v w, P x y z u v w -> Q x y z u v w) /\
  (forall x y z u v w, G P x y z u v w -> P x y z u v w).

Hypothesis Hind : is_ind6.

Let is_positive := proj1 Hind.
Definition is_positive6 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved6 Q :=
  forall x y z u v w, G (fun x y z u v w => P x y z u v w /\ Q x y z u v w) x y z u v w -> Q x y z u v w.
Definition preserved_with_inv6 Q R :=
  forall x y z u v w, G (fun x y z u v w => P x y z u v w /\ Q x y z u v w /\ R x y z u v w) x y z u v w -> R x y z u v w -> Q x y z u v w.
Definition preserved_down6 Q :=
  forall x y z u v w R, G (fun x y z u v w => P x y z u v w /\ R x y z u v w) x y z u v w -> Q x y z u v w -> G (fun x y z u v w => P x y z u v w /\ Q x y z u v w /\ R x y z u v w) x y z u v w.

Lemma preserved6_rec :
  forall Q, preserved6 Q -> forall x y z u v w, P x y z u v w -> Q x y z u v w.
Proof.
  intros Q HQ.
  enough (H : forall x y z u v w, P x y z u v w -> P x y z u v w /\ Q x y z u v w) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv6_rec :
  forall Q R, preserved_down6 R -> preserved_with_inv6 Q R -> forall x y z u v w, P x y z u v w -> R x y z u v w -> Q x y z u v w.
Proof.
  intros Q R H1 H2. refine (preserved6_rec (fun x y z u v w => R x y z u v w -> Q x y z u v w) _).
  intros x y z u v w H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x y z u v w => P x y z u v w /\ R x y z u v w /\ (R x y z u v w -> Q x y z u v w)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind6_inv :
  forall x y z u v w, P x y z u v w -> G P x y z u v w.
Proof.
  apply preserved6_rec. intros x y z u v w H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind6.

Ltac prove_ind6 :=
  unfold is_ind6;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    pose (Hmap := (ltac:(intros Q R H x y z u v w Hxyzuvw; destruct Hxyzuvw; econstructor; try eassumption; eapply H; eassumption) : G1));
    split; [exact Hmap|];
    split; [|intros x y z u v w Hxyzuvw; constructor; assumption];
    intros Q HQ; fix H 7; intros x y z u v w Hxyzuvw;
    destruct Hxyzuvw as [x1 y1 z1 u1 v1 w1 Hxyzuvw];
    apply (Hmap _ Q) in Hxyzuvw; [apply HQ; assumption|assumption]
  end.











(*
Inductive test (rec : nat -> nat -> Prop) : nat -> nat -> Prop :=
| test_O : test rec O O
| test_SS : forall n m, rec n m -> test rec (S (S n)) (S (S m)).

Inductive t : nat -> nat -> Prop :=
| t_intro : forall n m, test t n m -> t n m.

Lemma t_ind2 : is_ind2 test t.
Proof. prove_ind2. Qed.

Lemma test_preserved_down :
  preserved_down2 test t (fun k1 k2 => k1 = k2).
Proof.
  intros n m X H1 H2. inversion H1; subst; constructor.
  split; [|split]; try tauto. congruence.
Qed.

Lemma h : forall n1 n2, t n1 -> t n2 -> t (n1 + n2).
Proof.
  intros n1 n2 H1 H2. revert n1 H1; apply preserved_rec.
  intros n1 Hn1. destruct Hn1.
  - assumption.
  - simpl. constructor. constructor. tauto.
Qed.

*)
