Section Ind1.

Context {A1 : Type}.
Context (G : (A1 -> Prop) -> (A1 -> Prop)).
Context (P : A1 -> Prop).

Implicit Types Q R : A1 -> Prop.

Definition is_ind1 :=
  (forall Q R, (forall x1, Q x1 -> R x1) -> forall x1, G Q x1 -> G R x1) /\
  (forall Q, (forall x1, G Q x1 -> Q x1) -> forall x1, P x1 -> Q x1) /\
  (forall x1, G P x1 -> P x1).

Hypothesis Hind : is_ind1.

Let is_positive := proj1 Hind.
Definition is_positive1 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved1 Q :=
  forall x1, G (fun x1 => P x1 /\ Q x1) x1 -> Q x1.
Definition preserved_with_inv1 Q R :=
  forall x1, G (fun x1 => P x1 /\ Q x1 /\ R x1) x1 -> R x1 -> Q x1.
Definition preserved_down1 Q :=
  forall x1 R, G (fun x1 => P x1 /\ R x1) x1 -> Q x1 -> G (fun x1 => P x1 /\ Q x1 /\ R x1) x1.

Lemma preserved1_rec :
  forall Q, preserved1 Q -> forall x1, P x1 -> Q x1.
Proof.
  intros Q HQ.
  enough (H : forall x1, P x1 -> P x1 /\ Q x1) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv1_rec :
  forall Q R, preserved_down1 R -> preserved_with_inv1 Q R -> forall x1, P x1 -> R x1 -> Q x1.
Proof.
  intros Q R H1 H2. refine (preserved1_rec (fun x1 => R x1 -> Q x1) _).
  intros x1 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 => P x1 /\ R x1 /\ (R x1 -> Q x1)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind1_inv :
  forall x1, P x1 -> G P x1.
Proof.
  apply preserved1_rec. intros x1 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind1.

Ltac prove_ind1 :=
  unfold is_ind1;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 H; constructor; assumption];
    intros Q HQ; fix H 2; intros x1 H1;
    destruct H1 as [y1 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind2.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context (G : (forall x1, A2 x1 -> Prop) -> (forall x1, A2 x1 -> Prop)).
Context (P : forall x1, A2 x1 -> Prop).

Implicit Types Q R : forall x1, A2 x1 -> Prop.

Definition is_ind2 :=
  (forall Q R, (forall x1 x2, Q x1 x2 -> R x1 x2) -> forall x1 x2, G Q x1 x2 -> G R x1 x2) /\
  (forall Q, (forall x1 x2, G Q x1 x2 -> Q x1 x2) -> forall x1 x2, P x1 x2 -> Q x1 x2) /\
  (forall x1 x2, G P x1 x2 -> P x1 x2).

Hypothesis Hind : is_ind2.

Let is_positive := proj1 Hind.
Definition is_positive2 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved2 Q :=
  forall x1 x2, G (fun x1 x2 => P x1 x2 /\ Q x1 x2) x1 x2 -> Q x1 x2.
Definition preserved_with_inv2 Q R :=
  forall x1 x2, G (fun x1 x2 => P x1 x2 /\ Q x1 x2 /\ R x1 x2) x1 x2 -> R x1 x2 -> Q x1 x2.
Definition preserved_down2 Q :=
  forall x1 x2 R, G (fun x1 x2 => P x1 x2 /\ R x1 x2) x1 x2 -> Q x1 x2 -> G (fun x1 x2 => P x1 x2 /\ Q x1 x2 /\ R x1 x2) x1 x2.

Lemma preserved2_rec :
  forall Q, preserved2 Q -> forall x1 x2, P x1 x2 -> Q x1 x2.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2, P x1 x2 -> P x1 x2 /\ Q x1 x2) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv2_rec :
  forall Q R, preserved_down2 R -> preserved_with_inv2 Q R -> forall x1 x2, P x1 x2 -> R x1 x2 -> Q x1 x2.
Proof.
  intros Q R H1 H2. refine (preserved2_rec (fun x1 x2 => R x1 x2 -> Q x1 x2) _).
  intros x1 x2 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 => P x1 x2 /\ R x1 x2 /\ (R x1 x2 -> Q x1 x2)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind2_inv :
  forall x1 x2, P x1 x2 -> G P x1 x2.
Proof.
  apply preserved2_rec. intros x1 x2 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind2.

Ltac prove_ind2 :=
  unfold is_ind2;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 H; constructor; assumption];
    intros Q HQ; fix H 3; intros x1 x2 H1;
    destruct H1 as [y1 y2 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind3.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context (G : (forall x1 x2, A3 x1 x2 -> Prop) -> (forall x1 x2, A3 x1 x2 -> Prop)).
Context (P : forall x1 x2, A3 x1 x2 -> Prop).

Implicit Types Q R : forall x1 x2, A3 x1 x2 -> Prop.

Definition is_ind3 :=
  (forall Q R, (forall x1 x2 x3, Q x1 x2 x3 -> R x1 x2 x3) -> forall x1 x2 x3, G Q x1 x2 x3 -> G R x1 x2 x3) /\
  (forall Q, (forall x1 x2 x3, G Q x1 x2 x3 -> Q x1 x2 x3) -> forall x1 x2 x3, P x1 x2 x3 -> Q x1 x2 x3) /\
  (forall x1 x2 x3, G P x1 x2 x3 -> P x1 x2 x3).

Hypothesis Hind : is_ind3.

Let is_positive := proj1 Hind.
Definition is_positive3 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved3 Q :=
  forall x1 x2 x3, G (fun x1 x2 x3 => P x1 x2 x3 /\ Q x1 x2 x3) x1 x2 x3 -> Q x1 x2 x3.
Definition preserved_with_inv3 Q R :=
  forall x1 x2 x3, G (fun x1 x2 x3 => P x1 x2 x3 /\ Q x1 x2 x3 /\ R x1 x2 x3) x1 x2 x3 -> R x1 x2 x3 -> Q x1 x2 x3.
Definition preserved_down3 Q :=
  forall x1 x2 x3 R, G (fun x1 x2 x3 => P x1 x2 x3 /\ R x1 x2 x3) x1 x2 x3 -> Q x1 x2 x3 -> G (fun x1 x2 x3 => P x1 x2 x3 /\ Q x1 x2 x3 /\ R x1 x2 x3) x1 x2 x3.

Lemma preserved3_rec :
  forall Q, preserved3 Q -> forall x1 x2 x3, P x1 x2 x3 -> Q x1 x2 x3.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3, P x1 x2 x3 -> P x1 x2 x3 /\ Q x1 x2 x3) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv3_rec :
  forall Q R, preserved_down3 R -> preserved_with_inv3 Q R -> forall x1 x2 x3, P x1 x2 x3 -> R x1 x2 x3 -> Q x1 x2 x3.
Proof.
  intros Q R H1 H2. refine (preserved3_rec (fun x1 x2 x3 => R x1 x2 x3 -> Q x1 x2 x3) _).
  intros x1 x2 x3 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 => P x1 x2 x3 /\ R x1 x2 x3 /\ (R x1 x2 x3 -> Q x1 x2 x3)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind3_inv :
  forall x1 x2 x3, P x1 x2 x3 -> G P x1 x2 x3.
Proof.
  apply preserved3_rec. intros x1 x2 x3 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind3.

Ltac prove_ind3 :=
  unfold is_ind3;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 H; constructor; assumption];
    intros Q HQ; fix H 4; intros x1 x2 x3 H1;
    destruct H1 as [y1 y2 y3 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind4.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context (G : (forall x1 x2 x3, A4 x1 x2 x3 -> Prop) -> (forall x1 x2 x3, A4 x1 x2 x3 -> Prop)).
Context (P : forall x1 x2 x3, A4 x1 x2 x3 -> Prop).

Implicit Types Q R : forall x1 x2 x3, A4 x1 x2 x3 -> Prop.

Definition is_ind4 :=
  (forall Q R, (forall x1 x2 x3 x4, Q x1 x2 x3 x4 -> R x1 x2 x3 x4) -> forall x1 x2 x3 x4, G Q x1 x2 x3 x4 -> G R x1 x2 x3 x4) /\
  (forall Q, (forall x1 x2 x3 x4, G Q x1 x2 x3 x4 -> Q x1 x2 x3 x4) -> forall x1 x2 x3 x4, P x1 x2 x3 x4 -> Q x1 x2 x3 x4) /\
  (forall x1 x2 x3 x4, G P x1 x2 x3 x4 -> P x1 x2 x3 x4).

Hypothesis Hind : is_ind4.

Let is_positive := proj1 Hind.
Definition is_positive4 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved4 Q :=
  forall x1 x2 x3 x4, G (fun x1 x2 x3 x4 => P x1 x2 x3 x4 /\ Q x1 x2 x3 x4) x1 x2 x3 x4 -> Q x1 x2 x3 x4.
Definition preserved_with_inv4 Q R :=
  forall x1 x2 x3 x4, G (fun x1 x2 x3 x4 => P x1 x2 x3 x4 /\ Q x1 x2 x3 x4 /\ R x1 x2 x3 x4) x1 x2 x3 x4 -> R x1 x2 x3 x4 -> Q x1 x2 x3 x4.
Definition preserved_down4 Q :=
  forall x1 x2 x3 x4 R, G (fun x1 x2 x3 x4 => P x1 x2 x3 x4 /\ R x1 x2 x3 x4) x1 x2 x3 x4 -> Q x1 x2 x3 x4 -> G (fun x1 x2 x3 x4 => P x1 x2 x3 x4 /\ Q x1 x2 x3 x4 /\ R x1 x2 x3 x4) x1 x2 x3 x4.

Lemma preserved4_rec :
  forall Q, preserved4 Q -> forall x1 x2 x3 x4, P x1 x2 x3 x4 -> Q x1 x2 x3 x4.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4, P x1 x2 x3 x4 -> P x1 x2 x3 x4 /\ Q x1 x2 x3 x4) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv4_rec :
  forall Q R, preserved_down4 R -> preserved_with_inv4 Q R -> forall x1 x2 x3 x4, P x1 x2 x3 x4 -> R x1 x2 x3 x4 -> Q x1 x2 x3 x4.
Proof.
  intros Q R H1 H2. refine (preserved4_rec (fun x1 x2 x3 x4 => R x1 x2 x3 x4 -> Q x1 x2 x3 x4) _).
  intros x1 x2 x3 x4 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 => P x1 x2 x3 x4 /\ R x1 x2 x3 x4 /\ (R x1 x2 x3 x4 -> Q x1 x2 x3 x4)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind4_inv :
  forall x1 x2 x3 x4, P x1 x2 x3 x4 -> G P x1 x2 x3 x4.
Proof.
  apply preserved4_rec. intros x1 x2 x3 x4 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind4.

Ltac prove_ind4 :=
  unfold is_ind4;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 H; constructor; assumption];
    intros Q HQ; fix H 5; intros x1 x2 x3 x4 H1;
    destruct H1 as [y1 y2 y3 y4 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind5.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context (G : (forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Prop) -> (forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Prop)).
Context (P : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Prop.

Definition is_ind5 :=
  (forall Q R, (forall x1 x2 x3 x4 x5, Q x1 x2 x3 x4 x5 -> R x1 x2 x3 x4 x5) -> forall x1 x2 x3 x4 x5, G Q x1 x2 x3 x4 x5 -> G R x1 x2 x3 x4 x5) /\
  (forall Q, (forall x1 x2 x3 x4 x5, G Q x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5) -> forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5) /\
  (forall x1 x2 x3 x4 x5, G P x1 x2 x3 x4 x5 -> P x1 x2 x3 x4 x5).

Hypothesis Hind : is_ind5.

Let is_positive := proj1 Hind.
Definition is_positive5 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved5 Q :=
  forall x1 x2 x3 x4 x5, G (fun x1 x2 x3 x4 x5 => P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5.
Definition preserved_with_inv5 Q R :=
  forall x1 x2 x3 x4 x5, G (fun x1 x2 x3 x4 x5 => P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5 /\ R x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 -> R x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5.
Definition preserved_down5 Q :=
  forall x1 x2 x3 x4 x5 R, G (fun x1 x2 x3 x4 x5 => P x1 x2 x3 x4 x5 /\ R x1 x2 x3 x4 x5) x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5 -> G (fun x1 x2 x3 x4 x5 => P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5 /\ R x1 x2 x3 x4 x5) x1 x2 x3 x4 x5.

Lemma preserved5_rec :
  forall Q, preserved5 Q -> forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv5_rec :
  forall Q R, preserved_down5 R -> preserved_with_inv5 Q R -> forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> R x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5.
Proof.
  intros Q R H1 H2. refine (preserved5_rec (fun x1 x2 x3 x4 x5 => R x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5) _).
  intros x1 x2 x3 x4 x5 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 => P x1 x2 x3 x4 x5 /\ R x1 x2 x3 x4 x5 /\ (R x1 x2 x3 x4 x5 -> Q x1 x2 x3 x4 x5)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind5_inv :
  forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> G P x1 x2 x3 x4 x5.
Proof.
  apply preserved5_rec. intros x1 x2 x3 x4 x5 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind5.

Ltac prove_ind5 :=
  unfold is_ind5;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 H; constructor; assumption];
    intros Q HQ; fix H 6; intros x1 x2 x3 x4 x5 H1;
    destruct H1 as [y1 y2 y3 y4 y5 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind6.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Prop) -> (forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Prop.

Definition is_ind6 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6, Q x1 x2 x3 x4 x5 x6 -> R x1 x2 x3 x4 x5 x6) -> forall x1 x2 x3 x4 x5 x6, G Q x1 x2 x3 x4 x5 x6 -> G R x1 x2 x3 x4 x5 x6) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6, G Q x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6) -> forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6) /\
  (forall x1 x2 x3 x4 x5 x6, G P x1 x2 x3 x4 x5 x6 -> P x1 x2 x3 x4 x5 x6).

Hypothesis Hind : is_ind6.

Let is_positive := proj1 Hind.
Definition is_positive6 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved6 Q :=
  forall x1 x2 x3 x4 x5 x6, G (fun x1 x2 x3 x4 x5 x6 => P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6.
Definition preserved_with_inv6 Q R :=
  forall x1 x2 x3 x4 x5 x6, G (fun x1 x2 x3 x4 x5 x6 => P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6 /\ R x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6 -> R x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6.
Definition preserved_down6 Q :=
  forall x1 x2 x3 x4 x5 x6 R, G (fun x1 x2 x3 x4 x5 x6 => P x1 x2 x3 x4 x5 x6 /\ R x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6 -> G (fun x1 x2 x3 x4 x5 x6 => P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6 /\ R x1 x2 x3 x4 x5 x6) x1 x2 x3 x4 x5 x6.

Lemma preserved6_rec :
  forall Q, preserved6 Q -> forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv6_rec :
  forall Q R, preserved_down6 R -> preserved_with_inv6 Q R -> forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> R x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6.
Proof.
  intros Q R H1 H2. refine (preserved6_rec (fun x1 x2 x3 x4 x5 x6 => R x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6) _).
  intros x1 x2 x3 x4 x5 x6 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 => P x1 x2 x3 x4 x5 x6 /\ R x1 x2 x3 x4 x5 x6 /\ (R x1 x2 x3 x4 x5 x6 -> Q x1 x2 x3 x4 x5 x6)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind6_inv :
  forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> G P x1 x2 x3 x4 x5 x6.
Proof.
  apply preserved6_rec. intros x1 x2 x3 x4 x5 x6 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind6.

Ltac prove_ind6 :=
  unfold is_ind6;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 H; constructor; assumption];
    intros Q HQ; fix H 7; intros x1 x2 x3 x4 x5 x6 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind7.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Prop) -> (forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Prop.

Definition is_ind7 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7, Q x1 x2 x3 x4 x5 x6 x7 -> R x1 x2 x3 x4 x5 x6 x7) -> forall x1 x2 x3 x4 x5 x6 x7, G Q x1 x2 x3 x4 x5 x6 x7 -> G R x1 x2 x3 x4 x5 x6 x7) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7, G Q x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7) -> forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7) /\
  (forall x1 x2 x3 x4 x5 x6 x7, G P x1 x2 x3 x4 x5 x6 x7 -> P x1 x2 x3 x4 x5 x6 x7).

Hypothesis Hind : is_ind7.

Let is_positive := proj1 Hind.
Definition is_positive7 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved7 Q :=
  forall x1 x2 x3 x4 x5 x6 x7, G (fun x1 x2 x3 x4 x5 x6 x7 => P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7.
Definition preserved_with_inv7 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7, G (fun x1 x2 x3 x4 x5 x6 x7 => P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7 /\ R x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7 -> R x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7.
Definition preserved_down7 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 R, G (fun x1 x2 x3 x4 x5 x6 x7 => P x1 x2 x3 x4 x5 x6 x7 /\ R x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7 -> G (fun x1 x2 x3 x4 x5 x6 x7 => P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7 /\ R x1 x2 x3 x4 x5 x6 x7) x1 x2 x3 x4 x5 x6 x7.

Lemma preserved7_rec :
  forall Q, preserved7 Q -> forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv7_rec :
  forall Q R, preserved_down7 R -> preserved_with_inv7 Q R -> forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> R x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros Q R H1 H2. refine (preserved7_rec (fun x1 x2 x3 x4 x5 x6 x7 => R x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7) _).
  intros x1 x2 x3 x4 x5 x6 x7 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 => P x1 x2 x3 x4 x5 x6 x7 /\ R x1 x2 x3 x4 x5 x6 x7 /\ (R x1 x2 x3 x4 x5 x6 x7 -> Q x1 x2 x3 x4 x5 x6 x7)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind7_inv :
  forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> G P x1 x2 x3 x4 x5 x6 x7.
Proof.
  apply preserved7_rec. intros x1 x2 x3 x4 x5 x6 x7 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind7.

Ltac prove_ind7 :=
  unfold is_ind7;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 H; constructor; assumption];
    intros Q HQ; fix H 8; intros x1 x2 x3 x4 x5 x6 x7 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind8.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Prop.

Definition is_ind8 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8, Q x1 x2 x3 x4 x5 x6 x7 x8 -> R x1 x2 x3 x4 x5 x6 x7 x8) -> forall x1 x2 x3 x4 x5 x6 x7 x8, G Q x1 x2 x3 x4 x5 x6 x7 x8 -> G R x1 x2 x3 x4 x5 x6 x7 x8) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8, G Q x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8) -> forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8, G P x1 x2 x3 x4 x5 x6 x7 x8 -> P x1 x2 x3 x4 x5 x6 x7 x8).

Hypothesis Hind : is_ind8.

Let is_positive := proj1 Hind.
Definition is_positive8 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved8 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8, G (fun x1 x2 x3 x4 x5 x6 x7 x8 => P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8.
Definition preserved_with_inv8 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8, G (fun x1 x2 x3 x4 x5 x6 x7 x8 => P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 /\ R x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 -> R x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8.
Definition preserved_down8 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 => P x1 x2 x3 x4 x5 x6 x7 x8 /\ R x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 => P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 /\ R x1 x2 x3 x4 x5 x6 x7 x8) x1 x2 x3 x4 x5 x6 x7 x8.

Lemma preserved8_rec :
  forall Q, preserved8 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv8_rec :
  forall Q R, preserved_down8 R -> preserved_with_inv8 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> R x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  intros Q R H1 H2. refine (preserved8_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 => R x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 => P x1 x2 x3 x4 x5 x6 x7 x8 /\ R x1 x2 x3 x4 x5 x6 x7 x8 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 -> Q x1 x2 x3 x4 x5 x6 x7 x8)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind8_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> G P x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  apply preserved8_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind8.

Ltac prove_ind8 :=
  unfold is_ind8;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 H; constructor; assumption];
    intros Q HQ; fix H 9; intros x1 x2 x3 x4 x5 x6 x7 x8 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind9.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Prop.

Definition is_ind9 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9).

Hypothesis Hind : is_ind9.

Let is_positive := proj1 Hind.
Definition is_positive9 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved9 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9.
Definition preserved_with_inv9 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9.
Definition preserved_down9 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9) x1 x2 x3 x4 x5 x6 x7 x8 x9.

Lemma preserved9_rec :
  forall Q, preserved9 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv9_rec :
  forall Q R, preserved_down9 R -> preserved_with_inv9 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  intros Q R H1 H2. refine (preserved9_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind9_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  apply preserved9_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind9.

Ltac prove_ind9 :=
  unfold is_ind9;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 H; constructor; assumption];
    intros Q HQ; fix H 10; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind10.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Prop.

Definition is_ind10 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).

Hypothesis Hind : is_ind10.

Let is_positive := proj1 Hind.
Definition is_positive10 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved10 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Definition preserved_with_inv10 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Definition preserved_down10 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Lemma preserved10_rec :
  forall Q, preserved10 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv10_rec :
  forall Q R, preserved_down10 R -> preserved_with_inv10 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  intros Q R H1 H2. refine (preserved10_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind10_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  apply preserved10_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind10.

Ltac prove_ind10 :=
  unfold is_ind10;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H; constructor; assumption];
    intros Q HQ; fix H 11; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind11.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Prop.

Definition is_ind11 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).

Hypothesis Hind : is_ind11.

Let is_positive := proj1 Hind.
Definition is_positive11 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved11 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Definition preserved_with_inv11 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Definition preserved_down11 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Lemma preserved11_rec :
  forall Q, preserved11 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv11_rec :
  forall Q R, preserved_down11 R -> preserved_with_inv11 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  intros Q R H1 H2. refine (preserved11_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind11_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  apply preserved11_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind11.

Ltac prove_ind11 :=
  unfold is_ind11;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H; constructor; assumption];
    intros Q HQ; fix H 12; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind12.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context {A12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Prop.

Definition is_ind12 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).

Hypothesis Hind : is_ind12.

Let is_positive := proj1 Hind.
Definition is_positive12 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved12 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Definition preserved_with_inv12 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Definition preserved_down12 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Lemma preserved12_rec :
  forall Q, preserved12 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv12_rec :
  forall Q R, preserved_down12 R -> preserved_with_inv12 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  intros Q R H1 H2. refine (preserved12_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind12_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  apply preserved12_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind12.

Ltac prove_ind12 :=
  unfold is_ind12;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H; constructor; assumption];
    intros Q HQ; fix H 13; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind13.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context {A12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Type}.
Context {A13 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Prop.

Definition is_ind13 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).

Hypothesis Hind : is_ind13.

Let is_positive := proj1 Hind.
Definition is_positive13 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved13 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Definition preserved_with_inv13 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Definition preserved_down13 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Lemma preserved13_rec :
  forall Q, preserved13 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv13_rec :
  forall Q R, preserved_down13 R -> preserved_with_inv13 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  intros Q R H1 H2. refine (preserved13_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind13_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  apply preserved13_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind13.

Ltac prove_ind13 :=
  unfold is_ind13;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H; constructor; assumption];
    intros Q HQ; fix H 14; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind14.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context {A12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Type}.
Context {A13 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Type}.
Context {A14 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Prop.

Definition is_ind14 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14).

Hypothesis Hind : is_ind14.

Let is_positive := proj1 Hind.
Definition is_positive14 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved14 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Definition preserved_with_inv14 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Definition preserved_down14 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Lemma preserved14_rec :
  forall Q, preserved14 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv14_rec :
  forall Q R, preserved_down14 R -> preserved_with_inv14 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof.
  intros Q R H1 H2. refine (preserved14_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind14_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof.
  apply preserved14_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind14.

Ltac prove_ind14 :=
  unfold is_ind14;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H; constructor; assumption];
    intros Q HQ; fix H 15; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind15.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context {A12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Type}.
Context {A13 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Type}.
Context {A14 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Type}.
Context {A15 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Prop.

Definition is_ind15 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).

Hypothesis Hind : is_ind15.

Let is_positive := proj1 Hind.
Definition is_positive15 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved15 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Definition preserved_with_inv15 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Definition preserved_down15 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Lemma preserved15_rec :
  forall Q, preserved15 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv15_rec :
  forall Q R, preserved_down15 R -> preserved_with_inv15 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Proof.
  intros Q R H1 H2. refine (preserved15_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind15_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Proof.
  apply preserved15_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind15.

Ltac prove_ind15 :=
  unfold is_ind15;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H; constructor; assumption];
    intros Q HQ; fix H 16; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.

Section Ind16.

Context {A1 : Type}.
Context {A2 : A1 -> Type}.
Context {A3 : forall x1, A2 x1 -> Type}.
Context {A4 : forall x1 x2, A3 x1 x2 -> Type}.
Context {A5 : forall x1 x2 x3, A4 x1 x2 x3 -> Type}.
Context {A6 : forall x1 x2 x3 x4, A5 x1 x2 x3 x4 -> Type}.
Context {A7 : forall x1 x2 x3 x4 x5, A6 x1 x2 x3 x4 x5 -> Type}.
Context {A8 : forall x1 x2 x3 x4 x5 x6, A7 x1 x2 x3 x4 x5 x6 -> Type}.
Context {A9 : forall x1 x2 x3 x4 x5 x6 x7, A8 x1 x2 x3 x4 x5 x6 x7 -> Type}.
Context {A10 : forall x1 x2 x3 x4 x5 x6 x7 x8, A9 x1 x2 x3 x4 x5 x6 x7 x8 -> Type}.
Context {A11 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9, A10 x1 x2 x3 x4 x5 x6 x7 x8 x9 -> Type}.
Context {A12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> Type}.
Context {A13 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> Type}.
Context {A14 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> Type}.
Context {A15 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> Type}.
Context {A16 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> Type}.
Context (G : (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Prop) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Prop)).
Context (P : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Prop).

Implicit Types Q R : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> Prop.

Definition is_ind16 :=
  (forall Q R, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) /\
  (forall Q, (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, G Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16).

Hypothesis Hind : is_ind16.

Let is_positive := proj1 Hind.
Definition is_positive16 := is_positive.
Let has_ind := proj1 (proj2 Hind).
Let is_ind := proj2 (proj2 Hind).

Definition preserved16 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Definition preserved_with_inv16 Q R :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Definition preserved_down16 Q :=
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 R, G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Lemma preserved16_rec :
  forall Q, preserved16 Q -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof.
  intros Q HQ.
  enough (H : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) by (intros; apply H; assumption).
  apply has_ind. intros; split.
  - eapply is_ind, is_positive; [|eassumption].
    simpl. intros; tauto.
  - apply HQ. assumption.
Qed.

Lemma preserved_with_inv16_rec :
  forall Q R, preserved_down16 R -> preserved_with_inv16 Q R -> forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof.
  intros Q R H1 H2. refine (preserved16_rec (fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) _).
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H3 H4. apply H2; [|assumption].
  apply is_positive with (Q := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 /\ (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma ind16_inv :
  forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof.
  apply preserved16_rec. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H.
  eapply is_positive; [|eassumption].
  simpl. intros; tauto.
Qed.

End Ind16.

Ltac prove_ind16 :=
  unfold is_ind16;
  match goal with [ |- ?G1_ /\ ?G2_ /\ ?G3_ ] =>
    pose (G1 := G1_);
    assert (Hmap : G1) by (intros Q R H1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);
    split; [exact Hmap|];
    split; [|intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H; constructor; assumption];
    intros Q HQ; fix H 17; intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H1;
    destruct H1 as [y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 H1];
    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]
  end.


