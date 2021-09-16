Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Inductive.
Require Import Rewrite.


Lemma star_list :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : list A -> B) l1 l2,
    (forall l1 l2 x y, RA x y -> RB (f (l1 ++ x :: l2)) (f (l1 ++ y :: l2))) -> Forall2 (star RA) l1 l2 -> star RB (f l1) (f l2).
Proof.
  intros A B RA RB f l1 l2 Himpl Hl.
  enough (H : forall l, star RB (f (l ++ l1)) (f (l ++ l2))); [exact (H nil)|].
  induction Hl as [|x y l1 l2 Hxy Hl IH].
  - intros. constructor.
  - intros l. eapply star_compose.
    + specialize (IH (l ++ x :: nil)). rewrite <- !app_assoc in IH. apply IH.
    + eapply star_map_impl with (f := fun t => f (l ++ t :: l2)); [|eassumption].
      intros; apply Himpl; assumption.
Qed.

Inductive beta : term -> term -> Prop :=
| beta_app1 : forall t1 t2 t3, beta t1 t2 -> beta (app t1 t3) (app t2 t3)
| beta_app2 : forall t1 t2 t3, beta t1 t2 -> beta (app t3 t1) (app t3 t2)
| beta_abs : forall t1 t2, beta t1 t2 -> beta (abs t1) (abs t2)
| beta_redex : forall t1 t2, beta (app (abs t1) t2) (subst1 t2 t1)
| beta_constr : forall tag t1 t2 l1 l2, beta t1 t2 -> beta (constr tag (l1 ++ t1 :: l2)) (constr tag (l1 ++ t2 :: l2))
| beta_switch1 : forall t1 t2 l, beta t1 t2 -> beta (switch t1 l) (switch t2 l)
| beta_switch2 : forall t p t1 t2 l1 l2, beta t1 t2 -> beta (switch t (l1 ++ (p, t1) :: l2)) (switch t (l1 ++ (p, t2) :: l2))
| beta_switch_redex : forall l t l1 l2, beta (switch (constr (length l1) l) (l1 ++ (length l, t) :: l2)) (subst (read_env l) t).

Lemma star_beta_app :
  forall t1 t2 t3 t4, star beta t1 t2 -> star beta t3 t4 -> star beta (app t1 t3) (app t2 t4).
Proof.
  intros t1 t2 t3 t4 H12 H34.
  eapply star_compose.
  + eapply star_map_impl with (RA := beta) (f := fun t => app t _); [|eassumption].
    intros; constructor; assumption.
  + eapply star_map_impl with (RA := beta) (f := fun t => app _ t); [|eassumption].
    intros; constructor; assumption.
Qed.

Lemma star_beta_abs :
  forall t1 t2, star beta t1 t2 -> star beta (abs t1) (abs t2).
Proof.
  intros t1 t2 H12.
  eapply star_map_impl with (RA := beta) (f := fun t => abs t); [|eassumption].
  intros; constructor; assumption.
Qed.

Lemma star_beta_constr :
  forall tag l1 l2, Forall2 (star beta) l1 l2 -> star beta (constr tag l1) (constr tag l2).
Proof.
  intros tag l1 l2 H12.
  eapply star_list; [|eassumption].
  intros; constructor; assumption.
Qed.

Lemma star_beta_switch :
  forall t1 t2 l1 l2,
    star beta t1 t2 -> Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\ star beta (snd pt1) (snd pt2)) l1 l2 ->
    star beta (switch t1 l1) (switch t2 l2).
Proof.
  intros t1 t2 l1 l2 Ht Hl.
  eapply star_compose.
  - eapply star_map_impl with (RA := beta) (f := fun t => switch t _); [|eassumption].
    intros; constructor; assumption.
  - eapply star_list with (RA := fun pt1 pt2 => fst pt1 = fst pt2 /\ beta (snd pt1) (snd pt2)).
    + intros l3 l4 [p1 t3] [p2 t4] [Hp Hbeta]; simpl in *; subst.
      constructor. assumption.
    + eapply Forall2_impl; [|eassumption].
      intros [p1 t3] [p2 t4] [Hp Hbeta]; simpl in *; subst.
      eapply star_map_impl; [|eassumption].
      intros; simpl; tauto.
Qed.



Inductive pbeta : term -> term -> Prop :=
| pbeta_var : forall n, pbeta (var n) (var n)
| pbeta_dvar : forall n, pbeta (dvar n) (dvar n)
| pbeta_app : forall t1 t2 t3 t4, pbeta t1 t2 -> pbeta t3 t4 -> pbeta (app t1 t3) (app t2 t4)
| pbeta_redex : forall t1 t2 t3 t4, pbeta t1 t2 -> pbeta t3 t4 -> pbeta (app (abs t1) t3) (subst1 t4 t2)
| pbeta_abs : forall t1 t2, pbeta t1 t2 -> pbeta (abs t1) (abs t2)
| pbeta_constr : forall tag l1 l2, Forall2 pbeta l1 l2 -> pbeta (constr tag l1) (constr tag l2)
| pbeta_switch : forall t1 t2 l1 l2, pbeta t1 t2 -> Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\ pbeta (snd pt1) (snd pt2)) l1 l2 -> pbeta (switch t1 l1) (switch t2 l2)
| pbeta_switch_redex : forall lt1 lt2 t1 t2 l1 l2,
    Forall2 pbeta lt1 lt2 -> pbeta t1 t2 ->
    pbeta (switch (constr (length l1) lt1) (l1 ++ (length lt1, t1) :: l2)) (subst (read_env lt2) t2).

Lemma pbeta_refl :
  forall t, pbeta t t.
Proof.
  induction t using term_ind2.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor; assumption.
  - constructor. apply Forall2_map_same. assumption.
  - constructor; [assumption|].
    apply Forall2_map_same. eapply Forall_impl; [|exact H].
    intros [p t2]; simpl; tauto.
Qed.

Fixpoint pbeta_ind2 (P : term -> term -> Prop)
         (Hvar : forall n, P (var n) (var n))
         (Hdvar : forall n, P (dvar n) (dvar n))
         (Happ : forall t1 t2 t3 t4, pbeta t1 t2 -> P t1 t2 -> pbeta t3 t4 -> P t3 t4 -> P (app t1 t3) (app t2 t4))
         (Hredex : forall t1 t2 t3 t4, pbeta t1 t2 -> P t1 t2 -> pbeta t3 t4 -> P t3 t4 -> P (app (abs t1) t3) (subst1 t4 t2))
         (Hlam : forall t1 t2, pbeta t1 t2 -> P t1 t2 -> P (abs t1) (abs t2))
         (Hconstr : forall tag l1 l2, Forall2 pbeta l1 l2 -> Forall2 P l1 l2 -> P (constr tag l1) (constr tag l2))
         (Hswitch : forall t1 t2 l1 l2, pbeta t1 t2 -> P t1 t2 -> Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\ pbeta (snd pt1) (snd pt2)) l1 l2 -> Forall2 (fun pt1 pt2 => P (snd pt1) (snd pt2)) l1 l2 -> P (switch t1 l1) (switch t2 l2))
         (Hswitch_redex : forall lt1 lt2 t1 t2 l1 l2, Forall2 pbeta lt1 lt2 -> Forall2 P lt1 lt2 -> pbeta t1 t2 -> P t1 t2 -> P (switch (constr (length l1) lt1) (l1 ++ (length lt1, t1) :: l2)) (subst (read_env lt2) t2))
         (t1 t2 : term) (H : pbeta t1 t2) {struct H} : P t1 t2 :=
  let rec := pbeta_ind2 P Hvar Hdvar Happ Hredex Hlam Hconstr Hswitch Hswitch_redex in
  match H with
  | pbeta_var n => Hvar n
  | pbeta_dvar n => Hdvar n
  | pbeta_app t1 t2 t3 t4 H12 H34 => Happ t1 t2 t3 t4 H12 (rec t1 t2 H12) H34 (rec t3 t4 H34)
  | pbeta_redex t1 t2 t3 t4 H12 H34 => Hredex t1 t2 t3 t4 H12 (rec t1 t2 H12) H34 (rec t3 t4 H34)
  | pbeta_abs t1 t2 H12 => Hlam t1 t2 H12 (rec t1 t2 H12)
  | pbeta_constr tag l1 l2 H12 =>
    Hconstr tag l1 l2 H12
            (Forall2_impl_transparent _ _ pbeta P l1 l2 rec H12)
  | pbeta_switch t1 t2 l1 l2 Ht Hl =>
    Hswitch t1 t2 l1 l2 Ht (rec t1 t2 Ht) Hl
            (Forall2_impl_transparent _ _ _ _ l1 l2 (fun pt1 pt2 H => rec (snd pt1) (snd pt2) (match H with conj _ H2 => H2 end)) Hl)
  | pbeta_switch_redex lt1 lt2 t1 t2 l1 l2 Hl Ht =>
    Hswitch_redex lt1 lt2 t1 t2 l1 l2 Hl (Forall2_impl_transparent _ _ pbeta P lt1 lt2 rec Hl) Ht (rec t1 t2 Ht)
  end.

Lemma beta_pbeta :
  forall t1 t2, beta t1 t2 -> pbeta t1 t2.
Proof.
  intros t1 t2 Hbeta. induction Hbeta.
  - constructor; [assumption|apply pbeta_refl].
  - constructor; [apply pbeta_refl|assumption].
  - constructor; assumption.
  - constructor; apply pbeta_refl.
  - constructor; apply Forall2_app; [|apply Forall2_cons].
    + apply Forall2_map_same, Forall_True; intros; apply pbeta_refl.
    + assumption.
    + apply Forall2_map_same, Forall_True; intros; apply pbeta_refl.
  - constructor.
    + assumption.
    + apply Forall2_map_same, Forall_True; intros; split; [reflexivity|apply pbeta_refl].
  - constructor.
    + apply pbeta_refl.
    + apply Forall2_app; [|apply Forall2_cons].
      * apply Forall2_map_same, Forall_True; intros; split; [reflexivity|apply pbeta_refl].
      * split; [reflexivity|assumption].
      * apply Forall2_map_same, Forall_True; intros; split; [reflexivity|apply pbeta_refl].
  - constructor; [|apply pbeta_refl].
    apply Forall2_map_same, Forall_True; intros; apply pbeta_refl.
Qed.


Lemma pbeta_star_beta :
  forall t1 t2, pbeta t1 t2 -> star beta t1 t2.
Proof.
  intros t1 t2 Hpbeta. induction Hpbeta using pbeta_ind2.
  - constructor.
  - constructor.
  - apply star_beta_app; assumption.
  - eapply star_compose.
    + apply star_beta_app; [|eassumption].
      apply star_beta_abs; eassumption.
    + econstructor; [|constructor]. constructor.
  - eapply star_map_impl with (RA := beta) (f := abs); [|assumption].
    intros; constructor; assumption.
  - apply star_beta_constr; assumption.
  - apply star_beta_switch; [assumption|].
    eapply Forall2_impl; [|apply Forall2_and; [apply H|apply H0]].
    intros; simpl in *; tauto.
  - eapply star_compose; [|eapply star_compose].
    + eapply star_map_impl with (RA := beta) (f := fun t => switch t _); [intros; constructor; assumption|].
      apply star_beta_constr. eassumption.
    + eapply star_map_impl with (RA := beta) (f := fun t => switch _ (_ ++ (_, t) :: _)); [|eassumption].
      intros; simpl; constructor; assumption.
    + econstructor; [|constructor].
      rewrite (Forall2_length _ _ _ _ _ H).
      constructor.
Qed.

Lemma pbeta_ren : forall t1 t2 r, pbeta t1 t2 -> pbeta (ren_term r t1) (ren_term r t2).
Proof.
  intros t1 t2 r H. revert r. induction H using pbeta_ind2; intros r; simpl in *.
  - constructor.
  - constructor.
  - constructor; [apply IHpbeta1|apply IHpbeta2].
  - rewrite ren_subst1.
    constructor; [apply IHpbeta1|apply IHpbeta2].
  - constructor; apply IHpbeta.
  - constructor. apply Forall2_map_left, Forall2_map_right.
    eapply Forall2_impl; [|eassumption]. intros; auto.
  - constructor; [apply IHpbeta|].
    apply Forall2_map_left, Forall2_map_right.
    eapply Forall2_impl; [|apply Forall2_and; [apply H0|apply H1]].
    simpl.
    intros [p3 t3] [p4 t4] [[Heq Hbeta] IH].
    split; [assumption|]. simpl in *. subst.
    apply IH.
  - rewrite map_app. simpl.
    ereplace (length l1); [|eapply map_length].
    ereplace (length lt1); [|eapply map_length].
    rewrite ren_read_env.
    constructor.
    + rewrite Forall2_map_left, Forall2_map_right.
      eapply Forall2_impl; [|exact H0].
      simpl. intros; auto.
    + rewrite map_length, (Forall2_length _ _ _ _ _ H).
      apply IHpbeta.
Qed.

Lemma pbeta_subst : forall t1 t2 us1 us2, pbeta t1 t2 -> (forall n, pbeta (us1 n) (us2 n)) -> pbeta (subst us1 t1) (subst us2 t2).
Proof.
  intros t1 t2 us1 us2 H. revert us1 us2. induction H using pbeta_ind2; intros us1 us2 Hus; simpl in *.
  - apply Hus.
  - constructor.
  - constructor; [apply IHpbeta1|apply IHpbeta2]; assumption.
  - rewrite subst_subst1.
    constructor; [apply IHpbeta1|apply IHpbeta2; assumption].
    intros [|n]; simpl; [constructor|].
    unfold comp. apply pbeta_ren, Hus.
  - constructor. apply IHpbeta.
    intros [|n]; simpl; [constructor|].
    unfold comp. apply pbeta_ren, Hus.
  - constructor. apply Forall2_map_left, Forall2_map_right.
    eapply Forall2_impl; [|eassumption].
    intros; simpl in *; auto.
  - constructor.
    + apply IHpbeta. assumption.
    + rewrite Forall2_map_left, Forall2_map_right. simpl.
      eapply Forall2_impl; [|apply Forall2_and; [apply H0|apply H1]].
      simpl.
      intros [p3 t3] [p4 t4] [[Heq Hbeta] IH].
      split; [assumption|]. simpl in *. subst.
      apply IH.
      intros n. unfold liftn_subst.
      destruct le_lt_dec; [apply pbeta_ren; apply Hus|apply pbeta_refl].
  - rewrite map_app. simpl.
    ereplace (length l1); [|eapply map_length].
    ereplace (length lt1); [|eapply map_length].
    rewrite subst_read_env.
    constructor.
    + rewrite Forall2_map_left, Forall2_map_right.
      eapply Forall2_impl; [|exact H0].
      simpl. intros; auto.
    + rewrite map_length, (Forall2_length _ _ _ _ _ H).
      apply IHpbeta.
      intros n; unfold liftn_subst. destruct le_lt_dec; [apply pbeta_ren; apply Hus|apply pbeta_refl].
Qed.

Lemma read_env_pbeta :
  forall l1 l2, Forall2 pbeta l1 l2 -> forall n, pbeta (read_env l1 n) (read_env l2 n).
Proof.
  intros l1 l2 H n. unfold read_env.
  destruct (nth_error l1 n) eqn:H1.
  - destruct (nth_error l2 n) eqn:H2.
    + rewrite nth_error_Forall2_iff in H; eapply H; eassumption.
    + erewrite nth_error_Forall2_None in H2; [|eapply Forall2_comm; exact H]. congruence.
  - erewrite nth_error_Forall2_None in H1; [|exact H].
    rewrite H1. rewrite nth_error_Forall2_iff in H; rewrite (proj1 H).
    apply pbeta_refl.
Qed.

Lemma pbeta_diamond : diamond pbeta.
Proof.
  intros t1 t2 t3 H12. revert t3. induction H12 using pbeta_ind2; intros t5 H15; inversion H15; subst.
  - exists (var n). split; constructor.
  - exists (dvar n). split; constructor.
  - destruct (IHpbeta1 t6) as (t7 & H27 & H67); [assumption|].
    destruct (IHpbeta2 t8) as (t9 & H49 & H89); [assumption|].
    exists (app t7 t9). split; constructor; assumption.
  - destruct (IHpbeta1 (abs t6)) as (t7 & H27 & H67); [constructor; assumption|].
    destruct (IHpbeta2 t8) as (t9 & H49 & H89); [assumption|].
    inversion H67; subst.
    inversion H12_; subst.
    exists (subst1 t9 t5). split.
    + constructor; [inversion H27; subst; assumption|assumption].
    + apply pbeta_subst; [assumption|].
      intros [|n]; simpl; [assumption|constructor].
  - inversion H1; subst.
    destruct (IHpbeta1 t5) as (t7 & H27 & H57); [assumption|].
    destruct (IHpbeta2 t8) as (t9 & H49 & H89); [assumption|].
    exists (subst1 t9 t7). split.
    + apply pbeta_subst; [assumption|].
      intros [|n]; simpl; [assumption|constructor].
    + constructor; assumption.
  - destruct (IHpbeta1 t6) as (t7 & H27 & H67); [assumption|].
    destruct (IHpbeta2 t8) as (t9 & H49 & H89); [assumption|].
    exists (subst1 t9 t7). split; apply pbeta_subst.
    + assumption.
    + intros [|n]; simpl; [assumption|constructor].
    + assumption.
    + intros [|n]; simpl; [assumption|constructor].
  - destruct (IHpbeta t3) as (t4 & H24 & H34); [assumption|].
    exists (abs t4); split; constructor; assumption.
  - assert (H23 := Forall3_from_Forall2 _ _ _ _ _ _ _ _ H0 H4).
    simpl in *.
    eapply Forall3_impl in H23; [|intros x y z H123; exact (proj1 H123 z (proj2 H123))].
    apply Forall3_select23 in H23.
    apply Forall2_exists_Forall3 in H23.
    destruct H23 as (l4 & Hl4).
    exists (constr tag l4).
    split; constructor.
    + eapply Forall3_select13; eapply Forall3_impl; [|apply Hl4]. intros; simpl in *; tauto.
    + eapply Forall3_select23; eapply Forall3_impl; [|apply Hl4]. intros; simpl in *; tauto.
  - assert (H23 := Forall3_from_Forall2 _ _ _ _ _ _ _ _ (Forall2_and _ _ _ _ _ _ H H0) H5).
    simpl in *.
    eapply Forall3_impl in H23.
    + eapply Forall3_select23 in H23. eapply Forall2_exists_Forall3 in H23. destruct H23 as (l4 & Hl4).
      destruct (IHpbeta _ H3) as (t4 & Ht4).
      exists (switch t4 l4).
      split; constructor.
      * tauto.
      * eapply Forall3_select13; eapply Forall3_impl; [|apply Hl4]. intros x y z Hxyz; refine (proj1 Hxyz). shelve.
      * tauto.
      * eapply Forall3_select23; eapply Forall3_impl; [|apply Hl4]. intros x y z Hxyz; exact (proj2 Hxyz).
    + simpl. intros x y z (((Ha & Hb) & Hc) & Hd & He).
      destruct (Hc _ He) as (t4 & Ht4). exists (fst z, t4). simpl.
      intuition congruence.
  - assert (H6 := Forall2_and _ _ _ _ _ _ H0 H). simpl in *.
    apply Forall2_app_inv_l in H6. destruct H6 as (l2a & l2b & H6a & H6b & H6eq).
    inversion H6b; subst; simpl in *.
    destruct y as [p t1]; destruct H4 as [H4 [Hp Ht1]]; simpl in *; subst.
    destruct (H4 _ H5) as (t4 & Ht4).
    inversion H12; subst.
    destruct (IHpbeta (constr (length l0) lt2) ltac:(constructor; assumption)) as (t5 & Ht5a & Ht5b).
    inversion Ht5a; subst. inversion Ht5b; subst.
    exists (subst (read_env l4) t4).
    split.
    + rewrite (Forall2_length _ _ _ _ _ H6a).
      rewrite (Forall2_length _ _ _ _ _ H8).
      constructor; tauto.
    + apply pbeta_subst; [tauto|].
      apply read_env_pbeta. assumption.
  - apply Forall2_app_inv_l in H5. destruct H5 as (l2a & l2b & H5a & H5b & H5eq).
    inversion H5b; subst; simpl in *.
    destruct y as [p t4]; destruct H4 as [Hp Ht4]; simpl in *; subst.
    destruct (IHpbeta _ Ht4) as (t5 & Ht5).
    inversion H3; subst.
    assert (H7 := Forall3_from_Forall2 _ _ _ _ _ _ _ _ H0 H5).
    simpl in *.
    eapply Forall3_impl in H7; [|intros x y z Hxyz; exact (proj1 Hxyz z (proj2 Hxyz))].
    apply Forall3_select23, Forall2_exists_Forall3 in H7.
    destruct H7 as (l4 & Hl4).
    exists (subst (read_env l4) t5).
    split.
    + apply pbeta_subst; [tauto|].
      apply read_env_pbeta. eapply Forall3_select13, Forall3_impl, Hl4. intros; simpl in *; tauto.
    + rewrite (Forall2_length _ _ _ _ _ H5a).
      rewrite (Forall2_length _ _ _ _ _ H5).
      constructor; [|tauto]. eapply Forall3_select23, Forall3_impl, Hl4. intros; simpl in *; tauto.
  - apply list_app_eq_length in H4; [|assumption].
    destruct H4 as (? & [=]); subst.
    destruct (IHpbeta _ H6) as (t4 & Ht4).
    assert (H23 := Forall3_from_Forall2 _ _ _ _ _ _ _ _ H0 H5).
    simpl in *.
    eapply Forall3_impl in H23; [|intros x y z H123; exact (proj1 H123 z (proj2 H123))].
    apply Forall3_select23 in H23.
    apply Forall2_exists_Forall3 in H23.
    destruct H23 as (lt4 & Hlt4).
    exists (subst (read_env lt4) t4).
    split; eapply pbeta_subst; try apply Ht4; apply read_env_pbeta.
    + eapply Forall3_select13, Forall3_impl, Hlt4; intros; simpl in *; tauto.
    + eapply Forall3_select23, Forall3_impl, Hlt4; intros; simpl in *; tauto.
Qed.

Lemma beta_confluent :
  confluent beta.
Proof.
  eapply diamond_ext; [|apply diamond_is_confluent, pbeta_diamond].
  apply between_star; [apply beta_pbeta|apply pbeta_star_beta].
Qed.

Inductive iota defs : term -> term -> Prop :=
| iota_unfold : forall k t, nth_error defs k = Some t -> closed_at t 0 -> iota defs (dvar k) t
| iota_app1 : forall t1 t2 t3, iota defs t1 t2 -> iota defs (app t1 t3) (app t2 t3)
| iota_app2 : forall t1 t2 t3, iota defs t1 t2 -> iota defs (app t3 t1) (app t3 t2)
| iota_abs : forall t1 t2, iota defs t1 t2 -> iota defs (abs t1) (abs t2)
| iota_constr : forall tag t1 t2 l1 l2, iota defs t1 t2 -> iota defs (constr tag (l1 ++ t1 :: l2)) (constr tag (l1 ++ t2 :: l2))
| iota_switch1 : forall t1 t2 l, iota defs t1 t2 -> iota defs (switch t1 l) (switch t2 l)
| iota_switch2 : forall t p t1 t2 l1 l2, iota defs t1 t2 -> iota defs (switch t (l1 ++ (p, t1) :: l2)) (switch t (l1 ++ (p, t2) :: l2)).


Lemma iota_subst_left :
  forall defs t1 t2 us, iota defs t1 t2 -> iota defs (subst us t1) (subst us t2).
Proof.
  intros defs t1 t2 us H. revert us; induction H; intros us; unfold subst1, scons; simpl.
  - erewrite subst_closed_at_ext, subst_id; [constructor; eassumption|eassumption|].
    intros; lia.
  - constructor. apply IHiota.
  - constructor. apply IHiota.
  - constructor. apply IHiota.
  - rewrite !map_app; simpl.
    constructor. apply IHiota.
  - constructor. apply IHiota.
  - rewrite !map_app; simpl.
    constructor. apply IHiota.
Qed.

Lemma iota_subst_right :
  forall defs us1 us2 t, (forall n, star (iota defs) (us1 n) (us2 n)) -> star (iota defs) (subst us1 t) (subst us2 t).
Proof.
  intros defs us1 us2 t Hus.
  revert us1 us2 Hus; induction t using term_ind2; intros us1 us2 Hus; simpl.
  - apply Hus.
  - constructor.
  - eapply star_map_impl with (f := fun t => abs t); [|apply IHt]; [intros; constructor; assumption|].
    intros [|n]; unfold lift_subst; simpl.
    + constructor.
    + unfold comp. rewrite !ren_term_is_subst.
      eapply star_map_impl; [|apply Hus].
      intros t1 t2 H12; apply iota_subst_left; assumption.
  - eapply star_compose.
    + eapply star_map_impl with (f := fun t => app t _); [|apply IHt1, Hus].
      intros; constructor; assumption.
    + eapply star_map_impl with (f := fun t => app _ t); [|apply IHt2, Hus].
      intros; constructor; assumption.
  - eapply star_list; [intros; constructor; eassumption|].
    rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same.
    eapply Forall_impl; [|eassumption].
    intros t Ht; apply Ht; assumption.
  - eapply star_compose.
    + eapply star_map_impl with (f := fun t => switch t _); [|apply IHt; eassumption].
      intros; constructor; assumption.
    + eapply star_list with (RA := fun pt1 pt2 => fst pt1 = fst pt2 /\ iota defs (snd pt1) (snd pt2)).
      * intros l1 l2 [p1 t1] [p2 t2] [Hp Hiota]; simpl in *; subst.
        constructor; assumption.
      * rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same.
        eapply Forall_impl; [|eassumption].
        intros [p t1] Hpt; simpl in *.
        eapply star_map_impl with (f := fun t1 => (p, t1)); [|apply Hpt]; [intros; simpl; tauto|].
        intros n. unfold liftn_subst; simpl.
        destruct le_lt_dec; [|constructor].
        rewrite !ren_term_is_subst.
        eapply star_map_impl; [|apply Hus].
        intros; apply iota_subst_left; assumption.
Qed.

Lemma list_select_eq :
  forall (A : Type) (l1a l1b l2a l2b : list A) (x1 x2 : A),
    l1a ++ x1 :: l1b = l2a ++ x2 :: l2b ->
    (l1a = l2a /\ x1 = x2 /\ l1b = l2b) \/
    (exists l3, l1a ++ x1 :: l3 = l2a /\ l1b = l3 ++ x2 :: l2b) \/
    (exists l3, l1a = l2a ++ x2 :: l3 /\ l3 ++ x1 :: l1b = l2b).
Proof.
  intros A l1a. induction l1a as [|x1a l1a IH]; intros l1b l2a l2b x1 x2 Heq; destruct l2a as [|x2a l2a]; simpl in *.
  - left. split; [reflexivity|].
    split; congruence.
  - right. left. exists l2a. split; congruence.
  - right. right. exists l1a. split; congruence.
  - specialize (IH l1b l2a l2b x1 x2 ltac:(congruence)).
    destruct IH as [IH | [IH | IH]]; [left|right; left|right; right].
    + intuition congruence.
    + destruct IH as (l3 & H1 & H2). exists l3. intuition congruence.
    + destruct IH as (l3 & H1 & H2). exists l3. intuition congruence.
Qed.

Lemma select2_app_assoc :
  forall (A : Type) (l1 l2 l3 : list A) (x1 x2 : A),
    (l1 ++ x1 :: l2) ++ x2 :: l3 = l1 ++ x1 :: l2 ++ x2 :: l3.
Proof.
  intros.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma length_select :
  forall (A : Type) (l1 l2 : list A) (x1 x2 : A),
    length (l1 ++ x1 :: l2) = length (l1 ++ x2 :: l2).
Proof.
  intros; rewrite !app_length; reflexivity.
Qed.

Lemma beta_iota_strongly_commute :
  forall defs, strongly_commute (iota defs) beta.
Proof.
  intros defs t1 t2 t3 Hiota Hbeta.
  enough (exists w : term, beta t2 w /\ star (iota defs) t3 w) by (unfold reflc; firstorder).
  revert t2 Hiota; induction Hbeta; intros t4 Hiota; inversion Hiota; subst.
  - destruct (IHHbeta _ H2) as (t4 & Ht34 & Ht24).
    exists (app t4 t3).
    split; [constructor; assumption|].
    eapply star_map_impl with (f := fun t => app t t3); [|eassumption].
    intros; constructor; assumption.
  - exists (app t2 t5).
    split; [constructor; assumption|].
    eapply star_1. constructor. assumption.
  - exists (app t5 t2).
    split; [constructor; assumption|].
    eapply star_1. constructor. assumption.
  - destruct (IHHbeta _ H2) as (t4 & Ht34 & Ht24).
    exists (app t3 t4).
    split; [constructor; assumption|].
    eapply star_map_impl with (f := fun t => app t3 t); [|eassumption].
    intros; constructor; assumption.
  - destruct (IHHbeta _ H0) as (t4 & Ht34 & Ht24).
    exists (abs t4).
    split; [constructor; assumption|].
    eapply star_map_impl with (f := fun t => abs t); [|eassumption].
    intros; constructor; assumption.
  - inversion H2; subst.
    exists (subst1 t2 t4).
    split; [constructor|].
    apply star_1, iota_subst_left. assumption.
  - exists (subst1 t3 t1).
    split; [constructor|].
    apply iota_subst_right.
    intros [|n]; simpl; [apply star_1; assumption|constructor].
  - apply list_select_eq in H1.
    destruct H1 as [(-> & -> & ->) | [(l4 & <- & ->) | (l4 & -> & <-)]].
    + destruct (IHHbeta _ H2) as (t4 & Ht34 & Ht24).
      exists (constr tag (l1 ++ t4 :: l2)).
      split; [constructor; assumption|].
      eapply star_map_impl with (f := fun t => constr tag (l1 ++ t :: l2)); [|eassumption].
      intros; constructor; assumption.
    + exists (constr tag (l0 ++ t3 :: l4 ++ t2 :: l2)). split.
      * rewrite <- !select2_app_assoc. constructor. assumption.
      * apply star_1. rewrite select2_app_assoc. constructor. assumption.
    + exists (constr tag (l1 ++ t2 :: l4 ++ t3 :: l3)). split.
      * rewrite select2_app_assoc. constructor. assumption.
      * apply star_1. rewrite <- !select2_app_assoc. constructor. assumption.
  - destruct (IHHbeta _ H2) as (t4 & Ht34 & Ht24).
    exists (switch t4 l).
    split; [constructor; assumption|].
    eapply star_map_impl with (f := fun t => switch t l); [|eassumption].
    intros; constructor; assumption.
  - exists (switch t2 (l1 ++ (p, t3) :: l2)).
    split; [constructor; assumption|].
    apply star_1. constructor. assumption.
  - exists (switch t3 (l1 ++ (p, t2) :: l2)).
    split; [constructor; assumption|].
    apply star_1. constructor. assumption.
  - apply list_select_eq in H1.
    destruct H1 as [(-> & [=-> ->] & ->) | [(l4 & <- & ->) | (l4 & -> & <-)]].
    + destruct (IHHbeta _ H2) as (t4 & Ht34 & Ht24).
      exists (switch t (l1 ++ (p, t4) :: l2)).
      split; [constructor; assumption|].
      eapply star_map_impl with (f := fun t1 => switch t (l1 ++ (p, t1) :: l2)); [|eassumption].
      intros; constructor; assumption.
    + exists (switch t (l0 ++ (p0, t5) :: l4 ++ (p, t2) :: l2)). split.
      * rewrite <- !select2_app_assoc. constructor. assumption.
      * apply star_1. rewrite select2_app_assoc. constructor. assumption.
    + exists (switch t (l1 ++ (p, t2) :: l4 ++ (p0, t5) :: l3)). split.
      * rewrite select2_app_assoc. constructor. assumption.
      * apply star_1. rewrite <- !select2_app_assoc. constructor. assumption.
  - inversion H2; subst.
    exists (subst (read_env (l0 ++ t0 :: l3)) t). split.
    + erewrite length_select; constructor.
    + eapply iota_subst_right. intros n.
      unfold read_env. rewrite !app_length; simpl.
      destruct (le_lt_dec (length l0) n).
      * rewrite !nth_error_app2 by assumption.
        destruct (n - length l0); simpl; [apply star_1; assumption|constructor].
      * rewrite !nth_error_app1 by assumption. constructor.
  - apply list_select_eq in H1.
    destruct H1 as [(-> & [=-> ->] & ->) | [(l4 & <- & ->) | (l4 & -> & <-)]].
    + exists (subst (read_env l) t2).
      split; [constructor|].
      apply star_1, iota_subst_left. assumption.
    + exists (subst (read_env l) t). split; [|constructor].
      rewrite <- select2_app_assoc.
      erewrite length_select; constructor.
    + exists (subst (read_env l) t). split; [|constructor].
      rewrite select2_app_assoc. constructor.
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

Lemma star_reflc {A : Type} (R : A -> A -> Prop) :
  same_rel (star R) (star (reflc R)).
Proof.
  intros x y. split; intros H.
  - eapply star_map_impl with (f := id); [|eassumption].
    intros; left; assumption.
  - induction H.
    + constructor.
    + destruct H as [H | ->].
      * econstructor; eassumption.
      * assumption.
Qed.

Lemma weak_diamond_confluent {A : Type} (R : A -> A -> Prop) :
  weak_diamond R -> confluent R.
Proof.
  intros H.
  apply weak_diamond_diamond_reflc, diamond_is_confluent in H.
  eapply diamond_ext; [|eassumption].
  apply star_reflc.
Qed.

Lemma iota_weak_diamond :
  forall defs, weak_diamond (iota defs).
Proof.
  intros defs t1 t2 t3 H12. revert t3.
  induction H12; intros t4 H14; inversion H14; subst.
  - left. congruence.
  - destruct (IHiota _ H2) as [-> | (t4 & Ht24 & Ht34)]; [left; reflexivity|right].
    exists (app t4 t3). split; constructor; assumption.
  - right. exists (app t2 t5). split; constructor; assumption.
  - right. exists (app t5 t2). split; constructor; assumption.
  - destruct (IHiota _ H2) as [-> | (t4 & Ht24 & Ht34)]; [left; reflexivity|right].
    exists (app t3 t4). split; constructor; assumption.
  - destruct (IHiota _ H0) as [-> | (t4 & Ht2' & Ht34)]; [left; reflexivity|right].
    exists (abs t4). split; constructor; assumption.
  - apply list_select_eq in H1.
    destruct H1 as [(-> & -> & ->) | [(l4 & <- & ->) | (l4 & -> & <-)]].
    + destruct (IHiota _ H2) as [-> | (t4 & Ht24 & Ht34)]; [left; reflexivity|right].
      exists (constr tag (l1 ++ t4 :: l2)). split; constructor; assumption.
    + right.
      exists (constr tag (l0 ++ t3 :: l4 ++ t2 :: l2)). split.
      * rewrite select2_app_assoc. constructor; assumption.
      * rewrite <- !select2_app_assoc. constructor; assumption.
    + right.
      exists (constr tag (l1 ++ t2 :: l4 ++ t3 :: l3)). split.
      * rewrite <- !select2_app_assoc. constructor; assumption.
      * rewrite select2_app_assoc. constructor; assumption.
  - destruct (IHiota _ H2) as [-> | (t4 & Ht24 & Ht34)]; [left; reflexivity|right].
    exists (switch t4 l). split; constructor; assumption.
  - right. exists (switch t2 (l1 ++ (p, t3) :: l2)).
    split; constructor; assumption.
  - right. exists (switch t3 (l1 ++ (p, t2) :: l2)).
    split; constructor; assumption.
  - apply list_select_eq in H1.
    destruct H1 as [(-> & [=-> ->] & ->) | [(l4 & <- & ->) | (l4 & -> & <-)]].
    + destruct (IHiota _ H2) as [-> | (t4 & Ht24 & Ht34)]; [left; reflexivity|right].
      exists (switch t (l1 ++ (p, t4) :: l2)). split; constructor; assumption.
    + right.
      exists (switch t (l0 ++ (p0, t5) :: l4 ++ (p, t2) :: l2)). split.
      * rewrite select2_app_assoc. constructor; assumption.
      * rewrite <- !select2_app_assoc. constructor; assumption.
    + right.
      exists (switch t (l1 ++ (p, t2) :: l4 ++ (p0, t5) :: l3)). split.
      * rewrite <- !select2_app_assoc. constructor; assumption.
      * rewrite select2_app_assoc. constructor; assumption.
Qed.

Lemma iota_confluent :
  forall defs, confluent (iota defs).
Proof.
  intros defs. apply weak_diamond_confluent, iota_weak_diamond.
Qed.

Lemma beta_iota_confluent :
  forall defs, confluent (union (iota defs) beta).
Proof.
  intros defs.
  apply commuting_confluent.
  - apply iota_confluent.
  - apply beta_confluent.
  - apply strongly_commute_commutes, beta_iota_strongly_commute.
Qed.
