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

Definition betaiota defs := union (iota defs) beta.


Inductive is_head : term -> Prop :=
| is_head_var : forall n, is_head (var n)
| is_head_dvar : forall n, is_head (dvar n).

Inductive is_head_betaiota : list term -> term -> Prop :=
| is_head_betaiota_var : forall defs n, is_head_betaiota defs (var n)
| is_head_betaiota_dvar : forall defs n, nth_error defs n = None -> is_head_betaiota defs (dvar n).

Inductive hctx : Type :=
| h_hole : hctx
| h_app : hctx -> term -> hctx
| h_switch : hctx -> list (nat * term) -> hctx.

Fixpoint fill_hctx (h : hctx) (t : term) : term :=
  match h with
  | h_hole => t
  | h_app h t2 => app (fill_hctx h t) t2
  | h_switch h l => switch (fill_hctx h t) l
  end.


Fixpoint compose_hctx (h1 h2 : hctx) : hctx :=
  match h1 with
  | h_hole => h2
  | h_app h t => h_app (compose_hctx h h2) t
  | h_switch h l => h_switch (compose_hctx h h2) l
  end.

Theorem fill_compose :
  forall h1 h2 t, fill_hctx (compose_hctx h1 h2) t = fill_hctx h1 (fill_hctx h2 t).
Proof.
  induction h1; simpl in *; congruence.
Qed.

Definition in_ctx (P : term -> Prop) t := exists h t2, P t2 /\ t = fill_hctx h t2.
Definition is_hnf := in_ctx is_head.
Definition is_hnf_betaiota defs := in_ctx (is_head_betaiota defs).

Definition in_ctx_hole :
  forall (P : term -> Prop) t, P t -> in_ctx P t.
Proof.
  intros P t H; exists h_hole; exists t. split; [assumption|reflexivity].
Qed.

Definition in_ctx_fill :
  forall P h t, in_ctx P t -> in_ctx P (fill_hctx h t).
Proof.
  intros P h t (h2 & t2 & H & Ht).
  exists (compose_hctx h h2). exists t2.
  split; [assumption|]. rewrite Ht, fill_compose. reflexivity.
Qed.

Lemma in_ctx_app : forall P t1 t2, in_ctx P t1 -> in_ctx P (app t1 t2).
Proof.
  intros P t1 t2. apply in_ctx_fill with (h := h_app h_hole t2).
Qed.

Lemma in_ctx_switch : forall P t l, in_ctx P t -> in_ctx P (switch t l).
Proof.
  intros P t l. apply in_ctx_fill with (h := h_switch h_hole l).
Qed.

Lemma in_ctx_imp : forall (P Q : term -> Prop), (forall t, P t -> Q t) -> forall t, in_ctx P t -> in_ctx Q t.
Proof.
  intros P Q H t (h & t2 & Ht2 & ->).
  exists h. exists t2. split; [|reflexivity]. apply H; assumption.
Qed.

Lemma is_hnf_var : forall n, is_hnf (var n).
Proof.
  intros n. apply in_ctx_hole. constructor.
Qed.

Lemma is_hnf_dvar : forall n, is_hnf (dvar n).
Proof.
  intros n. apply in_ctx_hole. constructor.
Qed.

Lemma is_hnf_ctx : forall h t, is_hnf t -> is_hnf (fill_hctx h t).
Proof.
  apply in_ctx_fill.
Qed.

Lemma is_hnf_app : forall t1 t2, is_hnf t1 -> is_hnf (app t1 t2).
Proof.
  apply in_ctx_app.
Qed.

Lemma is_hnf_switch : forall t l, is_hnf t -> is_hnf (switch t l).
Proof.
  apply in_ctx_switch.
Qed.

Inductive is_value : term -> Prop :=
| is_value_abs : forall t, is_value (abs t)
| is_value_constr : forall tag l, is_value (constr tag l)
| is_value_hnf : forall t, is_hnf t -> is_value t.

Inductive beta_err : term -> Prop :=
| beta_err_app_constr : forall tag l t, beta_err (app (constr tag l) t)
| beta_err_switch_abs : forall t l, beta_err (switch (abs t) l)
| beta_err_switch_overflow : forall tag l l1, length l1 <= tag -> beta_err (switch (constr tag l) l1)
| beta_err_switch_numvars: forall l p t l1 l2, length l <> p -> beta_err (switch (constr (length l1) l) (l1 ++ (p, t) :: l2)).

Definition beta_herr := in_ctx beta_err.

Lemma beta_herr_err :
  forall t, beta_err t -> beta_herr t.
Proof.
  apply in_ctx_hole.
Qed.

Lemma beta_herr_ctx :
  forall h t, beta_herr t -> beta_herr (fill_hctx h t).
Proof.
  apply in_ctx_fill.
Qed.

Inductive beta_red : term -> term -> Prop :=
| beta_red_lam : forall t1 t2, beta_red (app (abs t1) t2) (subst1 t2 t1)
| beta_red_switch : forall l t l1 l2, beta_red (switch (constr (length l1) l) (l1 ++ (length l, t) :: l2)) (subst (read_env l) t).

Definition beta_hnf t1 t2 :=
  exists h t3 t4, t1 = fill_hctx h t3 /\ t2 = fill_hctx h t4 /\ beta_red t3 t4.

Definition beta_hnf_ctx :
  forall h t1 t2, beta_hnf t1 t2 -> beta_hnf (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros h t1 t2 (h2 & t3 & t4 & -> & -> & Hbeta).
  rewrite <- !fill_compose. eexists; eauto.
Qed.

Definition beta_hnf_red :
  forall t1 t2, beta_red t1 t2 -> beta_hnf t1 t2.
Proof.
  intros t1 t2 H. exists h_hole, t1, t2.
  auto.
Qed.

Lemma beta_hnf_beta :
  forall t1 t2, beta_hnf t1 t2 -> beta t1 t2.
Proof.
  intros t1 t2 (h & t3 & t4 & -> & -> & Hbeta).
  induction h; simpl in *; try (constructor; assumption).
  inversion Hbeta; constructor; assumption.
Qed.

Lemma beta_progress :
  forall t, is_value t \/ beta_herr t \/ exists t2, beta_hnf t t2.
Proof.
  induction t using term_ind2.
  - left. constructor. apply is_hnf_var.
  - left. constructor. apply is_hnf_dvar.
  - left. constructor.
  - destruct IHt1 as [Hval | [Herr | [t3 Ht3]]].
    + inversion Hval; subst.
      * right. right. eexists. apply beta_hnf_red. constructor.
      * right. left. apply beta_herr_err, beta_err_app_constr.
      * left. constructor. apply is_hnf_app. assumption.
    + right. left. apply in_ctx_app; eassumption.
    + right. right. eexists.
      apply beta_hnf_ctx with (h := h_app h_hole t2); eassumption.
  - left. constructor.
  - destruct IHt as [Hval | [Herr | [t2 Ht2]]].
    + inversion Hval; subst.
      * right. left. apply beta_herr_err, beta_err_switch_abs.
      * right.
        destruct (nth_error m tag) as [[p t]|] eqn:Htag.
        -- apply nth_error_split in Htag.
           destruct Htag as (l1 & l2 & -> & <-).
           destruct (Nat.eq_dec (length l) p).
           ++ subst. right. eexists. apply beta_hnf_red. constructor.
           ++ left. apply beta_herr_err, beta_err_switch_numvars. assumption.
        -- left. apply beta_herr_err, beta_err_switch_overflow.
           apply nth_error_None. assumption.
      * left. constructor. apply is_hnf_switch. assumption.
    + right. left. apply in_ctx_switch; eassumption.
    + right. right. eexists.
      apply beta_hnf_ctx with (h := h_switch h_hole m); eassumption.
Qed.


Definition mk_merge {A : Type} (l1 l2 : option (list A)) :=
  match l1, l2 with
  | Some l1, Some l2 => Some (l1 ++ l2)
  | _, _ => None
  end.

Arguments mk_merge {A} l1 l2 : simpl nomatch.

Lemma Forall_1 {A : Type} (P : A -> Prop) x : Forall P (x :: nil) <-> P x.
Proof.
  split; intros H.
  - inversion H; subst; assumption.
  - constructor; [assumption|constructor].
Qed.

Fixpoint compare_branches (l1 l2 : list (nat * term)) :=
  match l1, l2 with
  | nil, nil => Some nil
  | (p1, t1) :: l1, (p2, t2) :: l2 =>
    if Nat.eq_dec p1 p2 then mk_merge (Some ((t1, t2) :: nil)) (compare_branches l1 l2) else None
  | _, _ => None
  end.

Lemma compare_branches_app :
  forall l1 l2 l3 l4, length l1 = length l3 ->
                 compare_branches (l1 ++ l2) (l3 ++ l4) = mk_merge (compare_branches l1 l3) (compare_branches l2 l4).
Proof.
  induction l1; intros l2 l3 l4 Hlen; destruct l3; simpl in *.
  - destruct compare_branches; reflexivity.
  - discriminate.
  - discriminate.
  - destruct a; destruct p; simpl.
    destruct Nat.eq_dec; [|reflexivity].
    rewrite IHl1 by congruence.
    destruct compare_branches; simpl in *; [|reflexivity].
    destruct compare_branches; simpl in *; reflexivity.
Qed.

Fixpoint compare_hnf (t1 t2 : term) :=
  match t1, t2 with
  | var n1, var n2 => if Nat.eq_dec n1 n2 then Some nil else None
  | dvar d1, dvar d2 => if Nat.eq_dec d1 d2 then Some nil else None
  | app t1 u1, app t2 u2 => mk_merge (compare_hnf t1 t2) (Some ((u1, u2) :: nil))
  | switch t1 l1, switch t2 l2 => mk_merge (compare_hnf t1 t2) (compare_branches l1 l2)
  | _, _ => None
  end.

Definition curry {A B C : Type} (f : A * B -> C) x y := f (x, y).
Definition uncurry {A B C : Type} (f : A -> B -> C) '(x, y) := f x y.
Definition flip {A B C : Type} (f : A -> B -> C) x y := f y x.
Definition symc {A : Type} (R : A -> A -> Prop) := union R (flip R).
Definition convertible {A : Type} (R : A -> A -> Prop) := star (symc R).

Lemma convertible_refl {A : Type} (R : A -> A -> Prop) x : convertible R x x.
Proof.
  intros; apply star_refl.
Qed.

Lemma symc_sym {A : Type} (R : A -> A -> Prop) :
  forall x y, symc R x y -> symc R y x.
Proof.
  intros x y [H | H]; [right | left]; assumption.
Qed.

Lemma star_sym {A : Type} (R : A -> A -> Prop) (Hsym : forall x y, R x y -> R y x) :
  forall x y, star R x y -> star R y x.
Proof.
  intros x y H; induction H.
  - apply star_refl.
  - eapply star_compose; [eassumption|apply star_1, Hsym; assumption].
Qed.

Lemma convertible_sym {A : Type} (R : A -> A -> Prop) :
  forall x y, convertible R x y -> convertible R y x.
Proof.
  apply star_sym, symc_sym.
Qed.

Lemma beta_convertible_app :
  forall t1 t2 u1 u2, convertible beta t1 t2 -> convertible beta u1 u2 -> convertible beta (app t1 u1) (app t2 u2).
Proof.
  intros t1 t2 u1 u2 Ht Hu.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => app t u1); [|eassumption].
    intros x y [Hxy | Hxy]; [left|right]; constructor; assumption.
  - eapply star_map_impl with (f := fun u => app t2 u); [|eassumption].
    intros x y [Hxy | Hxy]; [left|right]; constructor; assumption.
Qed.

Lemma beta_convertible_switch :
  forall t1 t2 l1 l2, convertible beta t1 t2 -> Forall2 (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ convertible beta t1 t2) l1 l2 -> convertible beta (switch t1 l1) (switch t2 l2).
Proof.
  intros t1 t2 l1 l2 Ht Hl.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => switch t l1); [|eassumption].
    intros x y [Hxy | Hxy]; [left|right]; constructor; assumption.
  - apply star_list with (RA := (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ symc beta t1 t2)).
    + intros la lb [? u1] [p u2] [-> Hu].
      destruct Hu as [Hu | Hu]; [left | right]; constructor; assumption.
    + eapply Forall2_impl; [|eassumption].
      intros [? u1] [p u2] [-> Hu].
      eapply star_map_impl; [|eassumption].
      intros; tauto.
Qed.

Lemma betaiota_convertible_app :
  forall defs t1 t2 u1 u2, convertible (betaiota defs) t1 t2 -> convertible (betaiota defs) u1 u2 -> convertible (betaiota defs) (app t1 u1) (app t2 u2).
Proof.
  intros defs t1 t2 u1 u2 Ht Hu.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => app t u1); [|eassumption].
    intros x y [[Hxy | Hxy] | [Hxy | Hxy]]; [left; left|left; right|right; left|right; right]; constructor; assumption.
  - eapply star_map_impl with (f := fun u => app t2 u); [|eassumption].
    intros x y [[Hxy | Hxy] | [Hxy | Hxy]]; [left; left|left; right|right; left|right; right]; constructor; assumption.
Qed.

Lemma betaiota_convertible_switch :
  forall defs t1 t2 l1 l2, convertible (betaiota defs) t1 t2 -> Forall2 (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ convertible (betaiota defs) t1 t2) l1 l2 -> convertible (betaiota defs) (switch t1 l1) (switch t2 l2).
Proof.
  intros defs t1 t2 l1 l2 Ht Hl.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => switch t l1); [|eassumption].
    intros x y [[Hxy | Hxy] | [Hxy | Hxy]]; [left; left|left; right|right; left|right; right]; constructor; assumption.
  - apply star_list with (RA := (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ symc (betaiota defs) t1 t2)).
    + intros la lb [? u1] [p u2] [-> Hu].
      destruct Hu as [[Hu | Hu] | [Hu | Hu]]; [left; left|left; right|right; left|right; right]; constructor; assumption.
    + eapply Forall2_impl; [|eassumption].
      intros [? u1] [p u2] [-> Hu].
      eapply star_map_impl; [|eassumption].
      intros; tauto.
Qed.


Lemma Forall3_app :
  forall (A B C : Type) (P : A -> B -> C -> Prop) l1a l1b l1c l2a l2b l2c, Forall3 P l1a l1b l1c -> Forall3 P l2a l2b l2c -> Forall3 P (l1a ++ l2a) (l1b ++ l2b) (l1c ++ l2c).
Proof.
  intros A B C P l1a l1b l1c l2a l2b l2c H1 H2; induction H1; simpl in *.
  - assumption.
  - constructor; assumption.
Qed.

Lemma compare_branches_trans :
  forall l1 l2 l3 l12 l23, compare_branches l1 l2 = Some l12 -> compare_branches l2 l3 = Some l23 ->
                      exists l13, compare_branches l1 l3 = Some l13 /\ Forall3 (fun '(x1, x2) '(y2, y3) '(z1, z3) => x1 = z1 /\ x2 = y2 /\ y3 = z3) l12 l23 l13.
Proof.
  induction l1; intros l2 l3 l12 l23 H12 H23; destruct l2; simpl in *; try discriminate; destruct l3; simpl in *; try discriminate.
  - exists nil. split; [reflexivity|].
    injection H12 as H12; injection H23 as H23; subst. constructor.
  - destruct a; discriminate.
  - destruct p; discriminate.
  - destruct a; destruct p; destruct p0.
    destruct Nat.eq_dec; [|discriminate].
    destruct Nat.eq_dec; [|discriminate].
    destruct Nat.eq_dec; [|congruence].
    destruct (compare_branches l1 l2) eqn:Hl12; [|discriminate].
    destruct (compare_branches l2 l3) eqn:Hl23; [|discriminate].
    specialize (IHl1 _ _ _ _ Hl12 Hl23). destruct IHl1 as (l13 & Hl13 & Hall).
    exists ((t, t1) :: l13). rewrite Hl13.
    split; [reflexivity|].
    injection H12 as H12; injection H23 as H23; subst.
    constructor; [|assumption].
    tauto.
Qed.

Lemma compare_hnf_trans :
  forall t1 t2 t3 l12 l23, compare_hnf t1 t2 = Some l12 -> compare_hnf t2 t3 = Some l23 ->
                      exists l13, compare_hnf t1 t3 = Some l13 /\ Forall3 (fun '(x1, x2) '(y2, y3) '(z1, z3) => x1 = z1 /\ x2 = y2 /\ y3 = z3) l12 l23 l13.
Proof.
  induction t1; intros t2 t3 l12 l23 H12 H23; destruct t2; simpl in *; try discriminate; destruct t3; simpl in *; try discriminate.
  - destruct Nat.eq_dec; [|discriminate]. destruct Nat.eq_dec; [|discriminate].
    exists nil. split; [destruct Nat.eq_dec; congruence|].
    injection H12 as H12; injection H23 as H23; subst. constructor.
  - destruct Nat.eq_dec; [|discriminate]. destruct Nat.eq_dec; [|discriminate].
    exists nil. split; [destruct Nat.eq_dec; congruence|].
    injection H12 as H12; injection H23 as H23; subst. constructor.
  - specialize (IHt1_1 t2_1 t3_1).
    destruct compare_hnf as [l12a|]; [|discriminate].
    destruct compare_hnf as [l23a|]; [|discriminate].
    simpl in *; injection H12 as H12; injection H23 as H23.
    destruct (IHt1_1 _ _ eq_refl eq_refl) as (l13a & H13 & Hall).
    exists (l13a ++ (t1_2, t3_2) :: nil). split.
    + rewrite H13; reflexivity.
    + subst. apply Forall3_app; [assumption|].
      constructor; [|constructor]. tauto.
  - destruct (compare_hnf t1 t2) eqn:Hl12; [|discriminate].
    destruct (compare_hnf t2 t3) eqn:Hl23; [|discriminate].
    specialize (IHt1 _ _ _ _ Hl12 Hl23).
    destruct IHt1 as (l13 & Hl13 & Hall).
    destruct (compare_branches l l0) eqn:Hb12; [|discriminate].
    destruct (compare_branches l0 l1) eqn:Hb23; [|discriminate].
    destruct (compare_branches_trans _ _ _ _ _ Hb12 Hb23) as (l13b & Hl13b & Hallb).
    exists (l13 ++ l13b). rewrite Hl13, Hl13b.
    split; [reflexivity|].
    injection H12 as H12; injection H23 as H23; subst.
    apply Forall3_app; assumption.
Qed.

Definition all_are {A : Type} (R : A -> Prop) (x : option (list A)) :=
  match x with
  | Some l => Forall R l
  | None => False
  end.

Lemma all_are_impl {A : Type} (R1 R2 : A -> Prop) (H : forall x, R1 x -> R2 x) :
  forall l, all_are R1 l -> all_are R2 l.
Proof.
  intros [l|] Hl; [|assumption]; simpl in *.
  eapply Forall_impl; eassumption.
Qed.

Lemma all_are_merge :
  forall A (R : A -> Prop) l1 l2, all_are R l1 -> all_are R l2 -> all_are R (mk_merge l1 l2).
Proof.
  intros A R [l1|] [l2|] H1 H2; simpl in *; try tauto.
  apply Forall_app_iff; tauto.
Qed.

Lemma all_are_merge_iff :
  forall A (R : A -> Prop) l1 l2, all_are R (mk_merge l1 l2) <-> all_are R l1 /\ all_are R l2.
Proof.
  intros A R [l1|] [l2|]; simpl in *; try tauto.
  rewrite Forall_app_iff; tauto.
Qed.

Definition all_are2 {A B : Type} (R : A -> B -> Prop) l := all_are (uncurry R) l.
Lemma all_are2_impl {A B : Type} (R1 R2 : A -> B -> Prop) (H : forall x y, R1 x y -> R2 x y) :
  forall l, all_are2 R1 l -> all_are2 R2 l.
Proof.
  apply all_are_impl.
  intros [x y] Hxy; apply H; assumption.
Qed.

Lemma all_are2_merge :
  forall A B (R : A -> B -> Prop) l1 l2, all_are2 R l1 -> all_are2 R l2 -> all_are2 R (mk_merge l1 l2).
Proof.
  intros; apply all_are_merge; assumption.
Qed.

Lemma all_are2_merge_iff :
  forall A B (R : A -> B -> Prop) l1 l2, all_are2 R (mk_merge l1 l2) <-> all_are2 R l1 /\ all_are2 R l2.
Proof.
  intros; apply all_are_merge_iff.
Qed.

Lemma Forall3_select3 :
  forall A B C (P : C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall3 (fun _ _ c => P c) l1 l2 l3 -> Forall P l3.
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; tauto.
Qed.

Lemma Forall3_and :
  forall A B C (P Q : A -> B -> C -> Prop) l1 l2 l3, Forall3 P l1 l2 l3 -> Forall3 Q l1 l2 l3 -> Forall3 (fun a b c => P a b c /\ Q a b c) l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H1 H2; induction H1; simpl in *; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall3_unselect1 :
  forall A B C (P : A -> Prop) (R : A -> B -> C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall P l1 -> Forall3 R l1 l2 l3 -> Forall3 (fun a _ _ => P a) l1 l2 l3.
Proof.
  intros A B C P R l1 l2 l3 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.

Lemma Forall3_unselect2 :
  forall A B C (P : B -> Prop) (R : A -> B -> C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall P l2 -> Forall3 R l1 l2 l3 -> Forall3 (fun _ b _ => P b) l1 l2 l3.
Proof.
  intros A B C P R l1 l2 l3 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.

Lemma compare_hnf_all_are_trans :
  forall t1 t2 t3 P12 P23, all_are2 P12 (compare_hnf t1 t2) -> all_are2 P23 (compare_hnf t2 t3) -> all_are2 (fun x z => exists y, P12 x y /\ P23 y z) (compare_hnf t1 t3).
Proof.
  intros t1 t2 t3 P12 P23 H12 H13.
  destruct (compare_hnf t1 t2) as [l12|] eqn:Hhnf12; simpl in *; [|tauto].
  destruct (compare_hnf t2 t3) as [l23|] eqn:Hhnf23; simpl in *; [|tauto].
  destruct (compare_hnf_trans _ _ _ _ _ Hhnf12 Hhnf23) as (l13 & Hhnf13 & Hall).
  rewrite Hhnf13; simpl.
  eapply Forall3_select3, Forall3_impl; [|eapply Forall3_and; [eassumption|apply Forall3_and with (P := fun x _ _ => uncurry P12 x) (Q := fun _ y _ => uncurry P23 y)]].
  - intros [x1 x2] [y2 y3] [z1 z3] ((-> & -> & ->) & Hxy & Hyz). exists y2. split; [exact Hxy | exact Hyz].
  - eapply Forall3_unselect1; eassumption.
  - eapply Forall3_unselect2; eassumption.
Qed.

Lemma compare_branches_refl :
  forall l, all_are2 eq (compare_branches l l).
Proof.
  induction l; simpl in *.
  - constructor.
  - destruct a. destruct Nat.eq_dec; [|congruence].
    apply all_are2_merge; [|assumption].
    simpl. constructor; [|constructor]. reflexivity.
Qed.

Lemma compare_hnf_refl :
  forall t, is_hnf t -> all_are2 eq (compare_hnf t t).
Proof.
  intros t (h & t1 & Hhead & Hfill); subst. induction h.
  - simpl. inversion Hhead; subst; simpl; destruct Nat.eq_dec; simpl; try tauto; apply Forall_nil.
  - simpl. apply all_are2_merge; [assumption|].
    simpl. apply Forall_1. reflexivity.
  - simpl. apply all_are2_merge; [assumption|].
    apply compare_branches_refl.
Qed.

Lemma beta_for_hnf :
  forall t1 t2, is_hnf t1 -> beta t1 t2 -> all_are2 (reflc beta) (compare_hnf t1 t2).
Proof.
  intros t1 t2 (h & t & Hhead & Hfill); revert t2; subst.
  induction h; intros t2 Hbeta; inversion Hbeta; subst; simpl in *; subst; try solve [inversion Hhead].
  - apply all_are2_merge; simpl.
    + apply IHh; assumption.
    + apply Forall_1. right; reflexivity.
  - apply all_are2_merge; simpl.
    + eapply all_are2_impl; [|apply compare_hnf_refl; exists h; exists t; split; [assumption|reflexivity]].
      intros x y ->; right; reflexivity.
    + apply Forall_1. left; assumption.
  - destruct h; simpl in *; try discriminate; subst.
    inversion Hhead.
  - apply all_are2_merge; simpl.
    + apply IHh; assumption.
    + eapply all_are2_impl; [|apply compare_branches_refl].
      intros x y ->; right; reflexivity.
  - apply all_are2_merge; simpl.
    + eapply all_are2_impl; [|apply compare_hnf_refl; exists h; exists t; split; [assumption|reflexivity]].
      intros x y ->; right; reflexivity.
    + rewrite compare_branches_app by reflexivity.
      simpl.
      apply all_are2_merge; [eapply all_are2_impl; [|apply compare_branches_refl]; intros x y ->; right; reflexivity|].
      destruct Nat.eq_dec; [|tauto].
      apply all_are2_merge; [|eapply all_are2_impl; [|apply compare_branches_refl]; intros x y ->; right; reflexivity].
      simpl. constructor; [|constructor]. left; assumption.
  - destruct h; simpl in *; try discriminate; subst.
    inversion Hhead.
Qed.

Lemma beta_is_hnf :
  forall t1 t2, is_hnf t1 -> beta t1 t2 -> is_hnf t2.
Proof.
  intros t1 t2 (h & t & Hhead & Hfill); revert t2; subst.
  induction h; intros t2 Hbeta; inversion Hbeta; subst; simpl in *; subst; try solve [inversion Hhead].
  - apply IHh in H2. apply is_hnf_app; assumption.
  - apply is_hnf_app. exists h; exists t; tauto.
  - destruct h; simpl in *; try discriminate; subst; inversion Hhead.
  - apply IHh in H2. apply is_hnf_switch. assumption.
  - apply is_hnf_switch. exists h; exists t; tauto.
  - destruct h; simpl in *; try discriminate; subst; inversion Hhead.
Qed.

Lemma is_head_betaiota_head :
  forall defs t, is_head_betaiota defs t -> is_head t.
Proof.
  intros defs t H; inversion H; subst; constructor.
Qed.

Lemma iota_for_hnf :
  forall defs t1 t2, is_hnf_betaiota defs t1 -> iota defs t1 t2 -> all_are2 (reflc (iota defs)) (compare_hnf t1 t2).
Proof.
  intros defs t1 t2 (h & t & Hhead & Hfill); revert t2; subst.
  induction h; intros t2 Hbeta; inversion Hbeta; subst; simpl in *; subst; try solve [inversion Hhead].
  - inversion Hhead. congruence.
  - apply all_are2_merge; simpl.
    + apply IHh; assumption.
    + apply Forall_1. right; reflexivity.
  - apply all_are2_merge; simpl.
    + eapply all_are2_impl; [|apply compare_hnf_refl; exists h; exists t; split; [eapply is_head_betaiota_head; eassumption|reflexivity]].
      intros x y ->; right; reflexivity.
    + apply Forall_1. left; assumption.
  - apply all_are2_merge; simpl.
    + apply IHh; assumption.
    + eapply all_are2_impl; [|apply compare_branches_refl].
      intros x y ->; right; reflexivity.
  - apply all_are2_merge; simpl.
    + eapply all_are2_impl; [|apply compare_hnf_refl; exists h; exists t; split; [eapply is_head_betaiota_head; eassumption|reflexivity]].
      intros x y ->; right; reflexivity.
    + rewrite compare_branches_app by reflexivity.
      simpl.
      apply all_are2_merge; [eapply all_are2_impl; [|apply compare_branches_refl]; intros x y ->; right; reflexivity|].
      destruct Nat.eq_dec; [|tauto].
      apply all_are2_merge; [|eapply all_are2_impl; [|apply compare_branches_refl]; intros x y ->; right; reflexivity].
      simpl. constructor; [|constructor]. left; assumption.
Qed.

Lemma beta_is_hnf_betaiota :
  forall defs t1 t2, is_hnf_betaiota defs t1 -> beta t1 t2 -> is_hnf_betaiota defs t2.
Proof.
  intros defs t1 t2 (h & t & Hhead & Hfill); revert t2; subst.
  induction h; intros t2 Hbeta; inversion Hbeta; subst; simpl in *; subst; try solve [inversion Hhead].
  - apply IHh in H2. apply in_ctx_app; assumption.
  - apply in_ctx_app. exists h; exists t; tauto.
  - destruct h; simpl in *; try discriminate; subst; inversion Hhead.
  - apply IHh in H2. apply in_ctx_switch. assumption.
  - apply in_ctx_switch. exists h; exists t; tauto.
  - destruct h; simpl in *; try discriminate; subst; inversion Hhead.
Qed.

Lemma iota_is_hnf_betaiota :
  forall defs t1 t2, is_hnf_betaiota defs t1 -> iota defs t1 t2 -> is_hnf_betaiota defs t2.
  intros defs t1 t2 (h & t & Hhead & Hfill); revert t2; subst.
  induction h; intros t2 Hbeta; inversion Hbeta; subst; simpl in *; subst; try solve [inversion Hhead].
  - inversion Hhead; congruence.
  - apply IHh in H2. apply in_ctx_app; assumption.
  - apply in_ctx_app. exists h; exists t; tauto.
  - apply IHh in H2. apply in_ctx_switch. assumption.
  - apply in_ctx_switch. exists h; exists t; tauto.
Qed.

Lemma star_beta_for_hnf :
  forall t1 t2, is_hnf t1 -> star beta t1 t2 -> all_are2 (star beta) (compare_hnf t1 t2).
Proof.
  intros t1 t2 Ht1 Ht12. induction Ht12.
  - eapply all_are2_impl; [|apply compare_hnf_refl; assumption].
    intros ? ? ->; simpl; apply star_refl.
  - assert (is_hnf y) by (eapply beta_is_hnf; eassumption).
    apply beta_for_hnf in H; [|assumption].
    eapply all_are2_impl; [|eapply compare_hnf_all_are_trans; [eassumption|apply IHHt12; assumption]].
    intros u v (w & Huw & Hwv); simpl in *.
    destruct Huw as [Huw | ->]; [econstructor; eassumption|assumption].
Qed.

Lemma star_betaiota_for_hnf :
  forall defs t1 t2, is_hnf_betaiota defs t1 -> star (betaiota defs) t1 t2 -> all_are2 (star (betaiota defs)) (compare_hnf t1 t2).
Proof.
  intros defs t1 t2 Ht1 Ht12. induction Ht12.
  - eapply all_are2_impl; [|eapply compare_hnf_refl, (in_ctx_imp _ _ (is_head_betaiota_head defs)); assumption].
    intros ? ? ->; simpl; apply star_refl.
  - destruct H as [H | H].
    + assert (is_hnf_betaiota defs y) by (eapply iota_is_hnf_betaiota; eassumption).
      apply iota_for_hnf in H; [|eassumption].
      eapply all_are2_impl; [|eapply compare_hnf_all_are_trans; [eassumption|apply IHHt12; assumption]].
      intros u v (w & Huw & Hwv); simpl in *.
      destruct Huw as [Huw | ->]; [econstructor; [left|]; eassumption|assumption].
    + assert (is_hnf_betaiota defs y) by (eapply beta_is_hnf_betaiota; eassumption).
      apply beta_for_hnf in H; [|eapply (in_ctx_imp _ _ (is_head_betaiota_head defs)); eassumption].
      eapply all_are2_impl; [|eapply compare_hnf_all_are_trans; [eassumption|apply IHHt12; assumption]].
      intros u v (w & Huw & Hwv); simpl in *.
      destruct Huw as [Huw | ->]; [econstructor; [right|]; eassumption|assumption].
Qed.

Lemma star_flip :
  forall (A : Type) (R : A -> A -> Prop) x y, star R x y <-> star (flip R) y x.
Proof.
  intros A R x y; split; intros H; induction H; try apply star_refl; eapply star_compose; try eassumption; apply star_1; assumption.
Qed.

Lemma common_reduce_convertible :
  forall (A : Type) (R : A -> A -> Prop) x y z, star R x z -> star R y z -> convertible R x y.
Proof.
  intros A R x y z Hxz Hyz.
  eapply star_compose.
  - eapply star_map_impl with (f := fun x => x); [|eassumption].
    intros; left; assumption.
  - eapply star_map_impl with (f := fun x => x); [|apply -> star_flip; eassumption].
    intros; right; assumption.
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

Definition flipl {A : Type} (l : option (list (A * A))) :=
  match l with None => None | Some l => Some (map (fun '(x, y) => (y, x)) l) end.

Lemma mk_merge_flipl :
  forall (A : Type) (l1 l2 : option (list (A * A))), flipl (mk_merge l1 l2) = mk_merge (flipl l1) (flipl l2).
Proof.
  intros A [l1|] [l2|]; simpl in *; try reflexivity; rewrite map_app; reflexivity.
Qed.

Lemma compare_branches_flip :
  forall l1 l2, compare_branches l2 l1 = flipl (compare_branches l1 l2).
Proof.
  induction l1; intros l2; destruct l2; simpl in *.
  - reflexivity.
  - destruct p; reflexivity.
  - destruct a; reflexivity.
  - destruct p; destruct a; simpl in *.
    destruct Nat.eq_dec; simpl in *; destruct Nat.eq_dec; simpl in *; try congruence.
    rewrite IHl1. destruct compare_branches; simpl in *; reflexivity.
Qed.

Lemma compare_hnf_flip :
  forall t1 t2, compare_hnf t2 t1 = flipl (compare_hnf t1 t2).
Proof.
  induction t1; intros t2; destruct t2; simpl in *; try congruence.
  - destruct Nat.eq_dec; destruct Nat.eq_dec; simpl in *; congruence.
  - destruct Nat.eq_dec; destruct Nat.eq_dec; simpl in *; congruence.
  - rewrite IHt1_1; simpl.
    destruct compare_hnf; simpl in *; try rewrite map_app; reflexivity.
  - rewrite IHt1; simpl.
    rewrite mk_merge_flipl, compare_branches_flip. reflexivity.
Qed.

Lemma all_are2_flip :
  forall (A : Type) (P : A -> A -> Prop) l, all_are2 P (flipl l) <-> all_are2 (flip P) l.
Proof.
  intros A P [l|]; simpl in *; [|reflexivity].
  rewrite Forall_map.
  eapply Forall_ext; intros [a b]; reflexivity.
Qed.

Lemma convertible_compare_hnf :
  forall t1 t2, is_hnf t1 -> is_hnf t2 -> convertible beta t1 t2 -> all_are2 (convertible beta) (compare_hnf t1 t2).
Proof.
  intros t1 t2 Ht1 Ht2 Ht.
  apply convertible_confluent_common_reduce in Ht; [|apply beta_confluent].
  destruct Ht as (t3 & Ht13 & Ht23).
  apply star_beta_for_hnf in Ht13; [|assumption].
  apply star_beta_for_hnf in Ht23; [|assumption].
  rewrite compare_hnf_flip, all_are2_flip in Ht23.
  eapply all_are2_impl; [|eapply compare_hnf_all_are_trans; eassumption].
  intros x y (z & Hxz & Hyz).
  eapply common_reduce_convertible; eassumption.
Qed.

Lemma compare_branches_forall :
  forall l1 l2 R, all_are2 R (compare_branches l1 l2) -> Forall2 (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ R t1 t2) l1 l2.
Proof.
  induction l1; intros l2 R H; destruct l2; simpl in *; try tauto.
  - constructor.
  - destruct a; simpl in *; tauto.
  - destruct a; destruct p; simpl in *.
    destruct Nat.eq_dec; simpl in *; [|tauto].
    rewrite all_are2_merge_iff in H.
    simpl in *; rewrite Forall_1 in H.
    constructor; [tauto|].
    apply IHl1; tauto.
Qed.

Lemma compare_hnf_convertible :
  forall t1 t2, all_are2 (convertible beta) (compare_hnf t1 t2) -> convertible beta t1 t2.
Proof.
  induction t1; intros t2 H12; destruct t2; simpl in *; try tauto.
  - destruct Nat.eq_dec; subst; [apply convertible_refl|simpl in *; tauto].
  - destruct Nat.eq_dec; subst; [apply convertible_refl|simpl in *; tauto].
  - rewrite all_are2_merge_iff in H12; simpl in *.
    apply beta_convertible_app; [apply IHt1_1; tauto|].
    rewrite Forall_1 in H12; apply H12.
  - rewrite all_are2_merge_iff in H12; simpl in *.
    apply beta_convertible_switch; [apply IHt1; tauto|].
    eapply compare_branches_forall; tauto.
Qed.



Lemma convertible_compare_hnf_betaiota :
  forall defs t1 t2, is_hnf_betaiota defs t1 -> is_hnf_betaiota defs t2 -> convertible (betaiota defs) t1 t2 -> all_are2 (convertible (betaiota defs)) (compare_hnf t1 t2).
Proof.
  intros defs t1 t2 Ht1 Ht2 Ht.
  apply convertible_confluent_common_reduce in Ht; [|apply beta_iota_confluent].
  destruct Ht as (t3 & Ht13 & Ht23).
  apply star_betaiota_for_hnf in Ht13; [|assumption].
  apply star_betaiota_for_hnf in Ht23; [|assumption].
  rewrite compare_hnf_flip, all_are2_flip in Ht23.
  eapply all_are2_impl; [|eapply compare_hnf_all_are_trans; eassumption].
  intros x y (z & Hxz & Hyz).
  eapply common_reduce_convertible; eassumption.
Qed.

Lemma compare_hnf_convertible_betaiota :
  forall defs t1 t2, all_are2 (convertible (betaiota defs)) (compare_hnf t1 t2) -> convertible (betaiota defs) t1 t2.
Proof.
  intros defs; induction t1; intros t2 H12; destruct t2; simpl in *; try tauto.
  - destruct Nat.eq_dec; subst; [apply convertible_refl|simpl in *; tauto].
  - destruct Nat.eq_dec; subst; [apply convertible_refl|simpl in *; tauto].
  - rewrite all_are2_merge_iff in H12; simpl in *.
    apply betaiota_convertible_app; [apply IHt1_1; tauto|].
    rewrite Forall_1 in H12; apply H12.
  - rewrite all_are2_merge_iff in H12; simpl in *.
    apply betaiota_convertible_switch; [apply IHt1; tauto|].
    eapply compare_branches_forall; tauto.
Qed.

