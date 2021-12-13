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




Definition valptr := nat.
Definition rthreadptr := nat.
Definition cthreadptr := nat.
Definition threadptr := (nat + nat)%type.

Definition varname := nat.

Definition env := list valptr.

Inductive cont :=
| Kid : cont
| Kapp : valptr -> cont -> cont
| Kswitch : list (nat * term) -> env -> list (list varname * valptr) -> cont -> cont.

Record neutral := mkneutral {
  n_id : varname ;
  n_cont : cont ;
  n_unfold : option valptr ;
}.

Inductive value :=
| Thread : rthreadptr -> value
| Neutral : neutral -> value
| Clos : term -> env -> varname -> valptr -> value
| Block : nat -> list valptr -> value.

Inductive code :=
| Term : term -> env -> code
| Val : valptr -> code.

Record rthread := mkrthread {
  rt_code : code ;
  rt_cont : cont ;
}.



Inductive addr :=
| a_rthread : rthreadptr -> addr
| a_val : valptr -> addr.

Definition env_points_to e a :=
  match a with
  | a_val vp => In vp e
  | _ => False
  end.

Inductive cont_points_to : cont -> addr -> Prop :=
| kapp_points_to_1 : forall vp c, cont_points_to (Kapp vp c) (a_val vp)
| kapp_points_to_2 : forall vp c a, cont_points_to c a -> cont_points_to (Kapp vp c) a
| kswitch_points_to_1 : forall bs e bds c a, env_points_to e a -> cont_points_to (Kswitch bs e bds c) a
| kswitch_points_to_2 : forall bs e bds c a, cont_points_to c a -> cont_points_to (Kswitch bs e bds c) a.

Inductive val_points_to : value -> addr -> Prop :=
| thread_points_to : forall rid, val_points_to (Thread rid) (a_rthread rid)
| neutral_points_to_1 : forall n a, cont_points_to n.(n_cont) a -> val_points_to (Neutral n) a
(* todo | neutral_points_to_2 : *)
| clos_points_to_1 : forall t e vn vp a, env_points_to e a -> val_points_to (Clos t e vn vp) a
| clos_points_to_2 : forall t e vn vp, val_points_to (Clos t e vn vp) (a_val vp)
| block_points_to : forall tag l a, env_points_to l a -> val_points_to (Block tag l) a.

Inductive code_points_to : code -> addr -> Prop :=
| term_points_to : forall t e a, env_points_to e a -> code_points_to (Term t e) a
| cval_points_to : forall vp, code_points_to (Val vp) (a_val vp).

Definition rthread_points_to rt a := code_points_to rt.(rt_code) a \/ cont_points_to rt.(rt_cont) a.

Definition points_to rthreads vals a1 a2 :=
  match a1 with
  | a_rthread rid =>
    match nth_error rthreads rid with
    | Some rt => rthread_points_to rt a2
    | None => False
    end
  | a_val vp =>
    match nth_error vals vp with
    | Some v => val_points_to v a2
    | None => False
    end
  end.

Definition valid (rthreads : list rthread) (vals : list value) a :=
  match a with
  | a_rthread rid => rid < length rthreads
  | a_val vp => vp < length vals
  end.

Definition valid_addrs rthreads vals :=
  forall a1 a2, points_to rthreads vals a1 a2 -> valid rthreads vals a2.

Definition state_ok rthreads vals := well_founded (flip (points_to rthreads vals)) /\ valid_addrs rthreads vals.

Record state := mkstate {
  st_rthreads : list rthread ;
  st_vals : list value ;
  st_freename : nat ;
(*  st_ok : state_ok st_rthreads st_vals ; *)
}.

Fixpoint update {A : Type} (l : list A) (k : nat) (x : A) : list A :=
  match l with
  | nil => nil
  | y :: l =>
    match k with
    | O => x :: l
    | S k => y :: update l k x
    end
  end.
Arguments update {A} _ _ _ : simpl nomatch.

Inductive plus {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| plus_1 : forall x y, R x y -> plus R x y
| plus_S : forall x y z, R x y -> plus R y z -> plus R x z.

Lemma nth_error_update :
  forall (A : Type) (l : list A) k x y, nth_error l k = Some x -> nth_error (update l k y) k = Some y.
Proof.
  induction l; intros [|k] x y; simpl in *; intros; try congruence.
  eapply IHl; eassumption.
Qed.

Lemma nth_error_update2 :
  forall (A : Type) (l : list A) k x, nth_error (update l k x) k = match nth_error l k with Some _ => Some x | None => None end.
Proof.
  induction l; intros [|k] x; simpl in *; intros; try congruence.
  apply IHl.
Qed.

Lemma nth_error_update3 :
  forall (A : Type) (l : list A) k1 k2 x, k1 <> k2 -> nth_error (update l k1 x) k2 = nth_error l k2.
Proof.
  induction l; intros [|k1] [|k2] x H; simpl in *; try congruence.
  apply IHl; congruence.
Qed.

Lemma plus_star :
  forall (A : Type) (R : A -> A -> Prop) x y, plus R x y -> star R x y.
Proof.
  intros A R x y H; induction H.
  - apply star_1. assumption.
  - econstructor; eassumption.
Qed.

Lemma plus_star_iff :
  forall (A : Type) (R : A -> A -> Prop) x y, plus R x y <-> compose R (star R) x y.
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

Lemma Acc_star_down :
  forall (A : Type) (R : A -> A -> Prop) x y, Acc R x -> star R y x -> Acc R y.
Proof.
  intros A R x y H1 H2. induction H2.
  - assumption.
  - apply IHstar in H1. inversion H1.
    apply H0. assumption.
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

Lemma plus_same_rel :
  forall (A : Type) (R1 R2 : A -> A -> Prop), same_rel R1 R2 -> same_rel (plus R1) (plus R2).
Proof.
  intros A R1 R2 H x y. split; intros Hplus; induction Hplus.
  - apply plus_1, H. assumption.
  - eapply plus_S; [|eassumption]. apply H. assumption.
  - apply plus_1, H. assumption.
  - eapply plus_S; [|eassumption]. apply H. assumption.
Qed.

Lemma flip_flip :
  forall (A : Type) (R : A -> A -> Prop), same_rel (flip (flip R)) R.
Proof.
  intros A R x y. reflexivity.
Qed.

Lemma flip_plus_iff :
  forall (A : Type) (R : A -> A -> Prop) x y, plus (flip R) x y <-> plus R y x.
Proof.
  intros A R x y; split; intros H.
  - apply flip_plus. assumption.
  - eapply flip_plus, plus_same_rel; [|eassumption].
    apply flip_flip.
Qed.

Lemma plus_compose_star_right :
  forall (A : Type) (R : A -> A -> Prop) x y z, plus R x y -> star R y z -> plus R x z.
Proof.
  intros A R x y z H1 H2.
  apply flip_plus_iff.
  eapply plus_compose_star_left; [|apply flip_plus_iff; eassumption].
  apply star_flip in H2. eassumption.
Qed.

Lemma Acc_plus :
  forall (A : Type) (R : A -> A -> Prop) x, Acc R x -> Acc (plus R) x.
Proof.
  intros A R x H. induction H.
  constructor. intros y Hy.
  apply flip_plus_iff in Hy.
  inversion Hy; subst.
  - apply H0. assumption.
  - eapply Acc_star_down; [eapply H0; eassumption|].
    apply star_1, flip_plus_iff; eassumption.
Qed.

Definition updatep {A B : Type} (f : A -> B -> Prop) (x : A) (P : B -> Prop) (u : A) (v : B) :=
  (u <> x /\ f u v) \/ (u = x /\ P v).

(*
Lemma updatep_wf :
  forall (A : Type) (R : A -> A -> Prop) u (P : A -> Prop),
    (forall v, P v -> plus R u v) -> well_founded R -> well_founded (updatep R u P).
Proof.
  intros A R u P H Hwf v.
  induction (Acc_plus _ _ _ (Hwf v)). constructor.
  intros v [[Huv HR] | [-> HP]].
  - apply H1, plus_1, HR.
  - apply H1, H, HP.
Qed.
*)

(*
Lemma updatep_wf :
  forall (A : Type) (R : A -> A -> Prop) u (P : A -> Prop),
    (forall v, P v -> plus R u v \/ Acc (flip (updatep R u P)) v) -> well_founded (flip R) -> well_founded (flip (updatep R u P)).
Proof.
  intros A R u P H Hwf v.
  induction (Acc_plus _ _ _ (Hwf v)). constructor.
  intros v [[Huv HR] | [-> HP]].
  - apply H1, plus_1, HR.
  - destruct (H _ HP) as [Hplus | Hacc]; [apply H1, flip_plus_iff, Hplus|apply Hacc].
Qed.
*)

Inductive AccI {A : Type} (B : A -> Prop) (R : A -> A -> Prop) : A -> Prop :=
| AccI_base : forall a, B a -> AccI B R a
| AccI_intro : forall a, (forall b, R b a -> AccI B R b) -> AccI B R a.

Lemma updatep_wf2 :
  forall (A : Type) (R : A -> A -> Prop) u (P : A -> Prop),
    (forall v, P v -> AccI (fun v => plus R u v) (flip (updatep R u P)) v) -> well_founded (flip R) -> well_founded (flip (updatep R u P)).
Proof.
  intros A R u P H Hwf v.
  induction (Acc_plus _ _ _ (Hwf v)). constructor.
  intros v [[Huv HR] | [-> HP]].
  - apply H1, plus_1, HR.
  - specialize (H _ HP). clear HP. induction H.
    + apply H1, flip_plus_iff, H.
    + constructor. apply H2.
Qed.

Lemma updatep_wf_none :
  forall (A : Type) (R : A -> A -> Prop) u (P : A -> Prop),
    ~ P u -> (forall v, ~ R v u) -> well_founded (flip R) -> well_founded (flip (updatep R u P)).
Proof.
  intros A R u P HP Hu Hwf.
  assert (Hwf1 : forall v, v <> u -> Acc (flip (updatep R u P)) v).
  - intros v Hv. induction (Hwf v). constructor.
    intros v [[Huv HR] | [-> HPv]].
    + apply H0; [assumption|]. intros ->; eapply Hu, HR.
    + tauto.
  - intros v. constructor; intros w [[Hvw HR2] | [-> HPw]].
    + apply Hwf1. intros ->; eapply Hu, HR2.
    + apply Hwf1. intros ->; apply HP, HPw.
Qed.

Lemma Acc_ext :
  forall (A : Type) (R1 R2 : A -> A -> Prop) x, (forall u v, R2 u v -> R1 u v) -> Acc R1 x -> Acc R2 x.
Proof.
  intros A R1 R2 x H Hwf; induction Hwf; constructor.
  intros y HR; apply H1, H, HR.
Qed.

Lemma AccI_ext :
  forall (A : Type) (B : A -> Prop) (R1 R2 : A -> A -> Prop) x, (forall u v, R2 u v -> R1 u v) -> AccI B R1 x -> AccI B R2 x.
Proof.
  intros A B R1 R2 x H Hwf; induction Hwf.
  - apply AccI_base; assumption.
  - apply AccI_intro; intros; apply H1, H, H2.
Qed.

Lemma well_founded_ext :
  forall (A : Type) (R1 R2 : A -> A -> Prop), (forall u v, R2 u v -> R1 u v) -> well_founded R1 -> well_founded R2.
Proof.
  intros A R1 R2 H Hwf x; eapply Acc_ext; [eassumption|apply Hwf].
Qed.



Lemma points_to_updatep_rthread :
  forall rthreads vals rid rt a1 a2,
    points_to (update rthreads rid rt) vals a1 a2 <->
    updatep (points_to rthreads vals) (a_rthread rid) (fun a => rid < length rthreads /\ rthread_points_to rt a) a1 a2.
Proof.
  intros rthreads vals rid rt [rid2|vp] a; unfold updatep; simpl; [|intuition congruence].
  destruct (Nat.eq_dec rid rid2); subst.
  - rewrite nth_error_update2.
    destruct nth_error eqn:Hnth; [apply nth_error_Some3 in Hnth|apply nth_error_None in Hnth]; intuition lia.
  - rewrite nth_error_update3; [|assumption].
    intuition congruence.
Qed.

Lemma points_to_updatep_vals :
  forall rthreads vals vp v a1 a2,
    points_to rthreads (update vals vp v) a1 a2 <->
    updatep (points_to rthreads vals) (a_val vp) (fun a => vp < length vals /\ val_points_to v a) a1 a2.
Proof.
  intros rthreads vals vp v [rid|vp2] a; unfold updatep; simpl; [intuition congruence|].
  destruct (Nat.eq_dec vp vp2); subst.
  - rewrite nth_error_update2.
    destruct nth_error eqn:Hnth; [apply nth_error_Some3 in Hnth|apply nth_error_None in Hnth]; intuition lia.
  - rewrite nth_error_update3; [|assumption].
    intuition congruence.
Qed.

Lemma points_to_updatep_rthread_extend :
  forall rthreads vals rt a1 a2,
    points_to (rthreads ++ rt :: nil) vals a1 a2 <->
    updatep (points_to rthreads vals) (a_rthread (length rthreads)) (rthread_points_to rt) a1 a2.
Proof.
  intros rthreads vals rt [rid|vp] a; unfold updatep; simpl; [|intuition congruence].
  destruct (le_lt_dec (length rthreads) rid).
  - rewrite nth_error_app2 by assumption.
    remember (rid - length rthreads) as n. destruct n as [|m] eqn:Hn.
    + simpl. assert (rid = length rthreads) by lia. intuition congruence.
    + simpl. do 2 (replace (nth_error _ _) with (@None rthread) by (symmetry; apply nth_error_None; simpl; lia)).
      assert (rid <> length rthreads) by lia. intuition congruence.
  - rewrite nth_error_app1 by assumption.
    assert (rid <> length rthreads) by lia.
    destruct nth_error; intuition congruence.
Qed.

Lemma points_to_updatep_val_extend :
  forall rthreads vals v a1 a2,
    points_to rthreads (vals ++ v :: nil) a1 a2 <->
    updatep (points_to rthreads vals) (a_val (length vals)) (val_points_to v) a1 a2.
Proof.
  intros rthreads vals v [rid|vp] a; unfold updatep; simpl; [intuition congruence|].
  destruct (le_lt_dec (length vals) vp).
  - rewrite nth_error_app2 by assumption.
    remember (vp - length vals) as n. destruct n as [|m] eqn:Hn.
    + simpl. assert (vp = length vals) by lia. intuition congruence.
    + simpl. do 2 (replace (nth_error _ _) with (@None value) by (symmetry; apply nth_error_None; simpl; lia)).
      assert (vp <> length vals) by lia. intuition congruence.
  - rewrite nth_error_app1 by assumption.
    assert (vp <> length vals) by lia.
    destruct nth_error; intuition congruence.
Qed.




Lemma update_length :
  forall {A : Type} (l : list A) k x, length (update l k x) = length l.
Proof.
  induction l; intros [|k] x; simpl in *; congruence.
Qed.

Definition update_rthread_hyp rthreads vals rid rt :=
  forall a, rthread_points_to rt a -> AccI (plus (points_to rthreads vals) (a_rthread rid)) (flip (points_to (update rthreads rid rt) vals)) a /\ valid rthreads vals a.

Lemma update_rthread_wf :
  forall rthreads vals rid rt,
    update_rthread_hyp rthreads vals rid rt ->
     well_founded (flip (points_to rthreads vals)) -> well_founded (flip (points_to (update rthreads rid rt) vals)).
Proof.
  intros rthreads vals rid rt H Hwf.
  eapply well_founded_ext; [|apply updatep_wf2; [|eassumption]].
  - intros. apply points_to_updatep_rthread; eassumption.
  - intros a [Hrid Ha].
    eapply AccI_ext; [|eapply H; eassumption].
    intros; apply points_to_updatep_rthread; eassumption.
Qed.

Lemma update_rthread_valid :
  forall rthreads vals rid rt,
    update_rthread_hyp rthreads vals rid rt ->
    valid_addrs rthreads vals -> valid_addrs (update rthreads rid rt) vals.
Proof.
  intros rthreads vals rid rt H Hvalid [rid2|vp] a2 Ha; simpl in *; unfold valid.
  - destruct (Nat.eq_dec rid rid2); subst.
    + rewrite nth_error_update2 in Ha.
      destruct nth_error eqn:Hrid2; [|tauto].
      rewrite update_length.
      apply H; assumption.
    + rewrite nth_error_update3 in Ha by assumption.
      rewrite update_length.
      apply Hvalid with (a1 := a_rthread rid2); assumption.
  - rewrite update_length.
    apply Hvalid with (a1 := a_val vp); assumption.
Qed.

Lemma update_rthread_ok :
  forall rthreads vals rid rt,
    update_rthread_hyp rthreads vals rid rt ->
    state_ok rthreads vals -> state_ok (update rthreads rid rt) vals.
Proof.
  intros rthreads vals rid rt H [Hwf Hvalid].
  split; [apply update_rthread_wf|apply update_rthread_valid]; assumption.
Qed.

Definition update_val_hyp rthreads vals vp v :=
  forall a, val_points_to v a -> AccI (plus (points_to rthreads vals) (a_val vp)) (flip (points_to rthreads (update vals vp v))) a /\ valid rthreads vals a.

Lemma update_val_wf :
  forall rthreads vals vp v,
    update_val_hyp rthreads vals vp v ->
     well_founded (flip (points_to rthreads vals)) -> well_founded (flip (points_to rthreads (update vals vp v))).
Proof.
  intros rthreads vals vp v H Hwf.
  eapply well_founded_ext; [|apply updatep_wf2; [|eassumption]].
  - intros. apply points_to_updatep_vals; eassumption.
  - intros a [Hrid Ha].
    eapply AccI_ext; [|eapply H; eassumption].
    intros; apply points_to_updatep_vals; eassumption.
Qed.

Lemma update_val_valid :
  forall rthreads vals vp v,
    update_val_hyp rthreads vals vp v ->
    valid_addrs rthreads vals -> valid_addrs rthreads (update vals vp v).
Proof.
  intros rthreads vals vp v H Hvalid [rid|vp2] a2 Ha; simpl in *; unfold valid.
  - rewrite update_length.
    apply Hvalid with (a1 := a_rthread rid); assumption.
  - destruct (Nat.eq_dec vp vp2); subst.
    + rewrite nth_error_update2 in Ha.
      destruct nth_error eqn:Hvp2; [|tauto].
      rewrite update_length.
      apply H; assumption.
    + rewrite nth_error_update3 in Ha by assumption.
      rewrite update_length.
      apply Hvalid with (a1 := a_val vp2); assumption.
Qed.

Lemma update_val_ok :
  forall rthreads vals vp v,
    update_val_hyp rthreads vals vp v ->
    state_ok rthreads vals -> state_ok rthreads (update vals vp v).
Proof.
  intros rthreads vals vp v H [Hwf Hvalid].
  split; [apply update_val_wf|apply update_val_valid]; assumption.
Qed.

Definition add_rthread_hyp rthreads vals rt :=
  forall a, rthread_points_to rt a -> valid rthreads vals a.

Lemma add_rthread_wf :
  forall rthreads vals rt,
    add_rthread_hyp rthreads vals rt ->
    well_founded (flip (points_to rthreads vals)) ->
    valid_addrs rthreads vals ->
    well_founded (flip (points_to (rthreads ++ rt :: nil) vals)).
Proof.
  intros rthreads vals rt H Hwf Hvalid.
  eapply well_founded_ext; [|apply updatep_wf_none; [| |eassumption]].
  - intros. apply points_to_updatep_rthread_extend; eassumption.
  - intros Hrt. apply H in Hrt; simpl in Hrt. lia.
  - intros a Ha. apply Hvalid in Ha. simpl in Ha. lia.
Qed.

Lemma add_rthread_valid :
  forall rthreads vals rt,
    add_rthread_hyp rthreads vals rt ->
    valid_addrs rthreads vals ->
    valid_addrs (rthreads ++ rt :: nil) vals.
Proof.
  intros rthreads vals rt H Hvalid [rid|vp] a2 Ha; simpl in *; unfold valid; rewrite app_length; simpl.
  - destruct (le_lt_dec (length rthreads) rid).
    + rewrite nth_error_app2 in Ha by assumption.
      destruct (rid - length rthreads) as [|n]; simpl in *; [|destruct n; simpl in *; tauto].
      apply H in Ha. destruct a2; simpl in *; lia.
    + rewrite nth_error_app1 in Ha by assumption.
      apply (Hvalid (a_rthread rid)) in Ha.
      destruct a2; simpl in *; lia.
  - apply (Hvalid (a_val vp)) in Ha.
    destruct a2; simpl in *; lia.
Qed.

Lemma add_rthread_ok :
  forall rthreads vals rt,
    add_rthread_hyp rthreads vals rt ->
    state_ok rthreads vals -> state_ok (rthreads ++ rt :: nil) vals.
Proof.
  intros rthreads vals rt H [Hwf Hvalid].
  split; [apply add_rthread_wf|apply add_rthread_valid]; assumption.
Qed.


Definition add_val_hyp rthreads vals v :=
  forall a, val_points_to v a -> valid rthreads vals a.

Lemma add_val_wf :
  forall rthreads vals v,
    add_val_hyp rthreads vals v ->
    well_founded (flip (points_to rthreads vals)) ->
    valid_addrs rthreads vals ->
    well_founded (flip (points_to rthreads (vals ++ v :: nil))).
Proof.
  intros rthreads vals v H Hwf Hvalid.
  eapply well_founded_ext; [|apply updatep_wf_none; [| |eassumption]].
  - intros. apply points_to_updatep_val_extend; eassumption.
  - intros Hv. apply H in Hv; simpl in Hv. lia.
  - intros a Ha. apply Hvalid in Ha. simpl in Ha. lia.
Qed.

Lemma add_val_valid :
  forall rthreads vals v,
    add_val_hyp rthreads vals v ->
    valid_addrs rthreads vals ->
    valid_addrs rthreads (vals ++ v :: nil).
Proof.
  intros rthreads vals v H Hvalid [rid|vp] a2 Ha; simpl in *; unfold valid; rewrite app_length; simpl.
  - apply (Hvalid (a_rthread rid)) in Ha.
    destruct a2; simpl in *; lia.
  - destruct (le_lt_dec (length vals) vp).
    + rewrite nth_error_app2 in Ha by assumption.
      destruct (vp - length vals) as [|n]; simpl in *; [|destruct n; simpl in *; tauto].
      apply H in Ha. destruct a2; simpl in *; lia.
    + rewrite nth_error_app1 in Ha by assumption.
      apply (Hvalid (a_val vp)) in Ha.
      destruct a2; simpl in *; lia.
Qed.

Lemma add_val_ok :
  forall rthreads vals v,
    add_val_hyp rthreads vals v ->
    state_ok rthreads vals -> state_ok rthreads (vals ++ v :: nil).
Proof.
  intros rthreads vals v H [Hwf Hvalid].
  split; [apply add_val_wf|apply add_val_valid]; assumption.
Qed.


Definition update_addr st a (v : match a return Type with a_rthread _ => rthread | a_val _ => value end) :=
  match a, v with
  | a_rthread rid, rt =>
    {|
      st_rthreads := update st.(st_rthreads) rid rt ;
      st_vals := st.(st_vals) ;
      st_freename := st.(st_freename) ;
    |}
  | a_val vp, v =>
    {|
      st_rthreads := st.(st_rthreads);
      st_vals := update st.(st_vals) vp v ;
      st_freename := st.(st_freename) ;
    |}
  end.

Definition get_addr st a : option (match a return Type with a_rthread _ => rthread | a_val _ => value end) :=
  match a with
  | a_rthread rid => nth_error st.(st_rthreads) rid
  | a_val vp => nth_error st.(st_vals) vp
  end.

Definition update_rthread st rid rt (* H *) :=
(*  {|
    st_rthreads := update st.(st_rthreads) rid rt ;
    st_vals := st.(st_vals) ;
    st_freename := st.(st_freename) ;
(*    st_ok := update_rthread_ok _ _ _ _ H st.(st_ok) ; *)
  |}. *)
  update_addr st (a_rthread rid) rt.

Lemma freevar_ok :
  forall name rthreads vals,
    state_ok rthreads vals -> state_ok rthreads (vals ++ Neutral {| n_id := name ; n_cont := Kid ; n_unfold := None |} :: nil).
Proof.
  intros name rthreads vals Hok.
  apply add_val_ok; [|assumption].
  intros a Ha; inversion Ha; subst.
  inversion H0.
Qed.

Definition freevar (st : state) :=
  ({|
      st_rthreads := st.(st_rthreads) ;
      st_vals := st.(st_vals) ++ Neutral {| n_id := st.(st_freename) ; n_cont := Kid ; n_unfold := None |} :: nil ;
      st_freename := S st.(st_freename) ;
      (* st_ok := freevar_ok _ _ _ st.(st_ok) ; *)
    |}, st.(st_freename), length st.(st_vals)).

Definition makelazy_hyp rthreads vals e :=
  forall a, env_points_to e a -> valid rthreads vals a.

Lemma makelazy_ok :
  forall rthreads vals t e,
    makelazy_hyp rthreads vals e ->
    state_ok rthreads vals ->
    state_ok (rthreads ++ {| rt_code := Term t e; rt_cont := Kid |} :: nil) (vals ++ Thread (length rthreads) :: nil).
Proof.
  intros rthreads vals t e Hmakelazy Hok.
  eapply add_rthread_ok in Hok; [eapply add_val_ok; [|eassumption]|].
  - intros a Ha. inversion Ha; subst. simpl.
    rewrite app_length; simpl. lia.
  - intros a Ha. inversion Ha; subst; inversion H; subst.
    eapply Hmakelazy; eassumption.
Qed.

Definition makelazy (st : state) (t : term) (e : env) (* H *) :=
  (* For now, ignore variable optimization *)
  ({|
    st_rthreads := st.(st_rthreads) ++ {| rt_code := Term t e ; rt_cont := Kid |} :: nil ;
    st_vals := st.(st_vals) ++ Thread (length st.(st_rthreads)) :: nil ;
    st_freename := st.(st_freename) ;
    (* st_ok := makelazy_ok st.(st_rthreads) st.(st_vals) t e H st.(st_ok) ; *)
    |}, length st.(st_vals)).


(*
Definition dummy_term := abs (var 0).

Program Fixpoint read_thread st rid (acc : Acc (flip (points_to st.(st_rthreads) st.(st_vals))) (a_rthread rid)) {struct acc} :=
  match acc with
  | Acc_intro _ Hrec =>
    match nth_error st.(st_rthreads) rid with
    | None => dummy_term
    | Some rt =>
      let h := read_cont st rt.(rt_cont) _ in
      match rt.(rt_code) with
      | Val vp => read_val st vp (Hrec (a_val vp) _)
      | Term t e => dummy_term (* todo *)
      end
    end
  end

with read_val st vp (acc : Acc (flip (points_to st.(st_rthreads) st.(st_vals))) (a_val vp)) {struct acc} :=
  match acc with
  | Acc_intro _ Hrec =>
    match nth_error st.(st_vals) vp with
    | None => dummy_term
    | Some (Thread rid) => read_thread st rid (Hrec (a_rthread rid) _)
    | Some (Clos t e x vp2) =>
      dummy_term
    | Some _ => dummy_term
    end
  end

with read_cont st c (acc : forall a, cont_points_to c a -> Acc (flip (points_to st.(st_rthreads) st.(st_vals))) a) {struct c} :=
  match c with
  | Kid => h_hole
  | Kapp vp c => h_app (read_cont st c _) (read_val st vp  _)
  | Kswitch _ _ _ _ => h_hole
  end.
Next Obligation.
  apply acc. apply kapp_points_to_2. assumption.
Defined.
Next Obligation.
  apply acc. apply kapp_points_to_1.
Defined.
Next Obligation.
  apply Hrec. unfold flip, points_to; simpl.
  rewrite <- Heq_anonymous. right. assumption.
Defined.
Next Obligation.
  unfold flip, points_to. rewrite <- Heq_anonymous0.
  left. rewrite <- Heq_anonymous. constructor.
Defined.
Next Obligation.
  unfold flip, points_to. rewrite <- Heq_anonymous.
  constructor.
Defined.
Next Obligation.
  split; intros; discriminate.
Defined.
Next Obligation.
  split; intros; discriminate.
Defined.

Print read_thread.

| read_thread_val : forall rid vp c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Val vp ; rt_cont := c |} ->
    read_val st vp t ->
    read_cont st c h ->
    read_thread st rid (fill_hctx h t)
| read_thread_term : forall rid e el c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Term t e ; rt_cont := c |} ->
    Forall2 (read_val st) e el ->
    read_cont st c h ->
    read_thread st rid (fill_hctx h (subst (read_env el) t))

with read_val st : valptr -> term -> Prop :=
| read_val_thread :
    forall vp rid t,
      nth_error st.(st_vals) vp = Some (Thread rid) ->
      read_thread st rid t ->
      read_val st vp t
| read_val_clos :
    forall vp t e el x vp2,
      nth_error st.(st_vals) vp = Some (Clos t e x vp2) ->
      Forall2 (read_val st) e el ->
      read_val st vp (subst (read_env el) (abs t))

with read_cont st : cont -> hctx -> Prop :=
| read_cont_kid : read_cont st Kid h_hole
| read_cont_kapp :
    forall vp c t h,
      read_val st vp t ->
      read_cont st c h ->
      read_cont st (Kapp vp c) (h_app h t)
| read_cont_kswitch :
    forall bs e bds c el h,
      Forall2 (read_val st) e el ->
      read_cont st c h ->
      read_cont st (Kswitch bs e bds c) (h_switch h (map (fun '(p, t) => (p, subst (read_env el) t)) bs)).

*)






Definition exit_rthread (st : state) (rid : rthreadptr) (vp : valptr) :=
  update_rthread st rid {| rt_code := Val vp ; rt_cont := Kid |}.

Definition addval (st : state) (v : value) :=
  ({|
      st_rthreads := st.(st_rthreads) ;
      st_vals := st.(st_vals) ++ v :: nil ;
      st_freename := st.(st_freename) ;
    |}, length st.(st_vals)).

Definition is_finished (st : state) (rid : rthreadptr) :=
  match nth_error st.(st_rthreads) rid with
  | None => None
  | Some rthread =>
    match rthread.(rt_code), rthread.(rt_cont) with
    | Val vp, Kid => Some vp
    | _, _ => None
    end
  end.

Definition fst3 {A B C : Type} (x : A * B * C) := fst (fst x).
Definition snd3 {A B C : Type} (x : A * B * C) := snd (fst x).
Definition thd3 {A B C : Type} (x : A * B * C) := snd x.

Definition step_r (st : state) (rid : rthreadptr) : state :=
  match nth_error st.(st_rthreads) rid with
  | None => st
  | Some rthread =>
    match rthread.(rt_code) with
    | Term (app u v) e =>
      let st2vp := makelazy st v e in
      update_rthread (fst st2vp) rid {| rt_code := Term u e ; rt_cont := Kapp (snd st2vp) rthread.(rt_cont) |}
    | Term (abs u) e =>
      match rthread.(rt_cont) with
      | Kswitch _ _ _ _ => st (* type error *)
      | Kid =>
        let st2yfv := freevar st in
        let st3vp := makelazy (fst3 st2yfv) u ((thd3 st2yfv) :: e) in
        let st4vp2 := addval (fst st3vp) (Clos u e (snd3 st2yfv) (snd st3vp)) in
        exit_rthread (fst st4vp2) rid (snd st4vp2)
      | Kapp v c =>
        update_rthread st rid {| rt_code := Term u (v :: e) ; rt_cont := c |}
      end
    | Term (var n) e =>
      match nth_error e n with
      | None => st (* variable not found *)
      | Some vp =>
        update_rthread st rid {| rt_code := Val vp ; rt_cont := rthread.(rt_cont) |}
      end
    | Term (dvar n) e =>
      st (* todo use defs *)
    | Term _ e => st (* todo *)
    | Val vp =>
      match nth_error st.(st_vals) vp with
      | None => st (* value not found *)
      | Some (Thread rid2) =>
        match is_finished st rid2 with
        | None => st (* Thread is not finished yet, wait *)
        | Some vp2 =>
          update_rthread st rid {| rt_code := Val vp2 ; rt_cont := rthread.(rt_cont) |}
        end
      | Some (Clos u e y vp) =>
        match rthread.(rt_cont) with
        | Kid => st (* should be impossible? TODO *)
        | Kswitch _ _ _ _  => st (* type error *)
        | Kapp v c =>
          update_rthread st rid {| rt_code := Term u (v :: e) ; rt_cont := c |}
        end
      | Some _ => st (* todo *)
      end
    end
  end.

Inductive step : state -> state -> Prop :=
| step_rthread :
    forall st rid, rid < length st.(st_rthreads) -> step st (step_r st rid).




Inductive read_addr st : addr -> term -> Prop :=
| read_thread_val : forall rid vp c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Val vp ; rt_cont := c |} ->
    read_addr st (a_val vp) t ->
    read_cont st c h ->
    read_addr st (a_rthread rid) (fill_hctx h t)
| read_thread_term : forall rid e el c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Term t e ; rt_cont := c |} ->
    Forall2 (fun vp v => read_addr st (a_val vp) v) e el ->
    read_cont st c h ->
    read_addr st (a_rthread rid) (fill_hctx h (subst (read_env el) t))
| read_val_thread :
    forall vp rid t,
      nth_error st.(st_vals) vp = Some (Thread rid) ->
      read_addr st (a_rthread rid) t ->
      read_addr st (a_val vp) t
| read_val_clos :
    forall vp t e el x vp2 t2,
      nth_error st.(st_vals) vp = Some (Clos t e x vp2) ->
      Forall2 (fun vp v => read_addr st (a_val vp) v) e el ->
      read_addr st (a_val vp2) t2 ->
      convertible beta (subst (read_env (dvar x :: el)) t) t2 ->
      read_addr st (a_val vp) (subst (read_env el) (abs t))
| read_val_neutral :
    forall vp x c h uf,
      nth_error st.(st_vals) vp = Some (Neutral {| n_id := x ; n_cont := c ; n_unfold := uf |}) ->
      read_cont st c h ->
      read_addr st (a_val vp) (fill_hctx h (dvar x))

with read_cont st : cont -> hctx -> Prop :=
| read_cont_kid : read_cont st Kid h_hole
| read_cont_kapp :
    forall vp c t h,
      read_addr st (a_val vp) t ->
      read_cont st c h ->
      read_cont st (Kapp vp c) (compose_hctx h (h_app h_hole t))
| read_cont_kswitch :
    forall bs e bds c el h,
      Forall2 (fun vp v => read_addr st (a_val vp) v) e el ->
      read_cont st c h ->
      read_cont st (Kswitch bs e bds c) (compose_hctx h (h_switch h_hole (map (fun '(p, t) => (p, subst (read_env el) t)) bs))).

Lemma read_env_0 :
  forall t e, read_env (t :: e) 0 = t.
Proof.
  intros; reflexivity.
Qed.

Lemma read_env_S :
  forall t e n, read_env (t :: e) (S n) = read_env e n.
Proof.
  intros; reflexivity.
Qed.

Definition points st := points_to st.(st_rthreads) st.(st_vals).

Definition no_delete st1 st2 :=
  forall a, get_addr st2 a = None -> get_addr st1 a = None.

Lemma no_delete_refl :
  forall st, no_delete st st.
Proof.
  intros st a H; assumption.
Qed.

Lemma no_delete_iff :
  forall st1 st2, no_delete st1 st2 <->
             length st1.(st_rthreads) <= length st2.(st_rthreads) /\ length st1.(st_vals) <= length st2.(st_vals).
Proof.
  intros st1 st2. split.
  - intros H. split.
    + specialize (H (a_rthread (length (st_rthreads st2)))). simpl in H.
      rewrite !nth_error_None in H. lia.
    + specialize (H (a_val (length (st_vals st2)))). simpl in H.
      rewrite !nth_error_None in H. lia.
  - intros [H1 H2] [rid|vp] H; simpl in *; rewrite nth_error_None in *; lia.
Qed.

Lemma nth_error_app_Some :
  forall (A : Type) (l1 l2 : list A) k x, nth_error l1 k = Some x -> nth_error (l1 ++ l2) k = Some x.
Proof.
  induction l1; intros l2 [|k] x; simpl in *; intros; try congruence.
  apply IHl1; assumption.
Qed.

Lemma Forall2_impl_In_left_transparent :
  forall (A B : Type) (P Q : A -> B -> Prop) L1 L2,
    (forall x y, In x L1 -> P x y -> Q x y) -> Forall2 P L1 L2 -> Forall2 Q L1 L2.
Proof.
  intros A B P Q L1 L2 H Hforall. induction Hforall.
  - constructor.
  - econstructor.
    + apply H; [left; reflexivity|assumption].
    + apply IHHforall.
      intros; eapply H; [right|]; eassumption.
Defined.

Lemma Forall2_In_left_transparent :
  forall (A B : Type) (P : A -> B -> Prop) (Q : Prop) (L1 : list A) (L2 : list B) (x : A) (H : forall y, P x y -> Q), Forall2 P L1 L2 -> x ∈ L1 -> Q.
Proof.
  intros A B P Q L1 L2 x HQ H Hx; induction H.
  - simpl in Hx; tauto.
  - destruct Hx as [-> | Hx]; [eapply HQ; eassumption|apply (IHForall2 Hx)].
Defined.

Lemma read_cont_Acc :
  forall st a c h, read_cont st c h -> cont_points_to c a -> (forall a t, read_addr st a t -> Acc (flip (points st)) a) -> Acc (flip (points st)) a.
Proof.
  intros st a c h Hread Hpoint Hrec. induction Hread; inversion Hpoint; subst.
  - eapply Hrec; eassumption.
  - apply IHHread. assumption.
  - destruct a; simpl in *; [tauto|].
    eapply Forall2_In_left_transparent; [|eassumption|eassumption].
    intros; eapply Hrec, H0.
  - tauto.
Defined.

Lemma read_addr_Acc :
  forall st a t, read_addr st a t -> Acc (flip (points st)) a.
Proof.
  intros st. fix Hrec 3.
  intros a t H; inversion H; subst; simpl; constructor; intros a2 Ha2; unfold flip in Ha2; simpl in Ha2; rewrite H0 in Ha2; inversion Ha2; subst; simpl in *.
  - inversion H3; subst. eapply Hrec; eassumption.
  - eapply read_cont_Acc; eassumption.
  - inversion H3; subst.
    destruct a2; simpl in *; [tauto|].
    eapply Forall2_In_left_transparent; [|eassumption|eassumption].
    intros; eapply Hrec, H4.
  - eapply read_cont_Acc; eassumption.
  - eapply Hrec; eassumption.
  - destruct a2; simpl in *; [tauto|].
    eapply Forall2_In_left_transparent; [|eassumption|eassumption].
    intros; eapply Hrec, H4.
  - eapply Hrec; eassumption.
  - eapply read_cont_Acc; eassumption.
Qed.

Lemma read_cont_points_to :
  forall st c h a, read_cont st c h -> cont_points_to c a -> exists t, read_addr st a t.
Proof.
  intros st c h a Hread Hpoint; induction Hread; simpl in *; inversion Hpoint; subst.
  - eexists; eassumption.
  - apply IHHread; assumption.
  - destruct a; simpl in *; [tauto|].
    eapply Forall2_In_left in H; [|eassumption].
    destruct H; eexists; apply H.
  - apply IHHread; assumption.
Qed.

Lemma read_addr_points_to :
  forall st a1 t a2, read_addr st a1 t -> points st a1 a2 -> exists t2, read_addr st a2 t2.
Proof.
  intros st a1 t a2 Hread Hpoint; inversion Hread; subst; simpl in *; rewrite H in Hpoint.
  - destruct Hpoint; simpl in *.
    + inversion H2; subst. eexists; eassumption.
    + eapply read_cont_points_to; eassumption.
  - destruct Hpoint; simpl in *.
    + inversion H2; subst.
      destruct a2; simpl in *; [tauto|].
      eapply Forall2_In_left in H0; [|eassumption].
      destruct H0; eexists; apply H0.
    + eapply read_cont_points_to; eassumption.
  - inversion Hpoint; subst.
    eexists; eassumption.
  - inversion Hpoint; subst.
    + destruct a2; simpl in *; [tauto|].
      eapply Forall2_In_left in H0; [|eassumption].
      destruct H0; eexists; apply H0.
    + eexists; eassumption.
  - inversion Hpoint; subst.
    eapply read_cont_points_to; eassumption.
Qed.

Lemma read_addr_points_to_star :
  forall st a1 t a2, read_addr st a1 t -> star (points st) a1 a2 -> exists t2, read_addr st a2 t2.
Proof.
  intros st a1 t a2 Hread H. revert t Hread; induction H; intros t Hread.
  - eexists; eassumption.
  - eapply read_addr_points_to in Hread; [|eassumption].
    destruct Hread.
    eapply IHstar; eassumption.
Qed.

Lemma Acc_cycle :
  forall (A : Type) (R : A -> A -> Prop) x, plus R x x -> Acc (flip R) x -> False.
Proof.
  intros A R x Hplus Hacc. induction Hacc.
  inversion Hplus; subst.
  - eapply H0; eassumption.
  - eapply H0; [eassumption|].
    eapply plus_compose_star_right; [eassumption|].
    apply star_1; assumption.
Qed.

Lemma update_case :
  forall {A : Type} (l : list A) k1 k2 x, (k1 = k2 /\ nth_error (update l k1 x) k2 = Some x) \/ (nth_error (update l k1 x) k2 = nth_error l k2).
Proof.
  intros A l k1 k2 x.
  destruct (Nat.eq_dec k1 k2).
  + subst. rewrite nth_error_update2.
    destruct nth_error; tauto.
  + rewrite nth_error_update3 by assumption. tauto.
Qed.



Definition every_reachable st a (P : addr -> Prop) :=
  forall a2, star (points st) a a2 -> P a2.
Definition every_reachable_plus st a (P : addr -> Prop) :=
  forall a2, plus (points st) a a2 -> P a2.

Lemma every_reachable_impl :
  forall st a (P Q : addr -> Prop),
    (forall a2, star (points st) a a2 -> P a2 -> Q a2) -> every_reachable st a P -> every_reachable st a Q.
Proof.
  intros st a P Q H1 H2 a2 Hstar; apply H1; [assumption|]; apply H2; assumption.
Qed.

Lemma every_reachable_plus_impl :
  forall st a (P Q : addr -> Prop),
    (forall a2, plus (points st) a a2 -> P a2 -> Q a2) -> every_reachable_plus st a P -> every_reachable_plus st a Q.
Proof.
  intros st a P Q H1 H2 a2 Hplus; apply H1; [assumption|]; apply H2; assumption.
Qed.

Lemma every_reachable_star :
  forall st a a2 P, star (points st) a a2 -> every_reachable st a P -> every_reachable st a2 P.
Proof.
  intros st a a2 P Hstar H a3 Hstar2. apply H. eapply star_compose; eassumption.
Qed.

Lemma every_reachable_plus_star :
  forall st a a2 P, star (points st) a a2 -> every_reachable_plus st a P -> every_reachable_plus st a2 P.
Proof.
  intros st a a2 P Hstar H a3 Hplus. apply H. eapply plus_compose_star_left; eassumption.
Qed.

Lemma every_reachable_star_plus :
  forall st a a2 P, plus (points st) a a2 -> every_reachable_plus st a P -> every_reachable st a2 P.
Proof.
  intros st a a2 P Hplus H a3 Hstar. apply H. eapply plus_compose_star_right; eassumption.
Qed.

Lemma every_reachable_plus_iff :
  forall st a P, every_reachable_plus st a P <-> (forall a2, points st a a2 -> every_reachable st a2 P).
Proof.
  intros st a P. split; intros H.
  - intros a2 Ha2 a3 Ha3. apply H. rewrite plus_star_iff. exists a2. split; assumption.
  - intros a3 Ha3. rewrite plus_star_iff in Ha3; destruct Ha3 as (a2 & Ha2 & Ha3).
    apply (H a2 Ha2 a3 Ha3).
Qed.

Lemma every_reachable_same :
  forall st a P, every_reachable st a P -> P a.
Proof.
  intros st a P H; apply H, star_refl.
Qed.

Lemma every_reachable_is_plus :
  forall st a P, every_reachable st a P -> every_reachable_plus st a P.
Proof.
  intros st a P H a2 Ha2. apply H, plus_star, Ha2.
Qed.

Lemma every_reachable_iff :
  forall st a1 P, every_reachable st a1 P <-> P a1 /\ every_reachable_plus st a1 P.
Proof.
  intros st a1 P. split; intros H.
  - split; [eapply every_reachable_same|eapply every_reachable_is_plus]; eassumption.
  - intros a2 Ha2. inversion Ha2; subst; [tauto|].
    apply H. rewrite plus_star_iff; eexists; split; eassumption.
Qed.


Definition unchanged_from st1 st2 a := every_reachable st1 a (fun a2 => get_addr st1 a2 = get_addr st2 a2).
Definition unchanged_from_plus st1 st2 a := every_reachable_plus st1 a (fun a2 => get_addr st1 a2 = get_addr st2 a2).

Lemma unchanged_from_same :
  forall st1 st2 a, unchanged_from st1 st2 a -> get_addr st1 a = get_addr st2 a.
Proof.
  intros st1 st2 a. apply every_reachable_same.
Qed.

Lemma unchanged_from_points :
  forall st1 st2 a1 a2, unchanged_from st1 st2 a1 -> points st1 a1 a2 -> unchanged_from st1 st2 a2.
Proof.
  intros st1 st2 a1 a2 Hchanged Hpoint.
  apply every_reachable_is_plus in Hchanged.
  eapply every_reachable_plus_iff in Hchanged; eassumption.
Qed.

Definition unchanged_read st1 st2 a := every_reachable st1 a (fun a2 => forall t, read_addr st1 a t -> read_addr st2 a t).
Definition unchanged_read_plus st1 st2 a := every_reachable_plus st1 a (fun a2 => forall t, read_addr st1 a t -> read_addr st2 a t).

Lemma read_cont_same :
  forall st1 st2 c h,
    read_cont st1 c h ->
    (forall a t, read_addr st1 a t -> cont_points_to c a -> read_addr st2 a t) ->
    read_cont st2 c h.
Proof.
  intros st1 st2 c h Hread H; induction Hread.
  - constructor.
  - econstructor.
    + apply H; [assumption|]. apply kapp_points_to_1.
    + apply IHHread. intros; apply H, kapp_points_to_2; assumption.
  - econstructor.
    + eapply Forall2_impl_In_left_transparent; [|eassumption].
      intros; apply H; [assumption|]. apply kswitch_points_to_1. assumption.
    + apply IHHread. intros; apply H, kswitch_points_to_2; assumption.
Defined.

Lemma read_addr_same :
  forall st1 st2 a t, read_addr st1 a t -> unchanged_from st1 st2 a -> read_addr st2 a t.
Proof.
  intros st1 st2 a t H Hchanged.
  assert (Hacc := read_addr_Acc _ _ _ H).
  revert t H. induction Hacc; intros t Hread.
  assert (Hrec : forall y, points st1 x y -> forall t, read_addr st1 y t -> read_addr st2 y t).
  { intros; apply H0; [|eapply unchanged_from_points|]; eassumption. }
  inversion Hread; subst.
  - eapply read_thread_val.
    + rewrite (unchanged_from_same _ _ _ Hchanged) in H1. eassumption.
    + apply Hrec; [|assumption].
      simpl; rewrite H1. left; constructor.
    + eapply read_cont_same; [eassumption|].
      intros; apply Hrec; [|assumption].
      simpl; rewrite H1. right; assumption.
  - eapply read_thread_term.
    + rewrite (unchanged_from_same _ _ _ Hchanged) in H1. eassumption.
    + eapply Forall2_impl_In_left_transparent; [|eassumption].
      intros vp t Hvp; apply Hrec.
      simpl; rewrite H1. left; constructor; assumption.
    + eapply read_cont_same; [eassumption|].
      intros; apply Hrec; [|assumption].
      simpl; rewrite H1. right; assumption.
  - eapply read_val_thread.
    + rewrite (unchanged_from_same _ _ _ Hchanged) in H1. eassumption.
    + apply Hrec; [|assumption].
      simpl; rewrite H1. constructor.
  - eapply read_val_clos.
    + rewrite (unchanged_from_same _ _ _ Hchanged) in H1. eassumption.
    + eapply Forall2_impl_In_left_transparent; [|eassumption].
      intros; apply Hrec; [|assumption].
      simpl; rewrite H1. constructor; assumption.
    + eapply Hrec; [|eassumption].
      simpl; rewrite H1. apply clos_points_to_2.
    + assumption.
  - eapply read_val_neutral.
    + rewrite (unchanged_from_same _ _ _ Hchanged) in H1. eassumption.
    + eapply read_cont_same; [eassumption|].
      intros; apply Hrec; [|assumption].
      simpl; rewrite H1. constructor; assumption.
Qed.

Definition unchanged_from_plus st1 st2 a :=
  forall a2, points_to st1.(st_rthreads) st1.(st_vals) a a2 -> unchanged_from st1 st2 a2.

Lemma read_addr_same_Forall2 :
  forall st1 st2 e el,
    Forall2 (fun vp t => read_addr st1 (a_val vp) t) e el ->
    (forall vp, In vp e -> unchanged_from st1 st2 (a_val vp)) ->
    Forall2 (fun vp t => read_addr st2 (a_val vp) t) e el.
Proof.
  intros st1 st2 e el Hall Hchange.
  eapply Forall2_impl_In_left_transparent; [|eassumption].
  intros; eapply read_addr_same; [apply H0|apply Hchange; assumption].
Qed.

Lemma unchanged_from_trans :
  forall st1 st2 st3 a, unchanged_from st1 st2 a -> unchanged_from st2 st3 a -> unchanged_from st1 st3 a.
Proof.
  intros st1 st2 st3 a H1 H2 [rid|vp] Ha2; simpl.
  - etransitivity; [eapply (H1 (a_rthread _)); eassumption|eapply (H2 (a_rthread _))].
    clear H2.
    induction Ha2.
    + apply star_refl.
    + econstructor; [|eapply IHHa2; eapply unchanged_from_points_to; eassumption].
      destruct x; simpl in *; rewrite (unchanged_from_same _ _ _ H1) in H; assumption.
  - etransitivity; [eapply (H1 (a_val _)); eassumption|eapply (H2 (a_val _))].
    clear H2.
    induction Ha2.
    + apply star_refl.
    + econstructor; [|eapply IHHa2; eapply unchanged_from_points_to; eassumption].
      destruct x; simpl in *; rewrite (unchanged_from_same _ _ _ H1) in H; assumption.
Qed.

Lemma unchanged_from_cycle :
  forall st a1 v a2 t, plus (points_to st.(st_rthreads) st.(st_vals)) a1 a2 -> read_addr st a1 t -> unchanged_from st (update_addr st a1 v) a2.
Proof.
  intros st a1 v a2 t Hplus Hread a3 Ha3.
  destruct a1 as [rid|vp]; destruct a3 as [rid2|vp2]; simpl in *; try reflexivity.
  - destruct (update_case st.(st_rthreads) rid rid2 v).
    + destruct H; subst. exfalso.
      eapply Acc_cycle; [eapply plus_compose_star_right; eassumption|].
      eapply read_addr_Acc; eassumption.
    + congruence.
  - destruct (update_case st.(st_vals) vp vp2 v).
    + destruct H; subst. exfalso.
      eapply Acc_cycle; [eapply plus_compose_star_right; eassumption|].
      eapply read_addr_Acc; eassumption.
    + congruence.
Qed.

Lemma unchanged_from_plus_cycle :
  forall st a1 v a2 t, star (points_to st.(st_rthreads) st.(st_vals)) a1 a2 -> read_addr st a1 t -> unchanged_from_plus st (update_addr st a1 v) a2.
Proof.
  intros st a1 v a2 t Hstar Hread a3 Hpoint.
  eapply unchanged_from_cycle; [|eassumption].
  eapply plus_compose_star_left; [eassumption|].
  apply plus_1; assumption.
Qed.

Lemma unchanged_from_plus_update :
  forall st a v t, read_addr st a t -> unchanged_from_plus st (update_addr st a v) a.
Proof.
  intros; eapply unchanged_from_plus_cycle; [|eassumption].
  apply star_refl.
Qed.

Lemma unchanged_from_plus_trans :
  forall st1 st2 st3 a, unchanged_from st1 st2 a -> unchanged_from_plus st2 st3 a -> unchanged_from_plus st1 st3 a.
Proof.
  intros st1 st2 st3 a H12 H23 a2 Ha2.
  eapply unchanged_from_trans; [eapply unchanged_from_points_to; eassumption|apply H23].
  destruct a; simpl in *; rewrite (unchanged_from_same _ _ _ H12) in Ha2; assumption.
Qed.

Lemma nth_error_extend :
  forall {A : Type} (l : list A) x, nth_error (l ++ x :: nil) (length l) = Some x.
Proof.
  intros A l x. rewrite nth_error_app2 by lia.
  destruct (length l - length l) eqn:Hll; [reflexivity|lia].
Qed.

Lemma unchanged_from_addval :
  forall st v a t, read_addr st a t -> unchanged_from st (fst (addval st v)) a.
Proof.
  intros st v a t Hread a2 Ha2.
  eapply read_addr_points_to_star in Ha2; [|eassumption].
  destruct Ha2 as (t2 & Ha2).
  destruct a2 as [rid|vp]; [reflexivity|].
  simpl.
  inversion Ha2; subst; erewrite nth_error_app_Some; eassumption.
Qed.

Lemma unchanged_from_makelazy :
  forall st t e a t2,
    read_addr st a t2 ->
    unchanged_from st (fst (makelazy st t e)) a.
Proof.
  intros st t e a t2 Hread a2 Ha2.
  eapply read_addr_points_to_star in Ha2; [|eassumption].
  destruct Ha2 as (t3 & Ha2).
  inversion Ha2; simpl; subst; erewrite nth_error_app_Some; eassumption.
Qed.

Definition stable_partial st1 st2 st3 a :=
  no_delete st1 st2 /\ no_delete st2 st3 /\
  forall a2,
    (get_addr st2 a2 = get_addr st1 a2 \/
     ((get_addr st1 a2 = None \/ star (points st1) a a2) /\
      forall a3, points st2 a2 a3 -> star (points st1) a a3 \/ get_addr st1 a3 = None)) /\
    (get_addr st3 a2 = get_addr st2 a2 \/
     ((get_addr st1 a2 = None \/ star (points st1) a a2) /\
      forall a3, points st3 a2 a3 -> star (points st1) a a3 \/ get_addr st1 a3 = None)).

Definition stable st1 st2 a := stable_partial st1 st1 st2 a.

(*
Definition stable st1 st2 a :=
  no_delete st1 st2 /\
  forall a2,
    (get_addr st2 a2 = get_addr st1 a2 \/
     ((get_addr st1 a2 = None \/ star (points_to st1.(st_rthreads) st1.(st_vals)) a a2) /\
      forall a3, points st2 a2 a3 ->
            get_addr st1 a3 = None \/ star (points_to st1.(st_rthreads) st1.(st_vals)) a a3)).
 *)

(*
Lemma stable_partial_refl :
  forall st1 st2 a, no_delete st1 st2 -> stable_partial st1 st2 st2 a.
Proof.
  intros st1 st2 a Hdel.
  split; [apply Hdel|].
  split; [apply no_delete_refl|].
  intros a2. split; [|left; reflexivity].
  left; reflexivity.
Qed.
 *)

Lemma stable_refl :
  forall st a, stable st st a.
Proof.
  intros.
  split; [apply no_delete_refl|].
  split; [apply no_delete_refl|].
  intros a2. split; left; reflexivity.
Qed.


Definition a_points_to (a : addr) (v : match a return Type with a_rthread _ => rthread | a_val _ => value end) :=
  match a, v with a_rthread _, v => rthread_points_to v | a_val _, v => val_points_to v end.

Lemma get_addr_points :
  forall st1 st2 a1 a2, get_addr st1 a1 = get_addr st2 a1 -> points st1 a1 a2 <-> points st2 a1 a2.
Proof.
  intros st1 st2 [rid|vp] a2 H; simpl in *; rewrite H; reflexivity.
Qed.

Lemma get_addr_points2 :
  forall st a1 a2, points st a1 a2 <-> match get_addr st a1 with None => False | Some v => a_points_to a1 v a2 end.
Proof.
  intros st [rid|vp] a2; simpl; reflexivity.
Qed.


Lemma stable_partial_path :
  forall st1 st2 st3 a1 a2,
    stable_partial st1 st2 st3 a1 ->
    star (points st3) a1 a2 ->
    star (points st1) a1 a2 \/ get_addr st1 a2 = None.
Proof.
  intros st1 st2 st3 a1 a2 (Hdel1 & Hdel2 & Hstable) Hstar.
  apply star_flip in Hstar. induction Hstar.
  - left. apply star_refl.
  - specialize (IHHstar Hstable).
    destruct (Hstable y) as [[Hy1 | [Hy1a Hy1b]] [Hy2 | [Hy2a Hy2b]]].
    + eapply get_addr_points in H; [|symmetry; eassumption].
      destruct IHHstar;
        [|eapply get_addr_points in H; [|symmetry; eassumption]; destruct y; simpl in *; rewrite H0 in H; tauto].
      left. eapply star_compose; [eassumption|apply star_1].
      eapply get_addr_points; [symmetry|]; eassumption.
    + apply Hy2b. assumption.
    + apply Hy1b. eapply get_addr_points; [symmetry|]; eassumption.
    + apply Hy2b. assumption.
Qed.

(*
Lemma stable_path :
  forall st1 st2 a1 a2,
    stable st1 st2 a1 ->
    star (points_to st2.(st_rthreads) st2.(st_vals)) a1 a2 ->
    get_addr st1 a2 = None \/ star (points_to st1.(st_rthreads) st1.(st_vals)) a1 a2.
Proof.
  intros st1 st2 a1 a2 Hstable Hstar.
  apply star_flip in Hstar. induction Hstar.
  - right. apply star_refl.
  - specialize (IHHstar Hstable).
    destruct (Hstable y) as [HyNone [Hy | [Hy1 Hy2]]].
    + right. eapply get_addr_points_to in H; [|symmetry; eassumption].
      destruct IHHstar; [|eapply star_compose; [eassumption|apply star_1; eassumption]].
      destruct y; simpl in *; rewrite H0 in H; tauto.
    + apply Hy2. assumption.
Qed.
 *)
(*
Lemma stable_path_ext :
  forall st1 st2 a1 a2,
    stable st1 st2 a1 ->
    get_addr st2 a2 = None \/ star (points_to st2.(st_rthreads) st2.(st_vals)) a1 a2 ->
    get_addr st1 a2 = None \/ star (points_to st1.(st_rthreads) st1.(st_vals)) a1 a2.
Proof.
  intros st1 st2 a1 a2 Hstable [H | H].
  - left. apply Hstable. assumption.
  - eapply stable_path; eassumption.
Qed.
 *)

Lemma stable_partial_path_ext :
  forall st1 st2 st3 a1 a2,
    stable_partial st1 st2 st3 a1 ->
    star (points st3) a1 a2 \/ get_addr st3 a2 = None ->
    star (points st1) a1 a2 \/ get_addr st1 a2 = None.
Proof.
  intros st1 st2 st3 a1 a2 Hstable [H | H].
  - eapply stable_partial_path in H; eassumption.
  - right; apply Hstable, Hstable; assumption.
Qed.

Definition stable_partial_weak st1 st2 st3 a :=
  no_delete st2 st3 /\
  forall a2,
    (get_addr st3 a2 = get_addr st2 a2 \/
     ((get_addr st1 a2 = None \/ star (points st1) a a2) /\
      forall a3, points st3 a2 a3 -> star (points st1) a a3 \/ get_addr st1 a3 = None)).

Lemma stable_partial_trans :
  forall st1 st2 st3 st4 a, stable_partial st1 st2 st3 a -> stable_partial_weak st1 st3 st4 a -> stable_partial st1 st2 st4 a.
Proof.
  intros st1 st2 st3 st4 a (H1a & H1b & H1c) (H2a & H2b).
  split; [apply H1a|].
  split; [intros a2 Ha2; apply H1b, H2a; assumption|].
  intros a2. split; [apply H1c|].
  destruct (H2b a2) as [H2b1 | H2b2].
  - destruct (H1c a2) as [H1c1 [H1c2a | [H1c2b1 H1c2b2]]].
    + left. congruence.
    + right. split; [assumption|].
      intros a3 Ha3; apply H1c2b2.
      eapply get_addr_points; [symmetry|]; eassumption.
  - right. assumption.
Qed.

Lemma stable_partial_trans_flipped :
  forall st1 st2 st3 st4 a, stable_partial_weak st1 st3 st4 a -> stable_partial st1 st2 st3 a -> stable_partial st1 st2 st4 a.
Proof.
  intros; eapply stable_partial_trans; eassumption.
Qed.


(*
Lemma stable_trans :
  forall st1 st2 st3 a, stable st1 st2 a -> stable st2 st3 a -> stable st1 st3 a.
Proof.
  intros st1 st2 st3 a H1 H2 a2.
  split; [intros; apply H1, H2; assumption|].
  destruct (H2 a2) as [Ha2Noneb [Ha2b | [Ha2b1 Ha2b2]]].
  - destruct (H1 a2) as [Ha2Nonea [Ha2a | [Ha2a1 Ha2a2]]].
    + left. congruence.
    + right. split; [assumption|].
      intros a3 Ha3; apply Ha2a2.
      eapply get_addr_points_to; [|eassumption].
      symmetry; assumption.
  - destruct (H1 a2) as [Ha2Nonea [Ha2a | [Ha2a1 Ha2a2]]].
    + right. eapply stable_path_ext in Ha2b1; [|eassumption].
      split; [assumption|].
      intros; eapply stable_path_ext; [eassumption|apply Ha2b2; assumption].
    + right. split; [assumption|].
      intros a3 Ha3. eapply Ha2b2, stable_path_ext in Ha3; eassumption.
Qed.
 *)

Lemma stable_partial_stable :
  forall st1 st2 st3 a, stable_partial st1 st2 st3 a -> stable st1 st3 a.
Proof.
  intros st1 st2 st3 a (H1 & H2 & H3).
  split; [apply no_delete_refl|].
  split; [intros a2 Ha2; apply H1, H2; assumption|].
  intros a2.
  split; [left; reflexivity|].
  destruct (H3 a2) as [H3a [H3b1 | [H3b2a H3b2b]]].
  - destruct H3a as [H3a1 | [H3a2a H3a2b]].
    + left; congruence.
    + right. split; [assumption|].
      intros a3 Ha3; apply H3a2b.
      eapply get_addr_points; [symmetry|]; eassumption.
  - right. split; assumption.
Qed.

Lemma stable_partial_stable_trans :
  forall st1 st2 st3 st4 a,
    stable_partial st1 st2 st3 a -> stable st3 st4 a -> stable_partial st1 st2 st4 a.
Proof.
  intros st1 st2 st3 st4 a H123 H34.
  inversion H123 as (H1 & H2 & H3).
  inversion H34 as (H4 & H5 & H6).
  eapply stable_partial_trans; [split; [|split]; eassumption|].
  split; [assumption|].
  intros a2. destruct (H6 a2) as [H6a [H6b1 | [H6b2a H6b2b]]].
  - left; assumption.
  - right. eapply or_comm, stable_partial_path_ext, or_comm in H6b2a; [|eassumption].
    split; [assumption|].
    intros a3 Ha3. eapply stable_partial_path_ext; [eassumption|].
    apply H6b2b; assumption.
Qed.

(*
Lemma stable_stable_partial :
  forall st1 st2 st3 a, no_delete st3 st1 -> stable st1 st2 a -> stable_partial st3 st1 st2 a.
Proof.
  intros st1 st2 st3 a H (_ & H1 & H2).
  split; [apply H|].
  split; [apply H1|].
  intros a2.
  destruct (H2 a2) as [Ha2 | [Ha2a Ha2b]].
  - left. assumption.
  - right. split.
    + destruct Ha2a as [Ha2a | Ha2a]; [left; apply H; assumption|].
    destruct Ha2a.
    + 
    split; [|assumption].
    destruct Ha2a; [|right; assumption].
    left; apply H; assumption.
Qed.
 *)

(*
Lemma stable_trans :
  forall st1 st2 st3 a, no_delete st1 st2 -> stable st1 st2 a -> stable st2 st3 a -> stable st1 st3 a.
Proof.
  intros. eapply stable_partial_trans; [eassumption|].
  apply stable_stable_partial; assumption.
Qed.
 *)

Lemma get_update_addr_eq :
  forall st a v1 v2, get_addr st a = Some v1 -> get_addr (update_addr st a v2) a = Some v2.
Proof.
  intros. destruct a; eapply nth_error_update; eassumption.
Qed.

Lemma get_update_addr_eq2 :
  forall st a v, get_addr (update_addr st a v) a = match get_addr st a with None => None | Some _ => Some v end.
Proof.
  intros. destruct a; eapply nth_error_update2; eassumption.
Qed.

Lemma get_update_addr_eq3 :
  forall st a1 a2 v, a1 <> a2 -> get_addr (update_addr st a2 v) a1 = get_addr st a1.
Proof.
  intros. destruct a1, a2; simpl in *; try reflexivity; eapply nth_error_update3; congruence.
Qed.

Lemma addr_eq_dec :
  forall (a1 a2 : addr), { a1 = a2 } + { a1 <> a2 }.
Proof.
  intros [x|x] [y|y]; try (right; congruence);
    destruct (Nat.eq_dec x y); constructor; congruence.
Qed.

Lemma stable_update :
  forall st1 st2 a1 a2 v,
    get_addr st1 a2 = None \/ star (points st1) a1 a2 ->
    (forall a3, a_points_to a2 v a3 -> star (points st1) a1 a3 \/ get_addr st1 a3 = None) ->
    stable_partial_weak st1 st2 (update_addr st2 a2 v) a1.
Proof.
  intros st1 st2 a1 a2 v H1 H2.
  split.
  - intros a3 Ha3; destruct (addr_eq_dec a3 a2).
    + subst. rewrite get_update_addr_eq2 in Ha3. destruct (get_addr st2 a2); congruence.
    + rewrite get_update_addr_eq3 in Ha3; assumption.
  - intros a3. destruct (addr_eq_dec a3 a2).
    + subst. right. split; [assumption|].
      intros a3 Ha3.
      rewrite get_addr_points2, get_update_addr_eq2 in Ha3.
        destruct (get_addr st2 a2); [|tauto].
        apply H2; assumption.
    + left. rewrite get_update_addr_eq3; [reflexivity|assumption].
Qed.

Lemma nth_error_extend_case :
  forall {A : Type} l (x : A) n,
    nth_error (l ++ x :: nil) n = nth_error l n \/ (n = length l /\ nth_error (l ++ x :: nil) n = Some x).
Proof.
  intros A l x n.
  destruct (le_lt_dec (length l) n).
  - rewrite nth_error_app2 by assumption.
    destruct (n - length l) eqn:Hn; simpl; [right; split; [lia|reflexivity]|].
    left. destruct n0; symmetry; apply nth_error_None; assumption.
  - left. rewrite nth_error_app1; tauto.
Qed.

Lemma stable_addval :
  forall st1 st2 a v,
    length (st1.(st_vals)) <= length (st2.(st_vals)) ->
    (forall a2, val_points_to v a2 -> star (points st1) a a2 \/ get_addr st1 a2 = None) ->
    stable_partial_weak st1 st2 (fst (addval st2 v)) a.
Proof.
  intros st1 st2 a v Hlen H.
  split.
  - intros a2 Ha2.
    destruct a2; simpl in *; [assumption|].
    rewrite nth_error_None in *. rewrite app_length in Ha2. lia.
  - intros a2. destruct a2 as [rid|vp]; simpl in *; [left; reflexivity|].
    destruct (nth_error_extend_case (st_vals st2) v vp) as [-> | [-> ->]].
    + left. reflexivity.
    + right. split; [|assumption].
      left. rewrite nth_error_None. lia.
Qed.

Lemma stable_makelazy :
  forall st1 st2 a t e,
    length (st1.(st_rthreads)) <= length (st2.(st_rthreads)) ->
    length (st1.(st_vals)) <= length (st2.(st_vals)) ->
    (forall a2, env_points_to e a2 -> star (points st1) a a2 \/ get_addr st1 a2 = None) ->
    stable_partial_weak st1 st2 (fst (makelazy st2 t e)) a.
Proof.
  intros st1 st2 a t e Hlen1 Hlen2 H.
  split.
  - intros a2 Ha2.
    destruct a2; simpl in *; rewrite nth_error_None in *; rewrite app_length in Ha2; lia.
  - intros [rid|vp]; simpl in *.
    + destruct (nth_error_extend_case (st_rthreads st2) {| rt_code := Term t e; rt_cont := Kid |} rid) as [-> | [-> ->]].
      * left. reflexivity.
      * right. split; [left; rewrite nth_error_None; lia|].
        intros a2 [Ha2 | Ha2]; inversion Ha2; subst.
        apply H. assumption.
    + destruct (nth_error_extend_case (st_vals st2) (Thread (length (st_rthreads st2))) vp) as [-> | [-> ->]].
      * left. reflexivity.
      * right. split; [left; rewrite nth_error_None; lia|].
        intros a2 Ha2; inversion Ha2; subst.
        right. simpl. rewrite nth_error_None. lia.
Qed.


Lemma step_r_stable :
  forall st rid, stable st (step_r st rid) (a_rthread rid).
Proof.
  intros st rid. unfold step_r.
  destruct nth_error as [[code cont]|] eqn:Hrid; [|apply stable_refl].
  destruct code as [t e|vp].
  - destruct t; cbv beta delta [rt_code rt_cont] iota.
    + destruct (nth_error e n) as [vp|] eqn:He; [|apply stable_refl].
      eapply stable_partial_trans; [apply stable_refl|].
      apply stable_update; [right; apply star_refl|].
      intros a3 [Ha3 | Ha3].
      * inversion Ha3; subst. left. apply star_1.
        simpl. rewrite Hrid. left. constructor.
        eapply nth_error_In; eassumption.
      * left. apply star_1. simpl. rewrite Hrid. right. assumption.
    + apply stable_refl.
    + destruct cont.
      * eapply stable_partial_trans_flipped.
        {
          apply stable_update; [right; apply star_refl|].
          intros a3 [Ha3 | Ha3]; inversion Ha3; subst.
          simpl. rewrite nth_error_None, !app_length; lia.
        }
        eapply stable_partial_trans_flipped.
        {
          apply stable_addval; [simpl; rewrite !app_length; lia|].
          intros a2 Ha2. inversion Ha2; subst.
          -- left. apply star_1. simpl. rewrite Hrid. left. constructor. assumption.
          -- right. simpl. rewrite nth_error_None, app_length. lia.
        }
        eapply stable_partial_trans_flipped.
        {
          apply stable_makelazy; [simpl; lia|simpl; rewrite app_length; lia|].
          intros [rid2|vp2]; [intros [] | intros [H | H]]; simpl in *.
          -- subst. right. rewrite nth_error_None; lia.
          -- left. apply star_1. simpl. rewrite Hrid. left. constructor. assumption.
        }
        eapply stable_partial_trans_flipped; [|apply stable_refl].
        apply stable_addval; [lia|].
        intros a2 Ha2; inversion Ha2; subst. inversion H0.
      * eapply stable_partial_trans_flipped; [|apply stable_refl].
        apply stable_update; [right; apply star_refl|].
        intros a3 [Ha3 | Ha3]; left; apply star_1.
        -- inversion Ha3; subst.
           destruct a3; simpl in *; [tauto|]. rewrite Hrid.
           destruct H2 as [H2 | H2]; [subst; right; constructor|].
           left. constructor. assumption.
        -- simpl. rewrite Hrid. right. constructor. assumption.
      * apply stable_refl.
    + eapply stable_partial_trans_flipped.
      {
        apply stable_update; [right; apply star_refl|].
        intros a3 [Ha3 | Ha3].
        * inversion Ha3; subst. left. apply star_1. simpl. rewrite Hrid. left. constructor. assumption.
        * inversion Ha3; subst; [right; simpl; rewrite nth_error_None; lia|].
          left. apply star_1. simpl. rewrite Hrid. right. assumption.
      }
      eapply stable_partial_trans_flipped; [|apply stable_refl].
      apply stable_makelazy; [lia|lia|].
      intros a3 Ha3; left; apply star_1. simpl. rewrite Hrid. left. constructor. assumption.
    + admit.
    + admit.
  - cbv beta delta [rt_code rt_cont] iota.
    destruct (nth_error st.(st_vals) vp) as [v|] eqn:Hvp; [|apply stable_refl].
    destruct v.
    + destruct is_finished as [v|] eqn:Hfinished; [|apply stable_refl].
      eapply stable_partial_trans_flipped; [|apply stable_refl].
      apply stable_update; [right; apply star_refl|].
      intros a3 [Ha3 | Ha3]; [|left; apply star_1; simpl; rewrite Hrid; right; assumption].
      inversion Ha3; subst. unfold is_finished in Hfinished.
      destruct (nth_error (st_rthreads st) r) as [[code1 cont1]|]eqn:Hr; [|congruence].
      simpl in Hfinished.
      destruct code1 as [? ?|vp2]; [congruence|].
      destruct cont1; try congruence. injection Hfinished as Hfinished. subst.
      left.
      econstructor; [simpl; rewrite Hrid; left; constructor|].
      econstructor; [simpl; rewrite Hvp; constructor|].
      apply star_1. simpl. rewrite Hr. left. constructor.
    + admit.
    + destruct cont.
      * admit.
      * eapply stable_partial_trans_flipped; [|apply stable_refl].
        apply stable_update; [right; apply star_refl|].
        intros a3 [Ha3 | Ha3]; [|left; apply star_1; simpl; rewrite Hrid; right; constructor; assumption].
        inversion Ha3; subst. destruct a3; simpl in *; [tauto|].
        destruct H2 as [H2 | H2]; [left; apply star_1; simpl; rewrite Hrid; subst; right; constructor|].
        left. econstructor; simpl; [rewrite Hrid; left; constructor|].
        apply star_1. simpl. rewrite Hvp. apply clos_points_to_1. assumption.
      * apply stable_refl.
    + admit.
Admitted.



Lemma and_left :
  forall (A B : Prop), A -> (A -> B) -> A /\ B.
Proof.
  intros A B HA HB; split; [apply HA|apply HB, HA].
Qed.

Lemma and_right :
  forall (A B : Prop), (B -> A) -> B -> A /\ B.
Proof.
  intros A B HA HB; split; [apply HA, HB|apply HB].
Qed.

Ltac and_left := apply and_left.
Ltac and_right := apply and_right.
Tactic Notation "and_left" "as" simple_intropattern(p) := and_left; [|intros p].
Tactic Notation "and_right" "as" simple_intropattern(p) := and_right; [intros p|].



Lemma step_r_beta_hnf :
  forall st st2 rid t,
    step_r st rid = st2 ->
    read_addr st (a_rthread rid) t ->
    every_reachable_plus st (a_rthread rid) (fun a => forall t, read_addr st a t -> read_addr st2 a t) /\
    exists t2, read_addr st2 (a_rthread rid) t2 /\ reflc beta_hnf t t2.
Proof.
  intros st st2 rid t <- Hread.
  match goal with [ |- ?G ] => assert (Hsame : every_reachable st (a_rthread rid) (fun a => forall t, read_addr st a t -> read_addr (step_r st rid) a t) -> G) end.
  {
    intros H. rewrite every_reachable_iff in H; destruct H as [H1 H2].
    split; [apply H2|]. eexists; split; [|right; reflexivity]. apply H1, Hread.
  }
  match goal with [ |- ?G ] => assert (Hid : step_r st rid = st -> G) end.
  {
    intros Heq; rewrite Heq in *. apply Hsame. intros ? ? ? ?; assumption.
  }
  unfold step_r in *.
  inversion Hread; subst.
  - rewrite H0 in *; simpl in *.
    inversion H1; subst.
    + rewrite H3 in *. destruct is_finished eqn:Hfinished; [|apply Hid; reflexivity].
      and_left.
      * eapply unchanged_from_plus_update in Hread.
        eapply every_reachable_plus_impl; [|rewrite <- unchanged_from_plus_every_reachable; apply Hread].
        intros a2 Ha2 Heq t Ht; eapply read_addr_same; [eassumption|].
        eapply unchanged_from_plus_
        Search unchanged_from_plus. every_reachable_plus. Check unchanged_from_plus_every_reachable. apply <- unchanged_from_plus_every_reachable.
      intros a Ha t Ht.
      Search read_addr.
      eapply read_thread_val.
      * eapply nth_error_update; eassumption.
      * unfold is_finished in Hfinished.
        inversion H4; subst; rewrite H5 in Hfinished; simpl in *; [|congruence].
        inversion H7; simpl in *; subst; simpl in *; try congruence.
        injection Hfinished as Hfinished; subst.
        eapply read_addr_same; [eassumption|].
        eapply unchanged_from_cycle; [|eassumption].
        eapply plus_S; [|eapply plus_S; [|apply plus_1]].
        -- simpl. rewrite H0. left. constructor.
        -- simpl. rewrite H3. constructor.
        -- simpl. rewrite H5. left. constructor.
      * eapply read_cont_same; [eassumption|].
        intros; eapply read_addr_same; [eassumption|].
        eapply unchanged_from_cycle; [|eassumption].
        apply plus_1. simpl. rewrite H0. right. assumption.
    + rewrite H3.
      inversion H2; subst; try (eexists; split; [eassumption|right; reflexivity]).
      eexists; split; [|left; rewrite fill_compose; simpl; apply beta_hnf_ctx, beta_hnf_red, beta_red_lam].
      unfold subst1, lift_subst. rewrite subst_subst.
      erewrite subst_ext; [eapply read_thread_term|].
      * eapply nth_error_update; eassumption.
      * constructor.
        -- eapply read_addr_same; [eassumption|].
           eapply unchanged_from_cycle; [|eassumption].
           apply plus_1. simpl. rewrite H0. right. constructor.
        -- eapply read_addr_same_Forall2; [eassumption|].
           intros; eapply unchanged_from_cycle; [|eassumption].
           eapply plus_S; [simpl; rewrite H0; left; constructor|].
           apply plus_1. simpl. rewrite H3. apply clos_points_to_1. assumption.
      * eapply read_cont_same; [eassumption|].
        intros; eapply read_addr_same; [eassumption|].
        eapply unchanged_from_cycle; [|eassumption].
        apply plus_1. simpl. rewrite H0. right. constructor. assumption.
      * intros [|n]; unfold comp; simpl; [rewrite read_env_0; reflexivity|].
        rewrite read_env_S. rewrite subst_ren.
        erewrite subst_ext; [apply subst_id|].
        intros n2; unfold comp; simpl. destruct n2; reflexivity.
    + rewrite H3.
      admit.
  - rewrite H0; cbv beta delta [rt_code] iota.
    destruct t0; cbv iota.
    + eexists; split; [|right; reflexivity].
      destruct (nth_error e n) eqn:He; [|assumption].
      econstructor.
      * eapply nth_error_update; eassumption.
      * simpl.
        eapply nth_error_Forall2 in H1; [|eassumption].
        destruct H1 as (vv & Hvv1 & Hvv2).
        eapply read_addr_same; [unfold read_env; rewrite Hvv1; eassumption|].
        eapply unchanged_from_cycle; [|eassumption].
        apply plus_1. simpl. rewrite H0. left. constructor. simpl.
        eapply nth_error_In; eassumption.
      * eapply read_cont_same; [eassumption|].
        intros; eapply read_addr_same; [eassumption|].
        eapply unchanged_from_cycle; [|eassumption].
        apply plus_1. simpl. rewrite H0. right. assumption.
    + admit.
    + destruct c.
      * eexists; split; [|right; reflexivity]. cbv beta delta [rt_cont] iota.
        match goal with [ |- read_addr ?st _ _ ] => set (st5 := st) end.
        match eval unfold st5 in st5 with exit_rthread ?st _ _ => set (st4 := st) end; fold st4 in st5.
        match eval unfold st4 in st4 with fst (addval ?st _) => set (st3 := st) end; fold st3 in st4, st5.
        match eval unfold st3 in st3 with fst (makelazy ?st _ _) => set (st2 := st) end; fold st2 in st3, st4, st5.
        assert (Hchange2 : unchanged_from st st2 (a_rthread rid)) by (eapply unchanged_from_addval; eassumption).
        assert (Hchange3 : unchanged_from st2 st3 (a_rthread rid)) by (eapply unchanged_from_makelazy, read_addr_same; eassumption).
        assert (Hchange13 : unchanged_from st st3 (a_rthread rid)) by (eapply unchanged_from_trans; eassumption).
        assert (Hchange4 : unchanged_from st3 st4 (a_rthread rid)) by (eapply unchanged_from_addval, read_addr_same; eassumption).
        assert (Hchange14 : unchanged_from st st4 (a_rthread rid)) by (eapply unchanged_from_trans; eassumption).
        assert (Hchange5 : unchanged_from_plus st4 st5 (a_rthread rid)) by (eapply unchanged_from_plus_update, read_addr_same; eassumption).
        assert (Hchange15 : unchanged_from_plus st st5 (a_rthread rid)) by (eapply unchanged_from_plus_trans; eassumption).
        simpl. eapply read_thread_val.
        -- eapply nth_error_update, nth_error_app_Some; eassumption.
        -- eapply read_val_clos; [apply nth_error_extend| | |].
           ++ eapply read_addr_same_Forall2; [eassumption|].
             intros vp Hvp; apply Hchange15; simpl.
             rewrite H0; simpl. left; constructor. assumption.
           ++ eapply read_val_thread; [apply nth_error_app_Some, nth_error_extend|].
             eapply read_thread_term.
             ** unfold st5, exit_rthread; simpl; rewrite nth_error_update3; [apply nth_error_extend|].
                apply nth_error_Some3 in H0; lia.
             ** constructor.
                --- eapply read_val_neutral; [apply nth_error_app_Some, nth_error_app_Some, nth_error_extend|].
                    constructor.
                --- eapply read_addr_same_Forall2; [eassumption|].
                    intros vp Hvp; apply Hchange15; simpl.
                    rewrite H0; simpl. left; constructor. assumption.
             ** constructor.
           ++ simpl. apply star_refl.
        -- inversion H2; subst. constructor.
      * inversion H2; subst; simpl in *.
        eexists; split; [|left; rewrite fill_compose; simpl; apply beta_hnf_ctx, beta_hnf_red, beta_red_lam].
        unfold subst1, lift_subst. rewrite subst_subst.
        erewrite subst_ext; [eapply read_thread_term|].
        -- eapply nth_error_update; eassumption.
        -- constructor.
           ++ eapply read_addr_same; [eassumption|].
             eapply unchanged_from_cycle; [|eassumption].
             apply plus_1. simpl. rewrite H0. right.
             constructor.
           ++ eapply read_addr_same_Forall2; [eassumption|].
             intros; eapply unchanged_from_cycle; [|eassumption].
             apply plus_1. simpl. rewrite H0. left. constructor. assumption.
        -- eapply read_cont_same; [eassumption|].
           intros; eapply read_addr_same; [eassumption|].
           eapply unchanged_from_cycle; [|eassumption].
           apply plus_1. simpl. rewrite H0. right. constructor. assumption.
        -- intros [|n]; unfold comp; simpl; [rewrite read_env_0; reflexivity|].
           rewrite read_env_S. rewrite subst_ren.
           erewrite subst_ext; [apply subst_id|].
           intros n2; unfold comp; simpl. destruct n2; reflexivity.
      * simpl.
        eexists; split; [eassumption|right; reflexivity].
    + eexists. split.
      * match goal with [ |- read_addr ?st _ _ ] => pose (st2 := st) end.
        assert (Hchange : unchanged_from_plus st st2 (a_rthread rid)).
        {
          eapply unchanged_from_plus_trans; [|eapply unchanged_from_plus_update, read_addr_same; [eassumption|]];
            eapply unchanged_from_makelazy; eassumption.
        }
        eapply read_thread_term; [eapply nth_error_update, nth_error_app_Some; eassumption| |].
        -- eapply read_addr_same_Forall2; [eassumption|].
           intros; apply Hchange. simpl; rewrite H0.
           left. constructor. assumption.
        -- constructor.
           ++ eapply read_val_thread; simpl; [rewrite nth_error_extend; reflexivity|].
             eapply read_thread_term; simpl.
             ** rewrite nth_error_update3 by (apply nth_error_Some3 in H0; lia).
                apply nth_error_extend.
             ** eapply read_addr_same_Forall2; [eassumption|].
                intros; apply Hchange. simpl; rewrite H0.
                left. constructor. assumption.
             ** constructor.
           ++ eapply read_cont_same; [eassumption|].
             intros; eapply read_addr_same; [eassumption|].
             apply Hchange. simpl; rewrite H0.
             right. assumption.
      * right. rewrite fill_compose. reflexivity.
    + admit.
    + admit.
Admitted.

Lemma stable_beta_hnf :
  forall st st2 rid t t2,
    read_addr st (a_rthread rid) t ->
    read_addr st2 (a_rthread rid) t2 ->
    unchanged_from_plus st st2 (a_rthread rid) ->
    reflc beta_hnf t t2 ->
    stable st st2 (a_rthread rid) ->
    (forall a t3, read_addr st a t3 -> exists t4, read_addr st2 a t4 /\ star beta_hnf t3 t4).
Proof.
  intros st st2 rid t t2 Hread1 Hread2 Hchange Hreflc (_ & Hdel & Hstable) a t3 Hread.
  assert (Hacc := read_addr_Acc _ _ _ Hread). induction Hacc.
  destruct (proj2 (Hstable x)) as [Heq | [[Hnone | Hstar] Hpoints]].
  - admit.
  - inversion Hread; subst; simpl in *; congruence.
  inversion Hread; subst.
  - 
  Search Acc.
  induction Hread.
