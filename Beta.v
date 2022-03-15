Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import Rewrite.
Require Import STerm.
Require Import Inductive.
Require Import GenInd.

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

Lemma beta_subst1 : forall t1 t2 us, beta t1 t2 -> beta (subst us t1) (subst us t2).
Proof.
  intros t1 t2 us H. revert us. induction H; intros us; simpl in *.
  - constructor. apply IHbeta.
  - constructor. apply IHbeta.
  - constructor. apply IHbeta.
  - rewrite subst_subst1.
    constructor.
  - rewrite !map_app. simpl. constructor. apply IHbeta.
  - constructor. apply IHbeta.
  - rewrite !map_app. simpl. constructor. apply IHbeta.
  - rewrite !map_app. simpl.
    rewrite subst_read_env.
    ereplace (length l1); [|eapply map_length].
    ereplace (length l); [|eapply map_length].
    constructor.
Qed.

Lemma star_beta_subst1 : forall t1 t2 us, star beta t1 t2 -> star beta (subst us t1) (subst us t2).
Proof.
  intros t1 t2 us H. eapply star_map_impl with (f := fun t => subst us t); [|eassumption].
  intros; apply beta_subst1; assumption.
Qed.

Lemma beta_subst2 : forall t us1 us2, (forall n, star beta (us1 n) (us2 n)) -> star beta (subst us1 t) (subst us2 t).
Proof.
  intros t us1 us2 Hus. revert us1 us2 Hus. induction t using term_ind2; intros us1 us2 Hus; simpl in *.
  - apply Hus.
  - constructor.
  - apply star_beta_abs. apply IHt.
    intros [|n]; simpl; [constructor|].
    unfold comp. rewrite !ren_term_is_subst.
    apply star_beta_subst1, Hus.
  - apply star_beta_app; [apply IHt1|apply IHt2]; assumption.
  - apply star_beta_constr. rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same.
    eapply Forall_impl; [|eassumption].
    intros t H1; apply H1, Hus.
  - apply star_beta_switch; [apply IHt, Hus|].
    rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same.
    eapply Forall_impl; [|eassumption].
    intros [p t2] H1; split; [reflexivity|]; apply H1. simpl.
    intros n; unfold liftn_subst. destruct le_lt_dec; [|constructor].
    rewrite !ren_term_is_subst.
    apply star_beta_subst1, Hus.
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




(*
Inductive beta : term -> term -> Prop :=
| beta_app1 : forall t1 t2 t3, beta t1 t2 -> beta (app t1 t3) (app t2 t3)
| beta_app2 : forall t1 t2 t3, beta t1 t2 -> beta (app t3 t1) (app t3 t2)
| beta_abs : forall t1 t2, beta t1 t2 -> beta (abs t1) (abs t2)
| beta_redex : forall t1 t2, beta (app (abs t1) t2) (subst1 t2 t1)
| beta_constr : forall tag l1 l2, step_one beta l1 l2 -> beta (constr tag l1) (constr tag l2)
| beta_switch1 : forall t1 t2 l, beta t1 t2 -> beta (switch t1 l) (switch t2 l)
| beta_switch2 : forall t l1 l2, step_one (fun pt1 pt2 => fst pt1 = fst pt2 /\ beta (snd pt1) (snd pt2)) l1 l2 -> beta (switch t l1) (switch t l2)
| beta_switch_redex : forall l t l1 l2, beta (switch (constr (length l1) l) (l1 ++ (length l, t) :: l2)) (subst (read_env l) t).
Definition beta_ind2 := Induction For [ beta ].


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
  eapply star_map_impl; [|eapply step_one_star; eassumption].
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
  - eapply star_map_impl; [|eapply step_one_star]; [intros; constructor; eassumption|].
    eapply Forall2_impl; [|eassumption].
    intros [p t3] [? t4]; simpl in *; intros [<- H2].
    eapply star_map_impl; [|eassumption].
    intros; split; [reflexivity|assumption].
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
Definition pbeta_ind2 := Induction For [ pbeta ].

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

Lemma beta_pbeta :
  forall t1 t2, beta t1 t2 -> pbeta t1 t2.
Proof.
  apply beta_ind2.
  - intros t1 t2 t3 Hbeta IH; constructor; [assumption|apply pbeta_refl].
  - intros t1 t2 t3 Hbeta IH; constructor; [apply pbeta_refl|assumption].
  - intros t Hbeta IH; constructor; assumption.
  - intros t1 t2; constructor; apply pbeta_refl.
  - intros tag l1 l2 Hbeta IH. constructor.
    clear Hbeta; induction IH.
    + constructor; [tauto|]. eapply Forall2_map_same, Forall_True; intros; apply pbeta_refl.
    + constructor; [apply pbeta_refl|assumption].
  - intros t1 t2 l Hbeta IH; constructor.
    + assumption.
    + apply Forall2_map_same, Forall_True; intros; split; [reflexivity|apply pbeta_refl].
  - intros t l1 l2 Hbeta IH; constructor.
    + apply pbeta_refl.
    + clear Hbeta. induction IH.
      * constructor; [tauto|]. eapply Forall2_map_same, Forall_True; intros; split; [reflexivity|apply pbeta_refl].
      * constructor; [split; [reflexivity|apply pbeta_refl]|assumption].
  - constructor; [|apply pbeta_refl].
    apply Forall2_map_same, Forall_True; intros; apply pbeta_refl.
Qed.
*)

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


Definition fst3 {A B C : Type} (x : A * B * C) := fst (fst x).
Definition snd3 {A B C : Type} (x : A * B * C) := snd (fst x).
Definition thd3 {A B C : Type} (x : A * B * C) := snd x.


Definition rthreadptr := nat.
Definition cthreadptr := nat.
Definition threadptr := (nat + nat)%type.

Inductive cont : Type :=
| Kid : cont
| Kapp : value -> cont -> cont
| Kswitch : list (nat * term) -> list value (* env *) -> list (list nat * value) -> cont -> cont

with value : Type :=
| Thread : rthreadptr -> value
| Neutral : (nat * cont * option value) (* neutral *) -> value
| Clos : term -> list value (* env *) -> nat -> value -> value
| Block : nat -> list value -> value.

Definition env := list value.
Definition neutral := (nat * cont * option value)%type.

Definition n_var (n : neutral) := fst3 n.
Definition n_cont (n : neutral) := snd3 n.
Definition n_unfold (n : neutral) := thd3 n.

Inductive code :=
| Term : term -> env -> code
| Val : value -> code.

Record rthread := mkrthread {
  rt_code : code ;
  rt_cont : cont ;
}.

Inductive cthread :=
| cthread_done : bool -> cthread
| cthread_reduce : value -> value -> list nat -> list nat -> cthread
| cthread_and : cthread -> cthread -> cthread
| cthread_or : cthread -> cthread -> cthread.

(*
Inductive addr :=
| a_rthread : rthreadptr -> addr
| a_cthread : cthreadptr -> addr.
 *)
Definition addr := rthreadptr.

(*
Definition env_points_to e a :=
  match a with
  | a_val vp => In vp e
  | _ => False
  end.
 *)

Inductive cont_points_to : cont -> addr -> Prop :=
| kapp_points_to_1 : forall v c a, val_points_to v a -> cont_points_to (Kapp v c) a
| kapp_points_to_2 : forall v c a, cont_points_to c a -> cont_points_to (Kapp v c) a
| kswitch_points_to_1 : forall bs e bds c a, Exists (fun v => val_points_to v a) e -> cont_points_to (Kswitch bs e bds c) a
| kswitch_points_to_2 : forall bs e bds c a,
    Exists (fun bd => val_points_to (snd bd) a) bds -> cont_points_to (Kswitch bs e bds c) a
| kswitch_points_to_3 : forall bs e bds c a, cont_points_to c a -> cont_points_to (Kswitch bs e bds c) a

with val_points_to : value -> addr -> Prop :=
| thread_points_to : forall rid, val_points_to (Thread rid) rid
| neutral_points_to_1 : forall n a, cont_points_to (n_cont n) a -> val_points_to (Neutral n) a
| neutral_points_to_2 : forall n v a, n_unfold n = Some v -> val_points_to v a -> val_points_to (Neutral n) a
| clos_points_to_1 : forall t e vn vdeep a, Exists (fun v => val_points_to v a) e -> val_points_to (Clos t e vn vdeep) a
| clos_points_to_2 : forall t e vn vdeep a, val_points_to vdeep a -> val_points_to (Clos t e vn vdeep) a
| block_points_to : forall tag l a, Exists (fun v => val_points_to v a) l -> val_points_to (Block tag l) a.

Definition cont_val_ind := Induction For [cont_points_to ; val_points_to].
Check cont_val_ind.

Definition env_points_to e a := Exists (fun v => val_points_to v a) e.

Inductive code_points_to : code -> addr -> Prop :=
| term_points_to : forall t e a, env_points_to e a -> code_points_to (Term t e) a
| cval_points_to : forall v a, val_points_to v a -> code_points_to (Val v) a.

Definition rthread_points_to rt a := code_points_to rt.(rt_code) a \/ cont_points_to rt.(rt_cont) a.

Definition points_to rthreads (a1 a2 : rthreadptr):=
  match nth_error rthreads a1 with
  | Some rt => rthread_points_to rt a2
  | None => False
  end.

Record state := mkstate {
  st_rthreads : list rthread ;
  st_freename : nat ;
}.

Definition points st := points_to st.(st_rthreads).

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


Lemma Acc_star_down :
  forall (A : Type) (R : A -> A -> Prop) x y, Acc R x -> star R y x -> Acc R y.
Proof.
  intros A R x y H1 H2. induction H2.
  - assumption.
  - apply IHstar in H1. inversion H1.
    apply H0. assumption.
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
  forall rthreads rid rt a1 a2,
    points_to (update rthreads rid rt) a1 a2 <->
    updatep (points_to rthreads) rid (fun a => rid < length rthreads /\ rthread_points_to rt a) a1 a2.
Proof.
  intros rthreads rid rt rid2 a; unfold updatep, points_to; simpl.
  destruct (Nat.eq_dec rid rid2); subst.
  - rewrite nth_error_update2.
    destruct nth_error eqn:Hnth; [apply nth_error_Some3 in Hnth|apply nth_error_None in Hnth]; intuition lia.
  - rewrite nth_error_update3; [|assumption].
    intuition congruence.
Qed.

Lemma points_to_updatep_rthread_extend :
  forall rthreads rt a1 a2,
    points_to (rthreads ++ rt :: nil) a1 a2 <->
    updatep (points_to rthreads) (length rthreads) (rthread_points_to rt) a1 a2.
Proof.
  intros rthreads rt rid a; unfold updatep, points_to; simpl.
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



Lemma update_length :
  forall {A : Type} (l : list A) k x, length (update l k x) = length l.
Proof.
  induction l; intros [|k] x; simpl in *; congruence.
Qed.

Definition update_rthread st rid rt :=
  {|
    st_rthreads := update st.(st_rthreads) rid rt ;
    st_freename := st.(st_freename) ;
  |}.

Definition freevar (st : state) :=
  ({|
      st_rthreads := st.(st_rthreads) ;
      st_freename := S (st.(st_freename)) ;
    |}, st.(st_freename)).

Definition freevars (st : state) (n : nat) :=
  ({|
      st_rthreads := st.(st_rthreads) ;
      st_freename := n + st.(st_freename) ;
    |}, seq st.(st_freename) n).

Definition extend_rthread st rt :=
  {|
    st_rthreads := st.(st_rthreads) ++ rt :: nil ;
    st_freename := st.(st_freename) ;
  |}.

Definition makelazy (st : state) (t : term) (e : env) :=
  (* For now, ignore variable optimization *)
  (extend_rthread st {| rt_code := Term t e ; rt_cont := Kid |}, Thread (length st.(st_rthreads))).

Definition exit_rthread (st : state) (rid : rthreadptr) (v : value) :=
  update_rthread st rid {| rt_code := Val v ; rt_cont := Kid |}.

Definition is_finished (st : state) (rid : rthreadptr) :=
  match nth_error st.(st_rthreads) rid with
  | None => None
  | Some rthread =>
    match rthread.(rt_code), rthread.(rt_cont) with
    | Val v, Kid => Some v
    | _, _ => None
    end
  end.

Fixpoint compose_cont (c c2 : cont) :=
  match c with
  | Kid => c2
  | Kapp v c => Kapp v (compose_cont c c2)
  | Kswitch bs e bds c => Kswitch bs e bds (compose_cont c c2)
  end.

Fixpoint makenlazy (st : state) (ts : list term) (e : env) :=
  match ts with
  | nil => (st, nil)
  | t :: ts =>
    let st2v := makelazy st t e in
    let st3vl := makenlazy (fst st2v) ts e in
    (fst st3vl, snd st2v :: snd st3vl)
  end.

Fixpoint makendeeps (st : state) (bs : list (nat * term)) (e : env) :=
  match bs with
  | nil => (st, nil)
  | (p, t) :: bs =>
    let st2xs := freevars st p in
    let st3v := makelazy (fst st2xs) t (map (fun x => Neutral (x, Kid, None)) (snd st2xs) ++ e) in
    let st4vl := makendeeps (fst st3v) bs e in
    (fst st4vl, (snd st2xs, snd st3v) :: snd st4vl)
  end.

Fixpoint index {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y}) (l : list A) (x : A) :=
  match l with
  | nil => None
  | y :: l =>
    if eq_dec x y then Some 0 else match index eq_dec l x with None => None | Some n => Some (S n) end
  end.

Definition step_r (st : state) (rid : rthreadptr) : state :=
  match nth_error st.(st_rthreads) rid with
  | None => st
  | Some rthread =>
    match rthread.(rt_code) with
    | Term (app u v) e =>
      let st2v := makelazy st v e in
      update_rthread (fst st2v) rid {| rt_code := Term u e ; rt_cont := Kapp (snd st2v) rthread.(rt_cont) |}
    | Term (abs u) e =>
      match rthread.(rt_cont) with
      | Kswitch _ _ _ _ => st (* type error *)
      | Kid =>
        let st2y := freevar st in
        let st3v := makelazy (fst st2y) u ((Neutral (snd st2y, Kid, None)) :: e) in
        exit_rthread (fst st3v) rid (Clos u e (snd st2y) (snd st3v))
      | Kapp v c =>
        update_rthread st rid {| rt_code := Term u (v :: e) ; rt_cont := c |}
      end
    | Term (var n) e =>
      match nth_error e n with
      | None => st (* variable not found *)
      | Some v =>
        update_rthread st rid {| rt_code := Val v ; rt_cont := rthread.(rt_cont) |}
      end
    | Term (dvar n) e => st (* All dvars should be replaced with vars before execution *)
    | Term (constr tag l) e =>
      let st2vl := makenlazy st l e in
      update_rthread (fst st2vl) rid {| rt_code := Val (Block tag (snd st2vl)) ; rt_cont := rthread.(rt_cont) |}
    | Term (switch t m) e =>
      let st2vl := makendeeps st m e in
      update_rthread (fst st2vl) rid {| rt_code := Term t e ; rt_cont := Kswitch m e (snd st2vl) rthread.(rt_cont) |}
    | Val (Thread rid2) =>
      match is_finished st rid2 with
      | None => st (* Thread is not finished yet, wait *)
      | Some v =>
        update_rthread st rid {| rt_code := Val v ; rt_cont := rthread.(rt_cont) |}
      end
    | Val (Clos u e y vdeep) =>
      match rthread.(rt_cont) with
      | Kid => st (* Thread is finished *)
      | Kswitch _ _ _ _  => st (* type error *)
      | Kapp v c =>
        update_rthread st rid {| rt_code := Term u (v :: e) ; rt_cont := c |}
      end
    | Val (Neutral (x, c, uf)) =>
      let st2v :=
          match uf with
          | None => (st, None)
          | Some uf =>
            (extend_rthread st {| rt_code := Val uf ; rt_cont := rthread.(rt_cont) |},
             Some (Thread (length st.(st_rthreads))))
          end
      in
      exit_rthread (fst st2v) rid (Neutral (x, compose_cont c rthread.(rt_cont), (snd st2v)))
    | Val (Block tag l) =>
      match rthread.(rt_cont) with
      | Kid => st (* Thread is finished *)
      | Kapp _ _ => st (* type error *)
      | Kswitch bs e bds c =>
        match nth_error bs tag with
        | None => st (* type error *)
        | Some (p, t) =>
          if Nat.eq_dec p (length l) then
            update_rthread st rid {| rt_code := Term t (l ++ e) ; rt_cont := c |}
          else st (* type error *)
        end
      end
    end
  end.

Fixpoint cthread_andn (l : list cthread) :=
  match l with
  | nil => cthread_done true
  | c :: l => cthread_and c (cthread_andn l)
  end.

Fixpoint cmp_cont (c1 c2 : cont) varmap1 varmap2 :=
  match c1, c2 with
  | Kid, Kid => Some nil
  | Kapp u1 c1, Kapp u2 c2 =>
    match cmp_cont c1 c2 varmap1 varmap2 with
    | None => None
    | Some l => Some (cthread_reduce u1 u2 varmap1 varmap2 :: l)
    end
  | Kswitch _ _ l1 c1, Kswitch _ _ l2 c2 =>
    if Nat.eqb (length l1) (length l2) then
      let l12 := combine l1 l2 in
      if forallb (fun vv => Nat.eqb (length (fst (fst vv))) (length (fst (snd vv)))) l12 then
        match cmp_cont c1 c2 varmap1 varmap2 with
        | None => None
        | Some l => Some (map (fun vv => cthread_reduce (snd (fst vv)) (snd (snd vv)) (fst (fst vv) ++ varmap1) (fst (snd vv) ++ varmap2)) l12 ++ l)
        end
      else None
    else None
  | _, _ => None
  end.

Definition cmp_cont_cthread (c1 c2 : cont) varmap1 varmap2 :=
  match cmp_cont c1 c2 varmap1 varmap2 with
  | Some l => cthread_andn l
  | None => cthread_done false
  end.

Inductive cthread_red (st : state) : cthread -> cthread -> Prop :=
| cthread_reduce_1 :
    forall rid v1 v2 varmap1 varmap2,
      is_finished st rid = Some v1 ->
      cthread_red st (cthread_reduce (Thread rid) v2 varmap1 varmap2) (cthread_reduce v1 v2 varmap1 varmap2)
| cthread_reduce_2 :
    forall rid v1 v2 varmap1 varmap2,
      is_finished st rid = Some v2 ->
      cthread_red st (cthread_reduce v1 (Thread rid) varmap1 varmap2) (cthread_reduce v1 v2 varmap1 varmap2)
| cthread_reduce_clos_clos :
    forall t1 t2 e1 e2 x1 x2 v1 v2 varmap1 varmap2,
      cthread_red st (cthread_reduce (Clos t1 e1 x1 v1) (Clos t2 e2 x2 v2) varmap1 varmap2)
                  (cthread_reduce v1 v2 (x1 :: varmap1) (x2 :: varmap2))
| cthread_reduce_block_block_same :
    forall tag l1 l2 varmap1 varmap2,
      length l1 = length l2 ->
      cthread_red st (cthread_reduce (Block tag l1) (Block tag l2) varmap1 varmap2)
                  (cthread_andn (map (fun v12 => cthread_reduce (fst v12) (snd v12) varmap1 varmap2) (combine l1 l2)))
| cthread_reduce_block_block_different_lengths :
    forall tag l1 l2 varmap1 varmap2,
      length l1 <> length l2 ->
      cthread_red st (cthread_reduce (Block tag l1) (Block tag l2) varmap1 varmap2) (cthread_done false)
| cthread_reduce_block_block_different_tags :
    forall tag1 tag2 l1 l2 varmap1 varmap2,
      tag1 <> tag2 ->
      cthread_red st (cthread_reduce (Block tag1 l1) (Block tag2 l2) varmap1 varmap2) (cthread_done false)
| cthread_reduce_clos_block :
    forall t e x v tag l varmap1 varmap2,
      cthread_red st (cthread_reduce (Clos t e x v) (Block tag l) varmap1 varmap2) (cthread_done false)
| cthread_reduce_block_clos :
    forall tag l t e x v varmap1 varmap2,
      cthread_red st (cthread_reduce (Block tag l) (Clos t e x v) varmap1 varmap2) (cthread_done false)
| cthread_reduce_var_unfold_1 :
    forall x c uf v varmap1 varmap2,
      cthread_red st (cthread_reduce (Neutral (x, c, Some uf)) v varmap1 varmap2)
                  (cthread_reduce uf v varmap1 varmap2)
| cthread_reduce_var_unfold_2 :
    forall v x c uf varmap1 varmap2,
      cthread_red st (cthread_reduce v (Neutral (x, c, Some uf)) varmap1 varmap2)
                  (cthread_reduce v uf varmap1 varmap2)
| cthread_reduce_same_var_unfold :
    forall x c1 c2 uf1 uf2 varmap1 varmap2,
      cthread_red st (cthread_reduce (Neutral (x, c1, Some uf1)) (Neutral (x, c2, Some uf2)) varmap1 varmap2)
                  (cthread_or (cthread_reduce uf1 uf2 varmap1 varmap2) (cmp_cont_cthread c1 c2 varmap1 varmap2))
| cthread_reduce_var_nounfold :
    forall x1 x2 c1 c2 varmap1 varmap2,
      index Nat.eq_dec varmap1 x1 = index Nat.eq_dec varmap2 x2 ->
      cthread_red st (cthread_reduce (Neutral (x1, c1, None)) (Neutral (x2, c2, None)) varmap1 varmap2)
                  (cmp_cont_cthread c1 c2 varmap1 varmap2)
| cthread_reduce_different_var_nounfold :
    forall x1 x2 c1 c2 varmap1 varmap2,
      index Nat.eq_dec varmap1 x1 <> index Nat.eq_dec varmap2 x2 ->
      cthread_red st (cthread_reduce (Neutral (x1, c1, None)) (Neutral (x2, c2, None)) varmap1 varmap2)
                  (cthread_done false)
| cthread_reduce_clos_var_nounfold :
    forall t e x v y c varmap1 varmap2,
      cthread_red st (cthread_reduce (Clos t e x v) (Neutral (y, c, None)) varmap1 varmap2) (cthread_done false)
| cthread_reduce_block_var_nounfold :
    forall tag l x c varmap1 varmap2,
      cthread_red st (cthread_reduce (Block tag l) (Neutral (x, c, None)) varmap1 varmap2) (cthread_done false)
| cthread_reduce_var_clos_nounfold :
    forall y c t e x v varmap1 varmap2,
      cthread_red st (cthread_reduce (Neutral (y, c, None)) (Clos t e x v) varmap1 varmap2) (cthread_done false)
| cthread_reduce_var_block_nounfold :
    forall x c tag l varmap1 varmap2,
      cthread_red st (cthread_reduce (Neutral (x, c, None)) (Block tag l) varmap1 varmap2) (cthread_done false)
| cthread_and_true :
    cthread_red st (cthread_and (cthread_done true) (cthread_done true)) (cthread_done true)
| cthread_and_false_1 :
    forall ct, cthread_red st (cthread_and (cthread_done false) ct) (cthread_done false)
| cthread_and_false_2 :
    forall ct, cthread_red st (cthread_and ct (cthread_done false)) (cthread_done false)
| cthread_or_false :
    cthread_red st (cthread_or (cthread_done false) (cthread_done false)) (cthread_done false)
| cthread_or_true_1 :
    forall ct, cthread_red st (cthread_or (cthread_done true) ct) (cthread_done true)
| cthread_or_true_2 :
    forall ct, cthread_red st (cthread_or ct (cthread_done true)) (cthread_done true)
| cthread_and_1 :
    forall ct1 ct2 ct3, cthread_red st ct1 ct2 -> cthread_red st (cthread_and ct1 ct3) (cthread_and ct2 ct3)
| cthread_and_2 :
    forall ct1 ct2 ct3, cthread_red st ct1 ct2 -> cthread_red st (cthread_and ct3 ct1) (cthread_and ct3 ct2)
| cthread_or_1 :
    forall ct1 ct2 ct3, cthread_red st ct1 ct2 -> cthread_red st (cthread_or ct1 ct3) (cthread_or ct2 ct3)
| cthread_or_2 :
    forall ct1 ct2 ct3, cthread_red st ct1 ct2 -> cthread_red st (cthread_or ct3 ct1) (cthread_or ct3 ct2)
.

Inductive step : (cthread * state) -> (cthread * state) -> Prop :=
| step_rthread :
    forall ct st rid, rid < length st.(st_rthreads) -> step (ct, st) (ct, (step_r st rid))
| step_cthread :
    forall ct1 ct2 st, cthread_red st ct1 ct2 -> step (ct1, st) (ct2, st).



Inductive dvar_free x : term -> Prop :=
| dvar_free_var : forall n, dvar_free x (var n)
| dvar_free_dvar : forall y, x <> y -> dvar_free x (dvar y)
| dvar_free_abs : forall t, dvar_free x t -> dvar_free x (abs t)
| dvar_free_app : forall t1 t2, dvar_free x t1 -> dvar_free x t2 -> dvar_free x (app t1 t2)
| dvar_free_constr : forall tag l, Forall (dvar_free x) l -> dvar_free x (constr tag l)
| dvar_free_switch : forall t m, dvar_free x t -> Forall (fun pt => dvar_free x (snd pt)) m -> dvar_free x (switch t m).

Definition no_dvar t := forall x, dvar_free x t.

Fixpoint lift_dvars vars k t :=
  match t with
  | var n => var n
  | dvar n => match index Nat.eq_dec vars n with Some p => var (k + p) | None => dvar n end
  | app t1 t2 => app (lift_dvars vars k t1) (lift_dvars vars k t2)
  | abs t => abs (lift_dvars vars (S k) t)
  | constr tag l => constr tag (map (lift_dvars vars k) l)
  | switch t m => switch (lift_dvars vars k t) (map (fun pt => (fst pt, lift_dvars vars (fst pt + k) (snd pt))) m)
  end.

Fixpoint lift_dvars_hctx vars k h :=
  match h with
  | h_hole => h_hole
  | h_app h t => h_app (lift_dvars_hctx vars k h) (lift_dvars vars k t)
  | h_switch h m => h_switch (lift_dvars_hctx vars k h) (map (fun pt => (fst pt, lift_dvars vars (fst pt + k) (snd pt))) m)
  end.

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

Definition no_delete st1 st2 := forall rid, nth_error st2.(st_rthreads) rid = None -> nth_error st1.(st_rthreads) rid = None.

Lemma no_delete_refl :
  forall st, no_delete st st.
Proof.
  intros st rid H; assumption.
Qed.

Lemma no_delete_iff :
  forall st1 st2, no_delete st1 st2 <->
             length st1.(st_rthreads) <= length st2.(st_rthreads).
Proof.
  intros st1 st2. split.
  - intros H.
    + specialize (H (length (st_rthreads st2))). simpl in H.
      rewrite !nth_error_None in H. lia.
  - intros Hlen rid H; simpl in *; rewrite nth_error_None in *; lia.
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

Lemma Forall2_Exists_left_transparent :
  forall (A B : Type) (P : A -> B -> Prop) (Q : A -> Prop) (R : Prop) (L1 : list A) (L2 : list B) (H : forall x y, P x y -> Q x -> R), Forall2 P L1 L2 -> Exists Q L1 -> R.
Proof.
  intros A B P Q R L1 L2 H HP HQ; induction HP.
  - inversion HQ.
  - inversion HQ; subst; [eapply H; eassumption|].
    apply IHHP, H2.
Defined.

Lemma Forall3_Exists_2_transparent :
  forall (A B C : Type) (P : A -> B -> C -> Prop) (Q : B -> Prop) (R : Prop) L1 L2 L3 (H : forall x y z, P x y z -> Q y -> R), Forall3 P L1 L2 L3 -> Exists Q L2 -> R.
Proof.
  intros A B C P Q R L1 L2 L3 H HP HQ; induction HP.
  - inversion HQ.
  - inversion HQ; subst; [eapply H; eassumption|].
    apply IHHP, H2.
Defined.

Lemma Forall3_impl_In :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) L1 L2 L3,
    (forall x y z, In x L1 -> In y L2 -> In z L3 -> P x y z -> Q x y z) -> Forall3 P L1 L2 L3 -> Forall3 Q L1 L2 L3.
Proof.
  intros A B C P Q L1 L2 L3 H Hforall. induction Hforall.
  - constructor.
  - econstructor.
    + apply H; try (left; reflexivity). assumption.
    + apply IHHforall.
      intros; eapply H; try right; assumption.
Qed.


Inductive read_thread st defs : list nat -> rthreadptr -> term -> Prop :=
| read_thread_val : forall varmap rid v c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Val v ; rt_cont := c |} ->
    read_val st defs varmap v t ->
    read_cont st defs varmap c h ->
    read_thread st defs varmap rid (fill_hctx h t)
| read_thread_term : forall varmap rid e el c t h,
    nth_error st.(st_rthreads) rid = Some {| rt_code := Term t e ; rt_cont := c |} ->
    closed_at t (length e) ->
    Forall2 (read_val st defs varmap) e el ->
    read_cont st defs varmap c h ->
    no_dvar t ->
    read_thread st defs varmap rid (fill_hctx h (subst (read_env el) t))

with read_val st defs : list nat -> value -> term -> Prop :=
| read_val_thread :
    forall varmap rid t, read_thread st defs varmap rid t -> read_val st defs varmap (Thread rid) t
| read_val_clos :
    forall varmap t e el x vdeep tdeep,
      Forall2 (read_val st defs varmap) e el ->
      read_val st defs (x :: varmap) vdeep tdeep ->
      (* convertible beta (subst (read_env (dvar x :: el)) t) tdeep -> *)
      (* convertible beta (subst (read_env (var 0 :: el)) t) tdeep -> *)
      convertible beta (subst (lift_subst (read_env el)) t) tdeep ->
      no_dvar t -> (* Forall (dvar_free x) el -> *) length defs <= x < st.(st_freename) -> x \notin varmap ->
      closed_at t (S (length e)) ->
      read_val st defs varmap (Clos t e x vdeep) (subst (read_env el) (abs t))
| read_val_block :
    forall varmap tag e el,
      Forall2 (read_val st defs varmap) e el ->
      read_val st defs varmap (Block tag e) (constr tag el)
| read_val_neutral :
    forall varmap x c h uf tuf,
      read_cont st defs varmap c h ->
      if_Some3 (fun v2 t2 def =>
                  read_val st defs varmap v2 t2 /\
                  convertible beta (fill_hctx h def) t2 /\
                  closed_at def 0)
               uf tuf (nth_error defs x) ->
      x < st.(st_freename) ->
      (nth_error defs x = None -> In x varmap) ->
      read_val st defs varmap (Neutral (x, c, uf)) (fill_hctx h (match index Nat.eq_dec varmap x with None => dvar x | Some n => var n end))

with read_cont st defs : list nat -> cont -> hctx -> Prop :=
| read_cont_kid : forall varmap, read_cont st defs varmap Kid h_hole
| read_cont_kapp :
    forall varmap v c t h,
      read_val st defs varmap v t ->
      read_cont st defs varmap c h ->
      read_cont st defs varmap (Kapp v c) (compose_hctx h (h_app h_hole t))
| read_cont_kswitch :
    forall varmap bs e bds tdeeps c el h,
      Forall2 (read_val st defs varmap) e el ->
      read_cont st defs varmap c h ->
      Forall3
        (fun pt vdeeps tdeep =>
           length (fst vdeeps) = fst pt /\
           read_val st defs (fst vdeeps ++ varmap) (snd vdeeps) tdeep /\
           (* convertible beta (subst (read_env (map dvar (fst vdeeps) ++ el)) (snd pt)) tdeep /\ *)
           (* convertible beta (subst (read_env (map var (seq 0 (length (fst vdeeps))) ++ el)) (snd pt)) tdeep /\ *)
           convertible beta (subst (liftn_subst (fst pt) (read_env el)) (snd pt)) tdeep /\
           (* Forall (fun x => Forall (dvar_free x) el) (fst vdeeps) /\ *)
           closed_at (snd pt) (fst pt + length e) /\
           Forall (fun x => length defs <= x < st.(st_freename) /\ x \notin varmap) (fst vdeeps) /\
           NoDup (fst vdeeps) /\
           no_dvar (snd pt)
        ) bs bds tdeeps ->
      read_cont st defs varmap (Kswitch bs e bds c) (compose_hctx h (h_switch h_hole (map (fun '(p, t) => (p, subst (liftn_subst p (read_env el)) t)) bs))).

Definition read_ind st defs := Induction For [ read_thread st defs ; read_val st defs ; read_cont st defs ].

Ltac read_thread_val_intro :=
  intros varmap rid v c t h Hnth Hv Hc IHv IHc.
Ltac read_thread_term_intro :=
  intros varmap rid e el c t h Hnth Hclosed He Hc Hdv IHe IHc.
Ltac read_val_thread_intro :=
  intros varmap rid t Hrid IH.
Ltac read_val_clos_intro :=
  intros varmap t e el x vdeep tdeep He Hvdeep Hconv Hdv Hfree1 Hfree2 Hclosed IHe IHdeep.
Ltac read_val_block_intro :=
  intros varmap tag e el He IHe.
Ltac read_val_neutral_intro :=
  intros varmap x c h uf tuf Hc Huf Hfree Hin IHc IHuf.
Ltac read_cont_kid_intro :=
  intros varmap.
Ltac read_cont_kapp_intro :=
  intros varmap v c t h Hv Hc IHv IHc.
Ltac read_cont_kswitch_intro :=
  intros varmap bs e bds tdeeps c el h He Hc Hdeeps IHe IHc IHdeep.
Ltac read_ind :=
  apply read_ind; [read_thread_val_intro|read_thread_term_intro|read_val_thread_intro|read_val_clos_intro|read_val_block_intro|read_val_neutral_intro|read_cont_kid_intro|read_cont_kapp_intro|read_cont_kswitch_intro].

Lemma read_Acc_aux :
  forall st defs, (forall varmap a t, read_thread st defs varmap a t -> Acc (flip (points st)) a) /\
             (forall varmap v t, read_val st defs varmap v t -> forall a, val_points_to v a -> Acc (flip (points st)) a) /\
             (forall varmap c h, read_cont st defs varmap c h -> forall a, cont_points_to c a -> Acc (flip (points st)) a).
Proof.
  intros st defs. read_ind.
  - constructor. intros rid2 Hpoint. unfold flip, points, points_to in Hpoint; simpl in Hpoint.
    rewrite Hnth in Hpoint. destruct Hpoint as [Hpoint | Hpoint].
    + apply IHv. inversion Hpoint; subst. assumption.
    + apply IHc. assumption.
  - constructor. intros rid2 Hpoint. unfold flip, points, points_to in Hpoint; simpl in Hpoint.
    rewrite Hnth in Hpoint. destruct Hpoint as [Hpoint | Hpoint].
    + inversion Hpoint; subst. eapply Forall2_Exists_left_transparent; [|eassumption|eassumption].
      intros v1 t1 IH Hpoint2; apply IH, Hpoint2.
    + apply IHc, Hpoint.
  - intros a Hpoint; inversion Hpoint; subst; assumption.
  - intros a Hpoint.
    inversion Hpoint; subst.
    + eapply Forall2_Exists_left_transparent; [|eassumption|eassumption].
      intros v1 t1 IH Hpoint2; apply IH, Hpoint2.
    + apply IHdeep. assumption.
  - intros a Hpoint. inversion Hpoint; subst.
    eapply Forall2_Exists_left_transparent; [|eassumption|eassumption].
    intros v t IH Hpoint2; apply IH, Hpoint2.
  - intros a Hpoint. inversion Hpoint; subst.
    + apply IHc. assumption.
    + simpl in *. subst. inversion IHuf; subst. apply H3, H1.
  - intros a Hpoint. inversion Hpoint.
  - intros a Hpoint; inversion Hpoint; subst.
    + apply IHv. assumption.
    + apply IHc. assumption.
  - intros a Hpoint.
    inversion Hpoint; subst.
    + eapply Forall2_Exists_left_transparent; try eassumption.
      intros v1 t1 IH Hpoint2; apply IH, Hpoint2.
    + eapply Forall3_Exists_2_transparent; try eassumption.
      intros pt1 vd1 t1 IH Hpoint2. apply IH, Hpoint2.
    + apply IHc. assumption.
Qed.

Lemma read_thread_Acc :
  forall st defs varmap a t, read_thread st defs varmap a t -> Acc (flip (points st)) a.
Proof.
  intros. eapply (proj1 (read_Acc_aux st defs)); eassumption.
Qed.

Lemma read_val_Acc :
  forall st defs varmap v t a, read_val st defs varmap v t -> val_points_to v a -> Acc (flip (points st)) a.
Proof.
  intros. eapply (proj1 (proj2 (read_Acc_aux st defs))); eassumption.
Qed.

Lemma read_cont_Acc :
  forall st defs varmap c h a, read_cont st defs varmap c h -> cont_points_to c a -> Acc (flip (points st)) a.
Proof.
  intros. eapply (proj2 (proj2 (read_Acc_aux st defs))); eassumption.
Qed.


Lemma read_points_aux :
  forall st defs, (forall varmap a t, read_thread st defs varmap a t -> True) /\
             (forall varmap v t, read_val st defs varmap v t -> forall a, val_points_to v a -> exists t varmap2, read_thread st defs (varmap2 ++ varmap) a t) /\
             (forall varmap c h, read_cont st defs varmap c h -> forall a, cont_points_to c a -> exists t varmap2, read_thread st defs (varmap2 ++ varmap) a t).
Proof.
  intros st defs. read_ind.
  - tauto.
  - tauto.
  - intros a Hpoint; inversion Hpoint; subst. eexists; exists nil; eassumption.
  - intros a Hpoint.
    inversion Hpoint; subst.
    + eapply Forall2_Exists_left_transparent; [|eassumption|eassumption].
      intros v1 t1 IH Hpoint2; apply IH, Hpoint2.
    + destruct (IHdeep _ H4) as (t1 & varmap2 & IH).
      exists t1. exists (varmap2 ++ (x :: nil)). rewrite <- app_assoc. assumption.
  - intros a Hpoint.
    inversion Hpoint; subst.
    eapply Forall2_Exists_left_transparent; [|eassumption|eassumption].
    intros v t IH Hpoint2; apply IH, Hpoint2.
  - intros a Hpoint. inversion Hpoint; subst.
    + apply IHc. assumption.
    + simpl in *. subst. inversion IHuf; subst. apply H3, H1.
  - intros a Hpoint. inversion Hpoint.
  - intros a Hpoint; inversion Hpoint; subst.
    + apply IHv. assumption.
    + apply IHc. assumption.
  - intros a Hpoint.
    inversion Hpoint; subst.
    + eapply Forall2_Exists_left_transparent; try eassumption.
      intros v1 t1 IH Hpoint2; apply IH, Hpoint2.
    + eapply Forall3_Exists_2_transparent; try eassumption.
      intros pt1 vd1 t1 IH Hpoint2.
      destruct (IH _ Hpoint2) as (t2 & varmap2 & IH2).
      exists t2. exists (varmap2 ++ fst vd1). rewrite <- app_assoc. assumption.
    + apply IHc. assumption.
Qed.

Lemma read_val_points :
  forall st defs varmap v t a, read_val st defs varmap v t -> val_points_to v a ->
                          exists t varmap2, read_thread st defs (varmap2 ++ varmap) a t.
Proof.
  intros st defs varmap v t a H.
  eapply (proj1 (proj2 (read_points_aux st defs))); eassumption.
Qed.

Lemma read_cont_points :
  forall st defs varmap c h a, read_cont st defs varmap c h -> cont_points_to c a ->
                          exists t varmap2, read_thread st defs (varmap2 ++ varmap) a t.
Proof.
  intros st defs varmap c h a H.
  eapply (proj2 (proj2 (read_points_aux st defs))); eassumption.
Qed.

Lemma read_thread_points :
  forall st defs varmap a1 a2 t,
    read_thread st defs varmap a1 t -> points st a1 a2 ->
    exists t varmap2, read_thread st defs (varmap2 ++ varmap) a2 t.
Proof.
  intros st defs varmap a1 a2 t H1 H2. inversion H1; subst; unfold points, points_to in *; rewrite H in H2; destruct H2.
  - inversion H2. subst. eapply read_val_points; eassumption.
  - eapply read_cont_points; eassumption.
  - inversion H2; subst. eapply Forall2_Exists_left_transparent; try eassumption.
    intros; simpl in *; eapply read_val_points; eassumption.
  - eapply read_cont_points; eassumption.
Qed.

Lemma star_preserve :
  forall {A : Type} (R : A -> A -> Prop) (P : A -> Prop), (forall x y, R x y -> P x -> P y) -> forall x y, P x -> star R x y -> P y.
Proof.
  intros A R P H x y Hx Hxy. induction Hxy.
  - assumption.
  - eapply IHHxy, H, Hx. apply H0.
Qed.

(*
Lemma read_cont_points_to :
  forall st c h a, read_cont st c h -> cont_points_to c a -> exists t, read_thread st a t.
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

Lemma read_thread_points_to_star :
  forall st a1 t a2, read_thread st a1 t -> star (points st) a1 a2 -> exists t2, read_thread st a2 t2.
Proof.
  intros st a1 t a2 Hread H. revert t Hread; induction H; intros t Hread.
  - eexists; eassumption.
  - eapply read_addr_points_to in Hread; [|eassumption].
    destruct Hread.
    eapply IHstar; eassumption.
Qed.
 *)

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
  - intros a2 Ha2 a3 Ha3. apply H. rewrite (plus_star_iff _ _ _ _). exists a2. split; assumption.
  - intros a3 Ha3. rewrite (plus_star_iff _ _ _ _) in Ha3; destruct Ha3 as (a2 & Ha2 & Ha3).
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
    apply H. rewrite (plus_star_iff _ _ _ _); eexists; split; eassumption.
Qed.


Definition unchanged_from st1 st2 a := every_reachable st1 a (fun a2 => nth_error st1.(st_rthreads) a2 = nth_error st2.(st_rthreads) a2).
Definition unchanged_from_plus st1 st2 a := every_reachable_plus st1 a (fun a2 => nth_error st1.(st_rthreads) a2 = nth_error st2.(st_rthreads) a2).

Lemma unchanged_from_same :
  forall st1 st2 a, unchanged_from st1 st2 a -> nth_error st1.(st_rthreads) a = nth_error st2.(st_rthreads) a.
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

(*
Definition unchanged_read st1 st2 a := every_reachable st1 a (fun a2 => forall t, read_thread st1 a t -> read_thread st2 a t).
Definition unchanged_read_plus st1 st2 a := every_reachable_plus st1 a (fun a2 => forall t, read_thread st1 a t -> read_thread st2 a t).
 *)

Lemma read_same_aux :
  forall st1 st2 defs,
    st_freename st1 <= st_freename st2 ->
    (forall varmap a t, read_thread st1 defs varmap a t -> unchanged_from st1 st2 a -> read_thread st2 defs varmap a t) /\
    (forall varmap v t, read_val st1 defs varmap v t -> (forall a, val_points_to v a -> unchanged_from st1 st2 a) -> read_val st2 defs varmap v t) /\
    (forall varmap c h, read_cont st1 defs varmap c h -> (forall a, cont_points_to c a -> unchanged_from st1 st2 a) -> read_cont st2 defs varmap c h).
Proof.
  intros st1 st2 defs Hst12. read_ind; intros Hunchanged.
  - eapply read_thread_val.
    + erewrite unchanged_from_same in Hnth; eassumption.
    + apply IHv. intros a Ha; eapply unchanged_from_points; [eassumption|].
      unfold points, points_to. rewrite Hnth. left; constructor; assumption.
    + apply IHc. intros a Ha; eapply unchanged_from_points; [eassumption|].
      unfold points, points_to. rewrite Hnth. right; assumption.
  - eapply read_thread_term.
    + erewrite unchanged_from_same in Hnth; eassumption.
    + assumption.
    + eapply Forall2_impl_In_left_transparent; [|apply IHe].
      intros v2 t2 Hin IH; simpl in *.
      apply IH. intros a Ha; eapply unchanged_from_points; [eassumption|].
      unfold points, points_to. rewrite Hnth. left; constructor.
      apply Exists_exists; eexists; split; eassumption.
    + apply IHc. intros a Ha; eapply unchanged_from_points; [eassumption|].
      unfold points, points_to. rewrite Hnth. right; assumption.
    + assumption.
  - eapply read_val_thread. apply IH, Hunchanged. constructor.
  - eapply read_val_clos.
    + eapply Forall2_impl_In_left_transparent; [|apply IHe].
      intros v2 t2 Hin IH; simpl in *.
      apply IH. intros a Ha; apply Hunchanged. eapply clos_points_to_1.
      eapply Exists_exists. eexists; split; eassumption.
    + apply IHdeep. intros; apply Hunchanged; eapply clos_points_to_2; assumption.
    + assumption.
    + assumption.
    + lia.
    + assumption.
    + assumption.
  - apply read_val_block.
    eapply Forall2_impl_In_left_transparent; [|apply IHe].
    intros v t Hin IH; simpl in *.
    apply IH. intros a Ha; apply Hunchanged. apply block_points_to.
    eapply Exists_exists. eexists; split; eassumption.
  - eapply read_val_neutral.
    + apply IHc. intros a Ha; apply Hunchanged, neutral_points_to_1, Ha.
    + inversion IHuf; subst.
      * constructor.
      * constructor. inversion Huf; subst. assert (z0 = z) by congruence; subst. split; [|tauto].
        apply H2. intros a Ha; eapply Hunchanged, neutral_points_to_2, Ha. reflexivity.
    + lia.
    + assumption.
  - constructor.
  - eapply read_cont_kapp.
    + apply IHv. intros a Ha; apply Hunchanged, kapp_points_to_1, Ha.
    + apply IHc. intros a Ha; apply Hunchanged, kapp_points_to_2, Ha.
  - eapply read_cont_kswitch.
    + eapply Forall2_impl_In_left_transparent; [|apply IHe].
      intros v2 t2 Hin IH; simpl in *.
      apply IH. intros a Ha; apply Hunchanged. eapply kswitch_points_to_1.
      eapply Exists_exists. eexists; split; eassumption.
    + apply IHc. intros a Ha; eapply Hunchanged, kswitch_points_to_3, Ha.
    + eapply Forall3_impl_In; [|eapply Forall3_and; [apply Hdeeps|apply IHdeep]].
      intros pt vdeeps tdeep Hin1 Hin2 Hin3 [Hdeep IH].
      repeat (split; try tauto).
      * apply IH. intros a Ha; eapply Hunchanged, kswitch_points_to_2.
        eapply Exists_exists. eexists; split; eassumption.
      * eapply Forall_impl; [|apply Hdeep]. intros x [Hfree1 Hfree2]; split; [lia|assumption].
Qed.

Lemma read_thread_same :
  forall st1 st2 defs varmap a t, st_freename st1 <= st_freename st2 -> read_thread st1 defs varmap a t -> unchanged_from st1 st2 a -> read_thread st2 defs varmap a t.
Proof.
  intros st1 st2 defs varmap a t Hst12. apply (proj1 (read_same_aux st1 st2 defs Hst12)).
Qed.

Lemma read_val_same :
  forall st1 st2 defs varmap v t, st_freename st1 <= st_freename st2 -> read_val st1 defs varmap v t -> (forall a, val_points_to v a -> unchanged_from st1 st2 a) -> read_val st2 defs varmap v t.
Proof.
  intros st1 st2 defs varmap v t Hst12. apply (proj1 (proj2 (read_same_aux st1 st2 defs Hst12))).
Qed.

Lemma read_cont_same :
  forall st1 st2 defs varmap c h, st_freename st1 <= st_freename st2 -> read_cont st1 defs varmap c h -> (forall a, cont_points_to c a -> unchanged_from st1 st2 a) -> read_cont st2 defs varmap c h.
Proof.
  intros st1 st2 defs varmap c h Hst12. apply (proj2 (proj2 (read_same_aux st1 st2 defs Hst12))).
Qed.


(*
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
 *)

(*
*)
Lemma unchanged_from_trans :
  forall st1 st2 st3 a, unchanged_from st1 st2 a -> unchanged_from st2 st3 a -> unchanged_from st1 st3 a.
Proof.
  intros st1 st2 st3 a H1 H2 rid Ha.
  etransitivity; [eapply H1; eassumption|].
  eapply H2. clear H2. induction Ha.
  - constructor.
  - econstructor; [|eapply IHHa, unchanged_from_points; eassumption].
    eapply unchanged_from_same in H1. unfold points, points_to in H.
    rewrite H1 in H; assumption.
Qed.

Lemma unchanged_from_plus_trans :
  forall st1 st2 st3 a, unchanged_from st1 st2 a -> unchanged_from_plus st2 st3 a -> unchanged_from_plus st1 st3 a.
Proof.
  intros st1 st2 st3 a H12 H23.
  apply every_reachable_plus_iff.
  intros a2 Ha2.
  eapply every_reachable_plus_iff in H23; [eapply unchanged_from_trans; [|eassumption]|].
  - eapply unchanged_from_points; eassumption.
  - unfold points, points_to in *. rewrite <- (unchanged_from_same _ _ _ H12). assumption.
Qed.

Lemma nth_error_extend :
  forall {A : Type} (l : list A) x, nth_error (l ++ x :: nil) (length l) = Some x.
Proof.
  intros A l x. rewrite nth_error_app2 by lia.
  destruct (length l - length l) eqn:Hll; [reflexivity|lia].
Qed.

(*
Lemma unchanged_from_makelazy :
  forall st t e a t2,
    read_thread st a t2 ->
    unchanged_from st (fst (makelazy st t e)) a.
Proof.
  intros st t e a t2 Hread a2 Ha2. unfold makelazy; simpl.
  eapply read_thread_points_to_star in Ha2; [|eassumption].
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
*)
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
(*
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
*)

Definition only_extended st1 st2 :=
  forall rid rt, nth_error (st_rthreads st1) rid = Some rt -> nth_error (st_rthreads st2) rid = Some rt.

Definition only_changed st1 st2 rid :=
  forall rid2 rt, rid <> rid2 -> nth_error (st_rthreads st1) rid2 = Some rt -> nth_error (st_rthreads st2) rid2 = Some rt.

Lemma only_extended_refl :
  forall st, only_extended st st.
Proof.
  intros st rid rt H; assumption.
Qed.

Lemma only_changed_refl :
  forall st rid, only_changed st st rid.
Proof.
  intros st rid rid2 rt H1 H2; assumption.
Qed.

Lemma only_changed_refl_eq :
  forall st st2 rid, st_rthreads st = st_rthreads st2 -> only_changed st st2 rid.
Proof.
  intros st st2 rid Heq rid2 rt H1 H2; rewrite <- Heq; assumption.
Qed.

Lemma only_extended_trans :
  forall st1 st2 st3, only_extended st1 st2 -> only_extended st2 st3 -> only_extended st1 st3.
Proof.
  intros st1 st2 st3 H1 H2 rid rt H; apply H2, H1, H.
Qed.

Lemma only_changed_trans :
  forall st1 st2 st3 rid,
    only_changed st1 st2 rid -> only_changed st2 st3 rid -> only_changed st1 st3 rid.
Proof.
  intros st1 st2 st3 rid H1 H2 rid2 rt Hneq Hnth.
  apply H2, H1; assumption.
Qed.

Lemma only_extended_changed :
  forall st1 st2 rid, only_extended st1 st2 -> only_changed st1 st2 rid.
Proof.
  intros st1 st2 rid H rid2 rt H1 H2; apply H; assumption.
Qed.

Lemma only_changed_update :
  forall st rid rt, only_changed st (update_rthread st rid rt) rid.
Proof.
  intros st rid rt rid2 rt2 Hneq Hnth.
  simpl. rewrite nth_error_update3 by assumption. assumption.
Qed.

Lemma only_extended_extend :
  forall st rt, only_extended st (extend_rthread st rt).
Proof.
  intros st rt rid rt2 Hnth.
  simpl. apply nth_error_app_Some; assumption.
Qed.

Lemma only_extended_makelazy :
  forall st t e, only_extended st (fst (makelazy st t e)).
Proof.
  intros st t e. apply only_extended_extend.
Qed.

Lemma only_extended_makenlazy :
  forall st ts e, only_extended st (fst (makenlazy st ts e)).
Proof.
  intros st ts e; revert st; induction ts as [|t ts]; intros st.
  - apply only_extended_refl.
  - simpl. eapply only_extended_trans; [eapply only_extended_makelazy|].
    apply IHts.
Qed.

Lemma only_changed_extend :
  forall st rt rid, only_changed st (extend_rthread st rt) rid.
Proof.
  intros; apply only_extended_changed, only_extended_extend.
Qed.

Lemma only_changed_makelazy :
  forall st t e rid, only_changed st (fst (makelazy st t e)) rid.
Proof.
  intros; apply only_extended_changed, only_extended_makelazy.
Qed.

Lemma only_changed_makenlazy :
  forall st ts e rid, only_changed st (fst (makenlazy st ts e)) rid.
Proof.
  intros; apply only_extended_changed, only_extended_makenlazy.
Qed.

Lemma read_thread_star_points :
  forall st defs varmap a1 a2 t,
    read_thread st defs varmap a1 t -> star (points st) a1 a2 ->
    exists t2 varmap2, read_thread st defs (varmap2 ++ varmap) a2 t2.
Proof.
  intros st defs varmap a1 a2 t H1 H2.
  eapply star_preserve with (P := fun a => exists t3 varmap2, read_thread st defs (varmap2 ++ varmap) a t3); [|eexists; exists nil; eassumption|eassumption].
  intros ? ? ? (? & varmap2 & H3). eapply read_thread_points in H3; [|eassumption].
  destruct H3 as (? & varmap3 & H3).
  eexists; exists (varmap3 ++ varmap2); rewrite <- app_assoc; eassumption.
Qed.

Lemma unchanged_from_only_extended :
  forall st st2 defs varmap rid t2, read_thread st defs varmap rid t2 -> only_extended st st2 -> unchanged_from st st2 rid.
Proof.
  intros st st2 defs varmap rid t2 Hread Hext a Ha.
  simpl.
  destruct (nth_error (st_rthreads st) a) eqn:H; [symmetry; apply Hext; assumption|].
  exfalso.
  eapply read_thread_star_points in Ha; [|eassumption].
  destruct Ha as (t3 & varmap2 & Ha). inversion Ha; subst; congruence.
Qed.

Lemma unchanged_from_extend :
  forall st defs varmap rt rid t2, read_thread st defs varmap rid t2 -> unchanged_from st (extend_rthread st rt) rid.
Proof.
  intros. eapply unchanged_from_only_extended; [eassumption|].
  apply only_extended_extend.
Qed.

Lemma unchanged_from_makelazy :
  forall st defs varmap t e rid t2, read_thread st defs varmap rid t2 -> unchanged_from st (fst (makelazy st t e)) rid.
Proof.
  intros. eapply unchanged_from_extend; eassumption.
Qed.

Lemma unchanged_from_freevar :
  forall st rid, unchanged_from st (fst (freevar st)) rid.
Proof.
  intros st rid a Ha; reflexivity.
Qed.

Lemma unchanged_from_plus_only_changed :
  forall st st2 defs varmap rid t2, read_thread st defs varmap rid t2 -> only_changed st st2 rid -> unchanged_from_plus st st2 rid.
Proof.
  intros st st2 defs varmap rid t2 Hread Hchg a Ha.
  simpl.
  destruct (nth_error (st_rthreads st) a) eqn:H; [symmetry; apply Hchg; [|assumption]|exfalso].
  - intros Heq; subst.
    eapply Acc_cycle; [eassumption|].
    eapply read_thread_Acc; eassumption.
  - eapply plus_star, read_thread_star_points in Ha; [|eassumption].
    destruct Ha as (t3 & varmap2 & Ha). inversion Ha; subst; congruence.
Qed.

(*

Lemma unchanged_from_cycle :
  forall st defs a1 v a2 t, plus (points st) a1 a2 -> read_thread st defs a1 t -> unchanged_from st (update_rthread st a1 v) a2.
Proof.
  intros st defs rid v rid2 t Hplus Hread rid3 Ha3. unfold update_rthread in *; simpl in *.
  destruct (update_case st.(st_rthreads) rid rid3 v); [|congruence].
  destruct H; subst. exfalso.
  eapply Acc_cycle; [eapply plus_compose_star_right; eassumption|].
  eapply read_thread_Acc; eassumption.
Qed.

Lemma unchanged_from_plus_cycle :
  forall st defs a1 v a2 t, star (points st) a1 a2 -> read_thread st defs a1 t -> unchanged_from_plus st (update_rthread st a1 v) a2.
Proof.
  intros st defs a1 v a2 t Hstar Hread. eapply every_reachable_plus_iff. intros a3 Hpoints.
  eapply unchanged_from_cycle; [|eassumption].
  eapply plus_compose_star_left; [eassumption|].
  apply plus_1; assumption.
Qed.
*)

Lemma unchanged_from_plus_update :
  forall st defs varmap a v t, read_thread st defs varmap a t -> unchanged_from_plus st (update_rthread st a v) a.
Proof.
  intros; eapply unchanged_from_plus_only_changed; [eassumption|].
  apply only_changed_update.
Qed.


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

Definition same_read_plus st1 st2 defs rid :=
  every_reachable_plus st1 rid (fun a => forall varmap t, read_thread st1 defs varmap a t -> read_thread st2 defs varmap a t).

Lemma same_read_plus_aux :
  forall st1 st2 defs rid,
    st_freename st1 <= st_freename st2 ->
    same_read_plus st1 st2 defs rid ->
    (forall varmap a t, read_thread st1 defs varmap a t -> True) /\
    (forall varmap v t, read_val st1 defs varmap v t -> (forall a, val_points_to v a -> plus (points st1) rid a) -> read_val st2 defs varmap v t) /\
    (forall varmap c h, read_cont st1 defs varmap c h -> (forall a, cont_points_to c a -> plus (points st1) rid a) -> read_cont st2 defs varmap c h).
Proof.
  intros st1 st2 defs rid1 Hst12 H. read_ind; try intros Hplus.
  - tauto.
  - tauto.
  - constructor.
    apply H; [|assumption]. apply Hplus. constructor.
  - eapply read_val_clos; [| |eassumption|eassumption|lia|eassumption|eassumption].
    + eapply Forall2_impl_In_left_transparent; [|apply IHe].
      intros v1 t1 Hin IH. apply IH.
      intros a Ha; apply Hplus; apply clos_points_to_1.
      apply Exists_exists; eexists; split; eassumption.
    + apply IHdeep. intros a Ha; apply Hplus.
      apply clos_points_to_2. assumption.
  - eapply read_val_block.
    eapply Forall2_impl_In_left_transparent; [|apply IHe].
    intros v1 t1 Hin IH. apply IH.
    intros a Ha; apply Hplus; apply block_points_to.
    apply Exists_exists; eexists; split; eassumption.
  - eapply read_val_neutral.
    + apply IHc. intros a Ha; apply Hplus, neutral_points_to_1, Ha.
    + inversion IHuf; subst; [inversion Huf; subst; constructor|]. constructor.
      inversion Huf; subst. assert (z0 = z) by congruence; subst.
      split; [|tauto].
      apply H3. intros a Ha; eapply Hplus, neutral_points_to_2; [reflexivity|eassumption].
    + lia.
    + assumption.
  - eapply read_cont_kid.
  - eapply read_cont_kapp.
    + apply IHv. intros a Ha; apply Hplus, kapp_points_to_1, Ha.
    + apply IHc. intros a Ha; apply Hplus, kapp_points_to_2, Ha.
  - eapply read_cont_kswitch.
    + eapply Forall2_impl_In_left_transparent; [|apply IHe].
      intros v1 t1 Hin IH. apply IH.
      intros a Ha; apply Hplus; apply kswitch_points_to_1.
      apply Exists_exists; eexists; split; eassumption.
    + apply IHc. intros a Ha; apply Hplus, kswitch_points_to_3, Ha.
    + eapply Forall3_impl_In; [|apply Forall3_and; [apply Hdeeps|apply IHdeep]].
      intros ? ? ? ? ? ? [? ?].
      repeat (split; try tauto).
      * apply H4. intros a Ha; apply Hplus, kswitch_points_to_2.
        apply Exists_exists; eexists; split; eassumption.
      * eapply Forall_impl; [|apply H3]. intros ? [Hfree1 Hfree2]; split; [lia|assumption].
Qed.

Lemma same_read_plus_val :
  forall st1 st2 defs varmap rid v t,
    st_freename st1 <= st_freename st2 -> same_read_plus st1 st2 defs rid -> read_val st1 defs varmap v t ->
    (forall a, val_points_to v a -> plus (points st1) rid a) -> read_val st2 defs varmap v t.
Proof.
  intros st1 st2 defs varmap rid v t Hst12 H.
  apply (proj1 (proj2 (same_read_plus_aux st1 st2 defs rid Hst12 H))).
Qed.

Lemma same_read_plus_cont :
  forall st1 st2 defs varmap rid c h,
    st_freename st1 <= st_freename st2 -> same_read_plus st1 st2 defs rid -> read_cont st1 defs varmap c h ->
    (forall a, cont_points_to c a -> plus (points st1) rid a) -> read_cont st2 defs varmap c h.
Proof.
  intros st1 st2 defs varmap rid c h Hst12 H.
  apply (proj2 (proj2 (same_read_plus_aux st1 st2 defs rid Hst12 H))).
Qed.

Lemma same_read_plus_val_1 :
  forall st1 st2 defs varmap rid v t,
    st_freename st1 <= st_freename st2 -> same_read_plus st1 st2 defs rid -> read_val st1 defs varmap v t ->
    (forall a, val_points_to v a -> points st1 rid a) -> read_val st2 defs varmap v t.
Proof.
  intros st1 st2 defs varmap rid v t Hst12 H1 H2 H3.
  eapply same_read_plus_val; try eassumption.
  intros; apply plus_1, H3; assumption.
Qed.

Lemma same_read_plus_cont_1 :
  forall st1 st2 defs varmap rid c h,
    st_freename st1 <= st_freename st2 -> same_read_plus st1 st2 defs rid -> read_cont st1 defs varmap c h ->
    (forall a, cont_points_to c a -> points st1 rid a) -> read_cont st2 defs varmap c h.
Proof.
  intros st1 st2 defs varmap rid v t Hst12 H1 H2 H3.
  eapply same_read_plus_cont; try eassumption.
  intros; apply plus_1, H3; assumption.
Qed.

(*
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
 *)
Lemma same_read_plus_val_Forall2 :
  forall st1 st2 defs varmap e el rid,
    st_freename st1 <= st_freename st2 ->
    same_read_plus st1 st2 defs rid ->
    Forall2 (read_val st1 defs varmap) e el ->
    (forall v a, In v e -> val_points_to v a -> plus (points st1) rid a) ->
    Forall2 (read_val st2 defs varmap) e el.
Proof.
  intros st1 st2 defs varmap e el rid Hst12 H1 H2 H3.
  eapply Forall2_impl_In_left_transparent; [|eassumption].
  intros; eapply same_read_plus_val; try eassumption.
  intros; eapply H3; eassumption.
Qed.

Lemma same_read_plus_val_Forall2_1 :
  forall st1 st2 defs varmap e el rid,
    st_freename st1 <= st_freename st2 ->
    same_read_plus st1 st2 defs rid ->
    Forall2 (read_val st1 defs varmap) e el ->
    (forall v a, In v e -> val_points_to v a -> points st1 rid a) ->
    Forall2 (read_val st2 defs varmap) e el.
Proof.
  intros st1 st2 defs varmap e el rid Hst12 H1 H2 H3.
  eapply same_read_plus_val_Forall2; try eassumption.
  intros; eapply plus_1, H3; eassumption.
Qed.


Lemma same_read_unchanged :
  forall st st2 defs rid, st_freename st <= st_freename st2 -> unchanged_from_plus st st2 rid -> same_read_plus st st2 defs rid.
Proof.
  intros st st2 defs rid Hst12 H.
  eapply every_reachable_plus_impl; [|apply H].
  intros a Ha Heq varmap t Ht; eapply read_thread_same; [eassumption|eassumption|].
  eapply every_reachable_star_plus; eassumption.
Qed.

Lemma same_read_update :
  forall st defs varmap rid t rt, read_thread st defs varmap rid t -> same_read_plus st (update_rthread st rid rt) defs rid.
Proof.
  intros st defs varmap rid t rt Hread.
  eapply same_read_unchanged, unchanged_from_plus_update; try eassumption.
  simpl. lia.
Qed.

Ltac dedup x :=
  refine ((fun (x : _) => _) _).

Lemma only_extended_makendeeps :
  forall st bs e, only_extended st (fst (makendeeps st bs e)).
Proof.
  intros st bs e; revert st; induction bs as [|[p t] bs]; intros st.
  - apply only_extended_refl.
  - simpl. eapply only_extended_trans; [|eapply IHbs].
    eapply only_extended_trans; [|eapply only_extended_makelazy].
    intros rid rt H; assumption.
Qed.


Lemma only_changed_step_r :
  forall st rid, only_changed st (step_r st rid) rid.
Proof.
  intros st rid.
  unfold step_r; simpl in *.
  destruct (nth_error (st_rthreads st) rid) eqn:H; [|apply only_changed_refl].
  destruct (rt_code r).
  - destruct t.
    + destruct (nth_error e n); [|apply only_changed_refl].
      apply only_changed_update.
    + apply only_changed_refl.
    + destruct (rt_cont r); simpl.
      * eapply only_changed_trans; [|apply only_changed_update].
        eapply only_changed_trans; [|apply only_changed_makelazy].
        apply only_changed_refl_eq; reflexivity.
      * apply only_changed_update.
      * apply only_changed_refl.
    + eapply only_changed_trans; [|apply only_changed_update].
      apply only_changed_makelazy.
    + eapply only_changed_trans; [|apply only_changed_update].
      apply only_changed_makenlazy.
    + eapply only_changed_trans; [|apply only_changed_update].
      apply only_extended_changed. apply only_extended_makendeeps.
  - destruct v.
    + destruct is_finished.
      * simpl. apply only_changed_update.
      * apply only_changed_refl.
    + destruct p as [[x c] [uf|]]; simpl.
      * eapply only_changed_trans; [|apply only_changed_update].
        apply only_changed_extend.
      * apply only_changed_update.
    + destruct (rt_cont r); try apply only_changed_refl.
      apply only_changed_update.
    + destruct (rt_cont r); try apply only_changed_refl.
      destruct (nth_error l0 n) as [[p t]|] eqn:Hn; [|apply only_changed_refl].
      destruct Nat.eq_dec; [|apply only_changed_refl].
      apply only_changed_update.
Qed.








Definition defs_ok (defs : list term) st :=
  length defs <= st.(st_freename).

Definition nth_error_None_rw :
  forall {A : Type} (l : list A) (n : nat), length l <= n -> nth_error l n = None.
Proof.
  intros. apply nth_error_None. assumption.
Qed.

Fixpoint init_at (k : nat) (t : term) :=
  match t with
  | var n => var n
  | dvar i => var (k + i)
  | app t1 t2 => app (init_at k t1) (init_at k t2)
  | abs t => abs (init_at (S k) t)
  | constr tag l => constr tag (map (init_at k) l)
  | switch t m => switch (init_at k t) (map (fun '(p, t) => (p, init_at (p + k) t)) m)
  end.

Lemma init_at_no_dvar :
  forall t k, no_dvar (init_at k t).
Proof.
  induction t using term_ind2; simpl; intros k x; constructor.
  - apply IHt.
  - apply IHt1.
  - apply IHt2.
  - rewrite Forall_map. eapply Forall_impl; [|eassumption]. intros t H1; apply H1.
  - apply IHt.
  - rewrite Forall_map. eapply Forall_impl; [|eassumption].
    intros [p t2] H1; apply H1.
Qed.

Inductive dvar_below : nat -> term -> Prop :=
| dvar_below_var : forall k n, dvar_below k (var n)
| dvar_below_dvar : forall k k2, k2 < k -> dvar_below k (dvar k2)
| dvar_below_app : forall k t1 t2, dvar_below k t1 -> dvar_below k t2 -> dvar_below k (app t1 t2)
| dvar_below_abs : forall k t, dvar_below k t -> dvar_below k (abs t)
| dvar_below_constr : forall k tag l, Forall (dvar_below k) l -> dvar_below k (constr tag l)
| dvar_below_switch : forall k t m, dvar_below k t -> Forall (fun pt => dvar_below k (snd pt)) m -> dvar_below k (switch t m).

Lemma liftn_subst_1 :
  forall us, (forall n, liftn_subst 1 us n = lift_subst us n).
Proof.
  intros us n. unfold liftn_subst, lift_subst.
  destruct n as [|n]; simpl in *; [reflexivity|].
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma liftn_subst_add :
  forall us p q, (forall n, liftn_subst p (liftn_subst q us) n = liftn_subst (p + q) us n).
Proof.
  intros us p q n. unfold liftn_subst.
  repeat destruct le_lt_dec; try lia; try rewrite !ren_ren; simpl; f_equal.
  - apply renv_ext; intros m; rewrite renv_comp_correct, !plus_ren_correct. lia.
  - f_equal. lia.
  - rewrite plus_ren_correct. lia.
Qed.

Lemma liftn_subst_0 :
  forall us, (forall n, liftn_subst 0 us n = us n).
Proof.
  intros us n. unfold liftn_subst. destruct le_lt_dec; [|lia].
  erewrite Nat.sub_0_r, ren_term_is_subst, subst_ext, subst_id; [reflexivity|].
  intros; reflexivity.
Qed.

Lemma init_at_correct_aux :
  forall k p t, closed_at t p -> dvar_below k t -> t = subst (liftn_subst p (read_env (map dvar (seq 0 k)))) (init_at p t).
Proof.
  intros k p t H1 H2. revert p H1; induction t using term_ind2; intros p H1.
  - simpl. inversion H1; subst.
    unfold liftn_subst, read_env; simpl.
    destruct le_lt_dec; [lia|]. reflexivity.
  - simpl. inversion H2; subst.
    unfold liftn_subst, read_env; simpl.
    destruct le_lt_dec; [|lia]. rewrite nth_error_map.
    erewrite nth_error_nth' with (d := 0) by (rewrite seq_length; lia).
    rewrite seq_nth by lia. simpl. f_equal. lia.
  - simpl. f_equal.
    erewrite subst_ext; [|symmetry; apply liftn_subst_1].
    erewrite subst_ext; [|apply liftn_subst_add]. simpl.
    apply IHt; [inversion H2|inversion H1]; subst; assumption.
  - simpl. inversion H1; inversion H2; subst. f_equal; [apply IHt1|apply IHt2]; assumption.
  - simpl. f_equal. rewrite map_map.
    erewrite map_ext_Forall, map_id; [reflexivity|].
    inversion H1; inversion H2; subst.
    eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|erewrite <- Forall_and; split; [apply H8|apply Forall_forall, H5]]].
    intros t (Ht1 & Ht2 & Ht3); simpl. symmetry.
    apply Ht1; assumption.
  - simpl. inversion H1; inversion H2; subst. f_equal.
    + apply IHt; assumption.
    + rewrite map_map.
      erewrite map_ext_Forall, map_id; [reflexivity|].
      eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|erewrite <- Forall_and; split; [apply H11|apply Forall_forall with (P := (fun pt => closed_at (snd pt) (fst pt + p))); intros [? ?]; apply H6]]].
      intros [p2 t2] (Hpt1 & Hpt2 & Hpt3). simpl in *.
      f_equal. symmetry.
      erewrite subst_ext; [|apply liftn_subst_add].
      apply Hpt1; assumption.
Qed.

Lemma init_at_correct :
  forall k t, closed_at t 0 -> dvar_below k t -> t = subst (read_env (map dvar (seq 0 k))) (init_at 0 t).
Proof.
  intros k t H1 H2. etransitivity; [apply init_at_correct_aux; eassumption|].
  apply subst_ext, liftn_subst_0.
Qed.

Lemma init_at_closed :
  forall p k t, closed_at t p -> dvar_below k t -> closed_at (init_at p t) (p + k).
Proof.
  intros p k t H1 H2. revert p H1; induction t using term_ind2; intros p H1; simpl.
  - constructor. inversion H1; subst. lia.
  - constructor. inversion H2; subst. lia.
  - constructor. apply IHt; [inversion H2|inversion H1]; subst; assumption.
  - inversion H1; subst; inversion H2; subst. constructor; [apply IHt1|apply IHt2]; assumption.
  - constructor. apply Forall_forall. rewrite Forall_map.
    inversion H1; inversion H2; subst.
    eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|erewrite <- Forall_and; split; [apply H8|apply Forall_forall, H5]]].
    intros t (Ht1 & Ht2 & Ht3); simpl. apply Ht1; assumption.
  - inversion H1; inversion H2; subst. f_equal.
    constructor.
    + apply IHt; assumption.
    + intros p2 t3. remember (p2, t3) as pt3.
      replace p2 with (fst pt3) by (subst; reflexivity). replace t3 with (snd pt3) by (subst; reflexivity).
      clear p2 t3 Heqpt3. revert pt3.
      apply Forall_forall. rewrite Forall_map.
      eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|erewrite <- Forall_and; split; [apply H11|apply Forall_forall with (P := (fun pt => closed_at (snd pt) (fst pt + p))); intros [? ?]; apply H6]]].
      intros [p2 t3] (Hpt1 & Hpt2 & Hpt3); simpl in *.
      rewrite plus_assoc.
      apply Hpt1; assumption.
Qed.

Fixpoint init_all (st : state) (l : list value) (defs : list term) :=
  match defs with
  | nil => (st, l)
  | t :: defs =>
    let (st2, v) := makelazy st (init_at 0 t) l in
    init_all st2 (l ++ Neutral (length l, Kid, Some v) :: nil) defs
  end.

Definition init_term (defs : list term) (t : term) :=
  let (st, vs) := init_all {| st_rthreads := nil ; st_freename := length defs |} nil defs in
  makelazy st (init_at 0 t) vs.

Lemma nth_error_select :
  forall (A : Type) (l1 l2 : list A) (x : A), nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  intros; induction l1; simpl in *; [reflexivity|assumption].
Qed.

Lemma init_all_correct :
  forall st st2 defs1 defs2 l l2,
    Forall2 (fun t i => closed_at t 0 /\ dvar_below i t) defs2 (seq (length defs1) (length defs2)) ->
    Forall2 (read_val st (defs1 ++ defs2) nil) l (map dvar (seq 0 (length defs1))) ->
    length defs1 + length defs2 <= st_freename st ->
    init_all st l defs2 = (st2, l2) ->
    Forall2 (read_val st2 (defs1 ++ defs2) nil) l2 (map dvar (seq 0 (length defs1 + length defs2))).
Proof.
  intros st st2 defs1 defs2. revert st st2 defs1; induction defs2 as [|t defs2]; intros st st2 defs1 l l2 Hclosed H1 Hfree H2.
  - simpl in *. injection H2 as H2; subst.
    replace (length defs1 + 0) with (length defs1) by (apply plus_n_O).
    assumption.
  - simpl in *. eapply IHdefs2 in H2.
    + erewrite <- app_assoc with (m := t :: nil), app_length, plus_assoc_reverse in H2.
      apply H2.
    + inversion Hclosed; subst. rewrite app_length, plus_comm; simpl. assumption.
    + rewrite app_length, seq_app, map_app.
      apply Forall2_app.
      * eapply Forall2_impl; [|eassumption].
        intros v2 t2 H; simpl. eapply read_val_same; [|rewrite <- app_assoc; eassumption|]; [simpl; lia|].
        intros a Ha. eapply read_val_points in Ha; [|eassumption]. destruct Ha as (? & ? & ?).
        eapply unchanged_from_makelazy; eassumption.
      * constructor; [|constructor]. simpl.
        assert (Hlen : length l = length defs1) by (apply Forall2_length in H1; rewrite map_length, seq_length in H1; apply H1).
        rewrite <- Hlen.
        eapply read_val_neutral with (h := h_hole); [constructor| |simpl; lia|rewrite <- app_assoc, Hlen; simpl; rewrite nth_error_select; congruence].
        rewrite Hlen.
        rewrite nth_error_app1 by (rewrite app_length; simpl; lia).
        rewrite nth_error_app2 by lia.
        rewrite Nat.sub_diag. simpl.
        constructor.
        split; [|split; [apply star_refl|inversion Hclosed; subst; tauto]].
        constructor.
        refine (eq_rect _ (read_thread _ _ _ _) _ t _);
          [eapply read_thread_term with (h := h_hole)|symmetry; apply init_at_correct]; simpl.
        -- apply nth_error_extend.
        -- inversion Hclosed; subst. rewrite <- Hlen in H4. apply init_at_closed with (p := 0); apply H4.
        -- eapply Forall2_impl; [|eassumption].
           intros v2 t2 H; simpl. eapply read_val_same; [|rewrite <- app_assoc; eassumption|]; [simpl; lia|].
           intros a Ha. eapply read_val_points in Ha; [|eassumption]. destruct Ha as (? & ? & ?).
           eapply unchanged_from_makelazy; eassumption.
        -- constructor.
        -- apply init_at_no_dvar.
        -- inversion Hclosed; subst. tauto.
        -- inversion Hclosed; subst. tauto.
    + simpl. rewrite app_length; simpl. lia.
Qed.

Definition defs_wf defs := Forall2 (fun t i => closed_at t 0 /\ dvar_below i t) defs (seq 0 (length defs)).

Lemma init_term_correct :
  forall defs t st v,
    defs_wf defs ->
    closed_at t 0 ->
    dvar_below (length defs) t ->
    init_term defs t = (st, v) ->
    read_val st defs nil v t.
Proof.
  intros defs t st v H1 H2 H3 H4.
  unfold init_term in H4; simpl in *.
  destruct init_all as [st2 vs] eqn:Hinit; simpl in *.
  apply init_all_correct with (defs1 := nil) in Hinit.
  - unfold makelazy in H4; simpl in *; injection H4 as H4; subst.
    constructor.
    refine (eq_rect _ (read_thread _ _ _ _) _ t _);
      [eapply read_thread_term with (h := h_hole)|symmetry; apply init_at_correct]; simpl.
    + apply nth_error_extend.
    + apply Forall2_length in Hinit. rewrite Hinit, map_length, seq_length.
      apply init_at_closed with (p := 0); assumption.
    + eapply Forall2_impl; [|eassumption].
      intros v2 t2 H; simpl. eapply read_val_same; [|eassumption|]; [simpl; lia|].
      intros a Ha. eapply read_val_points in Ha; [|eassumption]. destruct Ha as (? & ? & ?).
      eapply unchanged_from_makelazy; eassumption.
    + constructor.
    + apply init_at_no_dvar.
    + assumption.
    + assumption.
  - simpl. assumption.
  - simpl. constructor.
  - simpl. lia.
Qed.

Lemma compose_hctx_hole_r :
  forall h, compose_hctx h h_hole = h.
Proof.
  induction h; simpl in *; f_equal; (reflexivity || assumption).
Qed.

Lemma compose_hctx_assoc :
  forall h1 h2 h3, compose_hctx (compose_hctx h1 h2) h3 = compose_hctx h1 (compose_hctx h2 h3).
Proof.
  intros h1 h2 h3; induction h1; simpl in *; f_equal; assumption.
Qed.

Lemma compose_cont_ctx :
  forall st defs varmap c1 c2 h1 h2,
    read_cont st defs varmap c1 h1 -> read_cont st defs varmap c2 h2 -> read_cont st defs varmap (compose_cont c1 c2) (compose_hctx h2 h1).
Proof.
  intros st defs varmap c1 c2 h1 h2 Hread1 Hread2. induction Hread1.
  - simpl. rewrite compose_hctx_hole_r. assumption.
  - simpl. rewrite <- compose_hctx_assoc. constructor; tauto.
  - simpl. rewrite <- compose_hctx_assoc. econstructor; try eassumption. tauto.
Qed.

Lemma beta_fill :
  forall t1 t2 h, beta t1 t2 -> beta (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros t1 t2 h H; induction h; simpl in *.
  - assumption.
  - constructor. assumption.
  - constructor. assumption.
Qed.

Lemma convertible_fill :
  forall t1 t2 h, convertible beta t1 t2 -> convertible beta (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros t1 t2 h H. eapply star_map_impl; [|eassumption].
  intros t3 t4 [Ht34 | Ht34]; [left | right]; apply beta_fill; assumption.
Qed.

Lemma read_env_app :
  forall e1 e2 n, read_env (e1 ++ e2) n = subst (read_env e1) (liftn_subst (length e1) (read_env e2) n).
Proof.
  intros e1 e2 n. unfold read_env, liftn_subst.
  destruct le_lt_dec.
  - rewrite nth_error_app2 by assumption.
    destruct nth_error eqn:Hn.
    + rewrite ren_term_is_subst, subst_subst.
      erewrite subst_ext; [symmetry; apply subst_id|].
      intros m. unfold comp; simpl. rewrite plus_ren_correct.
      rewrite nth_error_None_rw by lia. f_equal. lia.
    + simpl. rewrite plus_ren_correct.
      rewrite nth_error_None_rw by lia. f_equal. rewrite app_length; lia.
  - rewrite nth_error_app1 by assumption. simpl.
    destruct nth_error eqn:Hnth; [reflexivity|].
    apply nth_error_None in Hnth. lia.
Qed.

Lemma read_val_only_extended :
  forall st st2 defs varmap v t, st_freename st <= st_freename st2 -> only_extended st st2 -> read_val st defs varmap v t -> read_val st2 defs varmap v t.
Proof.
  intros st st2 defs varmap v t Hst12 H1 H2.
  eapply read_val_same; [eassumption|eassumption|].
  intros a Ha. eapply read_val_points in Ha; [|eassumption].
  destruct Ha as (? & ? & ?); eapply unchanged_from_only_extended; eassumption.
Qed.

Lemma read_thread_only_extended :
  forall st st2 defs varmap rid t, st_freename st <= st_freename st2 -> only_extended st st2 -> read_thread st defs varmap rid t -> read_thread st2 defs varmap rid t.
Proof.
  intros st st2 defs varmap rid t Hst12 H1 H2.
  eapply read_thread_same; [eassumption|eassumption|].
  eapply unchanged_from_only_extended; eassumption.
Qed.


Lemma read_val_makelazy :
  forall st defs varmap t e el,
    no_dvar t -> closed_at t (length e) ->
    Forall2 (read_val st defs varmap) e el ->
    read_val (fst (makelazy st t e)) defs varmap (snd (makelazy st t e)) (subst (read_env el) t).
Proof.
  intros st defs varmap t e el Hdv Hclosed H.
  simpl. constructor.
  eapply read_thread_term with (h := h_hole).
  - apply nth_error_extend.
  - assumption.
  - eapply Forall2_impl; [|eassumption].
    intros t2 v2 H2; simpl.
    eapply read_val_only_extended; [| |eassumption]; [simpl; lia|].
    apply only_extended_extend.
  - constructor.
  - assumption.
Qed.

Lemma makenlazy_freename :
  forall st ts e, st_freename st <= st_freename (fst (makenlazy st ts e)).
Proof.
  intros st ts; revert st; induction ts; intros st e; simpl.
  - lia.
  - etransitivity; [|apply IHts]. simpl. lia.
Qed.


Lemma read_val_makenlazy :
  forall st defs varmap ts e el,
    Forall no_dvar ts -> Forall (fun t => closed_at t (length e)) ts ->
    Forall2 (read_val st defs varmap) e el ->
    Forall2 (read_val (fst (makenlazy st ts e)) defs varmap) (snd (makenlazy st ts e)) (map (subst (read_env el)) ts).
Proof.
  intros st defs varmap ts e el.
  revert st; induction ts as [|t ts].
  - intros st Hdv Hclosed H; simpl in *; constructor.
  - intros st Hdv Hclosed H; simpl in *. inversion Hdv; subst. inversion Hclosed; subst. constructor.
    + eapply read_val_only_extended; [simpl; apply makenlazy_freename|apply only_extended_makenlazy|].
      apply read_val_makelazy; assumption.
    + apply IHts; [assumption|assumption|]. eapply Forall2_impl; [|eassumption].
      intros v2 t2 H6; simpl.
      eapply read_val_only_extended; [| |eassumption]; [simpl; lia|].
      apply only_extended_makelazy.
Qed.


Lemma read_val_makenlazy_new :
  forall st defs varmap ts e el,
    Forall no_dvar ts -> Forall (fun t => closed_at t (length e)) ts ->
    Forall2 (read_val st defs varmap) e el ->
    forall rid, nth_error (st_rthreads st) rid = None -> nth_error (st_rthreads (fst (makenlazy st ts e))) rid <> None -> exists t2 varmap2, read_thread (fst (makenlazy st ts e)) defs varmap2 rid t2.
Proof.
  intros st defs varmap ts e el.
  revert st; induction ts as [|t ts].
  - intros st Hdv Hclosed H; simpl in *. intros; tauto.
  - intros st Hdv Hclosed H; simpl in *. inversion Hdv; subst. inversion Hclosed; subst.
    intros rid Hrid1 Hrid2.
    destruct (nth_error (st_rthreads (extend_rthread st {| rt_code := Term t e; rt_cont := Kid |})) rid) eqn:Hrid3.
    + simpl in Hrid3. rewrite nth_error_app2 in Hrid3; [|rewrite nth_error_None in Hrid1; assumption].
      remember (rid - length (st_rthreads st)) as n.
      destruct n; [|destruct n; simpl in *; congruence]. simpl in Hrid3. injection Hrid3 as Hrid3; subst.
      assert (rid = length (st_rthreads st)) by (rewrite nth_error_None in Hrid1; lia). subst.
      eexists. eexists. eapply read_thread_only_extended; [simpl; apply makenlazy_freename|apply only_extended_makenlazy|].
      eapply read_thread_term.
      * apply nth_error_extend.
      * assumption.
      * eapply Forall2_impl; [|eassumption]. intros; eapply read_val_only_extended; [| |eassumption]; [simpl; lia|].
        apply only_extended_makelazy.
      * constructor.
      * assumption.
    + apply IHts; try eassumption.
      eapply Forall2_impl; [|eassumption].
      intros; simpl.
      eapply read_val_only_extended; [| |eassumption]; [simpl; lia|].
      apply only_extended_makelazy.
Qed.


Lemma makenlazy_points :
  forall st ts e v a, In v (snd (makenlazy st ts e)) -> val_points_to v a -> length (st_rthreads st) <= a.
Proof.
  intros st ts; revert st; induction ts as [|t ts]; intros st e v a H1 H2; simpl in *.
  - tauto.
  - destruct H1; subst.
    + inversion H2. lia.
    + eapply IHts in H; [|eassumption]. simpl in H. rewrite app_length in H. lia.
Qed.

Lemma only_extended_points :
  forall st st2 a1 a2, only_extended st st2 -> points st a1 a2 -> points st2 a1 a2.
Proof.
  intros st st2 a1 a2 H1 H2. unfold points, points_to in *.
  destruct nth_error eqn:H3; [|tauto].
  apply H1 in H3. rewrite H3; assumption.
Qed.

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (R : Prop) (L : list A),
    (forall x, P x -> Q x -> R) -> Forall P L -> Exists Q L -> R.
Proof.
  intros A P Q R L H1 H2; induction H2; intros H3; inversion H3; subst.
  - eapply H1; eassumption.
  - apply IHForall; assumption.
Qed.

Lemma only_changed_read_thread_ind :
  forall st st2 defs varmap varmap2 rid rid2 t t2,
    st_freename st <= st_freename st2 ->
    only_changed st st2 rid ->
    read_thread st defs varmap rid t ->
    read_thread st defs varmap2 rid2 t2 ->
    rid <> rid2 ->
    (forall a, points st rid2 a -> plus (points st) rid a) ->
    read_thread st2 defs varmap2 rid2 t2.
Proof.
  intros st st2 defs varmap varmap2 rid rid2 t t2 Hst12 H1 H2 H3 H4 H5.
  inversion H3; subst.
  - eapply read_thread_val.
    + eapply H1; eassumption.
    + eapply read_val_same; [eassumption|eassumption|].
      intros a Ha. eapply unchanged_from_plus_only_changed in H1; [|eassumption].
      eapply every_reachable_star_plus; [|eassumption].
      apply H5. unfold points, points_to. rewrite H. left. constructor. assumption.
    + eapply read_cont_same; [eassumption|eassumption|].
      intros a Ha. eapply unchanged_from_plus_only_changed in H1; [|eassumption].
      eapply every_reachable_star_plus; [|eassumption].
      apply H5. unfold points, points_to. rewrite H. right. assumption.
  - eapply read_thread_term.
    + eapply H1; eassumption.
    + assumption.
    + eapply Forall2_impl_In_left_transparent; [|eassumption].
      intros v t2 Hv Hread; eapply read_val_same; [eassumption|eassumption|].
      intros a Ha. eapply unchanged_from_plus_only_changed in H1; [|eassumption].
      eapply every_reachable_star_plus; [|eassumption].
      apply H5. unfold points, points_to. rewrite H. left. constructor.
      apply Exists_exists; eexists; split; eassumption.
    + eapply read_cont_same; [eassumption|eassumption|].
      intros a Ha. eapply unchanged_from_plus_only_changed in H1; [|eassumption].
      eapply every_reachable_star_plus; [|eassumption].
      apply H5. unfold points, points_to. rewrite H. right. assumption.
    + assumption.
Qed.

Lemma only_changed_read_thread_ind_1 :
  forall st st2 defs varmap varmap2 rid rid2 t t2,
    st_freename st <= st_freename st2 ->
    only_changed st st2 rid ->
    read_thread st defs varmap rid t ->
    read_thread st defs varmap2 rid2 t2 ->
    rid <> rid2 ->
    (forall a, points st rid2 a -> points st rid a) ->
    read_thread st2 defs varmap2 rid2 t2.
Proof.
  intros; eapply only_changed_read_thread_ind; try eassumption.
  intros a Ha; apply plus_1, H4; assumption.
Qed.



Lemma read_val_makenlazy_changed :
  forall st st2 defs varmap ts e el rid t2,
    st_freename st <= st_freename st2 ->
    Forall no_dvar ts -> Forall (fun t => closed_at t (length e)) ts ->
    read_thread st defs varmap rid t2 ->
    Forall (fun v => forall a, val_points_to v a -> points st rid a) e ->
    only_changed (fst (makenlazy st ts e)) st2 rid ->
    Forall2 (read_val st defs varmap) e el ->
    Forall2 (read_val st2 defs varmap) (snd (makenlazy st ts e)) (map (subst (read_env el)) ts).
Proof.
  intros st st2 defs varmap ts e el rid t2 Hst12 Hdv Hclosed Hread Hpoint Hchange H.
  revert st st2 Hst12 Hread Hpoint Hchange H; induction ts as [|t ts]; intros st st2 Hst12 Hread Hpoint Hchange H; simpl in *; constructor.
  - constructor.
    eapply only_changed_read_thread_ind_1; cycle 1.
    + eapply only_changed_trans; [|eassumption].
      apply only_extended_changed, only_extended_makenlazy.
    + eapply read_thread_only_extended; [|apply only_extended_extend|eassumption]; simpl; lia.
    + eapply read_thread_term with (h := h_hole); [apply nth_error_extend|inversion Hclosed; subst; assumption| |constructor|inversion Hdv; subst; assumption].
      eapply Forall2_impl; [|eassumption].
      intros; eapply read_val_only_extended; [| |eassumption]; [simpl; lia|]. apply only_extended_extend.
    + inversion Hread; subst; apply nth_error_Some3 in H0; lia.
    + intros a Ha. eapply only_extended_points; [apply only_extended_makelazy|].
      unfold points, points_to in Ha. simpl in Ha. rewrite nth_error_extend in Ha; simpl in Ha.
      destruct Ha as [Ha | Ha]; inversion Ha; subst.
      eapply Forall_Exists; [|eassumption|eassumption].
      intros v H4 H5; apply H4, H5.
    + simpl; assumption.
  - apply IHts; cycle 3.
    + eapply read_thread_only_extended; [| |eassumption]; [simpl; lia|]. apply only_extended_extend.
    + eapply Forall_impl; [|eassumption].
      intros v Hv a Ha. apply Hv in Ha. eapply only_extended_points; [|eassumption]. apply only_extended_extend.
    + assumption.
    + eapply Forall2_impl; [|eassumption].
      intros; eapply read_val_only_extended; [| |eassumption]; [simpl; lia|]. apply only_extended_extend.
    + inversion Hdv; subst; assumption.
    + inversion Hclosed; subst; assumption.
    + simpl. assumption.
Qed.

Lemma Forall2_select121 :
  forall (A B : Type) (P : A -> B -> A -> Prop) (L1 : list A) (L2 : list B), Forall2 (fun x y => P x y x) L1 L2 -> Forall3 P L1 L2 L1.
Proof.
  intros A B P L1 L2 H; induction H; constructor; assumption.
Qed.

Lemma Forall2_select12combine :
  forall (A B : Type) (P : A -> B -> A * B -> Prop) (L1 : list A) (L2 : list B), Forall2 (fun x y => P x y (x, y)) L1 L2 -> Forall3 P L1 L2 (combine L1 L2).
Proof.
  intros A B P L1 L2 H; induction H; constructor; assumption.
Qed.

Lemma Forall3_map3 :
  forall (A B C D : Type) (P : A -> B -> D -> Prop) (f : C -> D) (L1 : list A) (L2 : list B) (L3 : list C), Forall3 P L1 L2 (map f L3) <-> Forall3 (fun x y z => P x y (f z)) L1 L2 L3.
Proof.
  intros A B C D P f L1 L2 L3; split; intros H.
  - remember (map f L3) as L4. revert L3 HeqL4.
    induction H; intros; destruct L3; subst; simpl in *; try congruence; constructor.
    + injection HeqL4 as HeqL4; subst. assumption.
    + injection HeqL4 as HeqL4; subst. apply IHForall3. reflexivity.
  - induction H; constructor; assumption.
Qed.

Lemma makendeeps_freename :
  forall st bs e, st_freename st <= st_freename (fst (makendeeps st bs e)).
Proof.
  intros st bs e; revert st e; induction bs as [|[? ?] ?]; intros st e; simpl.
  - lia.
  - etransitivity; [|apply IHbs]. simpl. lia.
Qed.

Lemma seq_shiftn :
  forall n len a, map (fun k => k + n) (seq a len) = seq (a + n) len.
Proof.
  intros n; induction len; intros a; simpl in *; f_equal.
  apply IHlen.
Qed.

Lemma seq_is_shiftn :
  forall a len, seq a len = map (fun k => k + a) (seq 0 len).
Proof.
  intros a len; rewrite seq_shiftn; reflexivity.
Qed.

Lemma index_notin_None :
  forall A eq_dec (l : list A) (x : A), x \notin l -> index eq_dec l x = None.
Proof.
  intros A eq_dec l x H; induction l.
  - reflexivity.
  - simpl in *. destruct eq_dec; [intuition congruence|].
    rewrite IHl; tauto.
Qed.

Lemma index_app :
  forall A eq_dec (l1 l2 : list A) x,
    index eq_dec (l1 ++ l2) x =
    match index eq_dec l1 x with
    | Some n => Some n
    | None => option_map (fun n => length l1 + n) (index eq_dec l2 x)
    end.
Proof.
  intros A eq_dec l1 l2 x; induction l1; simpl in *.
  - destruct index; reflexivity.
  - destruct eq_dec; [reflexivity|].
    rewrite IHl1. destruct (index eq_dec l1 x); [reflexivity|].
    destruct (index eq_dec l2 x); reflexivity.
Qed.

Lemma index_seq :
  forall eq_dec a len x,
    a <= x < a + len ->
    index eq_dec (seq a len) x = Some (x - a).
Proof.
  intros eq_dec a len x Hx. revert a Hx; induction len; intros a Hx.
  - lia.
  - simpl index. destruct eq_dec.
    + subst. f_equal. lia.
    + rewrite IHlen; [|lia]. f_equal. lia.
Qed.

Fixpoint subst_hctx us h :=
  match h with
  | h_hole => h_hole
  | h_app h t => h_app (subst_hctx us h) (subst us t)
  | h_switch h m => h_switch (subst_hctx us h) (map (fun pt => (fst pt, subst (liftn_subst (fst pt) us) (snd pt))) m)
  end.

Lemma subst_hctx_fill :
  forall us h t, subst us (fill_hctx h t) = fill_hctx (subst_hctx us h) (subst us t).
Proof.
  intros us h t; induction h.
  - reflexivity.
  - simpl. f_equal. assumption.
  - simpl. f_equal. assumption.
Qed.

Lemma subst_liftn_closed_at :
  forall us k t, closed_at t k -> subst (liftn_subst k us) t = t.
Proof.
  intros us k t Ht. erewrite subst_closed_at_ext, subst_id; [reflexivity|eassumption|].
  intros n Hn. unfold liftn_subst. destruct le_lt_dec; [lia|reflexivity].
Qed.

Definition option_default {A : Type} (o : option A) (d : A) :=
  match o with Some x => x | None => d end.

Definition remap varmap1 varmap2 n :=
  match nth_error varmap1 n with
  | Some x => option_default (index Nat.eq_dec varmap2 x) 0
  | None => n
  end.

Definition remap_subst varmap1 varmap2 n := var (remap varmap1 varmap2 n).
Definition is_remap_ok freename varmap1 varmap2 :=
  Forall (fun x => In x varmap2) varmap1 /\ Forall (fun x => freename <= x \/ In x varmap1) varmap2.

Lemma is_remap_ok_cons :
  forall freename varmap1 varmap2 x, is_remap_ok freename varmap1 varmap2 -> is_remap_ok freename (x :: varmap1) (x :: varmap2).
Proof.
  intros freename varmap1 varmap2 x [H1 H2]. split; constructor.
  - simpl. tauto.
  - eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
  - simpl. tauto.
  - eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
Qed.

Lemma is_remap_ok_app :
  forall freename varmap1 varmap2 varmap3, is_remap_ok freename varmap2 varmap3 -> is_remap_ok freename (varmap1 ++ varmap2) (varmap1 ++ varmap3).
Proof.
  intros freename varmap1; induction varmap1; intros varmap2 varmap3 H; [assumption|].
  simpl; apply is_remap_ok_cons. apply IHvarmap1. assumption.
Qed.

Lemma index_in_Some :
  forall A eq_dec (l : list A) (x : A), x \in l -> exists k, index eq_dec l x = Some k.
Proof.
  intros A eq_dec l x H; induction l.
  - simpl in *; tauto.
  - simpl. destruct eq_dec; [exists 0; reflexivity|].
    destruct IHl as (k & Hk).
    + destruct H; [symmetry in H|]; tauto.
    + exists (S k). rewrite Hk; reflexivity.
Qed.

Lemma index_in_not_None :
  forall A eq_dec (l : list A) (x : A), x \in l -> index eq_dec l x <> None.
Proof.
  intros A eq_dec l x H. destruct (index_in_Some A eq_dec l x H) as (k & Hk). congruence.
Qed.


Lemma remap_cons_S :
  forall x freename varmap1 varmap2 n, x \notin varmap1 -> is_remap_ok freename varmap1 varmap2 -> remap (x :: varmap1) (x :: varmap2) (S n) = S (remap varmap1 varmap2 n).
Proof.
  intros x freename varmap1 varmap2 n Hx Hok. unfold remap.
  simpl. destruct nth_error eqn:Hn; [|reflexivity].
  destruct Nat.eq_dec.
  - subst. apply nth_error_In in Hn. tauto.
  - destruct index eqn:Hidx.
    + reflexivity.
    + apply index_in_not_None in Hidx; [tauto|].
      destruct Hok as [Hok1 Hok2]. eapply Forall_forall in Hok1; [eassumption|].
      apply nth_error_In in Hn; eassumption.
Qed.


Lemma remap_cons_subst_ren :
  forall freename varmap1 varmap2 x t,
    x \notin varmap1 -> is_remap_ok freename varmap1 varmap2 ->
    subst (remap_subst (x :: varmap1) (x :: varmap2)) (ren_term (plus_ren 1) t) = ren_term (plus_ren 1) (subst (remap_subst varmap1 varmap2) t).
Proof.
  intros freename varmap1 varmap2 x t Hx Hok.
  rewrite !ren_term_is_subst, !subst_subst. apply subst_ext. intros n; unfold comp; simpl.
  unfold remap_subst, ren. f_equal. erewrite plus_ren_correct, remap_cons_S; try eassumption.
  simpl. f_equal. f_equal. lia.
Qed.


Lemma nth_error_index :
  forall A eq_dec (x : A) l n, index eq_dec l x = Some n -> nth_error l n = Some x.
Proof.
  intros A eq_dec x. induction l; intros [|n]; simpl in *; try congruence; destruct eq_dec; simpl in *; try congruence.
  - destruct index; congruence.
  - destruct index; [|congruence]. intros; apply IHl; congruence.
Qed.


Lemma index_nth_error :
  forall (A : Type) eq_dec (vars : list A) k x, NoDup vars -> nth_error vars k = Some x -> index eq_dec vars x = Some k.
Proof.
  intros A eq_dec vars k x H1 H2. revert k H2; induction vars as [|y vars]; intros k H2; simpl in *.
  - destruct k; simpl in *; congruence.
  - destruct k; simpl in *.
    + injection H2 as H2; subst. destruct eq_dec; [|tauto]. reflexivity.
    + destruct eq_dec; [subst|].
      * inversion H1; subst. exfalso. apply H3. eapply nth_error_In; eassumption.
      * erewrite IHvars; [reflexivity| |eassumption].
        inversion H1; subst; assumption.
Qed.

Lemma remap_app_1 :
  forall varmap1 varmap2 varmap3 n, n < length varmap1 -> NoDup varmap1 -> remap (varmap1 ++ varmap2) (varmap1 ++ varmap3) n = n.
Proof.
  intros varmap1 varmap2 varmap3 n Hn Hvarmap1.
  unfold remap. rewrite nth_error_app1 by assumption.
  destruct nth_error as [x|] eqn:Hx; [|reflexivity].
  rewrite index_app. erewrite index_nth_error by eassumption.
  reflexivity.
Qed.

Lemma remap_app_2 :
  forall freename varmap1 varmap2 varmap3 n, length varmap1 <= n -> Forall (fun x => x \notin varmap2) varmap1 -> is_remap_ok freename varmap2 varmap3 -> remap (varmap1 ++ varmap2) (varmap1 ++ varmap3) n = length varmap1 + remap varmap2 varmap3 (n - length varmap1).
Proof.
  intros freename varmap1 varmap2 varmap3 n Hn Hvarmap1 Hok. unfold remap.
  rewrite nth_error_app2 by assumption.
  destruct nth_error as [x|] eqn:Hx; [|lia].
  rewrite index_app. rewrite index_notin_None.
  - destruct index eqn:Hx2; simpl; [reflexivity|].
    apply index_in_not_None in Hx2; [tauto|].
    destruct Hok as [Hok1 Hok2]. eapply Forall_forall in Hok1; [eassumption|].
    eapply nth_error_In in Hx; eassumption.
  - intros Hx2. eapply Forall_forall in Hvarmap1; [|eassumption].
    eapply nth_error_In in Hx; tauto.
Qed.

Lemma remap_app_subst_ren :
  forall freename varmap1 varmap2 varmap3 t,
    Forall (fun x => x \notin varmap2) varmap1 -> is_remap_ok freename varmap2 varmap3 ->
    subst (remap_subst (varmap1 ++ varmap2) (varmap1 ++ varmap3)) (ren_term (plus_ren (length varmap1)) t) = ren_term (plus_ren (length varmap1)) (subst (remap_subst varmap2 varmap3) t).
Proof.
  intros freename varmap1 varmap2 varmap3 t Hvarmap1 Hok.
  rewrite !ren_term_is_subst, !subst_subst. apply subst_ext. intros n; unfold comp; simpl.
  unfold remap_subst, ren. f_equal. erewrite !plus_ren_correct, remap_app_2; try eassumption; [|lia].
  f_equal. f_equal. lia.
Qed.


Lemma beta_convertible_subst :
  forall us t1 t2, convertible beta t1 t2 -> convertible beta (subst us t1) (subst us t2).
Proof.
  intros us t1 t2 H. eapply star_map_impl; [|eassumption].
  intros t3 t4 [H1 | H1]; constructor; apply beta_subst1; assumption.
Qed.

Lemma betaiota_convertible_subst :
  forall defs us t1 t2, convertible (betaiota defs) t1 t2 -> convertible (betaiota defs) (subst us t1) (subst us t2).
Proof.
  intros defs us t1 t2 H. eapply star_map_impl; [|eassumption].
  intros t3 t4 [H1 | H1]; destruct H1; constructor; constructor; ((apply beta_subst1; assumption) || (apply iota_subst_left; assumption)).
Qed.

Lemma subst_closed_at_id :
  forall us t k, closed_at t k -> (forall n, n < k -> us n = var n) -> subst us t = t.
Proof.
  intros us t k H1 H2. erewrite subst_closed_at_ext; [apply subst_id|eassumption|eassumption].
Qed.

Lemma subst_hctx_compose :
  forall us h1 h2, subst_hctx us (compose_hctx h1 h2) = compose_hctx (subst_hctx us h1) (subst_hctx us h2).
Proof.
  intros us h1 h2; induction h1; simpl in *; f_equal; assumption.
Qed.

Lemma Forall3_combine23_3 :
  forall (A B C : Type) (P : A -> B -> B * C -> Prop) l1 l2 l3, Forall3 (fun x y z => P x y (y, z)) l1 l2 l3 -> Forall3 P l1 l2 (combine l2 l3).
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; assumption.
Qed.

Lemma Forall3_select1 :
  forall (A B C : Type) (P : A -> Prop) l1 (l2 : list B) (l3 : list C), Forall3 (fun x y z => P x) l1 l2 l3 -> Forall P l1.
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; assumption.
Qed.

Lemma liftn_subst_comp :
  forall p us1 us2 n, comp (subst (liftn_subst p us1)) (liftn_subst p us2) n = liftn_subst p (comp (subst us1) us2) n.
Proof.
  intros p us1 us2 n. unfold comp, liftn_subst.
  destruct le_lt_dec.
  - rewrite ren_subst, subst_ren. apply subst_ext.
    intros m. unfold comp; simpl. rewrite plus_ren_correct. destruct le_lt_dec; [|lia].
    f_equal. f_equal. lia.
  - simpl. destruct le_lt_dec; [lia|]. reflexivity.
Qed.

Lemma read_extend_varmap_aux :
  forall st defs,
    (forall varmap a t, read_thread st defs varmap a t -> forall varmap2, is_remap_ok (st_freename st) varmap varmap2 -> read_thread st defs varmap2 a (subst (remap_subst varmap varmap2) t)) /\
    (forall varmap v t, read_val st defs varmap v t -> forall varmap2, is_remap_ok (st_freename st) varmap varmap2 -> read_val st defs varmap2 v (subst (remap_subst varmap varmap2) t)) /\
    (forall varmap c h, read_cont st defs varmap c h -> forall varmap2, is_remap_ok (st_freename st) varmap varmap2 -> read_cont st defs varmap2 c (subst_hctx (remap_subst varmap varmap2) h)).
Proof.
  intros st defs. read_ind; intros varmap2 Hremap.
  - rewrite subst_hctx_fill.
    eapply read_thread_val; eauto.
  - rewrite subst_hctx_fill.
    rewrite subst_read_env, subst_liftn_closed_at; [|apply Forall2_length in He; rewrite <- He; assumption].
    eapply read_thread_term; try solve [eauto].
    rewrite Forall2_map_right. eapply Forall2_impl; [|eassumption].
    intros; eauto.
  - constructor. eauto.
  - rewrite subst_read_env, subst_liftn_closed_at; [|constructor; apply Forall2_length in He; rewrite <- He; assumption].
    eapply read_val_clos.
    + rewrite Forall2_map_right. eapply Forall2_impl; [|eassumption].
      intros; simpl in *; eauto.
    + apply IHdeep. apply is_remap_ok_cons. assumption.
    + eapply star_compose; [|eapply beta_convertible_subst; eassumption].
      apply star_same. symmetry.
      rewrite subst_subst. eapply subst_closed_at_ext; [eassumption|].
      intros [|n] Hn; unfold lift_subst; simpl; unfold comp; simpl.
      * unfold remap_subst. f_equal. unfold remap. simpl. destruct Nat.eq_dec; [reflexivity|tauto].
      * unfold read_env; rewrite nth_error_map. destruct nth_error eqn:Hnth.
        -- eapply remap_cons_subst_ren; eassumption.
        -- simpl. apply nth_error_None in Hnth. apply Forall2_length in He; rewrite He in Hn. lia.
    + assumption.
    + assumption.
    + destruct Hremap as [Hremap1 Hremap2].
      intros Hx. eapply Forall_forall in Hremap2; [|eassumption]. destruct Hremap2; [lia|tauto].
    + assumption.
  - simpl. eapply read_val_block.
    rewrite Forall2_map_right. eapply Forall2_impl; [|apply IHe].
    intros v1 t1 IH. apply IH. assumption.
  - simpl. rewrite subst_hctx_fill.
    replace (subst (remap_subst varmap varmap2) (match index Nat.eq_dec varmap x with Some n => var n | None => dvar x end)) with (match index Nat.eq_dec varmap2 x with Some n => var n | None => dvar x end).
    + eapply read_val_neutral with (tuf := match tuf with None => None | Some tuf => Some (subst (remap_subst varmap varmap2) tuf) end).
      * apply IHc. assumption.
      * inversion Huf; subst; inversion IHuf; subst; [constructor|].
        constructor. split; [apply H4; assumption|].
        split; [|tauto].
        eapply star_compose; [|eapply beta_convertible_subst; apply H2].
        rewrite subst_hctx_fill. apply convertible_fill, star_same.
        symmetry; eapply subst_closed_at_id; [apply H2|].
        intros n Hn; lia.
      * assumption.
      * intros Hndef. apply Hin in Hndef. destruct Hremap as [Hremap1 Hremap2].
        eapply Forall_forall in Hremap1; eassumption.
    + destruct (index Nat.eq_dec varmap x) as [n|] eqn:Hx; simpl.
      * unfold remap_subst, remap. apply nth_error_index in Hx. rewrite Hx.
        destruct index eqn:Hx2; [reflexivity|].
        eapply index_in_not_None in Hx2; [tauto|].
        destruct Hremap as [Hremap1 Hremap2]. eapply Forall_forall in Hremap1; [eassumption|].
        eapply nth_error_In in Hx; eassumption.
      * rewrite index_notin_None; [reflexivity|].
        intros Hx2. destruct Hremap as [Hremap1 Hremap2].
        eapply Forall_forall in Hremap2; [|eassumption].
        destruct Hremap2 as [Hremap2 | Hremap2]; [lia|].
        eapply index_in_not_None in Hx; tauto.
  - apply read_cont_kid.
  - rewrite subst_hctx_compose.
    eapply read_cont_kapp.
    + apply IHv; assumption.
    + apply IHc; assumption.
  - rewrite subst_hctx_compose. simpl.
    erewrite map_map, map_ext_in; [eapply read_cont_kswitch|].
    + erewrite Forall2_map_right. eapply Forall2_impl; [|apply IHe].
      intros v1 t1 IH; apply IH. assumption.
    + apply IHc. assumption.
    + erewrite Forall3_map3 with (f := fun '(vdeeps, tdeep) => _). apply Forall3_combine23_3.
      eapply Forall3_impl; [|eapply Forall3_and; [apply Hdeeps|apply IHdeep]].
      intros pt vdeeps tdeep [Hdeep IH].
      repeat (split; try tauto).
      * apply (IH (fst vdeeps ++ varmap2)). apply is_remap_ok_app. assumption.
      * eapply star_compose; [|eapply beta_convertible_subst; apply Hdeep].
        apply star_same. symmetry. rewrite subst_subst.
        eapply subst_closed_at_ext; [apply Hdeep|].
        intros n Hn; unfold comp, liftn_subst. destruct le_lt_dec.
        -- unfold read_env. rewrite nth_error_map. destruct nth_error eqn:Hnth.
           ++ rewrite <- !(proj1 Hdeep). eapply remap_app_subst_ren; [|eassumption].
             eapply Forall_impl; [|apply Hdeep]. intros; simpl in *; tauto.
           ++ simpl. apply nth_error_None in Hnth. apply Forall2_length in He; rewrite He in Hn. lia.
        -- simpl. unfold remap_subst. f_equal. apply remap_app_1; [lia|apply Hdeep].
      * eapply Forall_impl; [|apply Hdeep].
        intros x [Hx1 Hx2]; split; [assumption|].
        intros Hx3. destruct Hremap as [Hremap1 Hremap2].
        eapply Forall_forall in Hremap2; [|eassumption].
        destruct Hremap2; [lia|tauto].
    + intros [p t2] Hpt2. simpl. f_equal. rewrite subst_subst.
      erewrite subst_ext; [|apply liftn_subst_comp].
      eapply Forall3_impl, Forall3_select1, Forall_forall in Hdeeps; [|apply Hpt2|intros ? ? ? (? & ? & ? & Hclosed & ?); exact Hclosed]. simpl in Hdeeps.
      eapply subst_closed_at_ext; [eassumption|].
      intros n Hn. unfold liftn_subst. destruct le_lt_dec; [|reflexivity].
      f_equal. unfold comp. unfold read_env. rewrite nth_error_map.
      destruct nth_error eqn:Hnth; [reflexivity|].
      eapply nth_error_None in Hnth. apply Forall2_length in He; rewrite He in Hn; lia.
Qed.

Lemma read_extend_varmap_thread :
  forall st defs varmap varmap2 a t, read_thread st defs varmap a t -> is_remap_ok (st_freename st) varmap varmap2 -> read_thread st defs varmap2 a (subst (remap_subst varmap varmap2) t).
Proof.
  intros st defs varmap varmap2 a t H. apply (proj1 (read_extend_varmap_aux st defs)); assumption.
Qed.

Lemma read_extend_varmap_val :
  forall st defs varmap varmap2 v t, read_val st defs varmap v t -> is_remap_ok (st_freename st) varmap varmap2 -> read_val st defs varmap2 v (subst (remap_subst varmap varmap2) t).
Proof.
  intros st defs varmap varmap2 v t H. apply (proj1 (proj2 (read_extend_varmap_aux st defs))); assumption.
Qed.

Lemma read_extend_varmap_cont :
  forall st defs varmap varmap2 c h, read_cont st defs varmap c h -> is_remap_ok (st_freename st) varmap varmap2 -> read_cont st defs varmap2 c (subst_hctx (remap_subst varmap varmap2) h).
Proof.
  intros st defs varmap varmap2 c h H. apply (proj2 (proj2 (read_extend_varmap_aux st defs))); assumption.
Qed.

Lemma prefix_varmap_ok :
  forall freename varmap1 varmap2, Forall (fun x => freename <= x) varmap2 -> is_remap_ok freename varmap1 (varmap2 ++ varmap1).
Proof.
  intros freename varmap1 varmap2 H. split.
  - rewrite Forall_forall. intros x Hx; rewrite in_app_iff; tauto.
  - rewrite Forall_app. split.
    + eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
    + rewrite Forall_forall. intros x Hx; tauto.
Qed.

Lemma prefix_varmap_remap :
  forall freename varmap1 varmap2 n, Forall (fun x => freename <= x) varmap2 -> Forall (fun x => x < freename) varmap1 -> NoDup varmap1 -> n < length varmap1 -> remap varmap1 (varmap2 ++ varmap1) n = length varmap2 + n.
Proof.
  intros freename varmap1 varmap2 n H2 H1 Hnodup Hn. unfold remap.
  destruct nth_error as [x|] eqn:Hx; [|rewrite nth_error_None in Hx; lia].
  rewrite index_app, index_notin_None.
  - erewrite index_nth_error by eassumption. reflexivity.
  - intros Hx2. apply nth_error_In in Hx.
    rewrite Forall_forall in H1, H2.
    specialize (H2 _ Hx2); specialize (H1 _ Hx). lia.
Qed.

Lemma closed_at_ren :
  forall t ren k1 k2, closed_at t k1 -> (forall n, n < k1 -> renv ren n < k2) -> closed_at (ren_term ren t) k2.
Proof.
  induction t using term_ind2; intros ren k1 k2 Ht Hren; inversion Ht; subst; simpl.
  - constructor. apply Hren. assumption.
  - constructor.
  - constructor. eapply IHt; [eassumption|].
    intros [|n]; rewrite lift_renv; [lia|]. intros; specialize (Hren n); lia.
  - constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - constructor. rewrite <- Forall_forall in *.
    rewrite Forall_map. eapply Forall_impl; [|rewrite <- Forall_and; split; [apply H|apply H3]].
    intros t [IH Ht2]; eapply IH; eassumption.
  - constructor; [eapply IHt; eassumption|].
    intros p t2 Hpt2; rewrite in_map_iff in Hpt2; destruct Hpt2 as [[p3 t3] [Hpt2 Hpt3]]; simpl in *.
    injection Hpt2 as Hpt2; subst. rewrite Forall_forall in H. specialize (H _ Hpt3); simpl in H.
    eapply H; [apply H4; eassumption|].
    intros n Hn. destruct (le_lt_dec p n).
    + rewrite liftn_renv_large by assumption. specialize (Hren (n - p)); lia.
    + rewrite liftn_renv_small by assumption; lia.
Qed.

Lemma closed_at_plus_ren :
  forall t p k, closed_at t k -> closed_at (ren_term (plus_ren p) t) (p + k).
Proof.
  intros t p k H. eapply closed_at_ren; [eassumption|].
  intros n Hn; rewrite plus_ren_correct; lia.
Qed.

Lemma closed_at_subst_read_env_lift :
  forall t k p el, Forall (fun t => closed_at t k) el -> closed_at t (p + length el + k) -> closed_at (subst (liftn_subst p (read_env el)) t) (p + k).
Proof.
  intros t k p el Hel Ht; revert p Ht; induction t using term_ind2; intros p Ht; inversion Ht; subst; simpl.
  - unfold read_env, liftn_subst. destruct le_lt_dec.
    + destruct nth_error eqn:Hnth.
      * apply closed_at_plus_ren. rewrite Forall_forall in Hel. eapply Hel, nth_error_In, Hnth.
      * simpl. constructor. rewrite plus_ren_correct. rewrite nth_error_None in Hnth. lia.
    + constructor. lia.
  - constructor.
  - constructor. erewrite subst_ext; [|intros n; rewrite <- liftn_subst_1; apply liftn_subst_add].
    apply IHt. assumption.
  - constructor; [apply IHt1|apply IHt2]; assumption.
  - constructor. rewrite <- Forall_forall in *.
    rewrite Forall_map. eapply Forall_impl; [|rewrite <- Forall_and; split; [apply H|apply H3]].
    intros t [IH Ht2]; eapply IH; eassumption.
  - constructor; [apply IHt; assumption|].
    intros p2 t2 Hpt2; rewrite in_map_iff in Hpt2; destruct Hpt2 as [[p3 t3] [Hpt2 Hpt3]]; simpl in *.
    injection Hpt2 as Hpt2; subst. rewrite Forall_forall in H. specialize (H _ Hpt3); simpl in H.
    rewrite plus_assoc.
    erewrite subst_ext; [|apply liftn_subst_add].
    eapply H. specialize (H4 _ _ Hpt3). rewrite !plus_assoc in H4. assumption.
Qed.

Lemma closed_at_subst_read_env :
  forall t k el, Forall (fun t => closed_at t k) el -> closed_at t (length el + k) -> closed_at (subst (read_env el) t) k.
Proof.
  intros t k el H1 H2. assert (H := closed_at_subst_read_env_lift t k 0 el H1 H2).
  erewrite subst_ext in H; [eassumption|].
  intros n. apply liftn_subst_0.
Qed.

Lemma closed_at_mono :
  forall t n m, n <= m -> closed_at t n -> closed_at t m.
Proof.
  intros t n m Hnm H; revert m Hnm. induction H; intros n2 Hn; constructor.
  - lia.
  - apply IHclosed_at1. assumption.
  - apply IHclosed_at2. assumption.
  - apply IHclosed_at. lia.
  - intros t Ht; apply H0; assumption.
  - apply IHclosed_at. assumption.
  - intros; eapply H1; [eassumption|lia].
Qed.

Lemma Forall2_select1 :
  forall (A B : Type) (P : A -> Prop) (l1 : list A) (l2 : list B), Forall2 (fun a b => P a) l1 l2 -> Forall P l1.
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma Forall2_select2 :
  forall (A B : Type) (P : B -> Prop) (l1 : list A) (l2 : list B), Forall2 (fun a b => P b) l1 l2 -> Forall P l2.
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma index_length :
  forall A eq_dec (x : A) l n, index eq_dec l x = Some n -> n < length l.
Proof.
  induction l; intros n Hn; simpl in *.
  - congruence.
  - destruct eq_dec; [injection Hn as Hn; lia|].
    destruct index eqn:Hidx; [|congruence].
    specialize (IHl n1 eq_refl). injection Hn as Hn; lia.
Qed.

Lemma read_closed_at_aux :
  forall st defs,
    (forall varmap a t, read_thread st defs varmap a t -> closed_at t (length varmap)) /\
    (forall varmap v t, read_val st defs varmap v t -> closed_at t (length varmap)) /\
    (forall varmap c h, read_cont st defs varmap c h -> forall t, closed_at t (length varmap) -> closed_at (fill_hctx h t) (length varmap)).
Proof.
  intros st defs. read_ind.
  - apply IHc, IHv.
  - apply IHc. apply closed_at_subst_read_env.
    + eapply Forall2_select2, Forall2_impl; [|apply IHe].
      intros; assumption.
    + eapply closed_at_mono; [|eassumption].
      apply Forall2_length in He; lia.
  - assumption.
  - apply closed_at_subst_read_env.
    + eapply Forall2_select2, Forall2_impl; [|apply IHe].
      intros; assumption.
    + constructor.
      eapply closed_at_mono; [|eassumption].
      apply Forall2_length in He; lia.
  - constructor. rewrite <- Forall_forall.
    eapply Forall2_select2, Forall2_impl; [|apply IHe].
    intros; assumption.
  - apply IHc. destruct index eqn:Hidx; [|constructor].
    constructor. apply index_length in Hidx. assumption.
  - intros t Ht; assumption.
  - intros t1 Ht1. rewrite fill_compose. apply IHc.
    simpl. constructor; assumption.
  - intros t Ht. rewrite fill_compose. apply IHc.
    simpl. constructor; [assumption|].
    intros p t2 Hpt2; rewrite in_map_iff in Hpt2; destruct Hpt2 as [[p2 t3] [Hpt2 Hpt3]]; injection Hpt2 as Hpt2; subst.
    eapply closed_at_subst_read_env_lift.
    + eapply Forall2_select2, Forall2_impl; [|apply IHe].
      intros; assumption.
    + eapply Forall3_impl in Hdeeps; [|intros ? ? ? (? & ? & ? & H & ?); exact H].
      apply Forall3_select12, Forall2_select1 in Hdeeps. rewrite Forall_forall in Hdeeps; specialize (Hdeeps _ Hpt3).
      simpl in Hdeeps. eapply closed_at_mono; [|eassumption].
      apply Forall2_length in He; lia.
Qed.

Lemma read_closed_at_thread :
  forall st defs varmap a t, read_thread st defs varmap a t -> closed_at t (length varmap).
Proof.
  intros st defs. apply (proj1 (read_closed_at_aux st defs)).
Qed.

Lemma read_closed_at_val :
  forall st defs varmap v t, read_val st defs varmap v t -> closed_at t (length varmap).
Proof.
  intros st defs. apply (proj1 (proj2 (read_closed_at_aux st defs))).
Qed.




Lemma read_prefix_varmap_thread :
  forall st defs varmap1 varmap2 a t, read_thread st defs varmap1 a t -> Forall (fun x => st_freename st <= x) varmap2 -> Forall (fun x => x < st_freename st) varmap1 -> NoDup varmap1 -> read_thread st defs (varmap2 ++ varmap1) a (subst (ren (plus_ren (length varmap2))) t).
Proof.
  intros st defs varmap1 varmap2 a t Hread H2 H1 Hnodup.
  assert (Hread2 := Hread).
  eapply read_extend_varmap_thread in Hread; [|apply prefix_varmap_ok; eassumption].
  erewrite subst_closed_at_ext; [eassumption|apply read_closed_at_thread in Hread2; eassumption|].
  intros n Hn; simpl. unfold ren, remap_subst. f_equal.
  rewrite plus_ren_correct. erewrite prefix_varmap_remap; try eassumption. reflexivity.
Qed.

Lemma read_prefix_varmap_val :
  forall st defs varmap1 varmap2 v t, read_val st defs varmap1 v t -> Forall (fun x => st_freename st <= x) varmap2 -> Forall (fun x => x < st_freename st) varmap1 -> NoDup varmap1 -> read_val st defs (varmap2 ++ varmap1) v (subst (ren (plus_ren (length varmap2))) t).
Proof.
  intros st defs varmap1 varmap2 v t Hread H2 H1 Hnodup.
  assert (Hread2 := Hread).
  eapply read_extend_varmap_val in Hread; [|apply prefix_varmap_ok; eassumption].
  erewrite subst_closed_at_ext; [eassumption|apply read_closed_at_val in Hread2; eassumption|].
  intros n Hn; simpl. unfold ren, remap_subst. f_equal.
  rewrite plus_ren_correct. erewrite prefix_varmap_remap; try eassumption. reflexivity.
Qed.

(*
Lemma read_extend_varmap_val :
  forall st defs varmap varmap2 v t, read_val st defs varmap v t -> is_remap_ok (st_freename st) varmap varmap2 -> read_val st defs varmap2 v (subst (remap_subst varmap varmap2) t).
Proof.
  intros st defs varmap varmap2 v t H. apply (proj1 (proj2 (read_extend_varmap_aux st defs))); assumption.
Qed.

Lemma read_extend_varmap_cont :
  forall st defs varmap varmap2 c h, read_cont st defs varmap c h -> is_remap_ok (st_freename st) varmap varmap2 -> read_cont st defs varmap2 c (subst_hctx (remap_subst varmap varmap2) h).
Proof.
  intros st defs varmap varmap2 c h H. apply (proj2 (proj2 (read_extend_varmap_aux st defs))); assumption.
Qed.
*)

(*
Lemma liftn_subst_is_ren :
  forall p us t, subst (liftn_subst p us) t = subst (ren (plus_ren p)) (subst us t).
Proof.
  intros p us t. rewrite subst_subst.
  eapply subst_closed_at_ext. admit. intros n Hn.
  unfold liftn_subst, comp, ren; simpl.
  destruct le_lt_dec.
  - simpl. admit.
  - 
 *)

Lemma seq_nth_error :
  forall len a n, n < len -> nth_error (seq a len) n = Some (a + n).
Proof.
  induction len; intros a [|n] Hn; simpl in *; try lia.
  - f_equal; lia.
  - rewrite IHlen; [f_equal|]; lia.
Qed.

Lemma liftn_subst_read_env :
  forall t p e, closed_at t (p + length e) -> subst (liftn_subst p (read_env e)) t = subst (read_env (map var (seq 0 p) ++ map (subst (ren (plus_ren p))) e)) t.
Proof.
  intros t p e Ht. eapply subst_closed_at_ext; [eassumption|]. intros n Hn.
  unfold liftn_subst, read_env.
  destruct le_lt_dec.
  - rewrite nth_error_app2; [|rewrite map_length, seq_length; assumption].
    rewrite map_length, seq_length, nth_error_map.
    destruct nth_error eqn:Hnth.
    + rewrite ren_term_is_subst. reflexivity.
    + simpl. rewrite nth_error_None in Hnth. lia.
  - rewrite nth_error_app1 by (rewrite map_length, seq_length; assumption). rewrite nth_error_map.
    rewrite seq_nth_error by assumption. reflexivity.
Qed.


Lemma read_val_makendeeps_changed :
  forall st st2 defs varmap bs e el rid t,
    st_freename (fst (makendeeps st bs e)) <= st_freename st2 ->
    Forall (fun pt => closed_at (snd pt) (fst pt + length e) /\ no_dvar (snd pt)) bs ->
    read_thread st defs varmap rid t ->
    Forall (fun v => forall a, val_points_to v a -> points st rid a) e ->
    only_changed (fst (makendeeps st bs e)) st2 rid ->
    Forall2 (read_val st defs varmap) e el ->
    length defs <= st_freename st ->
    Forall (fun x => x < st_freename st) varmap -> NoDup varmap ->
    Forall2 (fun pt vdeeps =>
               length (fst vdeeps) = fst pt /\
               read_val st2 defs (fst vdeeps ++ varmap) (snd vdeeps) (subst (liftn_subst (fst pt) (read_env el)) (snd pt)))
            bs (snd (makendeeps st bs e)).
Proof.
  intros st st2 defs varmap bs. revert st st2.
  induction bs as [|[p t2]]; intros st st2 e el rid t Hst12 Hbs H1 H2 H3 H4 H5 Hvarmap1 Hvarmap2; simpl; constructor; simpl.
  - split; [apply seq_length|]. constructor.
    eapply only_changed_read_thread_ind_1; cycle 1.
    + eapply only_changed_trans; [|eassumption]. simpl.
      apply only_extended_changed, only_extended_makendeeps.
    + eapply read_thread_only_extended; [| |eassumption]; [simpl; lia|].
      eapply only_extended_trans; [|apply only_extended_makelazy].
      intros ? ? ?; assumption.
    + inversion Hbs; subst. rewrite liftn_subst_read_env by (apply Forall2_length in H4; rewrite <- H4; tauto).
      eapply read_thread_term with (h := h_hole); [apply nth_error_extend| |apply Forall2_app|constructor|tauto].
      * rewrite app_length, map_length, seq_length. tauto.
      * rewrite seq_is_shiftn, !Forall2_map_left, Forall2_map_right, Forall2_map_same.
        rewrite <- seq_is_shiftn.
        rewrite Forall_forall. intros x Hx. rewrite in_seq in Hx.
        replace (var x) with (match index Nat.eq_dec (seq (st_freename st) p ++ varmap) (x + st_freename st) with None => dvar (x + st_freename st) | Some n => var n end) by (rewrite index_app, index_seq; [f_equal|]; lia).
        eapply read_val_neutral with (h := h_hole); [constructor| |simpl; lia|rewrite in_app_iff, in_seq; lia].
        rewrite nth_error_None_rw by lia.
        constructor.
      * rewrite Forall2_map_right.
        eapply Forall2_impl; [|eassumption].
        intros; eapply read_val_only_extended;
          [| |replace (plus_ren p) with (plus_ren (length (seq (st_freename st) p))) by
               (rewrite seq_length; reflexivity); eapply read_prefix_varmap_val]; [| |eassumption| | |].
        -- simpl. lia.
        -- eapply only_extended_trans; [|apply only_extended_makelazy].
           intros ? ? ?; assumption.
        -- rewrite Forall_forall. intros u Hu; rewrite in_seq in Hu; lia.
        -- assumption.
        -- assumption.
    + inversion H1; subst; apply nth_error_Some3 in H; lia.
    + intros a Ha. eapply only_extended_points; [apply only_extended_makelazy|].
      unfold points, points_to in Ha. simpl in Ha. rewrite nth_error_extend in Ha; simpl in Ha.
      destruct Ha as [Ha | Ha]; inversion Ha; subst.
      unfold env_points_to in H7. rewrite Exists_app in H7.
      destruct H7 as [H7 | H7]; [rewrite Exists_map, Exists_exists in H7; destruct H7 as (x & H7 & H8); inversion H8; subst; inversion H0|].
      eapply Forall_Exists; [|apply H2|eassumption].
      intros v H8 H9; apply H8, H9.
    + etransitivity; [|eassumption]. simpl. etransitivity; [|apply makendeeps_freename]. simpl. lia.
  - eapply IHbs.
    + assumption.
    + inversion Hbs; subst; assumption.
    + eapply read_thread_only_extended; [| |eassumption]; [simpl; lia|].
      eapply only_extended_trans; [|eapply only_extended_makelazy].
      intros ? ? ?; assumption.
    + eapply Forall_impl; [|eassumption]. intros v Hv a Ha.
      eapply only_extended_points; [|apply Hv, Ha].
      eapply only_extended_trans; [|eapply only_extended_makelazy].
      intros ? ? ?; assumption.
    + eassumption.
    + eapply Forall2_impl; [|eassumption].
      intros v t3 H; eapply read_val_only_extended; [| |eassumption]; [simpl; lia|].
      eapply only_extended_trans; [|eapply only_extended_makelazy].
      intros ? ? ?; assumption.
    + simpl. lia.
    + eapply Forall_impl; [|eassumption].
      intros; simpl in *; lia.
    + assumption.
Qed.

Lemma step_r_freename :
  forall st rid, st_freename st <= st_freename (step_r st rid).
Proof.
  intros st rid. unfold step_r.
  destruct nth_error; [|lia].
  destruct rt_code as [t e|v]; [destruct t | destruct v].
  - destruct nth_error; simpl; lia.
  - lia.
  - destruct rt_cont; simpl; lia.
  - simpl; lia.
  - simpl. apply makenlazy_freename.
  - simpl. apply makendeeps_freename.
  - destruct is_finished; simpl; lia.
  - destruct p as [[x c] uf]. destruct uf; simpl; lia.
  - destruct rt_cont; simpl; lia.
  - destruct rt_cont; try lia.
    destruct nth_error as [[p t]|]; [|lia].
    destruct Nat.eq_dec; simpl; lia.
Qed.

Lemma dvar_below_free :
  forall k t, dvar_below k t <-> (forall x, k <= x -> dvar_free x t).
Proof.
  intros k t; split.
  - induction t using term_ind2; intros H1; inversion H1; subst; intros x Hx; constructor.
    + lia.
    + apply IHt; assumption.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H3]].
      simpl; intros t [H4 H5]; apply H4; assumption.
    + apply IHt; assumption.
    + eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H5]].
      simpl; intros [p t2] [H6 H7]; apply H6; assumption.
  - induction t using term_ind2; intros H1; constructor.
    + specialize (H1 n). destruct (le_lt_dec k n) as [Hkn | Hkn]; [|assumption].
      specialize (H1 Hkn); inversion H1. lia.
    + apply IHt. intros x Hx; specialize (H1 x Hx); inversion H1; subst; assumption.
    + apply IHt1. intros x Hx; specialize (H1 x Hx); inversion H1; subst; assumption.
    + apply IHt2. intros x Hx; specialize (H1 x Hx); inversion H1; subst; assumption.
    + eapply Forall_forall. intros t Ht; eapply Forall_forall in H; [|eassumption].
      apply H. intros x Hx; specialize (H1 x Hx); inversion H1; subst.
      eapply Forall_forall in H2; eassumption.
    + apply IHt. intros x Hx; specialize (H1 x Hx); inversion H1; subst; assumption.
    + eapply Forall_forall. intros [p t2] Hpt2; eapply Forall_forall in H; [|eassumption].
      simpl in *. apply H. intros x Hx; specialize (H1 x Hx); inversion H1; subst.
      eapply Forall_forall in H4; [|eassumption]. assumption.
Qed.

Lemma dvar_free_ren :
  forall x t r, dvar_free x t -> dvar_free x (ren_term r t).
Proof.
  intros x t. induction t using term_ind2; intros r Ht; simpl.
  - constructor.
  - assumption.
  - constructor. apply IHt. inversion Ht; subst; assumption.
  - constructor; [apply IHt1 | apply IHt2]; inversion Ht; subst; assumption.
  - constructor. rewrite Forall_map. inversion Ht; subst.
    eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H1]].
    intros t [H2 H3]; apply H2, H3.
  - inversion Ht; subst. constructor; [apply IHt; assumption|].
    rewrite Forall_map.
    eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H3]].
    intros [p t2] [H4 H5]; apply H4, H5.
Qed.

Lemma dvar_free_liftn_subst :
  forall x us p, (forall n, dvar_free x (us n)) -> (forall n, dvar_free x (liftn_subst p us n)).
Proof.
  intros x us p H n. unfold liftn_subst.
  destruct le_lt_dec; [|constructor].
  apply dvar_free_ren, H.
Qed.

Lemma dvar_free_lift_subst :
  forall x us, (forall n, dvar_free x (us n)) -> (forall n, dvar_free x (lift_subst us n)).
Proof.
  intros x us H n. rewrite <- liftn_subst_1. apply dvar_free_liftn_subst. assumption.
Qed.

Lemma dvar_below_liftn_subst :
  forall k us p, (forall n, dvar_below k (us n)) -> (forall n, dvar_below k (liftn_subst p us n)).
Proof.
  intros k us p H n. rewrite dvar_below_free. intros x Hx.
  apply dvar_free_liftn_subst. intros n1; eapply dvar_below_free; [|eassumption].
  apply H.
Qed.

Lemma dvar_free_subst :
  forall x t us, (forall n, dvar_free x (us n)) -> dvar_free x t -> dvar_free x (subst us t).
Proof.
  intros x t. induction t using term_ind2; intros us Hus Ht; simpl.
  - apply Hus.
  - assumption.
  - constructor. apply IHt; [|inversion Ht; subst; assumption].
    apply dvar_free_lift_subst, Hus.
  - constructor; [apply IHt1 | apply IHt2]; inversion Ht; subst; assumption.
  - constructor. inversion Ht; subst.
    rewrite Forall_map. eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H1]].
    intros t [H2 H3]; apply H2, H3; assumption.
  - inversion Ht; subst. constructor; [apply IHt; assumption|].
    rewrite Forall_map. eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H3]].
    intros [p t2] [H4 H5]. simpl. apply H4, H5.
    apply dvar_free_liftn_subst, Hus.
Qed.

Lemma dvar_below_subst :
  forall k t us, (forall n, dvar_below k (us n)) -> dvar_below k t -> dvar_below k (subst us t).
Proof.
  intros k t us Hus Ht. rewrite dvar_below_free. intros x Hx; apply dvar_free_subst.
  - intros n; eapply dvar_below_free; [|eassumption]. apply Hus.
  - eapply dvar_below_free; eassumption.
Qed.

Lemma dvar_below_no_dvar :
  forall t k, no_dvar t -> dvar_below k t.
Proof.
  intros t k Ht. apply dvar_below_free. intros x Hx. apply Ht.
Qed.

Lemma dvar_free_read_env :
  forall x l, Forall (dvar_free x) l -> (forall n, dvar_free x (read_env l n)).
Proof.
  intros x l H n. unfold read_env.
  destruct nth_error eqn:H1.
  - rewrite Forall_forall in H. apply H. eapply nth_error_In; eassumption.
  - constructor.
Qed.

Lemma dvar_below_read_env :
  forall k l, Forall (dvar_below k) l -> (forall n, dvar_below k (read_env l n)).
Proof.
  intros k l H n. unfold read_env.
  destruct nth_error eqn:H1.
  - rewrite Forall_forall in H. apply H. eapply nth_error_In; eassumption.
  - constructor.
Qed.

Lemma Forall2_and_Forall_left :
  forall (A B : Type) (P : A -> B -> Prop) (Q : A -> Prop) (L1 : list A) (L2 : list B), Forall2 P L1 L2 -> Forall Q L1 -> Forall2 (fun x y => P x y /\ Q x) L1 L2.
Proof.
  intros A B P Q L1 L2 H1; induction H1; intros H2; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall2_and_Forall_right :
  forall (A B : Type) (P : A -> B -> Prop) (Q : B -> Prop) (L1 : list A) (L2 : list B), Forall2 P L1 L2 -> Forall Q L2 -> Forall2 (fun x y => P x y /\ Q y) L1 L2.
Proof.
  intros A B P Q L1 L2 H1; induction H1; intros H2; inversion H2; subst; constructor; tauto.
Qed.

Lemma makendeeps_dvar_below :
  forall l st e,
    Forall (fun vdeep => Forall (fun x => st_freename st <= x) (fst vdeep)) (snd (makendeeps st l e)).
Proof.
  intros l; induction l as [|[p t2] l]; intros st e; simpl in *; constructor.
  - simpl. rewrite Forall_forall. intros x Hx; rewrite in_seq in Hx. lia.
  - eapply Forall_impl; [|apply IHl].
    intros [vs v] H; simpl in *. eapply Forall_impl; [|eassumption]. intros; simpl in *; lia.
Qed.

Lemma makendeeps_dvar_above :
  forall l st e,
    Forall (fun vdeep => Forall (fun x => x < st_freename (fst (makendeeps st l e))) (fst vdeep)) (snd (makendeeps st l e)).
Proof.
  intros l; induction l as [|[p t2] l]; intros st e; simpl in *; constructor; simpl.
  - rewrite Forall_forall. intros x Hx; rewrite in_seq in Hx.
    eapply lt_le_trans; [|apply makendeeps_freename]. simpl. lia.
  - apply IHl.
Qed.

Lemma makendeeps_dvar_nodup :
  forall l st e,
    Forall (fun vdeep => NoDup (fst vdeep)) (snd (makendeeps st l e)).
Proof.
  intros l; induction l as [|[p t2] l]; intros st e; simpl in *; constructor; simpl.
  - apply seq_NoDup.
  - apply IHl.
Qed.

(*
Lemma read_dvar_below_aux :
  forall st defs,
    (forall varmap a t, read_thread varmap st defs a t -> dvar_below (st_freename st) t) /\
    (forall varmap v t, read_val varmap st defs v t -> dvar_below (st_freename st) t) /\
    (forall varmap c h, read_cont varmap st defs c h -> (forall t, dvar_below (st_freename st) t -> dvar_below (st_freename st) (fill_hctx h t))).
Proof.
  intros st defs; eapply read_ind.
  - intros rid v c t h H1 H2 H3 H4 H5.
    apply H5, H4.
  - intros rid e el c t h H1 H2 H3 H4 Hdv H5.
    apply H5.
    apply dvar_below_subst; [|apply dvar_below_no_dvar; assumption].
    eapply dvar_below_read_env, Forall2_select2. eassumption.
  - intros rid t H1 H2.
    assumption.
  - intros t e el n f tdeep H1 H2 H3 H4 H5 H6 H7.
    apply dvar_below_subst; [|constructor; apply dvar_below_no_dvar; assumption].
    eapply dvar_below_read_env, Forall2_select2. eassumption.
  - intros tag e el H1 H2.
    constructor. apply Forall2_select2 in H2. assumption.
  - intros x c h uf tuf H1 H2 H3 H4 H5.
    apply H4. constructor. assumption.
  - intros; simpl; assumption.
  - intros v c t h H1 H2 H3 H4.
    intros t2 Ht2. rewrite fill_compose. apply H4.
    simpl. constructor; assumption.
  - intros bs e bds tdeeps c el h H1 H2 H3 H4 H5 H6.
    intros t2 Ht2. rewrite fill_compose. apply H5.
    simpl. constructor; [assumption|].
    apply Forall2_select2 in H4.
    eapply Forall3_impl, Forall3_select12, Forall2_select1 in H3; [|intros ? ? ? (? & ? & ? & ? & Hdv); exact Hdv].
    rewrite Forall_map. eapply Forall_impl; [|eassumption].
    intros [p t3] Hpt3. simpl in *.
    apply dvar_below_subst; [|apply dvar_below_no_dvar; assumption].
    eapply dvar_below_liftn_subst, dvar_below_read_env.
    assumption.
Qed.

Lemma read_dvar_below_thread :
  forall st defs rid t, read_thread st defs rid t -> dvar_below (st_freename st) t.
Proof.
  intros st defs.
  apply (proj1 (read_dvar_below_aux st defs)).
Qed.

Lemma read_dvar_below_val :
  forall st defs v t, read_val st defs v t -> dvar_below (st_freename st) t.
Proof.
  intros st defs.
  apply (proj1 (proj2 (read_dvar_below_aux st defs))).
Qed.

Lemma read_dvar_below_cont :
  forall st defs c h, read_cont st defs c h -> forall t, dvar_below (st_freename st) t -> dvar_below (st_freename st) (fill_hctx h t).
Proof.
  intros st defs.
  apply (proj2 (proj2 (read_dvar_below_aux st defs))).
Qed.
 *)



Lemma nth_error_update_None :
  forall (A : Type) l k1 k2 (x : A), nth_error l k1 = None -> nth_error (update l k2 x) k1 = None.
Proof.
  intros A l; induction l; intros k1 k2 x H; destruct k1; destruct k2; simpl in *; try congruence.
  apply IHl. assumption.
Qed.

Lemma makenlazy_new_threads :
  forall st ts e rid,
    nth_error (st_rthreads st) rid = None ->
    nth_error (st_rthreads (fst (makenlazy st ts e))) rid <> None ->
    In (Thread rid) (snd (makenlazy st ts e)).
Proof.
  intros st ts e rid; revert st; induction ts as [|t ts]; intros st Hrid1 Hrid2; simpl in *.
  - tauto.
  - destruct (nth_error (st_rthreads (extend_rthread st {| rt_code := Term t e; rt_cont := Kid |})) rid) eqn:Hrid3.
    + simpl in Hrid3. rewrite nth_error_app2 in Hrid3; [|rewrite nth_error_None in Hrid1; assumption].
      remember (rid - length (st_rthreads st)) as n.
      destruct n; [|destruct n; simpl in *; congruence]. simpl in Hrid3. injection Hrid3 as Hrid3; subst.
      assert (rid = length (st_rthreads st)) by (rewrite nth_error_None in Hrid1; lia). subst.
      tauto.
    + right. apply IHts; assumption.
Qed.

Lemma makendeeps_new_threads :
  forall st l e rid,
    nth_error (st_rthreads st) rid = None ->
    nth_error (st_rthreads (fst (makendeeps st l e))) rid <> None ->
    exists vs, NoDup vs /\ Forall (fun v => st_freename st <= v < st_freename (fst (makendeeps st l e))) vs /\ In (vs, Thread rid) (snd (makendeeps st l e)).
Proof.
  intros st l e rid; revert st; induction l as [|[p t2] l]; intros st Hrid1 Hrid2; simpl in *.
  - tauto.
  - match goal with [ |- context[ extend_rthread ?st ?t ] ] =>
                    destruct (nth_error (st_rthreads (extend_rthread st t)) rid) eqn:Hrid3 end.
    + simpl in Hrid3. rewrite nth_error_app2 in Hrid3; [|rewrite nth_error_None in Hrid1; assumption].
      remember (rid - length (st_rthreads st)) as n.
      destruct n; [|destruct n; simpl in *; congruence]. simpl in Hrid3. injection Hrid3 as Hrid3; subst.
      assert (rid = length (st_rthreads st)) by (rewrite nth_error_None in Hrid1; lia). subst.
      eexists. repeat split; [apply seq_NoDup| |left; reflexivity].
      rewrite Forall_forall. intros x Hx; rewrite in_seq in Hx.
      split; [lia|]. eapply lt_le_trans; [|apply makendeeps_freename]. simpl. lia.
    + destruct (IHl _ Hrid3) as (vs & Hvs1 & Hvs2 & Hvs3); [assumption|].
      exists vs. repeat split; [assumption| |right; assumption].
      eapply Forall_impl; [|eassumption]. intros; simpl in *; lia.
Qed.

Definition varmap_ok freename varmap :=
  Forall (fun x => x < freename) varmap /\ NoDup varmap.

Lemma varmap_ok_cons :
  forall freename varmap x, varmap_ok freename varmap -> x < freename -> x \notin varmap -> varmap_ok freename (x :: varmap).
Proof.
  intros freename varmap x [H1 H2] H3 H4; split; constructor; assumption.
Qed.

Lemma NoDup_app :
  forall (A : Type) (l1 l2 : list  A), NoDup l1 -> NoDup l2 -> Forall (fun x => x \notin l2) l1 -> NoDup (l1 ++ l2).
Proof.
  induction l1; intros l2 Hnd1 Hnd2 Hdisj; inversion Hnd1; subst; inversion Hdisj; subst; simpl in *.
  - assumption.
  - constructor.
    + rewrite in_app_iff; tauto.
    + apply IHl1; assumption.
Qed.

Lemma varmap_ok_app :
  forall freename varmap varmap2, varmap_ok freename varmap -> Forall (fun x => x < freename /\ x \notin varmap) varmap2 -> NoDup varmap2 -> varmap_ok freename (varmap2 ++ varmap).
Proof.
  intros freename varmap varmap2 Hok Hvarmap2 Hnodup. split.
  - rewrite Forall_app; split; [|apply Hok].
    eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
  - apply NoDup_app; [assumption|apply Hok|].
    eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
Qed.

Lemma step_r_beta_hnf :
  forall st st2 defs varmap rid t,
    defs_ok defs st ->
    Forall (fun x => x < st_freename st) varmap ->
    NoDup varmap ->
    step_r st rid = st2 ->
    read_thread st defs varmap rid t ->
    same_read_plus st st2 defs rid /\
    (forall rid2, nth_error (st_rthreads st) rid2 = None -> nth_error (st_rthreads st2) rid2 <> None ->
             exists t2 varmap2, varmap_ok (st_freename st2) varmap2 /\ read_thread st2 defs varmap2 rid2 t2) /\
    exists t2, read_thread st2 defs varmap rid t2 /\ reflc beta_hnf t t2.
Proof.
  intros st st2 defs varmap rid t Hdefsok Hvarmap1 Hvarmap2 <- Hread.
  match goal with [ |- ?G1 /\ ?G2 /\ ?G3 ] =>
  assert (Hsame : every_reachable st rid (fun a => forall varmap2 t, read_thread st defs varmap2 a t -> read_thread (step_r st rid) defs varmap2 a t) -> G2 -> G1 /\ G2 /\ G3) end.
  {
    intros H Hnew. rewrite every_reachable_iff in H; destruct H as [H1 H2].
    split; [apply H2|]. split; [assumption|]. eexists; split; [|right; reflexivity]. apply H1, Hread.
  }
  match goal with [ |- ?G ] => assert (Hid : step_r st rid = st -> G) end.
  {
    intros Heq; rewrite Heq in *. apply Hsame; [intros ? ? ? ? ?; assumption|].
    intros; congruence.
  }
  assert (Hfree := step_r_freename st rid).
  unfold step_r in *.
  inversion Hread; subst.
  - rewrite H in *; simpl in *.
    inversion H0; subst.
    + destruct is_finished eqn:Hfinished; [|apply Hid; reflexivity].
      and_left as Hreach; [eapply same_read_update; eassumption|].
      unfold is_finished in Hfinished.
      inversion H2; subst; rewrite H3 in Hfinished; simpl in *; [|congruence].
      inversion H5; simpl in *; subst; simpl in *; try congruence.
      injection Hfinished as Hfinished; subst.
      split; [intros rid2 Hrid2a Hrid2b; rewrite nth_error_update_None in Hrid2b; tauto|].
      eexists. split; [|right; reflexivity].
      eapply read_thread_val; [eapply nth_error_update; eassumption| |].
      * eapply same_read_plus_val; [eassumption|eassumption|eassumption|].
        intros a Ha. eapply plus_S; [|apply plus_1]; unfold points, points_to.
        -- rewrite H. left. constructor. constructor.
        -- rewrite H3. left. constructor. assumption.
      * eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to. rewrite H. right. assumption.
    + inversion H1; subst; try (apply Hid; reflexivity).
      and_left as Hreach; [eapply same_read_update; eassumption|].
      split; [simpl; intros rid2 Hrid2a Hrid2b; rewrite nth_error_update_None in Hrid2b; tauto|].
      eexists; split; [|left; rewrite fill_compose; simpl; apply beta_hnf_ctx, beta_hnf_red, beta_red_lam].
      unfold subst1, lift_subst. rewrite subst_subst.
      erewrite subst_ext; [eapply read_thread_term|].
      * eapply nth_error_update; eassumption.
      * simpl. assumption.
      * constructor.
        -- eapply same_read_plus_val_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H; right; apply kapp_points_to_1, Ha.
        -- eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H; left; constructor; apply clos_points_to_1.
           apply Exists_exists; eexists; split; eassumption.
      * eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to; rewrite H; right; apply kapp_points_to_2, Ha.
      * assumption.
      * intros [|n]; unfold comp; simpl; [rewrite read_env_0; reflexivity|].
        rewrite read_env_S. rewrite subst_ren.
        erewrite subst_ext; [apply subst_id|].
        intros n2; unfold comp; simpl. destruct n2; reflexivity.
    + destruct c; try (apply Hid; reflexivity).
      destruct (nth_error l tag) as [[p t]|] eqn:Hpt; [|apply Hid; reflexivity].
      destruct Nat.eq_dec; [|apply Hid; reflexivity].
      and_left as Hreach; [eapply same_read_update; eassumption|].
      inversion H1; subst. rewrite fill_compose; simpl.
      split; [intros rid2 Hrid2a Hrid2b; rewrite nth_error_update_None in Hrid2b; tauto|].
      eexists; split; cycle 1.
      {
        left. apply beta_hnf_ctx, beta_hnf_red.
        apply nth_error_decompose in Hpt; destruct Hpt as (l2 & l3 & Hpt1 & Hpt2); rewrite Hpt1, <- Hpt2.
        erewrite map_app, <- map_length. simpl.
        replace (length e) with (length el) by (apply Forall2_length in H2; symmetry; assumption).
        apply beta_red_switch.
      }
      erewrite subst_subst, <- subst_ext; [|apply read_env_app].
      eapply read_thread_term; [eapply nth_error_update; eassumption| |apply Forall2_app| |].
      * eapply Forall3_impl in H11; [|intros ? ? ? (? & ? & ? & Hclosed & ?); exact Hclosed].
        apply Forall3_select12, Forall2_select1 in H11. rewrite Forall_forall in H11.
        rewrite app_length. apply nth_error_In, H11 in Hpt. assumption.
      * eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to; rewrite H; left; constructor; apply block_points_to.
        apply Exists_exists; eexists; split; eassumption.
      * eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to; rewrite H; right. apply kswitch_points_to_1.
        apply Exists_exists; eexists; split; eassumption.
      * eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to; rewrite H; right. apply kswitch_points_to_3. assumption.
      * eapply Forall3_impl, Forall3_select12, Forall2_select1 in H11; [|intros ? ? ? (? & ? & ? & ? & ? & ? & Hdv); exact Hdv].
        eapply Forall_forall in H11; [|eapply nth_error_In; eassumption]. assumption.
    + and_left as Hreach.
      {
        destruct uf as [uf|]; simpl in *; [|eapply same_read_update; eassumption].
        eapply same_read_unchanged; [simpl; lia|].
        dedup common; [eapply unchanged_from_plus_trans; [|eapply unchanged_from_plus_update, read_thread_same; [|eapply Hread|]; [simpl; lia|]]; exact common|].
        eapply unchanged_from_extend; eassumption.
      }
      inversion H3; subst.
      * split; [intros rid2 Hrid2a Hrid2b; unfold exit_rthread in Hrid2b; simpl in *; rewrite nth_error_update_None in Hrid2b; tauto|].
        eexists; split; [|right; reflexivity].
        eapply read_thread_val with (h := h_hole); [eapply nth_error_update; eassumption| |constructor].
        rewrite <- fill_compose.
        econstructor.
        -- apply compose_cont_ctx; eapply same_read_plus_cont_1; try eassumption;
             intros a Ha; unfold points, points_to; rewrite H;
               (left; constructor; constructor; assumption) || (right; assumption).
        -- rewrite <- H9. constructor.
        -- simpl. assumption.
        -- simpl. assumption.
      * refine ((fun (Hreadnew : read_thread _ _ varmap (length (st_rthreads st)) _) => _) _).
        -- split. {
             intros rid2 Hrid2a Hrid2b. unfold exit_rthread in Hrid2b; simpl in Hrid2b.
             rewrite nth_error_update3 in Hrid2b by congruence.
             rewrite nth_error_app2 in Hrid2b by (rewrite nth_error_None in Hrid2a; assumption).
             destruct (rid2 - length (st_rthreads st)) as [|n] eqn:Hr; simpl in *; [|destruct n; simpl in *; congruence].
             assert (rid2 = length (st_rthreads st)) by (rewrite nth_error_None in Hrid2a; lia). subst.
             eexists. eexists. split; [|apply Hreadnew].
             split; assumption.
           }
           eexists; split; [|right; reflexivity].
           eapply read_thread_val with (h := h_hole);
             [eapply nth_error_update; eapply nth_error_app_Some; eassumption| |constructor].
           rewrite <- fill_compose.
           econstructor;
             try (apply compose_cont_ctx; eapply same_read_plus_cont_1; try eassumption;
                  intros a Ha; unfold points, points_to; rewrite H;
                  (left; constructor; constructor; assumption) || (right; assumption));
             try (simpl; assumption).
           rewrite <- H6. constructor.
         split; [|split; [rewrite fill_compose; apply convertible_fill, H9|tauto]].
         apply read_val_thread. apply Hreadnew.
        -- eapply read_thread_val.
         ++ unfold exit_rthread; simpl. rewrite nth_error_update3; [apply nth_error_extend|].
           apply nth_error_Some3 in H; lia.
         ++ eapply same_read_plus_val_1; [eassumption|eassumption|apply H9|].
           intros a Ha; unfold points, points_to. rewrite H; left; constructor.
           eapply neutral_points_to_2; [reflexivity|eassumption].
         ++ eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to. rewrite H; right; assumption.
  - rewrite H in *; cbv beta delta [rt_code] iota in *.
    destruct t0; cbv delta [rt_code rt_cont] iota in *.
    + destruct (nth_error e n) eqn:He; [|apply Hid; reflexivity].
      and_left as Hreach; [eapply same_read_update; eassumption|].
      split; [simpl; intros rid2 Hrid2a Hrid2b; rewrite nth_error_update_None in Hrid2b; tauto|].
      eexists; split; [|right; reflexivity].
      econstructor.
      * eapply nth_error_update; eassumption.
      * simpl.
        eapply nth_error_Forall2 in H1; [|eassumption].
        destruct H1 as (vv & Hvv1 & Hvv2). unfold read_env; rewrite Hvv1.
        eapply same_read_plus_val_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to. rewrite H; left; constructor.
        apply Exists_exists; eexists; split; [eapply nth_error_In|]; eassumption.
      * eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
        intros a Ha; unfold points, points_to. rewrite H; right; assumption.
    + apply Hid. reflexivity.
    + destruct c.
      * and_left as Hreach. {
          eapply same_read_unchanged; [eassumption|].
          dedup common; [eapply unchanged_from_plus_trans;
                         [|eapply unchanged_from_plus_update, read_thread_same; [|eapply Hread|]; [simpl; lia|]]; exact common|].
          dedup common; [eapply unchanged_from_trans;
                         [|eapply unchanged_from_makelazy, read_thread_same; [|eapply Hread|]; [simpl; lia|]]; exact common|].
          eapply unchanged_from_freevar.
        }
        match goal with [ Hreach : same_read_plus st ?st2 defs rid |- _ ] =>
                        refine ((fun (Hreadnew : read_thread st2 defs (st_freename st :: varmap) (length (st_rthreads st)) _) => _) _) end; cycle 1.
        {
          eapply read_thread_term.
          -- unfold exit_rthread; simpl. rewrite nth_error_update3; [apply nth_error_extend|].
             apply nth_error_Some3 in H; lia.
          -- simpl. inversion H0; assumption.
          -- constructor.
             ++ eapply read_val_neutral; [constructor| |simpl; lia|simpl; tauto].
               rewrite nth_error_None_rw; [|apply Hdefsok]. constructor.
             ++ eapply same_read_plus_val_Forall2_1; [eassumption|eassumption| |].
               ** rewrite Forall2_map_right. eapply Forall2_impl; [|eassumption].
                  intros v t Hvt. eapply read_prefix_varmap_val with (varmap2 := st_freename st :: nil); try eassumption.
                  constructor; [lia|]. constructor.
               ** intros a Ha; unfold points, points_to; rewrite H; left; constructor.
                  apply Exists_exists; eexists; split; eassumption.
          -- constructor.
          -- intros x; specialize (H3 x); inversion H3; assumption.
        }
        split. {
          intros rid2 Hrid2a Hrid2b. unfold exit_rthread in Hrid2b; simpl in Hrid2b.
          rewrite nth_error_update3 in Hrid2b by congruence.
          rewrite nth_error_app2 in Hrid2b by (rewrite nth_error_None in Hrid2a; assumption).
          destruct (rid2 - length (st_rthreads st)) as [|n] eqn:Hr; simpl in *; [|destruct n; simpl in *; congruence].
          assert (rid2 = length (st_rthreads st)) by (rewrite nth_error_None in Hrid2a; lia). subst.
          eexists. eexists. split; [|apply Hreadnew].
          apply varmap_ok_cons; [split; [eapply Forall_impl; [|eassumption]; intros; simpl in *; lia|assumption]|lia|].
          intros Hin. rewrite Forall_forall in Hvarmap1. apply Hvarmap1 in Hin. lia.
        }
        eexists; split; [|right; reflexivity].
        simpl. eapply read_thread_val.
        -- eapply nth_error_update, nth_error_app_Some; eassumption.
        -- eapply read_val_clos.
           ++ eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
             intros a Ha; unfold points, points_to; rewrite H; left; constructor.
             apply Exists_exists; eexists; split; eassumption.
           ++ apply read_val_thread, Hreadnew.
           ++ simpl index. destruct Nat.eq_dec; [|tauto]. simpl.
             apply star_same. erewrite subst_ext; [|symmetry; apply liftn_subst_1].
             apply liftn_subst_read_env. inversion H0; subst. eapply Forall2_length in H1. rewrite <- H1; assumption.
           ++ intros x; specialize (H3 x); inversion H3; assumption.
           ++ simpl. unfold defs_ok in Hdefsok. lia.
           ++ intros Hin. rewrite Forall_forall in Hvarmap1. apply Hvarmap1 in Hin. lia.
           ++ inversion H0; subst; assumption.
           (* ++ eapply Forall2_select2. eapply Forall2_impl; [|eassumption].
             intros v t Hvt. apply read_dvar_below_val in Hvt. rewrite dvar_below_free in Hvt.
             apply Hvt; lia. *)
        -- inversion H2; subst. constructor.
      * and_left as Hreach; [eapply same_read_update; eassumption|].
        inversion H2; subst; simpl in *.
        split; [simpl; intros rid2 Hrid2a Hrid2b; rewrite nth_error_update_None in Hrid2b; tauto|].
        eexists; split; [|left; rewrite fill_compose; simpl; apply beta_hnf_ctx, beta_hnf_red, beta_red_lam].
        unfold subst1, lift_subst. rewrite subst_subst.
        erewrite subst_ext; [eapply read_thread_term|].
        -- eapply nth_error_update; eassumption.
        -- inversion H0; subst. assumption.
        -- constructor.
           ++ eapply same_read_plus_val_1; [eassumption|eassumption|eassumption|].
             intros a Ha; unfold points, points_to; rewrite H. right; constructor; assumption.
           ++ eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
             intros a Ha; unfold points, points_to; rewrite H; left; constructor.
             apply Exists_exists; eexists; split; eassumption.
        -- eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H. right; constructor; assumption.
        -- intros x; specialize (H3 x); inversion H3; subst; assumption.
        -- intros [|n]; unfold comp; simpl; [rewrite read_env_0; reflexivity|].
           rewrite read_env_S. rewrite subst_ren.
           erewrite subst_ext; [apply subst_id|].
           intros n2; unfold comp; simpl. destruct n2; reflexivity.
      * apply Hid; reflexivity.
    + and_left as Hreach. {
        eapply same_read_unchanged; [assumption|].
        dedup common; [eapply unchanged_from_plus_trans;
                       [|eapply unchanged_from_plus_update, read_thread_same; [|eapply Hread|]; [simpl; lia|]]; exact common|].
        eapply unchanged_from_makelazy; eassumption.
      }
      match goal with [ Hreach : same_read_plus st ?st2 defs rid |- _ ] =>
                      refine ((fun (Hreadnew : read_thread st2 defs varmap (length (st_rthreads st)) _) => _) _) end; cycle 1.
      {
        eapply read_thread_term; simpl.
        * rewrite nth_error_update3 by (apply nth_error_Some3 in H; lia).
          apply nth_error_extend.
        * inversion H0; subst; assumption.
        * eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
          intros a Ha; unfold points, points_to; rewrite H; left; constructor.
          apply Exists_exists; eexists; split; eassumption.
        * constructor.
        * intros x; specialize (H3 x); inversion H3; subst; assumption.
      }
      split.
      {
        intros rid2 Hrid2a Hrid2b. unfold exit_rthread in Hrid2b; simpl in Hrid2b.
        rewrite nth_error_update3 in Hrid2b by congruence.
        rewrite nth_error_app2 in Hrid2b by (rewrite nth_error_None in Hrid2a; assumption).
        destruct (rid2 - length (st_rthreads st)) as [|n] eqn:Hr; simpl in *; [|destruct n; simpl in *; congruence].
        assert (rid2 = length (st_rthreads st)) by (rewrite nth_error_None in Hrid2a; lia). subst.
        eexists. eexists. split; [|apply Hreadnew]. split; assumption.
      }
      eexists. split.
      * eapply read_thread_term; [eapply nth_error_update, nth_error_app_Some; eassumption| | | |].
        -- inversion H0; subst; assumption.
        -- eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H; left; constructor.
           apply Exists_exists; eexists; split; eassumption.
        -- constructor.
           ++ eapply read_val_thread. apply Hreadnew.
           ++ eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
             intros a Ha; unfold points, points_to; rewrite H. right; assumption.
        -- intros x; specialize (H3 x); inversion H3; subst; assumption.
      * right. rewrite fill_compose. reflexivity.
    + and_left as Hreach. {
        eapply same_read_unchanged; [assumption|].
        dedup common; [eapply unchanged_from_plus_trans;
                       [|eapply unchanged_from_plus_update, read_thread_same; [apply makenlazy_freename|eapply Hread|]]; exact common|].
        eapply unchanged_from_only_extended; [eassumption|].
        apply only_extended_makenlazy.
      }
      and_right; cycle 1.
      * eexists; split; [|right; reflexivity].
        eapply read_thread_val.
        -- eapply nth_error_update, only_extended_makenlazy; eassumption.
        -- simpl. constructor. eapply read_val_makenlazy_changed.
           ++ eassumption.
           ++ eapply Forall_forall. intros t Ht x; specialize (H3 x); inversion H3; subst; eapply Forall_forall; eassumption.
           ++ inversion H0; subst. rewrite Forall_forall. assumption.
           ++ eassumption.
           ++ eapply Forall_forall. intros v Hv a Ha.
             unfold points, points_to. rewrite H. simpl. left. constructor.
             eapply Exists_exists; eexists; split; eassumption.
           ++ eapply only_changed_update.
           ++ eassumption.
        -- eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H; right; assumption.
      * intros (t2 & Ht2 & _).
        inversion Ht2; subst; simpl in *; erewrite nth_error_update in H4;
          try (eapply only_extended_makenlazy; eassumption); try congruence; injection H4 as H4; subst.
        inversion H5; subst.
        intros rid2 Hrid2a Hrid2b.
        rewrite nth_error_update3 in Hrid2b by congruence.
        apply makenlazy_new_threads in Hrid2b; [|eassumption].
        eapply Forall2_In_left_transparent; [|eassumption|eassumption].
        intros t Ht. exists t. exists varmap. inversion Ht; subst. split; [|assumption].
        split; [|eassumption]. eapply Forall_impl; [|eassumption].
        intros; simpl in *. eapply lt_le_trans; [eassumption|].
        apply makenlazy_freename.
    + and_left as Hreach. {
        eapply same_read_unchanged; [assumption|]. eapply unchanged_from_plus_only_changed; [eassumption|].
        eapply only_changed_trans; [|eapply only_changed_update].
        apply only_extended_changed, only_extended_makendeeps.
      }
      and_right.
      {
        intros (t2 & Ht2 & _).
        inversion Ht2; subst; simpl in *; erewrite nth_error_update in H4;
          try (eapply only_extended_makendeeps; eassumption); try congruence. injection H4 as H4; subst.
        inversion H7; subst.
        intros rid2 Hrid2a Hrid2b.
        rewrite nth_error_update3 in Hrid2b by congruence.
        apply makendeeps_new_threads in Hrid2b; [|eassumption].
        destruct Hrid2b as (vs & Hvs1 & Hvs2 & Hvs3).
        eapply Forall3_impl, Forall3_select23 in H16; [|intros pt vdeeps tdeep (_ & Hreaddeep & _); exact Hreaddeep].
        eapply Forall2_In_left_transparent; [|apply H16|apply Hvs3].
        intros t3 Ht3. inversion Ht3; subst. eexists; eexists. split; [|eassumption].
        apply varmap_ok_app.
        * split; [|assumption]. eapply Forall_impl; [|eassumption].
          intros; simpl in *. eapply lt_le_trans; [|apply makendeeps_freename]. assumption.
        * eapply Forall_impl; [|eassumption]. intros x Hx; simpl in *; split; [tauto|].
          intros Hx2. rewrite Forall_forall in Hvarmap1. apply Hvarmap1 in Hx2. lia.
        * assumption.
      }
      eexists; split; [|right; reflexivity].
      simpl.
      refine (eq_rect _ (read_thread _ _ _ _) _ _ _); [|apply fill_compose with (h2 := h_switch h_hole _)].
      eapply read_thread_term.
      * simpl. erewrite nth_error_update; [reflexivity|].
        eapply only_extended_makendeeps; eassumption.
      * inversion H0; subst; assumption.
      * eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
        intros v a Ha1 Ha2; unfold points, points_to; rewrite H; left; constructor.
        apply Exists_exists; eexists; split; eassumption.
      * erewrite map_ext; [econstructor|].
        -- eapply same_read_plus_val_Forall2_1; [eassumption|eassumption|eassumption|].
           intros v a Ha1 Ha2; unfold points, points_to; rewrite H; left; constructor.
           apply Exists_exists; eexists; split; eassumption.
        -- eapply same_read_plus_cont_1; [eassumption|eassumption|eassumption|].
           intros a Ha; unfold points, points_to; rewrite H; right; assumption.
        -- eapply Forall3_map3 with (f := fun '(pt, vdeeps) => _).
           eapply Forall2_select12combine.
           eapply Forall2_impl; [|eapply Forall2_and_Forall_left; [eapply Forall2_and_Forall_right; [eapply read_val_makendeeps_changed|]|]].
           ++ simpl. intros pt2 vdeeps [[[Hlen Hreadval] Hdeeps] Hpt2].
             repeat split; cycle 2.
             ** apply star_refl.
             ** eapply (proj1 Hpt2).
             ** eapply (proj1 Hdeeps).
             ** eapply (proj2 Hdeeps).
             ** eapply (proj2 Hpt2).
             ** apply Hlen.
             ** eapply Hreadval.
           ++ simpl. lia.
           ++ rewrite Forall_forall. intros pt Hpt.
             split.
             ** inversion H0; subst. apply H8. destruct pt; assumption.
             ** intros x. specialize (H3 x); inversion H3; subst.
                rewrite Forall_forall in H7. apply H7; eassumption.
           ++ eassumption.
           ++ eapply Forall_forall; intros v Hv a Ha.
             unfold points, points_to. rewrite H. left. constructor.
             eapply Exists_exists; eexists; split; eassumption.
           ++ eapply only_changed_update.
           ++ assumption.
           ++ apply Hdefsok.
           ++ assumption.
           ++ assumption.
           ++ apply -> Forall_and; split; [|apply makendeeps_dvar_nodup].
             eapply Forall_impl; [|rewrite <- Forall_and; split; [apply makendeeps_dvar_below|apply makendeeps_dvar_above]].
             intros [vs v] [Hvs1 Hvs2]; simpl in *.
             apply -> Forall_and; split; [apply -> Forall_and; split; [|assumption]|].
             ** eapply Forall_impl; [|apply Hvs1]. intros x Hx; unfold defs_ok in Hdefsok; simpl in *; lia.
             ** eapply Forall_impl; [|apply Hvs1]. intros x Hx1 Hx2.
                rewrite Forall_forall in Hvarmap1; apply Hvarmap1 in Hx2. simpl in *; lia.
           ++ eapply Forall_forall. intros [p t2] Hpt2.
             split.
             ** inversion H0; subst. apply H8. assumption.
             ** intros x. specialize (H3 x); inversion H3; subst.
                rewrite Forall_forall in H7. apply H7; assumption.
        -- intros [p t2]; simpl; reflexivity.
      * intros x; specialize (H3 x); inversion H3; subst; assumption.
Qed.

Lemma beta_hctx :
  forall h t1 t2, beta t1 t2 -> beta (fill_hctx h t1) (fill_hctx h t2).
Proof.
  induction h; intros t1 t2 Hbeta.
  - assumption.
  - simpl. constructor. apply IHh; assumption.
  - simpl. constructor. apply IHh; assumption.
Qed.

Lemma star_beta_hctx :
  forall h t1 t2, star beta t1 t2 -> star beta (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros h t1 t2 H. eapply star_map_impl with (f := fun t => fill_hctx h t); [|eassumption].
  apply beta_hctx.
Qed.

Lemma star_beta_read_env :
  forall e1 e2, Forall2 (star beta) e1 e2 -> forall n, star beta (read_env e1 n) (read_env e2 n).
Proof.
  intros e1 e2 H n. unfold read_env.
  destruct (nth_error e1 n) eqn:Hn.
  * eapply nth_error_Forall2 in Hn; [|eassumption].
    destruct Hn as (? & -> & Hn). assumption.
  * replace (nth_error e2 n) with (@None term) by (symmetry; apply (nth_error_Forall2_None H); assumption).
    apply Forall2_length in H. rewrite H. constructor.
Qed.

Lemma Forall4_and :
  forall A B C D (P Q : A -> B -> C -> D -> Prop) l1 l2 l3 l4, Forall4 P l1 l2 l3 l4 -> Forall4 Q l1 l2 l3 l4 -> Forall4 (fun a b c d => P a b c d /\ Q a b c d) l1 l2 l3 l4.
Proof.
  intros A B C D P Q l1 l2 l3 l4 H1 H2; induction H1; simpl in *; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall4_unselect123 :
  forall A B C D (P : A -> B -> C -> Prop) (R : A -> B -> C -> D -> Prop) (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D), Forall3 P l1 l2 l3 -> Forall4 R l1 l2 l3 l4 -> Forall4 (fun a b c _ => P a b c) l1 l2 l3 l4.
Proof.
  intros A B C D P R l1 l2 l3 l4 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.

Lemma Forall2_eq :
  forall (A : Type) (l1 l2 : list A), Forall2 eq l1 l2 -> l1 = l2.
Proof.
  intros A l1 l2 H; induction H.
  - reflexivity.
  - congruence.
Qed.

Lemma read_inj_aux :
  forall st defs, (forall varmap a t, read_thread st defs varmap a t -> forall t2, read_thread st defs varmap a t2 -> t = t2) /\
             (forall varmap v t, read_val st defs varmap v t -> forall t2, read_val st defs varmap v t2 -> t = t2) /\
             (forall varmap c h, read_cont st defs varmap c h -> forall h2, read_cont st defs varmap c h2 -> h = h2).
Proof.
  intros st defs. read_ind.
  - intros t2 Ht2. inversion Ht2; subst; try congruence.
    assert (v0 = v) by congruence; subst.
    assert (c0 = c) by congruence; subst.
    f_equal; [apply IHc|apply IHv]; assumption.
  - intros t2 Ht2. inversion Ht2; subst; try congruence.
    assert (t0 = t) by congruence; subst.
    assert (e0 = e) by congruence; subst.
    assert (c0 = c) by congruence; subst.
    f_equal; [apply IHc; assumption|].
    f_equal. f_equal.
    assert (Heq := Forall3_from_Forall2 _ _ _ _ _ _ _ _ IHe H1).
    eapply Forall3_impl in Heq; [|intros v t1 t2 [IH Hread]; apply IH, Hread].
    apply Forall3_select23, Forall2_eq in Heq. assumption.
  - intros t2 Ht2; inversion Ht2; subst.
    apply IH; assumption.
  - intros t2 Ht2. inversion Ht2; subst.
    assert (Heq := Forall3_from_Forall2 _ _ _ _ _ _ _ _ IHe H3).
    eapply Forall3_impl in Heq; [|intros v t1 t2 [IH Hread]; apply IH, Hread].
    apply Forall3_select23, Forall2_eq in Heq. congruence.
  - intros t2 Ht2. inversion Ht2; subst.
    assert (Heq := Forall3_from_Forall2 _ _ _ _ _ _ _ _ IHe H3).
    eapply Forall3_impl in Heq; [|intros v t1 t2 [IH Hread]; apply IH, Hread].
    apply Forall3_select23, Forall2_eq in Heq. congruence.
  - intros t2 Ht2. inversion Ht2; subst. f_equal.
    apply IHc. assumption.
  - intros h2 H; inversion H; reflexivity.
  - intros h2 H. inversion H; subst.
    f_equal; [apply IHc; assumption|].
    f_equal. apply IHv; assumption.
  - intros h2 H. inversion H; subst.
    f_equal; [apply IHc; assumption|].
    assert (Heq := Forall3_from_Forall2 _ _ _ _ _ _ _ _ IHe H6).
    eapply Forall3_impl in Heq; [|intros v t1 t2 [IH Hread]; apply IH, Hread].
    apply Forall3_select23, Forall2_eq in Heq. subst. reflexivity.
Qed.

Lemma read_inj_thread :
  forall st defs varmap a t1 t2, read_thread st defs varmap a t1 -> read_thread st defs varmap a t2 -> t1 = t2.
Proof.
  intros st defs varmap a t1 t2 H1 H2. eapply (proj1 (read_inj_aux st defs)); eassumption.
Qed.

Lemma dvar_free_beta :
  forall x t1 t2, beta t1 t2 -> dvar_free x t1 -> dvar_free x t2.
Proof.
  intros x t1 t2 H; induction H; intros Hdv.
  - inversion Hdv; subst. constructor; tauto.
  - inversion Hdv; subst. constructor; tauto.
  - inversion Hdv; subst. constructor; tauto.
  - inversion Hdv; subst. inversion H1; subst. apply dvar_free_subst; [|assumption].
    intros [|n]; simpl; [assumption|constructor].
  - inversion Hdv; subst. constructor.
    rewrite Forall_app_iff, Forall_cons_iff in *. tauto.
  - inversion Hdv; subst. constructor; tauto.
  - inversion Hdv; subst. constructor; [assumption|].
    rewrite Forall_app_iff, Forall_cons_iff in *. simpl in *; tauto.
  - inversion Hdv; subst. rewrite Forall_app_iff, Forall_cons_iff in H2. simpl in *.
    apply dvar_free_subst; [|tauto].
    apply dvar_free_read_env.
    inversion H1; subst. assumption.
Qed.

Lemma dvar_free_star_beta :
  forall x t1 t2, star beta t1 t2 -> dvar_free x t1 -> dvar_free x t2.
Proof.
  intros. eapply star_preserve; [|eassumption|eassumption].
  apply dvar_free_beta.
Qed.


Lemma stable_beta_hnf_aux :
  forall st st2 defs rid,
    st_freename st <= st_freename st2 ->
    same_read_plus st st2 defs rid ->
    only_changed st st2 rid ->
    (forall varmap t,
        varmap_ok (st_freename st) varmap -> read_thread st defs varmap rid t ->
        exists t2, read_thread st2 defs varmap rid t2 /\ reflc beta_hnf t t2) ->
    (forall varmap2 rid2 t, read_thread st defs varmap2 rid2 t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_thread st2 defs varmap2 rid2 t2 /\ star beta t t2) /\
    (forall varmap2 v t, read_val st defs varmap2 v t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_val st2 defs varmap2 v t2 /\ star beta t t2) /\
    (forall varmap2 c h, read_cont st defs varmap2 c h -> varmap_ok (st_freename st) varmap2 -> exists h2, read_cont st2 defs varmap2 c h2 /\ (forall t, star beta (fill_hctx h t) (fill_hctx h2 t))).
Proof.
  intros st st2 defs rid2 Hst12 Hsame Honly Hred.
  read_ind; intros Hvok.
  - destruct (Nat.eq_dec rid2 rid).
    {
      subst.
      assert (Hread : read_thread st defs varmap rid (fill_hctx h t)) by (eapply read_thread_val; eassumption).
      apply Hred in Hread; [|assumption].
      destruct Hread as (t2 & Ht2a & Ht2b); exists t2; split; [assumption|].
      destruct Ht2b; [|subst; constructor]. apply star_1, beta_hnf_beta, H.
    }
    destruct IHv as (t2 & IHv1 & IHv2); [assumption|].
    destruct IHc as (h2 & IHc1 & IHc2); [assumption|].
    exists (fill_hctx h2 t2).
    split.
    + apply Honly in Hnth; [|assumption].
      eapply read_thread_val; eassumption.
    + eapply star_compose; [apply IHc2|].
      apply star_beta_hctx. assumption.
  - destruct (Nat.eq_dec rid2 rid).
    {
      subst.
      assert (Hread : read_thread st defs varmap rid (fill_hctx h (subst (read_env el) t))) by
          (eapply read_thread_term; eassumption).
      apply Hred in Hread; [|assumption].
      destruct Hread as (t2 & Ht2a & Ht2b); exists t2; split; [assumption|].
      destruct Ht2b; [|subst; constructor]. apply star_1, beta_hnf_beta, H.
    }
    destruct IHc as (h2 & IHc1 & IHc2); [assumption|].
    eapply Forall2_impl in IHe; [|intros ? ? IH; exact (IH Hvok)].
    apply Forall2_exists_Forall3 in IHe. destruct IHe as (el2 & IHe).
    exists (fill_hctx h2 (subst (read_env el2) t)).
    split.
    + apply Honly in Hnth; [|assumption].
      eapply read_thread_term; try eassumption.
      eapply Forall3_select13, Forall3_impl, IHe. intros; simpl in *; tauto.
    + eapply star_compose; [apply IHc2|].
      apply star_beta_hctx. apply beta_subst2.
      apply star_beta_read_env.
      eapply Forall3_select23, Forall3_impl, IHe. intros; simpl in *; tauto.
  - destruct IH as (t2 & IH1 & IH2); [assumption|].
    exists t2. split; [|assumption]. constructor. assumption.
  - eapply Forall2_impl in IHe; [|intros ? ? IH; exact (IH Hvok)].
    eapply Forall2_exists_Forall3 in IHe. destruct IHe as (el2 & IHe).
    destruct IHdeep as (tdeep2 & IHdeep1 & IHdeep2); [apply varmap_ok_cons; tauto|].
    exists (subst (read_env el2) (abs t)). split.
    + eapply read_val_clos; try eassumption.
      * eapply Forall3_select13, Forall3_impl, IHe; intros; simpl in *; tauto.
      * eapply star_compose; [|eapply star_impl; [|eassumption]; intros; left; assumption].
        eapply star_compose; [|eassumption]. eapply convertible_sym. eapply star_impl; [intros ? ? H; left; exact H|].
        eapply beta_subst2. intros [|n1]; [constructor|]. simpl. unfold comp; simpl.
        rewrite !ren_term_is_subst. eapply star_map_impl; [intros; apply beta_subst1; eassumption|].
        apply star_beta_read_env.
        eapply Forall3_select23, Forall3_impl, IHe. intros; simpl in *; tauto.
      * lia.
(*      * eapply Forall2_select2, Forall2_impl; [|eapply Forall2_and_Forall_left; [eapply Forall3_select23, Forall3_impl; [|eassumption]|eassumption]];
          [|intros v t5 t6 [? Hstar]; exact Hstar].
        intros ? ? (? & ?); eapply dvar_free_star_beta; eassumption. *)
    + eapply beta_subst2.
      apply star_beta_read_env.
      eapply Forall3_select23, Forall3_impl, IHe. intros; simpl in *; tauto.
  - eapply Forall2_impl in IHe; [|intros ? ? IH; exact (IH Hvok)].
    eapply Forall2_exists_Forall3 in IHe. destruct IHe as (el2 & IHe).
    exists (constr tag el2). split.
    + constructor. eapply Forall3_select13, Forall3_impl; [|eassumption].
      intros; simpl in *; tauto.
    + apply star_beta_constr. eapply Forall3_select23, Forall3_impl; [|eassumption].
      intros; simpl in *; tauto.
  - destruct IHc as (h2 & IHc1 & IHc2); [assumption|].
    exists (fill_hctx h2 (match index Nat.eq_dec varmap x with Some n => var n | None => dvar x end)).
    split; [|apply IHc2].
    inversion IHuf; subst; [econstructor; [eassumption|rewrite <- H2; constructor|lia|eassumption]|].
    rewrite <- H in *.
    inversion Huf; subst. destruct H2 as (tuf & IHuf1 & IHuf2); [assumption|].
    econstructor; [eassumption| |lia|congruence]. rewrite <- H. econstructor; split; [eassumption|].
    split; [|tauto].
    eapply star_compose; [|eapply star_impl; [|eassumption]; intros; left; assumption].
    eapply star_compose; [|apply H4].
    eapply convertible_sym. eapply star_impl; [|apply IHc2]. intros; left; assumption.
  - exists h_hole. split; [constructor|]. intros; simpl; constructor.
  - destruct IHv as (t2 & IHv1 & IHv2); [assumption|].
    destruct IHc as (h2 & IHc1 & IHc2); [assumption|].
    exists (compose_hctx h2 (h_app h_hole t2)). split.
    + constructor; assumption.
    + intros t5. rewrite !fill_compose; simpl.
      eapply star_compose; [apply IHc2|]. apply star_beta_hctx, star_beta_app; [constructor|assumption].
  - destruct IHc as (h2 & IHc1 & IHc2); [assumption|].
    eapply Forall2_impl in IHe; [|intros ? ? IH; exact (IH Hvok)].
    eapply Forall2_exists_Forall3 in IHe. destruct IHe as (el2 & IHe).
    exists (compose_hctx h2 (h_switch h_hole (map (fun '(p, t0) => (p, subst (liftn_subst p (read_env el2)) t0)) bs))).
    split.
    + eapply Forall3_and in IHdeep; [|apply Hdeeps].
      eapply Forall3_impl in IHdeep; cycle 1.
      { intros ? ? ? [IH1 IH2]. refine (IH2 _). apply varmap_ok_app; try tauto.
        eapply Forall_impl; [|apply IH1]. intros; simpl in *; tauto. }
      apply Forall3_exists_Forall4 in IHdeep. destruct IHdeep as (tdeeps2 & IHdeep).
      econstructor.
      * eapply Forall3_select13, Forall3_impl; [|eassumption]. intros; simpl in *; tauto.
      * assumption.
      * eapply Forall4_select124, Forall4_impl, Forall4_and; [|eapply Forall4_unselect123; eassumption|apply IHdeep].
        intros pt vdeeps tdeep tdeep2 ((Hlen & Hread & Hconv & Hclosed & Hvars1 & Hvars2 & Hdv) & (Hread2 & Hstar)); simpl in *.
        repeat split; try assumption.
        -- eapply star_compose; [|eapply star_impl; [|eassumption]; intros; left; assumption].
           eapply star_compose; [|eassumption]. eapply convertible_sym. eapply star_impl; [intros ? ? H; left; exact H|].
           apply beta_subst2.
           intros n. unfold liftn_subst. destruct le_lt_dec; [|apply star_refl].
           rewrite !ren_term_is_subst. apply star_beta_subst1.
           apply star_beta_read_env.
           eapply Forall3_select23, Forall3_impl, IHe. intros; simpl in *; tauto.
        -- eapply Forall_impl; [|eassumption].
           intros x [Hx1 Hx2]; simpl in *; split; [lia|assumption].
(*           eapply Forall2_select2, Forall2_impl; [|eapply Forall2_and_Forall_left; [eapply Forall3_select23, Forall3_impl; [|eassumption]|exact Hx]];
             [|intros v t5 t6 [? Hstar]; exact Hstar].
           intros ? ? (? & ?); eapply dvar_free_star_beta; eassumption. *)
    + intros t5. rewrite !fill_compose; simpl.
      eapply star_compose; [apply IHc2|]. apply star_beta_hctx, star_beta_switch; [constructor|].
      rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same. apply Forall_True. intros [p t0]; simpl.
      split; [reflexivity|]. apply beta_subst2.
      intros n. unfold liftn_subst. destruct le_lt_dec; [|apply star_refl].
      rewrite !ren_term_is_subst. apply star_beta_subst1.
      apply star_beta_read_env.
      eapply Forall3_select23, Forall3_impl, IHe. intros; simpl in *; tauto.
Qed.

Definition state_wf st defs :=
  forall rid, nth_error (st_rthreads st) rid <> None -> exists t varmap, varmap_ok (st_freename st) varmap /\ read_thread st defs varmap rid t.


Lemma stable_beta_hnf_aux2 :
  forall st defs varmap rid t,
    defs_ok defs st ->
    varmap_ok (st_freename st) varmap -> read_thread st defs varmap rid t ->
    (forall varmap2 rid2 t, read_thread st defs varmap2 rid2 t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_thread (step_r st rid) defs varmap2 rid2 t2 /\ star beta t t2) /\
    (forall varmap2 v t, read_val st defs varmap2 v t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_val (step_r st rid) defs varmap2 v t2 /\ star beta t t2) /\
    (forall varmap2 c h, read_cont st defs varmap2 c h -> varmap_ok (st_freename st) varmap2 -> exists h2, read_cont (step_r st rid) defs varmap2 c h2 /\ (forall t, star beta (fill_hctx h t) (fill_hctx h2 t))).
Proof.
  intros st defs varmap rid t H1 H2 H3.
  eapply stable_beta_hnf_aux.
  - apply step_r_freename.
  - eapply step_r_beta_hnf.
    + assumption.
    + apply H2.
    + apply H2.
    + reflexivity.
    + eassumption.
  - apply only_changed_step_r.
  - intros varmap2 t2 Hvarmap2 Hread.
    eapply step_r_beta_hnf.
    + eassumption.
    + apply Hvarmap2.
    + apply Hvarmap2.
    + reflexivity.
    + assumption.
Qed.

Lemma stable_beta_hnf_aux3 :
  forall st defs rid,
    defs_ok defs st -> state_wf st defs ->
    (forall varmap2 rid2 t, read_thread st defs varmap2 rid2 t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_thread (step_r st rid) defs varmap2 rid2 t2 /\ star beta t t2) /\
    (forall varmap2 v t, read_val st defs varmap2 v t -> varmap_ok (st_freename st) varmap2 -> exists t2, read_val (step_r st rid) defs varmap2 v t2 /\ star beta t t2) /\
    (forall varmap2 c h, read_cont st defs varmap2 c h -> varmap_ok (st_freename st) varmap2 -> exists h2, read_cont (step_r st rid) defs varmap2 c h2 /\ (forall t, star beta (fill_hctx h t) (fill_hctx h2 t))).
Proof.
  intros st defs rid H1 H2. specialize (H2 rid).
  destruct nth_error eqn:Hrid.
  - destruct H2 as (t & varmap & Hvarmap & Ht); [congruence|].
    eapply stable_beta_hnf_aux2; eassumption.
  - unfold step_r; rewrite Hrid.
    repeat split; intros; eexists; split; try eassumption; intros; apply star_refl.
Qed.

Lemma state_wf_preserve :
  forall st defs rid,
    defs_ok defs st -> state_wf st defs ->
    state_wf (step_r st rid) defs.
Proof.
  intros st defs rid H1 H2. destruct (nth_error (st_rthreads st) rid) eqn:Hrid; [|unfold step_r; rewrite Hrid; assumption].
  destruct (H2 rid) as (t & varmap & Hvarmap & Ht); [congruence|].
  intros rid2 Hrid2. destruct (nth_error (st_rthreads st) rid2) eqn:Hrid3.
  - destruct (H2 rid2) as (t2 & varmap2 & Hvarmap2 & Ht2); [congruence|].
    eapply stable_beta_hnf_aux2 in Ht; try assumption.
    destruct Ht as (Ht & _ & _). apply Ht in Ht2; [|assumption].
    destruct Ht2 as (t3 & Ht3 & _). exists t3. exists varmap2. split; [|assumption].
    split; [|apply Hvarmap2]. eapply Forall_impl; [|apply Hvarmap2].
    intros; simpl in *; eapply lt_le_trans; [eassumption|]. apply step_r_freename.
  - eapply step_r_beta_hnf.
    + eassumption.
    + apply Hvarmap.
    + apply Hvarmap.
    + reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
Qed.

Lemma step_r_correct_val :
  forall st defs rid varmap v t,
    defs_ok defs st -> state_wf st defs ->
    read_val st defs varmap v t -> varmap_ok (st_freename st) varmap ->
    exists t2, read_val (step_r st rid) defs varmap v t2 /\ star beta t t2.
Proof.
  intros st defs rid varmap v t Hdefsok Hwf Hread Hvarmap.
  refine (proj1 (proj2 (stable_beta_hnf_aux3 st defs rid _ _)) _ _ _ Hread Hvarmap); assumption.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| reflect_true : P -> reflect P true
| reflect_false : ~ P -> reflect P false.

Inductive read_cthread st defs : cthread -> bool -> Prop :=
| read_cthread_done : forall b, read_cthread st defs (cthread_done b) b
| read_cthread_and_true :
    forall ct1 ct2, read_cthread st defs ct1 true -> read_cthread st defs ct2 true ->
               read_cthread st defs (cthread_and ct1 ct2) true
| read_cthread_and_false_1 :
    (* Note: we don't require read_cthread ct2, to mimic the rule that reduces to false when ct1 is false *)
    forall ct1 ct2, read_cthread st defs ct1 false -> read_cthread st defs (cthread_and ct1 ct2) false
| read_cthread_and_false_2 :
    forall ct1 ct2, read_cthread st defs ct2 false -> read_cthread st defs (cthread_and ct1 ct2) false
| read_cthread_or_false :
    forall ct1 ct2, read_cthread st defs ct1 false -> read_cthread st defs ct2 false ->
               read_cthread st defs (cthread_or ct1 ct2) false
| read_cthread_or_true_1 :
    forall ct1 ct2, read_cthread st defs ct1 true -> read_cthread st defs (cthread_or ct1 ct2) true
| read_cthread_or_true_2 :
    forall ct1 ct2, read_cthread st defs ct2 true -> read_cthread st defs (cthread_or ct1 ct2) true
| read_cthread_reduce :
    forall v1 v2 varmap1 varmap2 b,
      (forall t1 t2,
          read_val st defs varmap1 v1 t1 -> read_val st defs varmap2 v2 t2 ->
          reflect (convertible (betaiota defs) t1 t2) b) ->
      read_cthread st defs (cthread_reduce v1 v2 varmap1 varmap2) b.

(*
Lemma lift_dvars_cons :
  forall t k vars x,
    closed_at t k -> x \notin vars ->
    subst (liftn_subst k (scons (dvar x) (fun n => var (S n)))) (lift_dvars (x :: vars) k t) = lift_dvars vars (S k) t.
Proof.
  intros t; induction t using term_ind2; intros k vars x Hclosed Hx; simpl in *.
  - unfold liftn_subst, scons. destruct le_lt_dec; [|reflexivity].
    inversion Hclosed; subst. lia.
  - destruct Nat.eq_dec.
    + subst. rewrite index_notin_None by assumption.
      simpl. unfold liftn_subst.
      destruct le_lt_dec; [|lia].
      replace (k + 0 - k) with 0 by lia. simpl. reflexivity.
    + destruct index.
      * simpl. unfold liftn_subst.
        destruct le_lt_dec; [|lia]. replace (k + S n1 - k) with (S n1) by lia. simpl.
        rewrite plus_ren_correct. f_equal. lia.
      * reflexivity.
  - f_equal. erewrite <- subst_ext; [|apply liftn_subst_1]. erewrite subst_ext; [|apply liftn_subst_add].
    apply IHt; [inversion Hclosed; subst; assumption|assumption].
  - f_equal; [apply IHt1|apply IHt2]; try assumption; inversion Hclosed; subst; assumption.
  - f_equal. rewrite map_map. eapply map_ext_in. intros t Ht.
    rewrite Forall_forall in H. apply H; try assumption.
    inversion Hclosed; subst. apply H3; assumption.
  - f_equal; [apply IHt; [inversion Hclosed; subst|]; assumption|].
    rewrite map_map. eapply map_ext_in. intros [p t2] Hpt. simpl. f_equal.
    rewrite Forall_forall in H. specialize (H (p, t2) Hpt). simpl in H.
    erewrite subst_ext; [|apply liftn_subst_add].
    rewrite H; [f_equal; lia| |assumption]. inversion Hclosed; subst. apply H4; assumption.
Qed.
 *)

Lemma lift_dvars_app :
  forall t k vars1 vars2,
    lift_dvars (vars1 ++ vars2) k t = lift_dvars vars2 (length vars1 + k) (lift_dvars vars1 k t).
Proof.
  intros t; induction t using term_ind2; intros k vars1 vars2; simpl in *.
  - reflexivity.
  - rewrite index_app.
    destruct (index _ vars1 n); [reflexivity|].
    simpl. destruct (index _ vars2 n); simpl; [|reflexivity].
    f_equal. lia.
  - f_equal. rewrite IHt. f_equal. lia.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. rewrite map_map.
    eapply map_ext_in; rewrite Forall_forall in H; intros; apply H; assumption.
  - f_equal; [apply IHt|].
    rewrite map_map.
    eapply map_ext_in; rewrite Forall_forall in H; intros [p t2] Hpt2; f_equal.
    specialize (H (p, t2) Hpt2). rewrite H. f_equal; simpl.
    lia.
Qed.

Lemma lift_dvars_cons :
  forall t k x vars,
    lift_dvars (x :: vars) k t = lift_dvars vars (S k) (lift_dvars (x :: nil) k t).
Proof.
  intros; apply lift_dvars_app with (vars1 := x :: nil).
Qed.

Lemma reflect_iff :
  forall P Q b, P <-> Q -> reflect P b <-> reflect Q b.
Proof.
  intros P Q H; split; intros H1; inversion H1; subst; constructor; tauto.
Qed.

Lemma betaiota_abs_red :
  forall defs t1 t2, betaiota defs (abs t1) t2 -> exists t3, t2 = abs t3 /\ betaiota defs t1 t3.
Proof.
  intros defs t1 t2 [H | H]; inversion H; subst; eexists; split; try reflexivity; constructor; assumption.
Qed.

Lemma betaiota_star_abs_red :
  forall defs t1 t2, star (betaiota defs) (abs t1) t2 -> exists t3, t2 = abs t3 /\ star (betaiota defs) t1 t3.
Proof.
  intros defs t1 t2 H; remember (abs t1) as t3; revert t1 Heqt3; induction H; intros t1 ->.
  - exists t1. split; [reflexivity|apply star_refl].
  - apply betaiota_abs_red in H. destruct H as (t2 & -> & H).
    destruct (IHstar _ eq_refl) as (t3 & Ht3 & Hstar).
    exists t3. split; [assumption|]. econstructor; eassumption.
Qed.

Lemma convertible_abs_iff :
  forall defs t1 t2, convertible (betaiota defs) (abs t1) (abs t2) <-> convertible (betaiota defs) t1 t2.
Proof.
  intros defs t1 t2; split; intros H.
  - apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
    destruct H as (t3 & Ht3a & Ht3b).
    apply betaiota_star_abs_red in Ht3a. destruct Ht3a as (t4 & -> & Ht4a).
    apply betaiota_star_abs_red in Ht3b. destruct Ht3b as (t5 & [=<-] & Ht4b).
    eapply common_reduce_convertible; eassumption.
  - eapply star_map_impl; [|eassumption].
    intros t3 t4 [H1 | H1]; destruct H1 as [H1 | H1]; constructor; constructor; constructor; assumption.
Qed.

Lemma betaiota_constr_red_weak :
  forall defs tag l1 t2, betaiota defs (constr tag l1) t2 -> exists l2, t2 = constr tag l2 /\ Forall2 (star (betaiota defs)) l1 l2.
Proof.
  intros defs tag l1 t2 [H | H]; inversion H; subst; eexists; split; try reflexivity;
    apply Forall2_app; try constructor; try apply Forall2_map_same, Forall_True, star_refl;
      apply star_1; constructor; assumption.
Qed.

Lemma betaiota_star_constr_red :
  forall defs tag l1 t2, star (betaiota defs) (constr tag l1) t2 -> exists l2, t2 = constr tag l2 /\ Forall2 (star (betaiota defs)) l1 l2.
Proof.
  intros defs tag l1 t2 H; remember (constr tag l1) as t3; revert l1 Heqt3; induction H; intros l1 ->.
  - exists l1. split; [reflexivity|apply Forall2_map_same, Forall_True, star_refl].
  - apply betaiota_constr_red_weak in H. destruct H as (l2 & -> & H).
    destruct (IHstar _ eq_refl) as (l3 & Hl3 & Hstar).
    exists l3. split; [assumption|].
    eapply Forall3_select23. eapply Forall3_impl; [|eapply Forall3_from_Forall2; [apply Forall2_comm in H|]; eassumption].
    intros t1 t2 t3 H123; simpl in *. eapply star_compose; apply H123.
Qed.

Lemma star_betaiota_constr :
  forall defs tag (l1 l2 : list term), Forall2 (star (betaiota defs)) l1 l2 -> star (betaiota defs) (constr tag l1) (constr tag l2).
Proof.
  intros defs tag l1 l2 H. eapply star_list; [|eassumption].
  intros l3 l4 x y [Hxy | Hxy]; [left|right]; constructor; assumption.
Qed.

Lemma convertible_constr_iff :
  forall defs tag1 tag2 l1 l2, convertible (betaiota defs) (constr tag1 l1) (constr tag2 l2) <-> (tag1 = tag2 /\ Forall2 (convertible (betaiota defs)) l1 l2).
Proof.
  intros defs tag1 tag2 l1 l2; split; intros H.
  - apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
    destruct H as (t3 & Ht3a & Ht3b).
    apply betaiota_star_constr_red in Ht3a. destruct Ht3a as (l4 & -> & Ht5a).
    apply betaiota_star_constr_red in Ht3b. destruct Ht3b as (l5 & [=<- <-] & Ht5b).
    split; [reflexivity|].
    apply Forall2_comm in Ht5a, Ht5b. eapply Forall3_select23.
    eapply Forall3_impl; [|eapply Forall3_from_Forall2; eassumption].
    intros t1 t2 t3 Ht123. eapply common_reduce_convertible; apply Ht123.
  - destruct H as [-> H].
    assert (H1 : exists l3, Forall3 (fun t1 t2 t3 => star (betaiota defs) t1 t3 /\ star (betaiota defs) t2 t3) l1 l2 l3).
    + apply Forall2_exists_Forall3. eapply Forall2_impl; [|eassumption].
      intros t1 t2 Ht12. eapply convertible_confluent_common_reduce in Ht12; [|apply beta_iota_confluent]. assumption.
    + destruct H1 as (l3 & Hl3).
      eapply common_reduce_convertible; apply star_betaiota_constr; [eapply Forall3_select13|eapply Forall3_select23];
        eapply Forall3_impl; try eassumption; intros; simpl in *; tauto.
Qed.

Lemma abs_constr_not_convertible :
  forall defs tag l t, ~ convertible (betaiota defs) (abs t) (constr tag l).
Proof.
  intros defs tag l t H.
  apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
  destruct H as (t3 & Ht3a & Ht3b).
  apply betaiota_star_abs_red in Ht3a. destruct Ht3a as (t4 & -> & _).
  apply betaiota_star_constr_red in Ht3b. destruct Ht3b as (l4 & Habsurd & _). congruence.
Qed.

Lemma constr_abs_not_convertible :
  forall defs tag l t, ~ convertible (betaiota defs) (constr tag l) (abs t).
Proof.
  intros defs tag l t H. apply convertible_sym in H. eapply abs_constr_not_convertible; eassumption.
Qed.

Inductive hctx_red defs : hctx -> hctx -> Prop :=
| hctx_red_app_1 : forall h1 h2 t, hctx_red defs h1 h2 -> hctx_red defs (h_app h1 t) (h_app h2 t)
| hctx_red_app_2 : forall h t1 t2, betaiota defs t1 t2 -> hctx_red defs (h_app h t1) (h_app h t2)
| hctx_red_switch_1 : forall h1 h2 m, hctx_red defs h1 h2 -> hctx_red defs (h_switch h1 m) (h_switch h2 m)
| hctx_red_switch_2 : forall h m1 m2 p t1 t2, betaiota defs t1 t2 -> hctx_red defs (h_switch h (m1 ++ (p, t1) :: m2)) (h_switch h (m1 ++ (p, t2) :: m2)).

Lemma hctx_red_fill :
  forall defs h1 h2, hctx_red defs h1 h2 -> forall t, betaiota defs (fill_hctx h1 t) (fill_hctx h2 t).
Proof.
  intros defs h1 h2 H t; induction H; simpl in *.
  - inversion IHhctx_red; subst; constructor; constructor; assumption.
  - inversion H; subst; constructor; constructor; assumption.
  - inversion IHhctx_red; subst; constructor; constructor; assumption.
  - inversion H; subst; constructor; constructor; assumption.
Qed.

Definition is_neutral_var (defs : list term) x := match x with var _ => True | dvar n => nth_error defs n = None | _ => False end.

Lemma fill_hctx_var_red :
  forall defs h x t, is_neutral_var defs x -> betaiota defs (fill_hctx h x) t -> exists h2, t = fill_hctx h2 x /\ hctx_red defs h h2.
Proof.
  intros defs h x t Hx H. destruct H as [H | H]; revert t H; induction h; intros t3 H; simpl in *.
  - destruct x; simpl in *; try tauto; inversion H; subst; congruence.
  - inversion H; subst.
    + apply IHh in H3. destruct H3 as (h2 & -> & Hh2).
      exists (h_app h2 t); split; [reflexivity|].
      constructor; assumption.
    + exists (h_app h t2). split; [reflexivity|].
      constructor; constructor; assumption.
  - inversion H; subst.
    + apply IHh in H3. destruct H3 as (h2 & -> & Hh2).
      exists (h_switch h2 l). split; [reflexivity|].
      constructor; assumption.
    + exists (h_switch h (l1 ++ (p, t2) :: l2)). split; [reflexivity|].
      constructor; constructor; assumption.
  - destruct x; simpl in *; try tauto; inversion H.
  - inversion H; subst.
    + apply IHh in H3. destruct H3 as (h2 & -> & Hh2).
      exists (h_app h2 t); split; [reflexivity|].
      constructor; assumption.
    + exists (h_app h t2). split; [reflexivity|].
      constructor; constructor; assumption.
    + destruct h; destruct x; simpl in *; try tauto; congruence.
  - inversion H; subst.
    + apply IHh in H3. destruct H3 as (h2 & -> & Hh2).
      exists (h_switch h2 l). split; [reflexivity|].
      constructor; assumption.
    + exists (h_switch h (l1 ++ (p, t2) :: l2)). split; [reflexivity|].
      constructor; constructor; assumption.
    + destruct h; destruct x; simpl in *; try tauto; congruence.
Qed.

Lemma fill_hctx_var_star_red :
  forall defs h x t, is_neutral_var defs x -> star (betaiota defs) (fill_hctx h x) t -> exists h2, t = fill_hctx h2 x /\ star (hctx_red defs) h h2.
Proof.
  intros defs h x t Hx H; remember (fill_hctx h x) as t3; revert h Heqt3; induction H; intros h ->.
  - exists h. split; [reflexivity|apply star_refl].
  - apply fill_hctx_var_red in H; [|assumption]. destruct H as (h2 & -> & H).
    destruct (IHstar _ eq_refl) as (h3 & Hh3 & Hstar).
    exists h3. split; [assumption|]. econstructor; eassumption.
Qed.

Definition is_var x := match x with var _ | dvar _ => True | _ => False end.

Lemma fill_hctx_var_eq :
  forall x1 x2 h1 h2, is_var x1 -> is_var x2 -> fill_hctx h1 x1 = fill_hctx h2 x2 <-> h1 = h2 /\ x1 = x2.
Proof.
  intros x1 x2; induction h1; intros h2 Hx1 Hx2; destruct h2; simpl in *; try (destruct x1; destruct x2; simpl in *; intuition congruence).
  - specialize (IHh1 h2). split.
    + intros [=]; intuition congruence.
    + intros [[=] ?]; intuition congruence.
  - specialize (IHh1 h2). split.
    + intros [=]; intuition congruence.
    + intros [[=] ?]; intuition congruence.
Qed.

Definition hctx_convertible defs h1 h2 := exists h3, star (hctx_red defs) h1 h3 /\ star (hctx_red defs) h2 h3.

Lemma iota_hctx :
  forall defs h t1 t2, iota defs t1 t2 -> iota defs (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros defs h t1 t2 H; induction h; simpl in *.
  - assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma star_betaiota_hctx :
  forall defs h t1 t2, star (betaiota defs) t1 t2 -> star (betaiota defs) (fill_hctx h t1) (fill_hctx h t2).
Proof.
  intros defs h t1 t2 H. eapply star_map_impl; [|eassumption].
  intros t3 t4 [H1 | H1]; [left | right].
  - apply iota_hctx. assumption.
  - apply beta_hctx. assumption.
Qed.

Lemma fill_hctx_star :
  forall defs h1 h2 t1 t2, star (betaiota defs) t1 t2 -> star (hctx_red defs) h1 h2 -> star (betaiota defs) (fill_hctx h1 t1) (fill_hctx h2 t2).
Proof.
  intros defs h1 h2 t1 t2 Ht Hh. eapply star_compose; [|eapply star_betaiota_hctx; eassumption].
  eapply star_map_impl with (f := fun h => fill_hctx h _); [|eassumption].
  intros h3 h4 H1; apply hctx_red_fill, H1.
Qed.

Lemma convertible_neutral_iff :
  forall defs h1 h2 x1 x2, is_neutral_var defs x1 -> is_neutral_var defs x2 ->
                      convertible (betaiota defs) (fill_hctx h1 x1) (fill_hctx h2 x2) <-> (x1 = x2 /\ hctx_convertible defs h1 h2).
Proof.
  intros defs h1 h2 x1 x2 Hx1 Hx2. split.
  - intros H. apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
    destruct H as (t3 & Ht3a & Ht3b).
    apply fill_hctx_var_star_red in Ht3a; [|assumption]. destruct Ht3a as (h4 & -> & Ht5a).
    apply fill_hctx_var_star_red in Ht3b; [|assumption]. destruct Ht3b as (h5 & Heq & Ht5b).
    apply fill_hctx_var_eq in Heq; [|destruct x1; simpl in *; tauto|destruct x2; simpl in *; tauto]. destruct Heq; subst.
    split; [reflexivity|]. eexists; split; eassumption.
  - intros [-> (h3 & Hh3a & Hh3b)]. eapply common_reduce_convertible; eapply fill_hctx_star; try eassumption; apply star_refl.
Qed.


Lemma abs_neutral_not_convertible :
  forall defs h x t, is_neutral_var defs x -> ~ convertible (betaiota defs) (abs t) (fill_hctx h x).
Proof.
  intros defs h x t Hx H.
  apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
  destruct H as (t3 & Ht3a & Ht3b).
  apply betaiota_star_abs_red in Ht3a. destruct Ht3a as (t4 & -> & _).
  apply fill_hctx_var_star_red in Ht3b; [|assumption]. destruct Ht3b as (h4 & Habsurd & _).
  destruct h4; destruct x; simpl in *; try tauto; congruence.
Qed.

Lemma neutral_abs_not_convertible :
  forall defs h x t, is_neutral_var defs x -> ~ convertible (betaiota defs) (fill_hctx h x) (abs t).
Proof.
  intros defs h x t Hx H. apply convertible_sym in H. eapply abs_neutral_not_convertible; eassumption.
Qed.

Lemma constr_neutral_not_convertible :
  forall defs h x tag l, is_neutral_var defs x -> ~ convertible (betaiota defs) (constr tag l) (fill_hctx h x).
Proof.
  intros defs h x tag l Hx H.
  apply convertible_confluent_common_reduce in H; [|apply beta_iota_confluent].
  destruct H as (t3 & Ht3a & Ht3b).
  apply betaiota_star_constr_red in Ht3a. destruct Ht3a as (l4 & -> & _).
  apply fill_hctx_var_star_red in Ht3b; [|assumption]. destruct Ht3b as (h4 & Habsurd & _).
  destruct h4; destruct x; simpl in *; try tauto; congruence.
Qed.

Lemma neutral_constr_not_convertible :
  forall defs h x tag l, is_neutral_var defs x -> ~ convertible (betaiota defs) (fill_hctx h x) (constr tag l).
Proof.
  intros defs h x tag l Hx H. apply convertible_sym in H. eapply constr_neutral_not_convertible; eassumption.
Qed.


Lemma convertible_convertible_left :
  forall (A : Type) (R : A -> A -> Prop) t1 t2 t3, convertible R t1 t2 -> convertible R t1 t3 <-> convertible R t2 t3.
Proof.
  intros A R t1 t2 t3 H. split; intros H2.
  - eapply star_compose; [|eassumption].
    eapply star_sym; [apply symc_sym|]. assumption.
  - eapply star_compose; eassumption.
Qed.

Lemma convertible_convertible_right :
  forall (A : Type) (R : A -> A -> Prop) t1 t2 t3, convertible R t1 t2 -> convertible R t3 t1 <-> convertible R t3 t2.
Proof.
  intros A R t1 t2 t3 H. split; intros H2.
  - eapply star_compose; eassumption.
  - eapply star_compose; [eassumption|].
    eapply star_sym; [apply symc_sym|]. assumption.
Qed.

Lemma convertible_convertible_leftright :
  forall (A : Type) (R : A -> A -> Prop) t1 t2 t3 t4, convertible R t1 t2 -> convertible R t3 t4 -> convertible R t1 t3 <-> convertible R t2 t4.
Proof.
  intros. etransitivity; [apply convertible_convertible_left|apply convertible_convertible_right]; assumption.
Qed.

(*
Lemma lift_dvars_read_env_aux :
  forall vars k l t, lift_dvars vars k (subst (read_env l) t) = subst (read_env (map (lift_dvars vars k) l)) (lift_dvars vars (length l + k) t).
Proof.
  intros vars k l t; revert k; induction t using term_ind2; intros k; simpl in *.
  - unfold read_env, liftn_subst. rewrite nth_error_map, map_length.
    destruct nth_error; simpl; reflexivity.
  - destruct index; simpl; [|reflexivity].
    unfold read_env. rewrite nth_error_map, nth_error_None_rw by lia.
    f_equal. rewrite map_length. lia.
  - f_equal. 
 *)

Lemma lift_dvars_fill :
  forall vars k t h, lift_dvars vars k (fill_hctx h t) = fill_hctx (lift_dvars_hctx vars k h) (lift_dvars vars k t).
Proof.
  intros vars k t h; induction h.
  - reflexivity.
  - simpl. f_equal. assumption.
  - simpl. f_equal. assumption.
Qed.

Lemma lift_liftn_1 :
  forall r, lift r = liftn 1 r.
Proof.
  intros r. apply renv_ext. intros [|n].
  - rewrite lift_renv, liftn_renv_small; lia.
  - rewrite lift_renv, liftn_renv_large by lia.
    simpl; f_equal. f_equal. lia.
Qed.

Lemma liftn_liftn :
  forall r k1 k2, liftn k1 (liftn k2 r) = liftn (k1 + k2) r.
Proof.
  intros r k1 k2. apply renv_ext. intros n.
  destruct (le_lt_dec k1 n).
  - rewrite liftn_renv_large by assumption.
    destruct (le_lt_dec k2 (n - k1)).
    + rewrite !liftn_renv_large by lia.
      replace (n - (k1 + k2)) with (n - k1 - k2) by lia. lia.
    + rewrite !liftn_renv_small; lia.
  - rewrite !liftn_renv_small; lia.
Qed.

Lemma liftn_0 :
  forall r, liftn 0 r = r.
Proof.
  intros. apply renv_ext. intros n.
  rewrite liftn_renv_large by lia. simpl. f_equal. lia.
Qed.

Lemma lift_dvars_ren_aux :
  forall vars k1 k2 k3 t, ren_term (liftn k1 (plus_ren k3)) (lift_dvars vars (k1 + k2) t) =
                lift_dvars vars (k3 + k1 + k2) (ren_term (liftn k1 (plus_ren k3)) t).
Proof.
  intros vars k1 k2 k3 t; revert k1; induction t using term_ind2; intros k1; simpl in *.
  - simpl. reflexivity.
  - destruct index; [|reflexivity]. simpl.
    rewrite liftn_renv_large by lia.
    rewrite plus_ren_correct. f_equal. lia.
  - f_equal. rewrite lift_liftn_1, liftn_liftn.
    specialize (IHt (S k1)). simpl in *.
    rewrite IHt. f_equal. lia.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. rewrite !map_map. apply map_ext_in.
    intros t Ht; rewrite Forall_forall in H; apply H; assumption.
  - f_equal; [apply IHt|].
    rewrite !map_map. apply map_ext_in.
    intros [p2 t2] Hpt2; rewrite Forall_forall in H; specialize (H _ Hpt2). simpl. f_equal.
    rewrite liftn_liftn. specialize (H (p2 + k1)). simpl in *.
    rewrite plus_assoc, H. f_equal. lia.
Qed.

Lemma lift_dvars_ren :
  forall vars k1 k2 t, ren_term (plus_ren k2) (lift_dvars vars k1 t) =
                lift_dvars vars (k2 + k1) (ren_term (plus_ren k2) t).
Proof.
  intros vars k1 k2 t. assert (H := lift_dvars_ren_aux vars 0 k1 k2 t).
  rewrite liftn_0 in H. simpl in H.
  rewrite H. f_equal. lia.
Qed.

Lemma liftn_subst_1_subst :
  forall us t, subst (liftn_subst 1 us) t = subst (lift_subst us) t.
Proof.
  intros us t. apply subst_ext, liftn_subst_1.
Qed.

Lemma liftn_subst_add_subst :
  forall us t k1 k2, subst (liftn_subst k1 (liftn_subst k2 us)) t = subst (liftn_subst (k1 + k2) us) t.
Proof.
  intros; apply subst_ext, liftn_subst_add.
Qed.

Lemma liftn_subst_0_subst :
  forall us t, subst (liftn_subst 0 us) t = subst us t.
Proof.
  intros us t. apply subst_ext, liftn_subst_0.
Qed.

Lemma lift_dvars_read_env_aux :
  forall vars k p l t, lift_dvars vars (p + k) (subst (liftn_subst p (read_env l)) t) = subst (liftn_subst p (read_env (map (lift_dvars vars k) l))) (lift_dvars vars (p + length l + k) t).
Proof.
  intros vars k p l t; revert p; induction t using term_ind2; intros p; simpl in *.
  - unfold read_env, liftn_subst. rewrite nth_error_map, map_length.
    destruct le_lt_dec.
    + destruct nth_error; simpl; [|reflexivity].
      rewrite lift_dvars_ren. reflexivity.
    + reflexivity.
  - destruct index; simpl; [|reflexivity].
    unfold read_env, liftn_subst.
    destruct le_lt_dec; [|lia].
    rewrite nth_error_map, nth_error_None_rw by lia.
    simpl. rewrite plus_ren_correct, map_length. f_equal. lia.
  - f_equal.
    rewrite <- !liftn_subst_1_subst, !liftn_subst_add_subst.
    specialize (IHt (S p)); simpl in *. assumption.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. rewrite !map_map. eapply map_ext_in.
    intros t Ht. rewrite Forall_forall in H. apply H. assumption.
  - f_equal; [apply IHt|].
    rewrite !map_map. apply map_ext_in.
    intros [p2 t2] Hpt2. simpl. f_equal.
    rewrite !liftn_subst_add_subst. rewrite Forall_forall in H; specialize (H _ Hpt2 (p2 + p)); simpl in H.
    rewrite plus_assoc, H. f_equal. f_equal. lia.
Qed.

Lemma lift_dvars_read_env :
  forall vars k l t, lift_dvars vars k (subst (read_env l) t) = subst (read_env (map (lift_dvars vars k) l)) (lift_dvars vars (length l + k) t).
Proof.
  intros vars k l t. assert (H := lift_dvars_read_env_aux vars k 0 l t).
  rewrite !liftn_subst_0_subst in H. assumption.
Qed.

Lemma subst1_read_env :
  forall t1 t2, subst1 t1 t2 = subst (read_env (t1 :: nil)) t2.
Proof.
  intros t1 t2. apply subst_ext. intros [|n].
  - reflexivity.
  - unfold read_env. simpl. destruct n; simpl; f_equal; lia.
Qed.

Lemma beta_lift_dvars :
  forall t1 t2 vars k, beta t1 t2 -> beta (lift_dvars vars k t1) (lift_dvars vars k t2).
Proof.
  intros t1 t2 vars k H; revert k; induction H; intros k.
  - constructor; apply IHbeta.
  - constructor; apply IHbeta.
  - constructor; apply IHbeta.
  - simpl. rewrite subst1_read_env, lift_dvars_read_env. simpl. rewrite <- subst1_read_env.
    constructor.
  - simpl. rewrite !map_app; simpl. constructor; apply IHbeta.
  - simpl. constructor; apply IHbeta.
  - simpl. rewrite !map_app; simpl. constructor; apply IHbeta.
  - simpl. rewrite lift_dvars_read_env.
    rewrite map_app; simpl.
    erewrite <- map_length with (l := l). erewrite <- map_length with (l := l1). constructor.
Qed.

(*
Inductive dvar_free x : term -> Prop :=
| dvar_free_var : forall n, dvar_free x (var n)
| dvar_free_dvar : forall y, x <> y -> dvar_free x (dvar y)
| dvar_free_abs : forall t, dvar_free x t -> dvar_free x (abs t)
| dvar_free_app : forall t1 t2, dvar_free x t1 -> dvar_free x t2 -> dvar_free x (app t1 t2)
| dvar_free_constr : forall tag l, Forall (dvar_free x) l -> dvar_free x (constr tag l)
| dvar_free_switch : forall t m, dvar_free x t -> Forall (fun pt => dvar_free x (snd pt)) m -> dvar_free x (switch t m).

Lemma dvar_free_lift :
  forall vars k t, Forall (fun x => dvar_free x t) vars -> lift_dvars vars k t = t.
Proof.
  intros vars k t. revert k; induction t using term_ind2; intros k Hvars.
  - reflexivity.
  - simpl. rewrite index_notin_None; [reflexivity|].
    intros Hn. rewrite Forall_forall in Hvars. specialize (Hvars n Hn).
    inversion Hvars; subst. tauto.
  - simpl. f_equal. apply IHt. eapply Forall_impl; [|eassumption].
    intros x Hx. inversion Hx; subst. assumption.
  - simpl. f_equal; [apply IHt1|apply IHt2]; eapply Forall_impl;
             try eassumption; intros x Hx; inversion Hx; subst; assumption.
  - simpl. f_equal. erewrite map_ext_in; [apply map_id|].
    intros t Ht. rewrite Forall_forall in H; apply H; [assumption|].
    eapply Forall_impl; [|eassumption].
    intros x Hx; inversion Hx; subst.
    rewrite Forall_forall in H1. apply H1, Ht.
  - simpl. f_equal; [apply IHt; eapply Forall_impl; [|eassumption]; intros x Hx; inversion Hx; subst; assumption|].
    erewrite map_ext_in; [apply map_id|].
    intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. specialize (H _ Hpt2).
    apply H. eapply Forall_impl; [|eassumption].
    intros x Hx; inversion Hx; subst.
    rewrite Forall_forall in H3; apply (H3 _ Hpt2).
Qed.
 *)

Lemma lift_dvars_below :
  forall vars k n t, Forall (fun x => n <= x) vars -> dvar_below n t -> lift_dvars vars k t = t.
Proof.
  intros vars k n t H1 H2. revert k; induction t using term_ind2; intros k.
  - reflexivity.
  - simpl. rewrite index_notin_None; [reflexivity|].
    intros Hn. rewrite Forall_forall in H1. apply H1 in Hn.
    inversion H2; subst. lia.
  - simpl. f_equal. apply IHt. inversion H2; assumption.
  - simpl. f_equal; [apply IHt1|apply IHt2]; inversion H2; assumption.
  - simpl. f_equal. erewrite map_ext_in; [apply map_id|].
    intros t Ht; rewrite Forall_forall in H; apply H; [assumption|].
    inversion H2; subst. rewrite Forall_forall in H4. apply H4; assumption.
  - simpl. f_equal; [apply IHt; inversion H2; assumption|].
    erewrite map_ext_in; [apply map_id|].
    intros [p t2] Hpt2; f_equal; rewrite Forall_forall in H; apply (H _ Hpt2).
    inversion H2; subst. rewrite Forall_forall in H6. apply (H6 _ Hpt2).
Qed.

Lemma dvar_below_impl :
  forall t k1 k2, k1 <= k2 -> dvar_below k1 t -> dvar_below k2 t.
Proof.
  intros t k1 k2 H1 H2; revert k2 H1; induction t using term_ind2; intros k3 H1.
  - constructor.
  - constructor. inversion H2; lia.
  - constructor; apply IHt; inversion H2; subst; assumption.
  - constructor; [apply IHt1|apply IHt2]; inversion H2; subst; assumption.
  - constructor. inversion H2; subst. eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H4]].
    intros t [Ht1 Ht2]; apply Ht1; [assumption|lia].
  - inversion H2; subst. constructor; [apply IHt; assumption|].
    eapply Forall_impl; [|erewrite <- Forall_and; split; [apply H|apply H6]].
    intros [p t2] [Hpt1 Hpt2]; apply Hpt1; [assumption|lia].
Qed.

Lemma iota_lift_dvars :
  forall defs t1 t2 vars k, Forall (fun x => length defs <= x) vars -> defs_wf defs -> iota defs t1 t2 -> iota defs (lift_dvars vars k t1) (lift_dvars vars k t2).
Proof.
  intros defs t1 t2 vars k H1 H2 H; revert k; induction H; intros k1.
  - simpl.
    rewrite index_notin_None; [|rewrite Forall_forall in H1; intros Hk; specialize (H1 _ Hk); apply nth_error_Some3 in H; lia].
    assert (H3 : lift_dvars vars k1 t = t).
    + eapply lift_dvars_below; [eassumption|]. unfold defs_wf in H2.
      eapply nth_error_Forall2 in H2; [|eassumption].
      destruct H2 as (y & Hy1 & Hy2). apply nth_error_nth with (d := y) in Hy1.
      rewrite seq_nth in Hy1 by (eapply nth_error_Some3; eassumption). subst; simpl in *.
      eapply dvar_below_impl; [|apply Hy2]. apply nth_error_Some3 in H. lia.
    + constructor; rewrite H3; assumption.
  - simpl. constructor. apply IHiota.
  - simpl. constructor. apply IHiota.
  - simpl. constructor. apply IHiota.
  - simpl. rewrite !map_app. constructor. apply IHiota.
  - simpl. constructor. apply IHiota.
  - simpl. rewrite !map_app. constructor. apply IHiota.
Qed.

Lemma convertible_lift_dvars :
  forall defs vars k t1 t2,
    Forall (fun x => length defs <= x) vars -> defs_wf defs ->
    convertible (betaiota defs) t1 t2 -> convertible (betaiota defs) (lift_dvars vars k t1) (lift_dvars vars k t2).
Proof.
  intros defs vars k t1 t2 H1 H2 H.
  eapply star_map_impl; [|eassumption].
  intros t3 t4 [[Ht34 | Ht34] | [Ht34 | Ht34]];
    (eapply beta_lift_dvars in Ht34 || eapply iota_lift_dvars in Ht34; try eassumption);
    constructor; constructor; eassumption.
Qed.

Lemma convertible_beta_betaiota :
  forall defs t1 t2, convertible beta t1 t2 -> convertible (betaiota defs) t1 t2.
Proof.
  intros defs t1 t2 H. eapply star_impl; [|eassumption].
  intros t3 t4 [Ht34 | Ht34]; constructor; right; assumption.
Qed.

Lemma read_env_app_subst :
  forall t e1 e2, subst (read_env (e1 ++ e2)) t = subst (read_env e1) (subst (liftn_subst (length e1) (read_env e2)) t).
Proof.
  intros t e1 e2. rewrite subst_subst.
  eapply subst_ext. apply read_env_app.
Qed.

Lemma read_env_app_subst1 :
  forall t e t2, subst (read_env (t2 :: e)) t = subst1 t2 (subst (lift_subst (read_env e)) t).
Proof.
  intros t e t2. rewrite subst1_read_env, <- liftn_subst_1_subst, <- read_env_app_subst. reflexivity.
Qed.

Lemma lift_dvars_subst :
  forall vars k t, NoDup vars -> closed_at t (k + length vars) -> Forall (fun x => dvar_free x t) vars -> lift_dvars vars k (subst (liftn_subst k (read_env (map dvar vars))) t) = t.
Proof.
  intros vars k t Hdup; revert k; induction t using term_ind2; intros k Hclosed Hfree.
  - simpl. unfold read_env, liftn_subst.
    destruct le_lt_dec; [|reflexivity].
    rewrite nth_error_map, map_length. destruct nth_error eqn:Hnk.
    + simpl. erewrite index_nth_error; [|eassumption|eassumption].
      f_equal. lia.
    + inversion Hclosed; subst. apply nth_error_None in Hnk. lia.
  - simpl. rewrite index_notin_None; [reflexivity|].
    intros Hn. rewrite Forall_forall in Hfree; apply Hfree in Hn. inversion Hn; tauto.
  - simpl. f_equal. rewrite <- liftn_subst_1_subst, liftn_subst_add_subst. simpl. apply IHt.
    + inversion Hclosed; subst; assumption.
    + eapply Forall_impl; [|eassumption].
      intros x Hx; inversion Hx; subst; assumption.
  - inversion Hclosed; subst.
    simpl; f_equal; [apply IHt1|apply IHt2]; try assumption; eapply Forall_impl; try eassumption; intros x Hx; inversion Hx; subst; assumption.
  - simpl. f_equal. rewrite map_map. erewrite map_ext_in; [apply map_id|].
    intros t Ht. rewrite Forall_forall in H; apply H; [assumption| |].
    + inversion Hclosed; subst. apply H3. assumption.
    + eapply Forall_impl; [|eassumption].
      intros x Hx; inversion Hx; subst. eapply Forall_forall; eassumption.
  - inversion Hclosed; subst. simpl.
    f_equal; [apply IHt; [assumption|eapply Forall_impl; [|eassumption]; intros x Hx; inversion Hx; subst; assumption]|].
    rewrite map_map. erewrite map_ext_in; [apply map_id|].
    intros [p t2] Hpt2. f_equal. simpl.
    rewrite liftn_subst_add_subst. rewrite Forall_forall in H.
    apply (H _ Hpt2).
    + specialize (H4 _ _ Hpt2). rewrite <- plus_assoc; assumption.
    + eapply Forall_impl; [|eassumption].
      intros x Hx; inversion Hx; subst. rewrite Forall_forall in H5; apply H5 in Hpt2; assumption.
Qed.

Lemma lift_dvars_subst_0 :
  forall vars t, NoDup vars -> closed_at t (length vars) -> Forall (fun x => dvar_free x t) vars -> lift_dvars vars 0 (subst (read_env (map dvar vars)) t) = t.
Proof.
  intros vars t H1 H2 H3. assert (H4 := lift_dvars_subst vars 0 t H1 H2 H3). rewrite liftn_subst_0_subst in H4. assumption.
Qed.

Lemma lift_dvars_subst_0_1 :
  forall x t, closed_at t 1 -> dvar_free x t -> lift_dvars (x :: nil) 0 (subst (read_env (dvar x :: nil)) t) = t.
Proof.
  intros x t H1 H2. apply lift_dvars_subst_0.
  - constructor; [|constructor]. simpl. tauto.
  - assumption.
  - constructor; [assumption|constructor].
Qed.


Inductive cthread_wf st (defs : list term) : cthread -> Prop :=
| cthread_wf_done : forall b, cthread_wf st defs (cthread_done b)
| cthread_wf_and : forall c1 c2, cthread_wf st defs c1 -> cthread_wf st defs c2 -> cthread_wf st defs (cthread_and c1 c2)
| cthread_wf_or : forall c1 c2, cthread_wf st defs c1 -> cthread_wf st defs c2 -> cthread_wf st defs (cthread_or c1 c2)
| cthread_wf_reduce : forall v1 v2 t1 t2 varmap1 varmap2,
    Forall (fun v => length defs <= v) varmap1 ->
    Forall (fun v => length defs <= v) varmap2 ->
    varmap_ok (st_freename st) varmap1 -> varmap_ok (st_freename st) varmap2 ->
    length varmap1 = length varmap2 ->
    read_val st defs varmap1 v1 t1 ->
    read_val st defs varmap2 v2 t2 ->
    cthread_wf st defs (cthread_reduce v1 v2 varmap1 varmap2).

Lemma cthread_andn_wf :
  forall st defs l, Forall (cthread_wf st defs) l -> cthread_wf st defs (cthread_andn l).
Proof.
  intros freename defs l H; induction H; simpl in *; constructor; assumption.
Qed.

(*
Lemma cmp_cont_cthread_wf :
  forall defs c1 c2 varmap1 varmap2,
    Forall (fun v => length defs <= v) varmap1 ->
    Forall (fun v => length defs <= v) varmap2 ->
    length varmap1 = length varmap2 ->
    cthread_wf defs (cmp_cont_cthread c1 c2 varmap1 varmap2).
*)

Lemma is_finished_read_thread :
  forall st rid v defs varmap t, is_finished st rid = Some v -> read_thread st defs varmap rid t -> read_val st defs varmap v t.
Proof.
  intros st rid v defs varmap t H1 H2; unfold is_finished in H1.
  inversion H2; subst; rewrite H in H1; simpl in *; [|congruence].
  destruct c; try congruence. injection H1 as H1; subst.
  inversion H3; subst. simpl in *. assumption.
Qed.

Lemma Forall_combine_lists :
  forall (A B : Type) (P : A -> Prop) (Q : B -> Prop) l1 l2, Forall P l1 -> Forall Q l2 -> Forall (fun ab => P (fst ab) /\ Q (snd ab)) (combine l1 l2).
Proof.
  intros A B P Q l1 l2 H1 H2; revert l2 H2; induction H1; intros l2 H2; inversion H2; subst; simpl; constructor.
  - split; assumption.
  - apply IHForall; assumption.
Qed.

Lemma cmp_cont_wf :
  forall st defs c1 c2 h1 h2 varmap1 varmap2 l,
    Forall (fun v => length defs <= v) varmap1 ->
    Forall (fun v => length defs <= v) varmap2 ->
    varmap_ok (st_freename st) varmap1 ->
    varmap_ok (st_freename st) varmap2 ->
    length varmap1 = length varmap2 ->
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    cmp_cont c1 c2 varmap1 varmap2 = Some l -> Forall (cthread_wf st defs) l.
Proof.
  intros st defs c1 c2 h1 h2 varmap1 varmap2 l Hdefs1 Hdefs2 Hok1 Hok2 Hlen Hread1 Hread2 Hcmp.
  revert c2 h2 l Hread2 Hcmp; induction Hread1; intros c2 h2 l Hread2 Hcmp; simpl in *; inversion Hread2; subst; simpl in *; try congruence.
  - injection Hcmp as Hcmp; subst. constructor.
  - destruct cmp_cont eqn:Hcmp1; [|congruence].
    injection Hcmp as Hcmp; subst. constructor.
    + econstructor; eassumption.
    + eapply IHHread1; eassumption.
  - destruct Nat.eqb eqn:Heq; [|congruence].
    destruct forallb eqn:Hforallb; [|congruence].
    destruct cmp_cont eqn:Hcmp1; [|congruence].
    injection Hcmp as Hcmp; subst. rewrite Forall_app. split; [|eapply IHHread1; eassumption].
    rewrite Forall_map. rewrite forallb_forall, <- Forall_forall in Hforallb.
    eapply Forall3_impl, Forall3_select12, Forall2_select2 in H0;
      [|intros pt vdeeps tdeep (_ & Hpt1 & _ & _ & Hpt2 & Hpt3 & _); refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hpt1 (conj Hpt2 Hpt3))].
    eapply Forall3_impl, Forall3_select12, Forall2_select2 in H3;
      [|intros pt vdeeps tdeep (_ & Hpt1 & _ & _ & Hpt2 & Hpt3 & _); refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hpt1 (conj Hpt2 Hpt3))].
    eapply Forall_impl; [|rewrite <- Forall_and; split; [apply Hforallb|apply Forall_combine_lists; eassumption]].
    intros [vdeeps1 vdeeps2] (Heq1 & (tdeep1 & Hdeep1 & Hvd1a & Hvd1b) & (tdeep2 & Hdeep2 & Hvd2a & Hvd2b)). simpl in *.
    econstructor.
    + rewrite Forall_app. split; [|assumption].
      eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
    + rewrite Forall_app. split; [|assumption].
      eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
    + apply varmap_ok_app; try eassumption.
      eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
    + apply varmap_ok_app; try eassumption.
      eapply Forall_impl; [|eassumption]. intros; simpl in *; tauto.
    + rewrite !app_length. f_equal; [|assumption].
      apply Nat.eqb_eq; assumption.
    + eassumption.
    + eassumption.
Qed.

Lemma cmp_cont_cthread_wf :
  forall st defs c1 c2 h1 h2 varmap1 varmap2,
    Forall (fun v => length defs <= v) varmap1 ->
    Forall (fun v => length defs <= v) varmap2 ->
    varmap_ok (st_freename st) varmap1 ->
    varmap_ok (st_freename st) varmap2 ->
    length varmap1 = length varmap2 ->
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    cthread_wf st defs (cmp_cont_cthread c1 c2 varmap1 varmap2).
Proof.
  intros. unfold cmp_cont_cthread. destruct cmp_cont eqn:Hcmp.
  - eapply cthread_andn_wf, cmp_cont_wf with (varmap1 := varmap1) (varmap2 := varmap2); eassumption.
  - constructor.
Qed.

Lemma cthread_red_wf :
  forall st defs ct1 ct2, cthread_wf st defs ct1 -> cthread_red st ct1 ct2 -> cthread_wf st defs ct2.
Proof.
  intros st defs ct1 ct2 H1 H2; induction H2; subst; inversion H1; subst; try (constructor; tauto).
  - inversion H10; subst.
    eapply is_finished_read_thread in H3; [|eassumption].
    econstructor; eassumption.
  - inversion H11; subst.
    eapply is_finished_read_thread in H3; [|eassumption].
    econstructor; eassumption.
  - inversion H9; subst.
    inversion H10; subst.
    econstructor.
    + constructor; [|assumption]. tauto.
    + constructor; [|assumption]. tauto.
    + apply varmap_ok_cons; tauto.
    + apply varmap_ok_cons; tauto.
    + simpl; congruence.
    + eassumption.
    + eassumption.
  - apply cthread_andn_wf. rewrite Forall_map.
    inversion H10; subst. inversion H11; subst.
    rewrite Forall_forall. intros [v1 v2] Hv12.
    eapply Forall2_In_left in H12; [|eapply in_combine_l; eassumption].
    eapply Forall2_In_left in H13; [|eapply in_combine_r; eassumption].
    destruct H12 as (t1 & Ht1a & Ht1b).
    destruct H13 as (t2 & Ht2a & Ht2b).
    econstructor; eassumption.
  - inversion H9; subst. inversion H12; subst.
    econstructor; try eassumption. apply H11.
  - inversion H10; subst. inversion H12; subst.
    econstructor; try eassumption. apply H11.
  - constructor.
    + inversion H9; subst. inversion H12; subst.
      inversion H10; subst. inversion H18; subst.
      econstructor; try eassumption; [apply H11|apply H17].
    + inversion H9; subst. inversion H10; subst.
      eapply cmp_cont_cthread_wf; eassumption.
  - inversion H10; subst. inversion H11; subst.
    eapply cmp_cont_cthread_wf; eassumption.
Qed.


Lemma read_cthread_andn_true :
  forall st defs l, read_cthread st defs (cthread_andn l) true <-> Forall (fun c => read_cthread st defs c true) l.
Proof.
  intros st defs. induction l; split; intros H; simpl in *; inversion H; subst; constructor; tauto.
Qed.

Lemma read_cthread_andn_false :
  forall st defs l, read_cthread st defs (cthread_andn l) false <-> Exists (fun c => read_cthread st defs c false) l.
Proof.
  intros st defs. induction l; split; intros H; simpl in *; inversion H; subst; constructor; tauto.
Qed.

Lemma Forall2_from_combine :
  forall (A B : Type) (P : A * B -> Prop) l1 l2, length l1 = length l2 -> Forall P (combine l1 l2) -> Forall2 (fun x y => P (x, y)) l1 l2.
Proof.
  intros A B P; induction l1; intros l2; destruct l2; intros H1 Hforall; simpl in *; try congruence.
  - constructor.
  - inversion Hforall; subst. constructor; [assumption|].
    apply IHl1; [congruence|assumption].
Qed.

Lemma Forall_square :
  forall (A B C D : Type) (P : A -> B -> Prop) (Q : C -> D -> Prop) (R : A -> C -> Prop) l1 l2 l3 l4,
    Forall2 P l1 l2 -> Forall2 Q l3 l4 -> Forall2 R l1 l3 -> Forall2 (fun b d => exists a c, P a b /\ Q c d /\ R a c) l2 l4.
Proof.
  intros A B C D P Q R; induction l1; intros l2 l3 l4 H1 H2 H3; inversion H1; subst; inversion H3; subst; inversion H2; subst;
    constructor.
  - eexists. eexists. split; [eassumption|]. split; eassumption.
  - eapply IHl1; eassumption.
Qed.

Lemma Exists_neg_Forall2 :
  forall (A B : Type) (P : A -> B -> Prop) l1 l2, Exists (fun xy => ~ P (fst xy) (snd xy)) (combine l1 l2) -> ~ (Forall2 P l1 l2).
Proof.
  intros A B P; induction l1; intros l2 H1 H2; destruct l2; simpl in *; inversion H1; subst; inversion H2; subst; simpl in *.
  - tauto.
  - eapply IHl1; eassumption.
Qed.

Lemma Exists_square :
  forall (A B C D : Type) (P : A -> B -> Prop) (Q : C -> D -> Prop) (R : A * C -> Prop) l1 l2 l3 l4,
    Forall2 P l1 l2 -> Forall2 Q l3 l4 -> Exists R (combine l1 l3) -> Exists (fun bd => exists a c, P a (fst bd) /\ Q c (snd bd) /\ R (a, c)) (combine l2 l4).
Proof.
  intros A B C D P Q R; induction l1; intros l2 l3 l4 H1 H2 H3; inversion H1; subst; simpl in *; inversion H2; subst; simpl in *; inversion H3; subst.
  - apply Exists_cons_hd. eexists. eexists. split; [eassumption|]. split; eassumption.
  - apply Exists_cons_tl. eapply IHl1; eassumption.
Qed.

(*
Inductive hctx_convertible_i defs : hctx -> hctx -> Prop :=
| hctx_convertible_i_hole : hctx_convertible_i defs h_hole h_hole
| hctx_converitble_i_app :
    forall h1 h2 t1 t2, hctx_convertible defs h1 h2 -> convertible (betaiota defs) t1 t2 ->
                   hctx_convertible_i defs (h_app h1 t1) (h_app h2 t2)
| hctx_converitble_i_switch :
    forall h1 h2 m1 m2,
      hctx_convertible defs h1 h2 ->
      Forall2 (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ convertible (betaiota defs) t1 t2) m1 m2 ->
      hctx_convertible_i defs (h_switch h1 m1) (h_switch h2 m2).

Lemma hctx_convertible_i1 :
  forall defs h1 h2, hctx_convertible_i defs h1 h2 -> hctx_convertible defs h1 h2.
Proof.
  intros defs h1 h2 H. inversion H; subst.
  - exists h_hole. split; apply star_refl.
  - destruct H0 as (h4 & H2 & H3).
    eapply convertible_confluent_common_reduce in H1; [|apply beta_iota_confluent].
    destruct H1 as (t4 & H4 & H5).
    exists (h_app h4 t4). split; eapply star_compose.
    + eapply star_map_impl; [|eassumption]. intros x y Hxy t; simpl.
      destruct Hxy; constructor; constructor; assumption.
    + eapply star_map_impl with (f := fun h => h_app h _); [|eassumption].
      intros x y Hxy t; simpl. destruct (Hxy t); constructor; constructor; assumption.
    + eapply star_map_impl; [|eassumption]. intros x y Hxy t; simpl.
      destruct Hxy; constructor; constructor; assumption.
    + eapply star_map_impl with (f := fun h => h_app h _); [|eassumption].
      intros x y Hxy t; simpl. destruct (Hxy t); constructor; constructor; assumption.
  - destruct H0 as (h4 & H2 & H3).
    admit.
Admitted.

Lemma hctx_convertible_i2 :
  forall defs h1 h2, hctx_convertible defs h1 h2 -> hctx_convertible_i defs h1 h2.
Proof.
  intros defs h1 h2 H.
  assert (H2 := convertible_neutral_iff defs h1 h2 (var 0) (var 0) I I).
  assert (Hconv : convertible (betaiota defs) (fill_hctx h1 (var 0)) (fill_hctx h2 (var 0))) by tauto.
  destruct h1; destruct h2; subst.
  - constructor.
  - exfalso. simpl in Hconv. 
  apply <- H2 in H.
*)

Lemma hctx_red_hole :
  forall defs h, hctx_red defs h_hole h -> h = h_hole.
Proof.
  intros defs h H. inversion H; reflexivity.
Qed.

Lemma hctx_red_hole_star :
  forall defs h, star (hctx_red defs) h_hole h -> h = h_hole.
Proof.
  intros defs h H. apply star_preserve with (P := fun h => h = h_hole) in H; [assumption| |reflexivity].
  intros; subst; eapply hctx_red_hole; eassumption.
Qed.

Lemma hctx_red_app_star :
  forall defs h1 t1 h, star (hctx_red defs) (h_app h1 t1) h -> exists h2 t2, h = h_app h2 t2 /\ star (hctx_red defs) h1 h2 /\ star (betaiota defs) t1 t2.
Proof.
  intros defs h1 t1 h H.
  eapply star_preserve with (P := fun h => exists h2 t2, h = h_app h2 t2 /\ _ /\ _); [| |eassumption].
  - intros h3 h4 H34 (h2 & t2 & -> & Hh & Ht).
    inversion H34; subst.
    + eexists; eexists; split; [reflexivity|]. split; [|assumption].
      eapply star_compose; [eassumption|]. apply star_1. assumption.
    + eexists; eexists; split; [reflexivity|]. split; [assumption|].
      eapply star_compose; [eassumption|]. apply star_1. assumption.
  - eexists; eexists; split; [reflexivity|]. split; apply star_refl.
Qed.

Inductive hctx_conv defs : hctx -> hctx -> Prop :=
| hctx_conv_hole : hctx_conv defs h_hole h_hole
| hctx_conv_app : forall h1 h2 t1 t2, hctx_conv defs h1 h2 -> convertible (betaiota defs) t1 t2 -> hctx_conv defs (h_app h1 t1) (h_app h2 t2)
| hctx_conv_switch : forall h1 h2 m1 m2,
    hctx_conv defs h1 h2 -> Forall2 (fun '(p1, t1) '(p2, t2) => p1 = p2 /\ convertible (betaiota defs) t1 t2) m1 m2 -> hctx_conv defs (h_switch h1 m1) (h_switch h2 m2).

Lemma hctx_conv_refl :
  forall defs h, hctx_conv defs h h.
Proof.
  intros defs h; induction h; constructor; simpl in *; try assumption.
  - apply convertible_refl.
  - apply Forall2_map_same. eapply Forall_True; intros [p t]; simpl; split; [reflexivity|apply convertible_refl].
Qed.

Lemma hctx_conv_sym :
  forall defs h1 h2, hctx_conv defs h1 h2 -> hctx_conv defs h2 h1.
Proof.
  intros defs h1 h2 H; induction H; constructor; simpl in *; try assumption.
  - apply convertible_sym. assumption.
  - apply Forall2_comm. eapply Forall2_impl; [|eassumption].
    intros [p1 t1] [p2 t2] [H1 H2]; simpl; split; [congruence|].
    apply convertible_sym. assumption.
Qed.

Lemma hctx_conv_trans :
  forall defs h1 h2 h3, hctx_conv defs h1 h2 -> hctx_conv defs h2 h3 -> hctx_conv defs h1 h3.
Proof.
  intros defs h1 h2 h3 H12; revert h3; induction H12; intros h3 H23; inversion H23; subst; constructor.
  - eapply IHhctx_conv; eassumption.
  - eapply star_compose; eassumption.
  - eapply IHhctx_conv; eassumption.
  - apply Forall2_comm in H. eapply Forall3_select23.
    eapply Forall3_impl, Forall3_from_Forall2; [|apply H|apply H4].
    intros [p2 t2] [p1 t1] [p3 t3] [[Heq12 Hconv12] [Heq23 Hconv23]].
    split; [congruence|]. eapply star_compose; eassumption.
Qed.

Lemma hctx_red_is_conv :
  forall defs h1 h2, hctx_red defs h1 h2 -> hctx_conv defs h1 h2.
Proof.
  intros defs h1 h2 H. induction H; constructor.
  - assumption.
  - apply convertible_refl.
  - apply hctx_conv_refl.
  - apply star_1. left. assumption.
  - assumption.
  - rewrite Forall2_map_same. eapply Forall_True; intros [p t]; simpl; split; [reflexivity|apply convertible_refl].
  - apply hctx_conv_refl.
  - apply Forall2_app; [|constructor]; try (rewrite Forall2_map_same; eapply Forall_True; intros [p3 t3]; simpl; split; (reflexivity || apply convertible_refl)).
    split; [reflexivity|].
    apply star_1. left. assumption.
Qed.

Lemma hctx_star_red_is_conv :
  forall defs h1 h2, star (hctx_red defs) h1 h2 -> hctx_conv defs h1 h2.
Proof.
  intros defs h1 h2 H. induction H.
  - apply hctx_conv_refl.
  - eapply hctx_conv_trans; [|eassumption].
    apply hctx_red_is_conv; assumption.
Qed.

Lemma hctx_convertible_conv :
  forall defs h1 h2, hctx_convertible defs h1 h2 -> hctx_conv defs h1 h2.
Proof.
  intros defs h1 h2 (h3 & H1 & H2).
  apply hctx_star_red_is_conv in H1, H2.
  apply hctx_conv_sym in H2. eapply hctx_conv_trans; eassumption.
Qed.

Lemma hctx_conv_convertible :
  forall defs h1 h2, hctx_conv defs h1 h2 -> hctx_convertible defs h1 h2.
Proof.
  intros defs h1 h2 H. induction H.
  - exists h_hole. split; apply star_refl.
  - destruct IHhctx_conv as (h3 & H1 & H2).
    eapply convertible_confluent_common_reduce in H0; [|apply beta_iota_confluent].
    destruct H0 as (t3 & H3 & H4).
    exists (h_app h3 t3).
    split; eapply star_compose.
    + eapply star_map_impl; [|eassumption]. intros; constructor; eassumption.
    + eapply star_map_impl with (f := fun h => h_app h _); [|eassumption]. intros; constructor; eassumption.
    + eapply star_map_impl; [|eassumption]. intros; constructor; eassumption.
    + eapply star_map_impl with (f := fun h => h_app h _); [|eassumption]. intros; constructor; eassumption.
  - destruct IHhctx_conv as (h3 & H1 & H2).
    eapply Forall2_impl in H0; [apply Forall2_exists_Forall3 in H0|].
    + destruct H0 as (m3 & Hm3). exists (h_switch h3 m3).
      split; eapply star_compose.
      * eapply star_map_impl with (f := fun h => h_switch h _); [|eassumption]. intros; constructor; eassumption.
      * eapply star_list with (RA := fun pt1 pt2 => fst pt1 = fst pt2 /\ betaiota defs (snd pt1) (snd pt2));
          [|eapply Forall3_select13, Forall3_impl; [|eassumption]; intros x y z Hxyz; refine (proj1 Hxyz); shelve].
        intros l1 l2 [p1 t1] [p2 t2] [Hp Ht]; simpl in *.
        subst. constructor. assumption.
      * eapply star_map_impl with (f := fun h => h_switch h _); [|eassumption]. intros; constructor; eassumption.
      * eapply star_list with (RA := fun pt1 pt2 => fst pt1 = fst pt2 /\ betaiota defs (snd pt1) (snd pt2));
          [|eapply Forall3_select23, Forall3_impl; [|eassumption]; intros x y z Hxyz; refine (proj2 Hxyz)].
        intros l1 l2 [p1 t1] [p2 t2] [Hp Ht]; simpl in *.
        subst. constructor. assumption.
    + intros [p1 t1] [p2 t2] [Hp Hconv].
      eapply convertible_confluent_common_reduce in Hconv; [|apply beta_iota_confluent].
      destruct Hconv as (t3 & Hconv1 & Hconv2); subst.
      exists (p2, t3).
      split; eapply star_map_impl with (f := fun t => (p2, t)); try eassumption;
        intros; split; try reflexivity; assumption.
Qed.


Fixpoint hctx_length h :=
  match h with
  | h_hole => 0
  | h_app h _ => S (hctx_length h)
  | h_switch h _ => S (hctx_length h)
  end.

Lemma hctx_conv_length :
  forall defs h1 h2, hctx_conv defs h1 h2 -> hctx_length h1 = hctx_length h2.
Proof.
  intros defs h1 h2 H; induction H; simpl in *; congruence.
Qed.

Lemma hctx_compose_length :
  forall h1 h2, hctx_length (compose_hctx h1 h2) = hctx_length h1 + hctx_length h2.
Proof.
  intros h1 h2; induction h1; simpl; lia.
Qed.

Lemma hctx_convertible_compose_r :
  forall defs h1 h2 h3 h4,
    hctx_length h1 = hctx_length h2 ->
    hctx_conv defs (compose_hctx h3 h1) (compose_hctx h4 h2) ->
    hctx_conv defs h3 h4 /\ hctx_conv defs h1 h2.
Proof.
  intros defs h1 h2 h3 h4 Hlen; revert h4; induction h3; intros h4 H; simpl in *; destruct h4; simpl in *.
  - split; [constructor|]. assumption.
  - apply hctx_conv_length in H. simpl in H; rewrite hctx_compose_length in H.
    lia.
  - apply hctx_conv_length in H. simpl in H; rewrite hctx_compose_length in H.
    lia.
  - apply hctx_conv_length in H. simpl in H; rewrite hctx_compose_length in H.
    lia.
  - inversion H; subst. apply IHh3 in H3.
    split; [|tauto]. constructor; tauto.
  - inversion H.
  - apply hctx_conv_length in H. simpl in H; rewrite hctx_compose_length in H.
    lia.
  - inversion H.
  - inversion H; subst. apply IHh3 in H3.
    split; [|tauto]. constructor; tauto.
Qed.

Lemma hctx_convertible_compose :
  forall defs h1 h2 h3 h4,
    hctx_conv defs h3 h4 -> hctx_conv defs h1 h2 ->
    hctx_conv defs (compose_hctx h3 h1) (compose_hctx h4 h2).
Proof.
  intros defs h1 h2 h3 h4 H34 H12; induction H34; simpl.
  - assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.


Lemma Forall_combine_from_Forall2 :
  forall (A B : Type) (P : A * B -> Prop) l1 l2, Forall2 (fun a b => P (a, b)) l1 l2 -> Forall P (combine l1 l2).
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma cmp_cont_cthread_correct_None :
  forall st defs c1 c2 varmap1 varmap2 h1 h2,
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    cmp_cont c1 c2 varmap1 varmap2 = None ->
    ~ (hctx_conv defs h1 h2).
Proof.
  intros st defs c1 c2 varmap1 varmap2 h1 h2 Hread1 Hread2 Hcmp.
  revert c2 h2 Hread2 Hcmp; induction Hread1; intros c2 h2 Hread2 Hcmp; inversion Hread2; subst; simpl in *;
    simpl in Hcmp; try congruence.
  - intros Hconv; inversion Hconv.
    destruct h; simpl in *; congruence.
  - intros Hconv; inversion Hconv.
    destruct h; simpl in *; congruence.
  - intros Hconv; inversion Hconv.
    destruct h; simpl in *; congruence.
  - intros Hconv.
    apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct cmp_cont eqn:Hcmp1; [congruence|]. eapply IHHread1 in Hcmp1; [|eassumption].
    tauto.
  - intros Hconv.
    apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct Hconv as [Hconv1 Hconv2]; inversion Hconv2.
  - intros Hconv; inversion Hconv.
    destruct h; simpl in *; congruence.
  - intros Hconv.
    apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct Hconv as [Hconv1 Hconv2]; inversion Hconv2.
  - intros Hconv.
    apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct Hconv as [Hconv1 Hconv2]; inversion Hconv2; subst.
    destruct Nat.eqb eqn:Heq; [|rewrite Nat.eqb_neq in Heq].
    + destruct forallb eqn:Hforallb.
      * destruct cmp_cont eqn:Hcmp1; [congruence|].
        eapply IHHread1 in Hcmp1; [|eassumption].
        tauto.
      * rewrite <- Bool.not_true_iff_false in Hforallb. apply Hforallb.
        rewrite forallb_forall, <- Forall_forall.
        apply Forall_combine_from_Forall2. simpl.
        eapply Forall2_impl; [|eapply Forall_square;
                               [eapply Forall3_select12, Forall3_impl, H0; intros pt vdeeps tdeep Hpt; exact (proj1 Hpt)|
                                eapply Forall3_select12, Forall3_impl, H3; intros pt vdeeps tdeep Hpt; exact (proj1 Hpt)|
                                rewrite Forall2_map_left, Forall2_map_right in H9; apply H9]].
        intros vdeep1 vdeep2 ([p1 t1] & [p2 t2] & Hp1 & Hp2 & Hp & _). simpl in *.
        apply Nat.eqb_eq. congruence.
    + rewrite Forall2_map_left, Forall2_map_right in H9; eapply Forall2_length in H9.
      eapply Forall3_impl, Forall3_select12, Forall2_length in H0; [|intros; exact I].
      eapply Forall3_impl, Forall3_select12, Forall2_length in H3; [|intros; exact I].
      congruence.
Qed.

Lemma cmp_cont_cthread_correct_Some_false :
  forall st defs c1 c2 varmap1 varmap2 h1 h2 l,
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    cmp_cont c1 c2 varmap1 varmap2 = Some l ->
    Exists (fun c => read_cthread st defs c false) l ->
    ~ (hctx_conv defs h1 h2).
Proof.
  intros st defs c1 c2 varmap1 varmap2 h1 h2 l Hread1 Hread2 Hcmp.
  revert l c2 h2 Hread2 Hcmp; induction Hread1; intros l c2 h2 Hread2 Hcmp Hexist; inversion Hread2; subst; simpl in *;
    simpl in Hcmp; try congruence.
  - injection Hcmp as Hcmp; subst. inversion Hexist.
  - destruct cmp_cont eqn:Hcmp1; [|congruence]. injection Hcmp as Hcmp; subst.
    intros Hconv. apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct Hconv as [Hconv1 Hconv2]; inversion Hconv2; subst.
    inversion Hexist; subst.
    + inversion H3; subst. specialize (H10 _ _ H H0). inversion H10; subst. tauto.
    + eapply IHHread1 in H3; try eassumption. tauto.
  - destruct Nat.eqb eqn:Heq; [|congruence]. rewrite Nat.eqb_eq in Heq.
    destruct forallb eqn:Hforallb; [|congruence]. rewrite forallb_forall, <- Forall_forall in Hforallb.
    apply Forall2_from_combine in Hforallb; [|assumption]. simpl in Hforallb.
    destruct cmp_cont eqn:Hcmp1; [|congruence]. injection Hcmp as Hcmp; subst.
    intros Hconv. apply hctx_convertible_compose_r in Hconv; [|reflexivity].
    destruct Hconv as [Hconv1 Hconv2]; inversion Hconv2; subst.
    rewrite Exists_app in Hexist; destruct Hexist as [Hexist | Hexist].
    + rewrite Exists_map in Hexist.
      rewrite Forall2_map_left, Forall2_map_right in H9.
      eapply Forall3_impl in H0; [|intros pt vdeeps tdeep (_ & Hread & Hconv & _);
                                   refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hread Hconv)].
      apply Forall3_select12 in H0.
      eapply Forall3_impl in H3; [|intros pt vdeeps tdeep (_ & Hread & Hconv & _);
                                   refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hread Hconv)].
      apply Forall3_select12 in H3.
      eapply Forall_Exists_neg; [|eassumption].
      apply Forall_combine_from_Forall2.
      eapply Forall2_impl; [|eapply Forall_square; eassumption].
      intros vdeeps1 vdeeps2 ([p1 t1] & [p2 t2] & (tdeep1 & Ht1a & Ht1b) & (tdeep2 & Ht2a & Ht2b) & Hp & Hcv).
      simpl in *.
      intros Hreadc. inversion Hreadc; subst. specialize (H11 _ _ Ht1a Ht2a). inversion H11; subst.
      apply H4. eapply star_compose; [|apply convertible_beta_betaiota; eassumption].
      eapply star_compose; [apply convertible_sym, convertible_beta_betaiota; eassumption|].
      assumption.
    + eapply IHHread1 in Hexist; try eassumption. tauto.
Qed.

Lemma cmp_cont_cthread_correct_Some_true :
  forall st defs c1 c2 varmap1 varmap2 h1 h2 l,
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    cmp_cont c1 c2 varmap1 varmap2 = Some l ->
    Forall (fun c => read_cthread st defs c true) l ->
    hctx_conv defs h1 h2.
Proof.
  intros st defs c1 c2 varmap1 varmap2 h1 h2 l Hread1 Hread2 Hcmp.
  revert l c2 h2 Hread2 Hcmp; induction Hread1; intros l c2 h2 Hread2 Hcmp Hforall; inversion Hread2; subst; simpl in *;
    simpl in Hcmp; try congruence.
  - injection Hcmp as Hcmp; subst. constructor.
  - destruct cmp_cont eqn:Hcmp1; [|congruence]. injection Hcmp as Hcmp; subst.
    inversion Hforall; subst.
    apply hctx_convertible_compose; [|constructor; [constructor|]].
    + eapply IHHread1 in H5; eassumption.
    + inversion H4; subst. specialize (H9 _ _ H H0). inversion H9; subst. assumption.
  - destruct Nat.eqb eqn:Heq; [|congruence]. rewrite Nat.eqb_eq in Heq.
    destruct forallb eqn:Hforallb; [|congruence]. rewrite forallb_forall, <- Forall_forall in Hforallb.
    apply Forall2_from_combine in Hforallb; [|assumption]. simpl in Hforallb.
    destruct cmp_cont eqn:Hcmp1; [|congruence]. injection Hcmp as Hcmp; subst.
    rewrite Forall_app_iff in Hforall; destruct Hforall as [Hforall1 Hforall2].
    apply hctx_convertible_compose; [|constructor; [constructor|]].
    + eapply IHHread1 in Hforall2; eassumption.
    + rewrite Forall_map in Hforall1.
      rewrite Forall2_map_left, Forall2_map_right.
      eapply Forall3_impl in H0; [|intros pt vdeeps tdeep (Hlen & Hread & Hconv & _);
                                   refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hlen (conj Hread Hconv))].
      apply Forall3_select12, Forall2_comm in H0.
      eapply Forall3_impl in H3; [|intros pt vdeeps tdeep (Hlen & Hread & Hconv & _);
                                   refine (ex_intro (fun tdeep => _) tdeep _); exact (conj Hlen (conj Hread Hconv))].
      apply Forall3_select12, Forall2_comm in H3.
      eapply Forall2_from_combine in Hforall1; [|eassumption].
      eapply Forall2_impl; [|eapply Forall_square; [eassumption|eassumption|eapply Forall2_and; [apply Hforallb|apply Hforall1]]].
      intros [p1 t1] [p2 t2] (vdeeps1 & vdeeps2 & (tdeep1 & Hlen1 & Ht1a & Ht1b) & (tdeep2 & Hlen2 & Ht2a & Ht2b) & (Hlen & Hreadc)).
      simpl in *.
      inversion Hreadc; subst. specialize (H9 _ _ Ht1a Ht2a). inversion H9; subst.
      split.
      * rewrite Nat.eqb_eq in Hlen. congruence.
      * eapply star_compose; [apply convertible_beta_betaiota; eassumption|].
        eapply star_compose; [|apply convertible_sym, convertible_beta_betaiota; eassumption].
        assumption.
Qed.

Lemma cmp_cont_cthread_correct :
  forall st defs c1 c2 varmap1 varmap2 h1 h2 b,
    read_cont st defs varmap1 c1 h1 ->
    read_cont st defs varmap2 c2 h2 ->
    read_cthread st defs (cmp_cont_cthread c1 c2 varmap1 varmap2) b ->
    reflect (hctx_convertible defs h1 h2) b.
Proof.
  intros st defs c1 c2 varmap1 varmap2 h1 h2 b Hread1 Hread2 Hread.
  unfold cmp_cont_cthread in Hread. destruct cmp_cont eqn:Hcmp.
  - destruct b.
    + constructor. apply hctx_conv_convertible.
      eapply cmp_cont_cthread_correct_Some_true; try eassumption.
      apply read_cthread_andn_true in Hread. assumption.
    + constructor. intros Hconv; apply hctx_convertible_conv in Hconv; revert Hconv.
      eapply cmp_cont_cthread_correct_Some_false; try eassumption.
      apply read_cthread_andn_false in Hread. assumption.
  - inversion Hread; subst. constructor.
    intros Hconv; apply hctx_convertible_conv in Hconv; revert Hconv.
    eapply cmp_cont_cthread_correct_None; eassumption.
Qed.

Lemma convertible_fill_betaiota :
  forall defs h1 h2 t1 t2, hctx_convertible defs h1 h2 -> convertible (betaiota defs) t1 t2 -> convertible (betaiota defs) (fill_hctx h1 t1) (fill_hctx h2 t2).
Proof.
  intros defs h1 h2 t1 t2 Hh Ht.
  destruct Hh as (h3 & Hh1 & Hh2).
  apply convertible_confluent_common_reduce in Ht; [|apply beta_iota_confluent].
  destruct Ht as (t3 & Ht1 & Ht2).
  apply common_reduce_convertible with (z := fill_hctx h3 t3); apply fill_hctx_star; assumption.
Qed.

Lemma cthread_red_correct :
  forall st defs ct1 ct2 b,
    defs_wf defs ->
    cthread_wf st defs ct1 ->
    cthread_red st ct1 ct2 ->
    read_cthread st defs ct2 b ->
    read_cthread st defs ct1 b.
Proof.
  intros st defs ct1 ct2 b Hdefs Hwf H1 H2.
  revert H2; induction H1; intros H2; subst.
  - inversion H2; subst; constructor.
    intros t1 t2 Ht1 Ht2. apply H6; [|assumption].
    inversion Ht1; subst.
    eapply is_finished_read_thread in H3; [|eassumption].
    assumption.
  - inversion H2; subst; constructor.
    intros t1 t2 Ht1 Ht2. apply H6; [assumption|].
    inversion Ht2; subst.
    eapply is_finished_read_thread in H3; [|eassumption].
    assumption.
  - inversion H2; subst. eapply cthread_red_wf in Hwf; [|constructor].
    constructor.
    intros t3 t4 Ht3 Ht4.
    inversion Ht3; subst.
    inversion Ht4; subst.
    specialize (H5 _ _ H6 H10). simpl in *.
    eapply reflect_iff; [|eassumption].
    rewrite convertible_abs_iff.
    etransitivity; [|eapply convertible_convertible_left, convertible_beta_betaiota, H7; assumption].
    etransitivity; [|eapply convertible_convertible_right, convertible_beta_betaiota, H14; assumption].
    reflexivity.
  - constructor. intros t3 t4 Ht3 Ht4. inversion Ht3; subst. inversion Ht4; subst.
    eapply reflect_iff; [apply convertible_constr_iff|].
    eapply reflect_iff; [split; [intros [Heq Hconv]; exact Hconv|tauto]|].
    destruct b; constructor; simpl.
    + rewrite read_cthread_andn_true in H2. rewrite Forall_map in H2.
      apply Forall2_from_combine in H2; [|assumption]; simpl in H2.
      eapply Forall2_impl; [|eapply Forall_square; eassumption].
      intros t1 t2 (v1 & v2 & (Hread1 & Hread2 & Hread)). inversion Hread; subst.
      specialize (H8 _ _ Hread1 Hread2). inversion H8. assumption.
    + rewrite read_cthread_andn_false in H2. rewrite Exists_map in H2.
      apply Exists_neg_Forall2.
      eapply Exists_impl; [|eapply Exists_square; eassumption].
      intros [t1 t2] (v1 & v2 & (Hread1 & Hread2 & Hread)). simpl in *. inversion Hread; subst.
      specialize (H8 _ _ Hread1 Hread2). inversion H8. assumption.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2; inversion Ht1; inversion Ht2; subst. constructor.
    simpl. rewrite convertible_constr_iff.
    intros [_ Hconv]. apply Forall2_length in H5, H10, Hconv. congruence.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2; inversion Ht1; inversion Ht2; subst. constructor.
    simpl. rewrite convertible_constr_iff. tauto.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2; inversion Ht1; inversion Ht2; subst. constructor.
    simpl. apply abs_constr_not_convertible.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2; inversion Ht1; inversion Ht2; subst. constructor.
    simpl. apply constr_abs_not_convertible.
  - constructor. intros t1 t2 Ht1 Ht2.
    inversion H2; subst.
    inversion Ht1; subst. inversion H6; subst.
    eapply reflect_iff; [|apply H5; [apply H4|apply Ht2]].
    apply convertible_convertible_left.
    eapply star_compose; [|eapply star_impl; [|apply H4]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
    apply star_1. left. left. apply iota_hctx.
    rewrite index_notin_None; [constructor; [congruence|tauto]|].
    intros Hx. inversion Hwf; subst.
    rewrite Forall_forall in H11. apply H11 in Hx. symmetry in H0. apply nth_error_Some3 in H0. lia.
  - constructor. intros t1 t2 Ht1 Ht2.
    inversion H2; subst.
    inversion Ht2; subst. inversion H6; subst.
    eapply reflect_iff; [|apply H5; [apply Ht1|apply H4]].
    apply convertible_convertible_right.
    eapply star_compose; [|eapply star_impl; [|apply H4]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
    apply star_1. left. left. apply iota_hctx.
    rewrite index_notin_None; [constructor; [congruence|tauto]|].
    intros Hx. inversion Hwf; subst.
    rewrite Forall_forall in H12. apply H12 in Hx. symmetry in H0. apply nth_error_Some3 in H0. lia.
  - constructor. intros t1 t2 Ht1 Ht2.
    inversion H2; subst.
    + inversion H1; subst.
      inversion Ht1; subst. inversion Ht2; subst. inversion H8; subst. inversion H12; subst.
      eapply reflect_iff; [|apply H7; [apply H9|apply H16]].
      inversion Hwf; subst.
      apply convertible_convertible_leftright; try assumption.
      * eapply star_compose; [|eapply star_impl; [|apply H9]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
        apply star_1. left. left. apply iota_hctx.
        rewrite index_notin_None; [constructor; [congruence|tauto]|].
        intros Hx. rewrite Forall_forall in H19. apply H19 in Hx. symmetry in H0. apply nth_error_Some3 in H0. lia.
      * eapply star_compose; [|eapply star_impl; [|apply H16]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
        apply star_1. left. left. apply iota_hctx.
        rewrite index_notin_None; [constructor; [congruence|tauto]|].
        intros Hx. rewrite Forall_forall in H20. apply H20 in Hx. symmetry in H3. apply nth_error_Some3 in H3. lia.
    + inversion H3; subst.
      inversion Ht1; subst. inversion Ht2; subst. inversion H7; subst. inversion H11; subst.
      eapply reflect_iff; [|apply H6; [apply H8|apply H15]].
      inversion Hwf; subst.
      apply convertible_convertible_leftright; try assumption.
      * eapply star_compose; [|eapply star_impl; [|apply H8]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
        apply star_1. left. left. apply iota_hctx.
        rewrite index_notin_None; [constructor; [congruence|tauto]|].
        intros Hx. rewrite Forall_forall in H18. apply H18 in Hx. symmetry in H0. apply nth_error_Some3 in H0. lia.
      * eapply star_compose; [|eapply star_impl; [|apply H15]; intros u1 u2 [Hu | Hu]; [left | right]; right; assumption].
        apply star_1. left. left. apply iota_hctx.
        rewrite index_notin_None; [constructor; [congruence|tauto]|].
        intros Hx. rewrite Forall_forall in H19. apply H19 in Hx. symmetry in H1. apply nth_error_Some3 in H1. lia.
    + constructor.
      inversion Ht1; subst. inversion Ht2; subst.
      eapply cmp_cont_cthread_correct in H3; try eassumption. inversion H3; subst.
      apply convertible_fill_betaiota; [assumption|]. apply star_same.
      inversion Hwf; subst.
      assert (x < length defs) by (inversion H6; subst; eapply nth_error_Some3; symmetry; eassumption).
      rewrite !index_notin_None; [reflexivity| |].
      * intros Hx. rewrite Forall_forall in H15. apply H15 in Hx. lia.
      * intros Hx. rewrite Forall_forall in H14. apply H14 in Hx. lia.
  - constructor. intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    eapply reflect_iff; [apply convertible_neutral_iff|].
    + simpl; destruct (index Nat.eq_dec varmap1 x1); simpl; [tauto|]. inversion H6; subst; reflexivity.
    + simpl; destruct (index Nat.eq_dec varmap2 x2); simpl; [tauto|]. inversion H10; subst; reflexivity.
    + simpl. eapply reflect_iff.
      * split; [intros [_ Hctx]; exact Hctx|].
        intros Hctx; split; [|assumption].
        inversion H6; subst. inversion H10; subst.
        symmetry in H0; symmetry in H1. apply H9 in H0; apply H13 in H1.
        destruct index eqn:Hidx1; rewrite <- H; [reflexivity|].
        eapply index_in_not_None in Hidx1; tauto.
      * eapply cmp_cont_cthread_correct; eassumption.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    constructor.
    inversion Hwf; subst.
    rewrite convertible_neutral_iff.
    + intros [Heq Hconv]. apply H.
      destruct (index Nat.eq_dec varmap1 x1); destruct (index Nat.eq_dec varmap2 x2); congruence.
    + destruct (index Nat.eq_dec varmap1 x1); simpl; [tauto|]. inversion H6; subst; reflexivity.
    + destruct (index Nat.eq_dec varmap2 x2); simpl; [tauto|]. inversion H10; subst; reflexivity.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    constructor. simpl.
    apply abs_neutral_not_convertible. destruct index; simpl; [tauto|].
    inversion H9; subst. reflexivity.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    constructor. simpl.
    apply constr_neutral_not_convertible. destruct index; simpl; [tauto|].
    inversion H6; subst. reflexivity.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    constructor. simpl.
    apply neutral_abs_not_convertible. destruct index; simpl; [tauto|].
    inversion H5; subst. reflexivity.
  - inversion H2; subst. constructor.
    intros t1 t2 Ht1 Ht2. inversion Ht1; subst. inversion Ht2; subst.
    constructor. simpl.
    apply neutral_constr_not_convertible. destruct index; simpl; [tauto|].
    inversion H5; subst. reflexivity.
  - inversion H2; subst. constructor; constructor.
  - inversion H2; subst. constructor; constructor.
  - inversion H2; subst. constructor; constructor.
  - inversion H2; subst. constructor; constructor.
  - inversion H2; subst. constructor; constructor.
  - inversion H2; subst. constructor; constructor.
  - inversion Hwf; subst. inversion H2; subst; constructor; tauto.
  - inversion Hwf; subst. inversion H2; subst; constructor; tauto.
  - inversion Hwf; subst. inversion H2; subst; constructor; tauto.
  - inversion Hwf; subst. inversion H2; subst; constructor; tauto.
Qed.

Lemma read_cthread_step_r :
  forall st defs rid ct b,
    defs_wf defs ->
    defs_ok defs st ->
    state_wf st defs ->
    cthread_wf st defs ct ->
    read_cthread (step_r st rid) defs ct b ->
    read_cthread st defs ct b.
Proof.
  intros st defs rid ct b Hdefswf Hdefsok Hstwf Hwf Hread. induction Hread; subst.
  - constructor; assumption.
  - inversion Hwf; subst. constructor; tauto.
  - inversion Hwf; subst. constructor; tauto.
  - inversion Hwf; subst. constructor; tauto.
  - inversion Hwf; subst. constructor; tauto.
  - inversion Hwf; subst. constructor; tauto.
  - inversion Hwf; subst. constructor; tauto.
  - constructor. intros t1 t2 Ht1 Ht2.
    inversion Hwf; subst.
    eapply step_r_correct_val in Ht1; try eassumption.
    eapply step_r_correct_val in Ht2; try eassumption.
    destruct Ht1 as (t5 & Hread5 & Ht15).
    destruct Ht2 as (t6 & Hread6 & Ht26).
    specialize (H _ _ Hread5 Hread6).
    eapply reflect_iff; [|eassumption].
    apply convertible_convertible_leftright.
    + eapply star_impl; [|eassumption]. intros; constructor; constructor; assumption.
    + eapply star_impl; [|eassumption]. intros; constructor; constructor; assumption.
Qed.

Lemma cthread_wf_step_r :
  forall st defs rid ct,
    defs_wf defs ->
    defs_ok defs st ->
    state_wf st defs ->
    cthread_wf st defs ct ->
    cthread_wf (step_r st rid) defs ct.
Proof.
  intros st defs rid ct Hdefswf Hdefsok Hstwf Hwf. induction Hwf.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - eapply step_r_correct_val in H4; try eassumption.
    destruct H4 as (t3 & Ht3 & _).
    eapply step_r_correct_val in H5; try eassumption.
    destruct H5 as (t4 & Ht4 & _).
    econstructor; try eassumption.
    + split; [|apply H1]. eapply Forall_impl; [|apply H1].
      intros; simpl in *. eapply lt_le_trans; [eassumption|apply step_r_freename].
    + split; [|apply H2]. eapply Forall_impl; [|apply H2].
      intros; simpl in *. eapply lt_le_trans; [eassumption|apply step_r_freename].
Qed.

Definition complete_wf defs ctst :=
  defs_wf defs /\ defs_ok defs (snd ctst) /\ state_wf (snd ctst) defs /\ cthread_wf (snd ctst) defs (fst ctst).

Lemma step_wf :
  forall ctst1 ctst2 defs,
    step ctst1 ctst2 ->
    complete_wf defs ctst1 ->
    complete_wf defs ctst2.
Proof.
  intros ctst1 ctst2 defs Hstep Hwf.
  repeat split.
  - apply Hwf.
  - unfold defs_ok. eapply le_trans; [apply Hwf|].
    inversion Hstep; subst; simpl; [|lia].
    apply step_r_freename.
  - inversion Hstep; subst; simpl; [|apply Hwf].
    apply state_wf_preserve; apply Hwf.
  - inversion Hstep; subst; simpl.
    + apply cthread_wf_step_r; apply Hwf.
    + eapply cthread_red_wf; [|eassumption]. apply Hwf.
Qed.

Lemma step_correct :
  forall st1 st2 defs ct1 ct2 b,
    complete_wf defs (ct1, st1) ->
    step (ct1, st1) (ct2, st2) ->
    read_cthread st2 defs ct2 b ->
    read_cthread st1 defs ct1 b.
Proof.
  intros st1 st2 defs ct1 ct2 b Hwf Hstep Hread.
  inversion Hstep; subst.
  - eapply read_cthread_step_r; try eassumption; apply Hwf.
  - eapply cthread_red_correct; try eassumption; apply Hwf.
Qed.

