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
  enough (H : forall l, star beta (constr tag (l ++ l1)) (constr tag (l ++ l2))).
  { exact (H nil). }
  induction H12 as [|t1 t2 l1 l2 Ht Hl IH].
  - intros. apply star_refl.
  - intros l. eapply star_compose.
    + specialize (IH (l ++ (t1 :: nil))). rewrite <- !app_assoc in IH. simpl in IH. apply IH.
    + eapply star_map_impl with (RA := beta) (f := fun t => constr tag (l ++ t :: l2)); [|eassumption].
      intros; constructor; assumption.
Qed.

Lemma star_beta_switch :
  forall t1 t2 l1 l2,
    star beta t1 t2 -> Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\ star beta (snd pt1) (snd pt2)) l1 l2 ->
    star beta (switch t1 l1) (switch t2 l2).
Proof.
  intros t1 t2 l1 l2 Ht Hl.
  eapply star_compose.
  { eapply star_map_impl with (RA := beta) (f := fun t => switch t _); [|eassumption]; intros; constructor; assumption. }
  enough (H : forall l, star beta (switch t2 (l ++ l1)) (switch t2 (l ++ l2))).
  { exact (H nil). }
  induction Hl as [|pt1 pt2 l1 l2 [Hp H] Hl IH].
  - intros. apply star_refl.
  - intros l. eapply star_compose.
    + specialize (IH (l ++ (pt1 :: nil))). rewrite <- !app_assoc in IH. simpl in IH. apply IH.
    + destruct pt1 as [p1 t3]; destruct pt2 as [p2 t4]; simpl in *; subst.
      eapply star_map_impl with (RA := beta) (f := fun t => switch t2 (l ++ (p2, t) :: l2)); [|assumption].
      intros; constructor; assumption.
Qed.



Inductive pbeta : term -> term -> Prop :=
| pbeta_var : forall n, pbeta (var n) (var n)
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
  - constructor. assumption.
  - constructor; assumption.
  - constructor. apply Forall2_map_same. assumption.
  - constructor; [assumption|].
    apply Forall2_map_same. eapply Forall_impl; [|exact H].
    intros [p t2]; simpl; tauto.
Qed.


Lemma Forall2_impl_transparent : forall (A B : Type) (P Q : A -> B -> Prop) (L1 : list A) (L2 : list B), (forall (x : A) (y : B), P x y -> Q x y) -> Forall2 P L1 L2 -> Forall2 Q L1 L2.
Proof.
  intros A B P Q L1 L2 Himpl H. induction H.
  - constructor.
  - constructor.
    + apply Himpl. assumption.
    + assumption.
Defined.

Fixpoint pbeta_ind2 (P : term -> term -> Prop)
         (Hvar : forall n, P (var n) (var n))
         (Happ : forall t1 t2 t3 t4, pbeta t1 t2 -> P t1 t2 -> pbeta t3 t4 -> P t3 t4 -> P (app t1 t3) (app t2 t4))
         (Hredex : forall t1 t2 t3 t4, pbeta t1 t2 -> P t1 t2 -> pbeta t3 t4 -> P t3 t4 -> P (app (abs t1) t3) (subst1 t4 t2))
         (Hlam : forall t1 t2, pbeta t1 t2 -> P t1 t2 -> P (abs t1) (abs t2))
         (Hconstr : forall tag l1 l2, Forall2 pbeta l1 l2 -> Forall2 P l1 l2 -> P (constr tag l1) (constr tag l2))
         (Hswitch : forall t1 t2 l1 l2, pbeta t1 t2 -> P t1 t2 -> Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\ pbeta (snd pt1) (snd pt2)) l1 l2 -> Forall2 (fun pt1 pt2 => P (snd pt1) (snd pt2)) l1 l2 -> P (switch t1 l1) (switch t2 l2))
         (Hswitch_redex : forall lt1 lt2 t1 t2 l1 l2, Forall2 pbeta lt1 lt2 -> Forall2 P lt1 lt2 -> pbeta t1 t2 -> P t1 t2 -> P (switch (constr (length l1) lt1) (l1 ++ (length lt1, t1) :: l2)) (subst (read_env lt2) t2))
         (t1 t2 : term) (H : pbeta t1 t2) {struct H} : P t1 t2 :=
  let rec := pbeta_ind2 P Hvar Happ Hredex Hlam Hconstr Hswitch Hswitch_redex in
  match H with
  | pbeta_var n => Hvar n
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

Lemma Forall2_and :
  forall (A B : Type) (P Q : A -> B -> Prop) L1 L2, Forall2 P L1 L2 -> Forall2 Q L1 L2 -> Forall2 (fun x y => P x y /\ Q x y) L1 L2.
Proof.
  intros A B P Q L1 L2 HP. induction HP; intros HQ; inversion HQ; subst.
  - constructor.
  - constructor; [split; assumption|apply IHHP; assumption].
Qed.

Lemma Forall2_length :
  forall (A B : Type) (P : A -> B -> Prop) L1 L2, Forall2 P L1 L2 -> length L1 = length L2.
Proof.
  intros A B P L1 L2 H. induction H; simpl; congruence.
Qed.

Lemma pbeta_star_beta :
  forall t1 t2, pbeta t1 t2 -> star beta t1 t2.
Proof.
  intros t1 t2 Hpbeta. induction Hpbeta using pbeta_ind2.
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

Lemma nth_error_Forall2_iff:
  forall A B (P : A -> B -> Prop) L1 L2,
    Forall2 P L1 L2 <-> (length L1 = length L2 /\ forall n x y, nth_error L1 n = Some x -> nth_error L2 n = Some y -> P x y).
Proof.
  intros A B P L1 L2. split.
  - intros H. induction H.
    + split; [reflexivity|]. intros; destruct n; simpl in *; discriminate.
    + destruct IHForall2 as [Hlen Hforall].
      split; [simpl; congruence|].
      intros [|n]; simpl; [|apply Hforall].
      intros; congruence.
  - revert L2; induction L1 as [|x L1 IH]; intros [|y L2] [Hlen Hforall]; simpl in *.
    + constructor.
    + discriminate.
    + discriminate.
    + constructor; [apply (Hforall 0); reflexivity|].
      apply IH. split; [congruence|].
      intros n; apply (Hforall (S n)).
Qed.

Lemma nth_error_Forall_iff :
  forall A (P : A -> Prop) L,
    Forall P L <-> (forall n x, nth_error L n = Some x -> P x).
Proof.
  intros A P L. split.
  - intros H. induction H.
    + intros; destruct n; simpl in *; discriminate.
    + intros [|n]; simpl; [|apply IHForall].
      intros; congruence.
  - induction L as [|x L IH]; intros Hforall; simpl in *.
    + constructor.
    + constructor.
      * apply (Hforall 0); reflexivity.
      * apply IH. intros n; apply (Hforall (S n)).
Qed.

Ltac ereplace t :=
  let tmp := fresh "_tmp" in
  let typ := type of t in
  evar (tmp : typ);
  replace t with tmp; unfold tmp.


Lemma subst_subst1 :
  forall us t1 t2, subst us (subst1 t1 t2) = subst1 (subst us t1) (subst (lift_subst us) t2).
Proof.
  intros us t1 t2. unfold subst1. rewrite !subst_subst.
  apply subst_ext. unfold comp. intros [|n].
  * reflexivity.
  * simpl. unfold comp. rewrite subst_ren.
    etransitivity; [symmetry; apply subst_id|].
    apply subst_ext. intros n1. unfold comp. simpl. f_equal. lia.
Qed.

Lemma lift_ren :
  forall r n, ren (lift r) n = lift_subst (ren r) n.
Proof.
  intros r n. unfold ren, lift_subst, comp.
  rewrite lift_renv. simpl.
  destruct n; simpl; [reflexivity|].
  f_equal; lia.
Qed.

Lemma ren_subst1 :
  forall r t1 t2, ren_term r (subst1 t1 t2) = subst1 (ren_term r t1) (ren_term (lift r) t2).
Proof.
  intros r t1 t2.
  rewrite !ren_term_is_subst, subst_subst1.
  f_equal. apply subst_ext.
  intros n; rewrite lift_ren; reflexivity.
Qed.

Lemma subst_read_env :
  forall us l t, subst us (subst (read_env l) t) = subst (read_env (map (subst us) l)) (subst (liftn_subst (length l) us) t).
Proof.
  intros us l t. rewrite !subst_subst. apply subst_ext; intros n.
  unfold comp, read_env, liftn_subst.
  destruct nth_error as [u|] eqn:Hln.
  - destruct le_lt_dec; [apply nth_error_None in l0; congruence|]. simpl.
    rewrite nth_error_map, Hln. reflexivity.
  - destruct le_lt_dec; [|apply nth_error_None in Hln; lia].
    simpl. rewrite subst_ren.
    etransitivity; [symmetry; apply subst_id|].
    eapply subst_ext.
    intros m. unfold comp, ren. simpl.
    rewrite plus_ren_correct.
    replace (nth_error _ _) with (@None term).
    + f_equal. rewrite map_length. lia.
    + symmetry. apply nth_error_None. rewrite map_length; lia.
Qed.

Lemma ren_read_env :
  forall r l t, ren_term r (subst (read_env l) t) = subst (read_env (map (ren_term r) l)) (ren_term (liftn (length l) r) t).
Proof.
  intros r l t.
  rewrite !ren_term_is_subst, subst_read_env.
  f_equal.
  - f_equal. apply map_ext. intros; rewrite ren_term_is_subst; reflexivity.
  - apply subst_ext. intros n.
    unfold liftn_subst, ren. destruct le_lt_dec; simpl.
    + rewrite plus_ren_correct.
      rewrite liftn_renv_large; [reflexivity|assumption].
    + rewrite liftn_renv_small; [reflexivity|assumption].
Qed.

Lemma pbeta_ren : forall t1 t2 r, pbeta t1 t2 -> pbeta (ren_term r t1) (ren_term r t2).
Proof.
  intros t1 t2 r H. revert r. induction H using pbeta_ind2; intros r; simpl in *.
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

Lemma list_exists :
  forall (A : Type) (P : nat -> A -> Prop) n, (forall k, k < n -> exists x, P k x) -> exists L, length L = n /\ (forall k x, nth_error L k = Some x -> P k x).
Proof.
  intros A P n. induction n; intros H.
  - exists nil. split; [reflexivity|].
    intros [|k]; simpl; intros; discriminate.
  - destruct IHn as [L HL]; [intros k Hk; apply H; lia|].
    destruct (H n) as [x Hx]; [lia|].
    exists (L ++ x :: nil). split.
    + rewrite app_length; simpl. lia.
    + intros k y.
      destruct (le_lt_dec n k).
      * rewrite nth_error_app2 by lia.
        destruct (k - length L) as [|u] eqn:Hu; simpl.
        -- assert (k = n) by lia. congruence.
        -- destruct u; simpl; discriminate.
      * rewrite nth_error_app1 by lia. apply HL.
Qed.

Lemma nth_error_Some2 :
  forall (A : Type) (l : list A) n, n < length l -> exists x, nth_error l n = Some x.
Proof.
  intros A l n. revert l; induction n; intros l H; destruct l as [|x l]; simpl in *; try lia.
  - exists x. reflexivity.
  - apply IHn. lia.
Qed.

Lemma nth_error_Some3 :
  forall (A : Type) (l : list A) n x, nth_error l n = Some x -> n < length l.
Proof.
  intros. apply nth_error_Some. destruct nth_error; congruence.
Qed.


Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 R nil nil nil
| Forall3_cons : forall x y z l1 l2 l3, R x y z -> Forall3 R l1 l2 l3 -> Forall3 R (x :: l1) (y :: l2) (z :: l3).

Inductive Forall4 {A B C D : Type} (R : A -> B -> C -> D -> Prop) : list A -> list B -> list C -> list D -> Prop :=
| Forall4_nil : Forall4 R nil nil nil nil
| Forall4_cons : forall x y z w l1 l2 l3 l4, R x y z w -> Forall4 R l1 l2 l3 l4 -> Forall4 R (x :: l1) (y :: l2) (z :: l3) (w :: l4).

Lemma Forall3_select12 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R x y) l1 l2 l3 -> Forall2 R l1 l2.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall3_select13 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R x z) l1 l2 l3 -> Forall2 R l1 l3.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall3_select23 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R y z) l1 l2 l3 -> Forall2 R l2 l3.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select123 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y z) l1 l2 l3 l4 -> Forall3 R l1 l2 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select124 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y w) l1 l2 l3 l4 -> Forall3 R l1 l2 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select134 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x z w) l1 l2 l3 l4 -> Forall3 R l1 l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select234 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y z w) l1 l2 l3 l4 -> Forall3 R l2 l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select12 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y) l1 l2 l3 l4 -> Forall2 R l1 l2.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select13 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x z) l1 l2 l3 l4 -> Forall2 R l1 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select14 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x w) l1 l2 l3 l4 -> Forall2 R l1 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select23 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y z) l1 l2 l3 l4 -> Forall2 R l2 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select24 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y w) l1 l2 l3 l4 -> Forall2 R l2 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select34 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R z w) l1 l2 l3 l4 -> Forall2 R l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.



Lemma Forall_exists_Forall2 :
  forall (A B : Type) (P : A -> B -> Prop) (l1 : list A),
    Forall (fun x => exists y, P x y) l1 -> exists l2, Forall2 P l1 l2.
Proof.
  intros A B P l1 H; induction H.
  - exists nil. constructor.
  - destruct IHForall as [l2 IH].
    destruct H as [y Hy].
    exists (y :: l2). constructor; assumption.
Qed.

Lemma Forall2_exists_Forall3 :
  forall (A B C : Type) (P : A -> B -> C -> Prop) (l1 : list A) (l2 : list B),
    Forall2 (fun x y => exists z, P x y z) l1 l2 -> exists l3, Forall3 P l1 l2 l3.
Proof.
  intros A B C P l1 l2 H; induction H.
  - exists nil. constructor.
  - destruct IHForall2 as [l3 IH].
    destruct H as [z Hz].
    exists (z :: l3). constructor; assumption.
Qed.

Lemma Forall3_exists_Forall4 :
  forall (A B C D: Type) (P : A -> B -> C -> D -> Prop) (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => exists w, P x y z w) l1 l2 l3 -> exists l4, Forall4 P l1 l2 l3 l4.
Proof.
  intros A B C D P l1 l2 l3 H; induction H.
  - exists nil. constructor.
  - destruct IHForall3 as [l4 IH].
    destruct H as [w Hw].
    exists (w :: l4). constructor; assumption.
Qed.


Lemma Forall3_impl :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) l1 l2 l3,
    (forall x y z, P x y z -> Q x y z) -> Forall3 P l1 l2 l3 -> Forall3 Q l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 HPQ H; induction H; constructor; [apply HPQ|]; assumption.
Qed.

Lemma Forall4_impl :
  forall (A B C D : Type) (P Q : A -> B -> C -> D -> Prop) l1 l2 l3 l4,
    (forall x y z w, P x y z w -> Q x y z w) -> Forall4 P l1 l2 l3 l4 -> Forall4 Q l1 l2 l3 l4.
Proof.
  intros A B C D P Q l1 l2 l3 l4 HPQ H; induction H; constructor; [apply HPQ|]; assumption.
Qed.


Lemma Forall3_from_Forall2 :
  forall (A B C : Type) (P : A -> B -> Prop) (Q : A -> C -> Prop) l1 l2 l3,
    Forall2 P l1 l2 -> Forall2 Q l1 l3 -> Forall3 (fun x y z => P x y /\ Q x z) l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H1. revert l3; induction H1; intros l3 H2; inversion H2; subst.
  - constructor.
  - constructor.
    + split; assumption.
    + apply IHForall2. assumption.
Qed.

Lemma list_app_eq_length :
  forall A (l1 l2 l3 l4 : list A), l1 ++ l3 = l2 ++ l4 -> length l1 = length l2 -> l1 = l2 /\ l3 = l4.
Proof.
  intros A l1 l2 l3 l4; revert l2; induction l1; intros l2 H1 H2; destruct l2; simpl in *; try intuition congruence.
  specialize (IHl1 l2 ltac:(congruence) ltac:(congruence)).
  intuition congruence.
Qed.


Definition locally_confluent {A : Type} (R : A -> A -> Prop) :=
  forall x y z, R x y -> R x z -> exists w, R y w /\ R z w.

Definition confluent {A : Type} (R : A -> A -> Prop) := locally_confluent (star R).

Lemma pbeta_lc : locally_confluent pbeta.
Proof.
  intros t1 t2 t3 H12. revert t3. induction H12 using pbeta_ind2; intros t5 H15; inversion H15; subst.
  - exists (var n). split; constructor.
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

Lemma lc_is_confluent :
  forall (A : Type) (R : A -> A -> Prop), locally_confluent R -> confluent R.
Proof.
  intros A R H.
  assert (H1 : forall x y z, star R x y -> R x z -> exists w, star R z w /\ R y w).
  - intros x y z Hxy; revert z. induction Hxy.
    + intros z Hxz. exists z. split; [apply star_refl|assumption].
    + intros w Hw. destruct (H _ _ _ H0 Hw) as (t & Hyt & Hwt).
      destruct (IHHxy t Hyt) as (s & Hs1 & Hs2).
      exists s. split; [|assumption]. econstructor; eassumption.
  - intros x y z Hxy; revert z. induction Hxy.
    + intros z Hxz; exists z. split; [assumption|apply star_refl].
    + intros w Hxw. destruct (H1 _ _ _ Hxw H0) as (t & Ht1 & Ht2).
      destruct (IHHxy _ Ht1) as (s & Hs1 & Hs2).
      exists s. split; [assumption|]. econstructor; eassumption.
Qed.

Lemma star_beta_is_star_pbeta :
  forall x y, star beta x y <-> star pbeta x y.
Proof.
  intros x y. split; intros H.
  - eapply star_map_impl with (f := id); [|eassumption].
    intros x1 y1; simpl. apply beta_pbeta.
  - eapply star_star.
    eapply star_map_impl with (f := id); [|eassumption].
    intros x1 y1; simpl. apply pbeta_star_beta.
Qed.

Lemma locally_confluent_ext :
  forall (A : Type) (R1 R2 : A -> A -> Prop), (forall x y, R1 x y <-> R2 x y) -> locally_confluent R1 <-> locally_confluent R2.
Proof.
  intros A R1 R2 Heq; split; intros H x y z Hxy Hxz.
  - rewrite <- Heq in Hxy, Hxz. destruct (H _ _ _ Hxy Hxz) as (w & Hyw & Hzw).
    exists w; split; rewrite <- Heq; assumption.
  - rewrite Heq in Hxy, Hxz. destruct (H _ _ _ Hxy Hxz) as (w & Hyw & Hzw).
    exists w; split; rewrite Heq; assumption.
Qed.

Lemma beta_confluent :
  confluent beta.
Proof.
  eapply locally_confluent_ext; [apply star_beta_is_star_pbeta|].
  apply lc_is_confluent, pbeta_lc.
Qed.
