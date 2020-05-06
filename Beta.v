Require Import Misc.
Require Import List.
Require Import Freevar.
Require Import Term.
Require Import Star.
Require Import Psatz.

(* Beta and parallel beta *)

Inductive beta : term -> term -> Prop :=
| beta_redex : forall t1 t2, body t1 -> lc t2 -> beta (app (lam t1) t2) (t1 ^^ t2)
| beta_app_left : forall t1 t2 t3, beta t1 t2 -> lc t3 -> beta (app t1 t3) (app t2 t3)
| beta_app_right : forall t1 t2 t3, beta t1 t2 -> lc t3 -> beta (app t3 t1) (app t3 t2)
| beta_lam : forall t1 t2 L, (forall x, x ∉ L -> beta (t1 ^ x) (t2 ^ x)) -> beta (lam t1) (lam t2)
| beta_constr : forall p l1 l2 t1 t2, beta t1 t2 -> (forall t, t \in l1 -> lc t) -> (forall t, t \in l2 -> lc t) ->
                                 beta (constr p (l1 ++ t1 :: l2)) (constr p (l1 ++ t2 :: l2))
| beta_switch1 : forall t1 t2 m, beta t1 t2 -> (forall p t3, (p, t3) \in m -> bodies p t3) -> beta (switch t1 m) (switch t2 m)
| beta_switch2 : forall t p t1 t2 m1 m2 L,
    (forall xs, distinct L p xs -> beta (substb_list 0 (map fvar xs) t1) (substb_list 0 (map fvar xs) t2)) ->
    lc t -> (forall p2 t3, (p2, t3) \in m1 -> bodies p2 t3) -> (forall p2 t3, (p2, t3) \in m2 -> bodies p2 t3) ->
    beta (switch t (m1 ++ (p, t1) :: m2)) (switch t (m1 ++ (p, t2) :: m2))
| beta_switch_redex : forall k l m t,
    (forall t2, t2 \in l -> lc t2) -> (forall p t2, (p, t2) \in m -> bodies p t2) -> nth_error m k = Some (length l, t) ->
    beta (switch (constr k l) m) (substb_list 0 l t).


Lemma beta_lc : forall t1 t2, beta t1 t2 -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H. induction H.
  - split.
    + constructor; [apply lc_lam_body|]; assumption.
    + apply substb_lc; assumption.
  - split; constructor; tauto.
  - split; constructor; tauto.
  - split; apply lc_lam with (L := L) ; firstorder.
  - split; constructor; intros t Ht; rewrite in_app_iff in Ht; simpl in Ht; firstorder congruence.
  - split; rewrite lc_switch_bodies, Forall_forall; split; try apply IHbeta; intros [p t3]; apply H0.
  - split; rewrite lc_switch_bodies, Forall_forall; split; try apply H1;
      intros [p2 t3] [Hpt3 | [[= <- <-] | Hpt3]]%in_app_iff; try solve [apply H2; assumption | apply H3; assumption];
        exists L; intros xs Hxs; apply H0; assumption.
  - split.
    + rewrite lc_switch_bodies, Forall_forall. split.
      * constructor. assumption.
      * intros [p t2] Hpt2. apply H0. assumption.
    + apply nth_error_In in H1. apply H0 in H1.
      apply substb_list_lc; assumption.
Qed.

Lemma beta_subst :
  forall t1 t2 x u, lc u -> beta t1 t2 -> beta (t1 [x := u]) (t2 [x := u]).
Proof.
  intros t1 t2 x u Hu Hbeta. induction Hbeta.
  - simpl. rewrite substb_substf by auto. constructor.
    + rewrite <- lc_lam_body. apply substf_lc with (t := lam t1); [rewrite lc_lam_body|]; auto.
    + apply substf_lc; auto.
  - intros; simpl; constructor; auto using substf_lc.
  - intros; simpl; constructor; auto using substf_lc.
  - intros; simpl.
    eapply beta_lam with (L := Bound _); intros y Hy.
    specialize_fresh H0 y.
    rewrite !substb_substf in H0 by auto.
    simpl in H0. rewrite freevar_eq_dec_neq_ifte in H0 by use_fresh y.
    assumption.
  - simpl. rewrite !map_app; simpl. constructor.
    + assumption.
    + rewrite forall_map. intros t Ht; apply substf_lc; auto.
    + rewrite forall_map. intros t Ht; apply substf_lc; auto.
  - simpl. constructor; [assumption|].
    rewrite forall_pair, forall_map, forall_pair2. simpl. intros p t3 Hpt3; specialize (H p t3 Hpt3).
    rewrite bodies_substf; assumption.
  - simpl. rewrite !map_app; simpl. apply beta_switch2 with (L := x :: L).
    + intros xs Hxs. specialize (H0 xs ltac:(eapply distinct_incl; [|eassumption]; prove_list_inc)).
      rewrite !substf_substb_list_free; try assumption; rewrite forall_map;
        intros y Hy; apply notin_one; intros ->; eapply distinct_distinct; try eassumption; simpl; tauto.
    + apply substf_lc; assumption.
    + rewrite forall_pair, forall_map, forall_pair2. simpl. intros p2 t3 Hpt3; specialize (H2 p2 t3 Hpt3).
      rewrite bodies_substf; assumption.
    + rewrite forall_pair, forall_map, forall_pair2. simpl. intros p2 t3 Hpt3; specialize (H3 p2 t3 Hpt3).
      rewrite bodies_substf; assumption.
  - simpl. rewrite substb_list_substf by assumption.
    constructor.
    + rewrite forall_map. intros t2 Ht2. apply substf_lc; auto.
    + rewrite forall_pair, forall_map, forall_pair2. simpl. intros p t2 Hpt2. specialize (H0 p t2 Hpt2).
      rewrite bodies_substf; assumption.
    + rewrite map_length, nth_error_map, H1. reflexivity.
Unshelve. all: exact nil.
Qed.

Lemma beta_subst_list_core :
  forall t1 t2 xs us, length xs = length us -> (forall x, x \in xs -> x \notin concat (map fv us)) -> (forall u, u \in us -> lc u) ->
                 beta t1 t2 ->
                 beta (substb_list 0 us (closeb_list 0 xs t1)) (substb_list 0 us (closeb_list 0 xs t2)).
Proof.
  intros t1 t2 xs us.
  revert t1 t2 us. induction xs as [|x xs] using rev_ind; intros t1 t2 us; induction us as [|u us] using rev_ind; intros Hlength Hxs Hlc Hbeta; simpl in *.
  - assumption.
  - rewrite app_length in *; simpl in *; lia.
  - rewrite app_length in *; simpl in *; lia.
  - clear IHus.
    rewrite !substb_list_app, !closeb_list_app; simpl.
    assert (Hlength2 : length xs = length us) by (rewrite !app_length in Hlength; simpl in Hlength; lia).
    rewrite !Hlength2, !open_close_at.
    + destruct (in_dec freevar_eq_dec x xs) as [Hxxs | Hxxs].
      * rewrite !substf_fv; [apply IHxs with (us := us)| |].
        -- assumption.
        -- intros y Hy. specialize (Hxs y).
           rewrite map_app, concat_app in Hxs; simpl in *; rewrite !in_app_iff in Hxs; tauto.
        -- intros; apply Hlc; rewrite in_app_iff; tauto.
        -- assumption.
        -- apply closeb_list_vars_free. assumption.
        -- apply closeb_list_vars_free. assumption.
      * apply beta_subst with (x := x) (u := u) in Hbeta; [|apply Hlc; rewrite in_app_iff; simpl; tauto].
        apply IHxs with (us := us) in Hbeta; [|assumption| |intros; apply Hlc; rewrite in_app_iff; tauto].
        -- rewrite !closeb_list_substf in Hbeta; [apply Hbeta| |].
           all: intros y Hy1 [-> | Hy2]; try tauto; specialize (Hxs y).
           all: rewrite map_app, concat_app in Hxs; simpl in *; rewrite !in_app_iff in Hxs; tauto.
        -- intros y Hy. specialize (Hxs y).
           rewrite map_app, concat_app in Hxs; simpl in *; rewrite !in_app_iff in Hxs; tauto.
    + rewrite <- Hlength2.
      assert (Hlc2 : lc t2) by (apply beta_lc in Hbeta; tauto).
      rewrite lc_at_lc in Hlc2.
      rewrite <- open_close_var_list_at with (xs := xs) (k := 0) (t := t2) in Hlc2 by assumption.
      apply lc_at_substb_list_lc_at2 in Hlc2. rewrite map_length in Hlc2; assumption.
    + apply Hlc. rewrite in_app_iff; simpl; tauto.
    + rewrite <- Hlength2.
      assert (Hlc2 : lc t1) by (apply beta_lc in Hbeta; tauto).
      rewrite lc_at_lc in Hlc2.
      rewrite <- open_close_var_list_at with (xs := xs) (k := 0) (t := t1) in Hlc2 by assumption.
      apply lc_at_substb_list_lc_at2 in Hlc2. rewrite map_length in Hlc2; assumption.
    + apply Hlc. rewrite in_app_iff; simpl; tauto.
Qed.

Lemma beta_subst_list :
  forall t1 t2 xs us, length xs = length us -> (forall u, u \in us -> lc u) -> beta t1 t2 ->
                 beta (substb_list 0 us (closeb_list 0 xs t1)) (substb_list 0 us (closeb_list 0 xs t2)).
Proof.
  intros t1 t2 xs us Hlength Hlc Hbeta.
  pickn (length us) distinct ys \notin (concat (map fv us) ++ xs ++ fv (closeb_list 0 xs t1) ++ fv (closeb_list 0 xs t2)) as Hys.
  rewrite <- close_open_list with (xs := ys) (k := 0) (p := length us) (t := closeb_list 0 xs t1)
    by (eapply distinct_incl; [|eassumption]; prove_list_inc).
  rewrite <- close_open_list with (xs := ys) (k := 0) (p := length us) (t := closeb_list 0 xs t2)
    by (eapply distinct_incl; [|eassumption]; prove_list_inc).
  apply beta_subst_list_core; [apply distinct_length in Hys; assumption| |eassumption|].
  - intros y Hy1 Hy2; eapply distinct_distinct; [eassumption| |eassumption]; rewrite !in_app_iff; tauto.
  - apply beta_subst_list_core; [| |rewrite forall_map; intros; constructor|assumption].
    + apply distinct_length in Hys. rewrite map_length. congruence.
    + intros x Hx1 Hx2. rewrite map_map, concat_map_In in Hx2. destruct Hx2 as (y & Hy1 & Hy2).
      simpl in Hy1. destruct Hy1 as [-> | []].
      eapply distinct_distinct; [eassumption| |eassumption]; rewrite !in_app_iff; tauto.
Qed.

Lemma beta_lam_one :
  forall x t1 t2, x \notin fv t1 -> x \notin fv t2 -> beta (t1 ^ x) (t2 ^ x) -> beta (lam t1) (lam t2).
Proof.
  intros x t1 t2 Hx1 Hx2 Hbeta.
  apply beta_lam with (L := nil). intros y _.
  rewrite substb_is_substf with (x := x) (t := t1) by assumption.
  rewrite substb_is_substf with (x := x) (t := t2) by assumption.
  apply beta_subst; [constructor|assumption].
Qed.

Lemma star_beta_lc :
  forall t1 t2, star beta t1 t2 -> lc t1 -> lc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using beta_lc.
Qed.

Lemma star_beta_lc_left :
  forall t1 t2, star beta t1 t2 -> lc t2 -> lc t1.
Proof.
  intros t1 t2 H. destruct H.
  - intros; assumption.
  - intros _. apply beta_lc in H. tauto.
Qed.

Lemma star_beta_app :
  forall t1 t2 t3 t4,
    lc t1 -> lc t2 ->
    star beta t1 t3 -> star beta t2 t4 -> star beta (app t1 t2) (app t3 t4).
Proof.
  intros t1 t2 t3 t4 Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => app _ t); [|eassumption].
    intros t5 t6 Hbeta; constructor; assumption.
  - eapply star_map_impl with (f := fun t => app t _); [|eassumption].
    intros t5 t6 Hbeta; constructor; [|eapply star_beta_lc]; eassumption.
Qed.

Lemma star_beta_lam :
  forall t1 t2 x,
    x \notin fv t1 -> x \notin fv t2 -> star beta (t1 ^ x) (t2 ^ x) ->
    star beta (lam t1) (lam t2).
Proof.
  intros t1 t2 x Hx1 Hx2 Hbeta.
  rewrite <- (close_open t1 0 x), <- (close_open t2 0 x) by tauto.
  eapply star_map_impl with (f := fun t => lam (closeb 0 x t)); [|eassumption].
  intros t3 t4 Hbeta1.
  eapply beta_lam with (L := nil). intros y _.
  rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
  apply beta_subst; [constructor | auto].
Qed.

Lemma star_beta_constr :
  forall p l1 l2, (forall t, t \in l1 -> lc t) -> Forall2 (star beta) l1 l2 -> star beta (constr p l1) (constr p l2).
Proof.
  intros p l1 l2 Hlc HForall2.
  apply star_map_impl with
      (RA := fun l1 l2 => exists l3 l4 t1 t2, (forall t, t \in l3 -> lc t) /\ (forall t, t \in l4 -> lc t) /\
                                      beta t1 t2 /\ l1 = l3 ++ t1 :: l4 /\ l2 = l3 ++ t2 :: l4)
      (f := fun l => constr p l).
  - intros l3 l4 (l5 & l6 & t1 & t2 & Hl5 & Hl6 & Hbeta & Hl3 & Hl4); subst.
    constructor; assumption.
  - revert Hlc; induction HForall2 as [|t1 t2 l1 l2 Hstar HForall2 IH]; intros Hlc.
    + constructor.
    + eapply star_compose.
      * eapply star_map_impl with (RA := beta) (f := fun t => t :: l1); [|eassumption].
        intros t3 t4 Hbeta. exists nil. exists l1. exists t3. exists t4.
        splits 5; [intros _ []|intros; apply Hlc; simpl; tauto|assumption|reflexivity|reflexivity].
      * assert (Hlc2 : lc t2) by (apply star_beta_lc in Hstar; [assumption|apply Hlc; simpl; tauto]).
        eapply star_map_impl with (f := fun l => t2 :: l); [|apply IH; intros; apply Hlc; simpl; tauto].
        intros l3 l4 (l5 & l6 & t3 & t4 & Hl5 & Hl6 & Hbeta & Hl3 & Hl4); subst.
        exists (t2 :: l5). exists l6. exists t3. exists t4.
        split; [intros t [Ht | Ht]; [subst; apply Hlc2 | apply Hl5; simpl; tauto]|].
        split; [assumption|].
        split; [assumption|].
        split; reflexivity.
Qed.

Lemma star_beta_switch :
  forall t1 t2 m1 m2, lc t1 -> (forall p t3, (p, t3) \in m1 -> bodies p t3) -> star beta t1 t2 ->
                 Forall2 (fun pt1 pt2 => fst pt1 = fst pt2 /\
                                      exists xs, distinct (fv (snd pt1) ++ fv (snd pt2)) (fst pt1) xs /\
                                            star beta
                                                 (substb_list 0 (map fvar xs) (snd pt1))
                                                 (substb_list 0 (map fvar xs) (snd pt2))) m1 m2 ->
                 star beta (switch t1 m1) (switch t2 m2).
Proof.
  intros t1 t2 m1 m2 Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply star_compose.
  { eapply star_map_impl with (f := fun t => switch t m1); [|eassumption].
    intros t3 t4 Hbeta; constructor; assumption. }
  assert (Hlc3 : lc t2) by (eapply star_beta_lc; eassumption).
  clear t1 Hlc1 Hbeta1.
  apply star_map_impl with
      (RA := fun m1 m2 => exists m3 m4 pt1 pt2,
                 (forall p t3, (p, t3) \in m3 -> bodies p t3) /\ (forall p t3, (p, t3) \in m4 -> bodies p t3) /\
                 fst pt1 = fst pt2 /\
                 (exists L, forall xs, distinct L (fst pt1) xs ->
                             beta (substb_list 0 (map fvar xs) (snd pt1))
                                  (substb_list 0 (map fvar xs) (snd pt2))) /\
                 m1 = m3 ++ pt1 :: m4 /\ m2 = m3 ++ pt2 :: m4)
      (f := fun m => switch t2 m).
  - intros m3 m4 (m5 & m6 & [p t3] & [p2 t4] & Hm5 & Hm6 & H1 & [L H2] & Hm3 & Hm4); simpl in H1; subst.
    apply beta_switch2 with (L := L); assumption.
  - revert Hlc2; induction Hbeta2 as [|[p t3] [p2 t4] m1 m2 [Hpeq (xs & Hxs & Hbeta2)] Hbeta3 IH]; intros Hlc2.
    + constructor.
    + simpl in *; subst p2. eapply star_compose.
      * replace t3 with (closeb_list 0 xs (substb_list 0 (map fvar xs) t3))
          by (eapply close_open_list, distinct_incl; [|eassumption]; prove_list_inc).
        eapply star_map_impl with (f := fun t => (p, closeb_list 0 xs t) :: m1); [|exact Hbeta2].
        intros t5 t6 Hbeta. exists nil. exists m1. exists (p, closeb_list 0 xs t5). exists (p, closeb_list 0 xs t6). simpl.
        splits 6; [intros _ _ []|intros; apply Hlc2; simpl; tauto|reflexivity| |reflexivity|reflexivity].
        exists nil. intros ys Hys.
        apply beta_subst_list; [|rewrite forall_map; intros; constructor|assumption].
        erewrite map_length, !distinct_length; [|eassumption|eassumption]. reflexivity.
      * assert (Hbodies : bodies p t4).
        { apply star_beta_lc in Hbeta2.
          { apply lc_at_lc, lc_at_substb_list_lc_at2, bodies_lc_at in Hbeta2.
            erewrite map_length, distinct_length, <- plus_n_O in Hbeta2 by eassumption. assumption. }
          apply substb_list_lc; [|rewrite forall_map; intros; constructor].
          erewrite map_length, distinct_length; [|eassumption]. apply Hlc2; tauto. }
        erewrite close_open_list; [|eapply distinct_incl; [|eassumption]; prove_list_inc].
        eapply star_map_impl with (f := fun m => _ :: m); [|apply IH; intros; apply Hlc2; tauto].
        intros m3 m4 (m5 & m6 & pt3 & pt4 & Hm5 & Hm6 & Hpt34 & Hred & Hm3 & Hm4); subst.
        exists ((p, t4) :: m5). exists m6. exists pt3. exists pt4.
        splits 6; try assumption; try reflexivity.
        intros p2 t [[= <- <-] | Hpt2]; [assumption|apply Hm5; simpl; tauto].
Qed.

Lemma beta_subst2 :
  forall t u1 u2 x, beta u1 u2 -> lc t -> star beta (t [x := u1]) (t [x := u2]).
Proof.
  intros t u1 u2 x Hbeta Ht. induction Ht.
  - simpl. destruct freevar_eq_dec.
    + econstructor; [eassumption|constructor].
    + constructor.
  - simpl. apply star_beta_app; try assumption; apply substf_lc; try assumption; apply beta_lc in Hbeta; tauto.
  - simpl. pick fresh y as Hy.
    apply star_beta_lam with (x := y); try solve [use_fresh y].
    rewrite !substf_substb_free by solve [apply beta_lc in Hbeta; tauto | apply notin_one; use_fresh y].
    apply H0. use_fresh y.
  - simpl. apply star_beta_constr.
    + rewrite forall_map. intros t Ht. apply substf_lc; [apply H; assumption|].
      apply beta_lc in Hbeta; tauto.
    + rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same, Forall_forall. assumption.
  - simpl. eapply star_beta_switch.
    + apply substf_lc; [assumption|]. apply beta_lc in Hbeta; tauto.
    + rewrite forall_pair, forall_map, forall_pair2. intros p t2 Hpt2; simpl.
      rewrite bodies_substf by (apply beta_lc in Hbeta; tauto). exists L. intros l Hl; eapply H; eassumption.
    + assumption.
    + rewrite Forall2_map_left, Forall2_map_right, Forall2_map_same, Forall_forall. intros [p t2] Hpt2. simpl.
      split; [reflexivity|].
      pickn p distinct xs \notin (x :: L ++ fv (t2 [x := u1]) ++ fv (t2 [x := u2])) as Hxs. exists xs.
      split; [eapply distinct_incl; [|eassumption]; prove_list_inc|].
      rewrite !substf_substb_list_free.
      * eapply H0; [eassumption|]. eapply distinct_incl; [|eassumption]. prove_list_inc.
      * rewrite forall_map. intros y Hy1 [-> | []]; eapply distinct_distinct; [apply Hxs| |apply Hy1]; simpl; tauto.
      * apply beta_lc in Hbeta; tauto.
      * rewrite forall_map. intros y Hy1 [-> | []]; eapply distinct_distinct; [apply Hxs| |apply Hy1]; simpl; tauto.
      * apply beta_lc in Hbeta; tauto.
Unshelve. all: exact nil.
Qed.

(*
Inductive parallel_beta : term -> term -> Prop :=
| pbeta_var : forall x, parallel_beta (fvar x) (fvar x)
| pbeta_app : forall t1 t2 t3 t4, parallel_beta t1 t3 -> parallel_beta t2 t4 -> parallel_beta (app t1 t2) (app t3 t4)
| pbeta_lam : forall t1 t2 L, (forall x, x \notin L -> parallel_beta (t1 ^ x) (t2 ^ x)) -> parallel_beta (lam t1) (lam t2)
| pbeta_redex : forall t1 t2, body t1 -> lc t2 -> parallel_beta (app (lam t1) t2) (t1 ^^ t2).

Lemma parallel_beta_lc : forall t1 t2, parallel_beta t1 t2 -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H. induction H.
  - split; constructor.
  - split; constructor; tauto.
  - split; apply lc_lam with (L := L); firstorder.
  - split.
    + constructor; [apply lc_lam_body|]; assumption.
    + apply substb_lc; assumption.
Qed.

Lemma parallel_beta_refl : forall t, lc t -> parallel_beta t t.
Proof.
  intros t H. induction H.
  - constructor.
  - constructor; assumption.
  - econstructor; eassumption.
Qed.

Lemma beta_incl_parallel_beta :
  forall t1 t2, beta t1 t2 -> parallel_beta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor; assumption.
  - constructor; [|apply parallel_beta_refl]; assumption.
  - constructor; [apply parallel_beta_refl|]; assumption.
  - econstructor; eassumption.
Qed.

Lemma parallel_beta_incl_star_beta :
  forall t1 t2, parallel_beta t1 t2 -> star beta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor.
  - apply star_compose with (y := app t3 t2).
    + eapply star_map_impl with (f := fun t => app t t2); [|eassumption].
      intros; constructor; firstorder using parallel_beta_lc.
    + eapply star_map_impl with (f := fun t => app t3 t); [|eassumption].
      intros; constructor; firstorder using parallel_beta_lc.
  - pick fresh x.
    rewrite <- (close_open t1 0 x), <- (close_open t2 0 x) by use_fresh x.
    apply star_map_impl with (RA := beta) (f := fun t => lam (closeb 0 x t)); [|apply H0; use_fresh x].
    intros t3 t4 Hbeta.
    apply beta_lam with (L := nil).
    intros y _.
    rewrite !open_close by (constructor || apply beta_lc in Hbeta; tauto).
    apply beta_subst; [constructor | auto].
  - econstructor; constructor; auto.
Unshelve. all: exact nil.
Qed.

*)

Lemma star_beta_substf :
  forall t1 t2 t3 t4 x,
    lc t1 -> lc t2 ->
    star beta t1 t3 -> star beta t2 t4 -> star beta (t1 [ x := t2 ]) (t3 [ x := t4 ]).
Proof.
  intros t1 t2 t3 t4 x Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => t [ x := _ ]); [|eassumption].
    intros t5 t6 Hbeta. apply beta_subst; assumption.
  - apply star_star.
    eapply star_map_impl with (f := fun t => _ [ x := t ]); [|eassumption].
    intros t5 t6 Hbeta. apply beta_subst2; [assumption|].
    eapply star_beta_lc; eassumption.
Qed.

Lemma beta_fv :
  forall t1 t2, beta t1 t2 -> fv t2 \subseteq fv t1.
Proof.
  intros t1 t2 H. induction H.
  - rewrite substb_fv. simpl. reflexivity.
  - simpl. rewrite IHbeta. reflexivity.
  - simpl. rewrite IHbeta. reflexivity.
  - pick fresh x as Hx.
    specialize_fresh H0 x.
    simpl. rewrite substb_fv with (t := t1) in H0.
    rewrite <- substb_fv2 in H0.
    intros z Hz. specialize (H0 z Hz). rewrite in_app_iff in H0; simpl in H0.
    intuition (subst z; use_fresh x).
  - simpl. rewrite !map_app; simpl; rewrite !concat_app; simpl.
    rewrite IHbeta; reflexivity.
  - simpl. rewrite IHbeta; reflexivity.
  - simpl. rewrite !map_app; simpl; rewrite !concat_app; simpl.
    enough (Hsub : fv t2 \subseteq fv t1) by (rewrite Hsub; reflexivity).
    intros z Hz.
    pickn p distinct xs \notin (z :: L) as Hxs. specialize (H0 xs ltac:(eapply distinct_incl; [|eassumption]; prove_list_inc)).
    destruct (in_dec freevar_eq_dec z (fv t1)) as [Hz1 | Hz1]; [assumption|]. exfalso.
    eapply substb_list_fv; [|apply Hz1|apply H0].
    + rewrite forall_map. intros x Hx1 [-> | []]. eapply distinct_distinct; [eassumption| |eassumption]; simpl; tauto.
    + apply substb_list_fv2. assumption.
  - simpl. intros z Hz.
    lazymatch goal with [ |- z \in ?t ] => destruct (in_dec freevar_eq_dec z t) as [Hz1 | Hz1]; [exact Hz1|exfalso] end.
    revert Hz. apply substb_list_fv.
    + rewrite in_app_iff, !concat_map_In in Hz1. intros u Hu Hzu. apply Hz1. left. exists u. tauto.
    + apply nth_error_In in H1.
      rewrite in_app_iff, !concat_map_In in Hz1. intros Hzt. apply Hz1. right. exists (length l, t). tauto.
Unshelve. all: exact nil.
Qed.

Lemma star_beta_fv :
  forall t1 t2, star beta t1 t2 -> fv t2 \subseteq fv t1.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - etransitivity; [eassumption|]. apply beta_fv. assumption.
Qed.
