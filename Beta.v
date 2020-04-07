Require Import Misc.
Require Import List.
Require Import Freevar.
Require Import Term.
Require Import Star.

(* Beta and parallel beta *)

Inductive beta : term -> term -> Prop :=
| beta_redex : forall t1 t2, body t1 -> lc t2 -> beta (app (lam t1) t2) (t1 ^^ t2)
| beta_app_left : forall t1 t2 t3, beta t1 t2 -> lc t3 -> beta (app t1 t3) (app t2 t3)
| beta_app_right : forall t1 t2 t3, beta t1 t2 -> lc t3 -> beta (app t3 t1) (app t3 t2)
| beta_lam : forall t1 t2 L, (forall x, x ∉ L -> beta (t1 ^ x) (t2 ^ x)) -> beta (lam t1) (lam t2).

Lemma beta_lc : forall t1 t2, beta t1 t2 -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H. induction H.
  - split.
    + constructor; [apply lc_lam_body|]; assumption.
    + apply substb_lc; assumption.
  - split; constructor; tauto.
  - split; constructor; tauto.
  - split; apply lc_lam with (L := L) ; firstorder.
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
Unshelve. all: exact nil.
Qed.

Lemma beta_subst2 :
  forall t u1 u2 x, beta u1 u2 -> lc t -> star beta (t [x := u1]) (t [x := u2]).
Proof.
  intros t u1 u2 x Hbeta Ht. induction Ht.
  - simpl. destruct freevar_eq_dec.
    + econstructor; [eassumption|constructor].
    + constructor.
  - simpl. destruct (beta_lc _ _ Hbeta) as [Hlc1 Hlc2]. eapply star_compose.
    + eapply star_map_impl with (f := fun t => app t _); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
    + eapply star_map_impl with (f := fun t => app _ t); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
  - simpl. pick fresh y as Hy.
    rewrite <- (close_open t 0 y), !closeb_substf_free by use_fresh y.
    eapply star_map_impl with (f := fun t => lam (closeb 0 y t)); [|apply H0; use_fresh y].
    intros t3 t4 Hbeta1.
    apply beta_lam with (L := nil).
    intros z _.
    rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
    apply beta_subst; [constructor | auto].
Unshelve. all: exact nil.
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
Unshelve. all: exact nil.
Qed.

Lemma star_beta_fv :
  forall t1 t2, star beta t1 t2 -> fv t2 \subseteq fv t1.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - etransitivity; [eassumption|]. apply beta_fv. assumption.
Qed.
