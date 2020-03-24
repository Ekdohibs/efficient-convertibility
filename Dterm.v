Require Import Misc.
Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Star.

(* dterm *)

Inductive dterm :=
| dbvar : nat -> dterm
| dfvar : freevar -> dterm
| dlam : dterm -> dterm -> dterm
| dapp : dterm -> dterm -> dterm
| dmark : dterm -> dterm.

Fixpoint dsubstb k u t :=
  match t with
  | dbvar i => if Nat.eq_dec i k then u else dbvar i
  | dfvar x => dfvar x
  | dlam t1 t2 => dlam (dsubstb (S k) u t1) (dsubstb (S k) u t2)
  | dapp t1 t2 => dapp (dsubstb k u t1) (dsubstb k u t2)
  | dmark t => dmark (dsubstb k u t)
  end.

Fixpoint dcloseb k x t :=
  match t with
  | dbvar i => dbvar i
  | dfvar y => if freevar_eq_dec x y then dbvar k else dfvar y
  | dlam t1 t2 => dlam (dcloseb (S k) x t1) (dcloseb (S k) x t2)
  | dapp t1 t2 => dapp (dcloseb k x t1) (dcloseb k x t2)
  | dmark t => dmark (dcloseb k x t)
  end.

Notation "t 'd[' k <- u ]" := (dsubstb k u t) (at level 67).
Notation "t 'd^^' u" := (t d[ 0 <- u ]) (at level 67).
Notation "t 'd^' x" := (t d^^ (dfvar x)) (at level 67).

Fixpoint dsubstf x u t :=
  match t with
  | dbvar i => dbvar i
  | dfvar y => if freevar_eq_dec x y then u else dfvar y
  | dlam t1 t2 => dlam (dsubstf x u t1) (dsubstf x u t2)
  | dapp t1 t2 => dapp (dsubstf x u t1) (dsubstf x u t2)
  | dmark t => dmark (dsubstf x u t)
  end.

Notation "t 'd[' x := u ]" := (dsubstf x u t) (at level 67).

Fixpoint dfv t :=
  match t with
  | dbvar i => nil
  | dfvar x => x :: nil
  | dlam t1 t2 => dfv t1 ++ dfv t2
  | dapp t1 t2 => dfv t1 ++ dfv t2
  | dmark t => dfv t
  end.

Lemma dsubstf_dfv :
  forall t u x, x \notin dfv t -> t d[ x := u ] = t.
Proof.
  induction t; intros u x Hx; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; intuition congruence.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
  - f_equal; apply IHt; auto.
Qed.

Inductive dlc : dterm -> Prop :=
| dlc_dvar : forall v, dlc (dfvar v)
| dlc_dapp : forall t1 t2, dlc t1 -> dlc t2 -> dlc (dapp t1 t2)
| dlc_dlam : forall t1 t2 L, (forall x, ~ In x L -> dlc (t1 d^ x)) -> (forall x, ~ In x L -> dlc (t2 d^ x)) -> dlc (dlam t1 t2)
| dlc_dmark : forall t, dlc t -> dlc (dmark t).

Lemma dlc_dlam2 : forall t1 t2 L, (forall x, ~ In x L -> dlc (t1 d^ x) /\ dlc (t2 d^ x)) -> dlc (dlam t1 t2).
Proof.
  intros t1 t2 L H. apply dlc_dlam with (L := L); intros x Hx; apply H; assumption.
Qed.

Definition dbody t := exists L, forall x, x \notin L -> dlc (t d^ x).
Lemma dlc_dlam_dbody : forall t1 t2, dlc (dlam t1 t2) <-> dbody t1 /\ dbody t2.
Proof.
  intros t. split.
  - intros H; inversion H; split; exists L; firstorder.
  - intros [[L1 H1] [L2 H2]].
    apply dlc_dlam with (L := L1 ++ L2); intros x Hx; rewrite in_app_iff in Hx; firstorder.
Qed.

Lemma dsubstb_dlc_id_core :
  forall t u v k1 k2, k1 <> k2 -> t d[ k2 <- v ] d[ k1 <- u ] = t d[ k2 <- v ] -> t d[ k1 <- u ] = t.
Proof.
  induction t; intros u v k1 k2 Hk Heq; simpl in *; inversion Heq; try (f_equal; eauto).
  repeat ( destruct Nat.eq_dec; simpl in * ); congruence.
Qed.

Lemma dsubstb_dlc_id : forall t u, dlc t -> forall k, t d[ k <- u ] = t.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - intros; simpl; rewrite IHdlc1, IHdlc2; reflexivity.
  - intros k. simpl.
    pick x \notin L as Hx.
    f_equal; eapply dsubstb_dlc_id_core with (k2 := 0); eauto.
  - intros; simpl; rewrite IHdlc; reflexivity.
Qed.

Lemma dsubstb_dsubstf :
  forall t u v k x, dlc u -> t d[ k <- v ] d[ x := u ] = t d[ x := u ] d[ k <- v d[ x := u ]].
Proof.
  induction t.
  - intros; simpl. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl. destruct freevar_eq_dec; [|reflexivity].
    rewrite dsubstb_dlc_id; auto.
  - intros; simpl. f_equal; [apply IHt1 | apply IHt2]; auto.
  - intros; simpl. f_equal; auto.
  - intros; simpl. f_equal; auto.
Qed.

Lemma dsubstf_dsubstb_free :
  forall t u v k x, x ∉ dfv v -> dlc u -> t d[ x := u ] d[ k <- v ] = t d[ k <- v ] d[ x := u ].
Proof.
  intros. rewrite dsubstb_dsubstf; [|assumption].
  f_equal. rewrite dsubstf_dfv; auto.
Qed.

Lemma dsubstf_dsubstb_free2 :
  forall t u v k x, x ∉ dfv t -> t d[ k <- v ] d[ x := u ] = t d[ k <- v d[ x := u ] ].
Proof.
  induction t.
  - intros; simpl in *. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl in *. destruct freevar_eq_dec; intuition congruence.
  - intros; simpl in *. f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
  - intros; simpl in *. f_equal; auto.
Qed.

Lemma dcloseb_id :
  forall t k x, x \notin dfv t -> dcloseb k x t = t.
Proof.
  intros t. induction t.
  - intros; reflexivity.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt1, IHt2 ; rewrite !in_app_iff in *; tauto.
  - intros; simpl in *; rewrite in_app_iff in *; f_equal; auto.
  - intros; simpl in *. f_equal; auto.
Qed.

Lemma dcloseb_dsubstf_free :
  forall t u k x y, x <> y -> x \notin dfv u -> (dcloseb k x t) d[ y := u ] = dcloseb k x (t d[ y := u ]).
Proof.
  intros t. induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite dcloseb_id; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
Qed.

Lemma dsubstf_dlc : forall t, dlc t -> forall u x, dlc u -> dlc (t d[ x := u ]).
Proof.
  intros t Ht. induction Ht; intros u x Hu.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; auto.
  - simpl. apply dlc_dlam2 with (L := x :: L). intros y Hy.
    rewrite !dsubstf_dsubstb_free by (simpl in *; intuition congruence).
    split; [apply H0 | apply H2]; simpl in *; tauto.
  - simpl. constructor; auto.
Qed.

Lemma dsubstb_is_dsubstf :
  forall t u x, x ∉ dfv t -> t d^^ u = t d^ x d[ x := u ].
Proof.
  intros t u x Hx.
  rewrite dsubstf_dsubstb_free2; [|assumption].
  simpl. destruct freevar_eq_dec; tauto.
Qed.

Lemma dsubstb_dlc : forall t u, dbody t -> dlc u -> dlc (t d^^ u).
Proof.
  intros t u [L Ht] Hu.
  pick x ∉ (L ++ dfv t).
  rewrite in_app_iff in *.
  rewrite dsubstb_is_dsubstf with (x := x); [|tauto].
  apply dsubstf_dlc; intuition.
Qed.

Lemma dlc_open_gen :
  forall t x, dbody t -> dlc (t d^ x).
Proof.
  intros.
  apply dsubstb_dlc; [assumption | constructor].
Qed.

Lemma dclose_open :
  forall t k x, x \notin dfv t -> dcloseb k x (t d[ k <- dfvar x ]) = t.
Proof.
  intros t. induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; try destruct freevar_eq_dec; congruence.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
  - intros; simpl in *; rewrite IHt; auto.
Qed.

Lemma dopen_inj :
  forall x t1 t2, x \notin dfv t1 -> x \notin dfv t2 -> t1 d^ x = t2 d^ x -> t1 = t2.
Proof.
  intros.
  rewrite <- (dclose_open t1 0 x), <- (dclose_open t2 0 x); auto; congruence.
Qed.

Lemma open_dclose_core :
  forall t i j x y u, i <> j -> x <> y -> dlc u -> y \notin dfv t -> (dcloseb j x t) d[ j <- u ] d[ i <- dfvar y ] = (dcloseb j x (t d[ i <- dfvar y ])) d[ j <- u ].
Proof.
  intros t. induction t.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite dsubstb_dlc_id; auto.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite dsubstb_dlc_id; auto.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; simpl in *; try tauto; congruence.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; tauto.
  - intros; simpl in *.
    f_equal. apply IHt; auto.
Qed.

Lemma open_dclose :
  forall t, dlc t -> forall k x u, dlc u -> dsubstb k u (dcloseb k x t) = t d[ x := u ].
Proof.
  intros t H. induction H; intros k x u Hu.
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. f_equal; auto.
  - simpl.
    f_equal; match goal with [ |- ?t3 = ?t4 ] => pick y \notin (x :: L ++ dfv t3 ++ dfv t4 ++ dfv t1 ++ dfv t2) end; simpl in *; rewrite !in_app_iff in *.
    + apply (dopen_inj y); try tauto.
      rewrite open_dclose_core by intuition.
      rewrite dsubstf_dsubstb_free by (simpl; intuition).
      intuition.
    + apply (dopen_inj y); try tauto.
      rewrite open_dclose_core by intuition.
      rewrite dsubstf_dsubstb_free by (simpl; intuition).
      intuition.
  - simpl. f_equal; auto.
Qed.

Lemma dsubstf_id :
  forall x t, t d[ x := dfvar x ] = t.
Proof.
  intros x t; induction t; simpl; try congruence.
  destruct freevar_eq_dec; congruence.
Qed.

Lemma open_dclose_var :
  forall t, dlc t -> forall k x, dsubstb k (dfvar x) (dcloseb k x t) = t.
Proof.
  intros. rewrite open_dclose, dsubstf_id; auto.
  constructor.
Qed.

(*
(* dbeta *)

Inductive dbeta : bool -> term -> term -> Prop :=
| dbeta_redex : forall t1 t2 t3, dbody t1 -> dbody t2 -> dlc t3 -> dbeta true (dapp (dlam t1 t2) t3) (t1 ^^ (dmark t3))
| dbeta_dapp_left : forall b t1 t2 t3, dbeta b t1 t2 -> dlc t3 -> dbeta b (app t1 t3) (app t2 t3)
| dbeta_dapp_right : forall b t1 t2 t3, dbeta b t1 t2 -> dlc t3 -> dbeta b (app t3 t1) (app t3 t2)
| dbeta_dlam_left : forall b t1 t2 t3 L, (forall x, x ∉ L -> dbeta false (t1 ^ x) (t2 ^ x)) -> dbody t3 -> dbeta b (dlam t1 t3) (dlam t2 t3)
| dbeta_dlam_right : forall b t1 t2 t3 L, (forall x, x ∉ L -> dbeta b (t1 ^ x) (t2 ^ x)) -> dbody t3 -> dbeta b (dlam t3 t1) (dlam t3 t2).

Lemma beta_lc : forall t1 t2, beta t1 t2 -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H. induction H.
  - split.
    + constructor; [apply lc_lam_body|]; assumption.
    + apply substb_lc; assumption.
  - split; constructor; tauto.
  - split; constructor; tauto.
  - split; apply lc_lam with (L := L); firstorder.
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
  - intros; simpl; apply beta_lam with (L := x :: L).
    intros y Hy; simpl in Hy.
    specialize (H0 y (ltac:(tauto))).
    rewrite !substb_substf in H0 by auto.
    simpl in H0. destruct freevar_eq_dec; tauto.
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
  - simpl.
    pick y \notin (x :: L ++ fv t ++ fv u1 ++ fv u2) as Hy; simpl in Hy.
    rewrite !in_app_iff in Hy.
    rewrite <- (close_open t 0 y), !closeb_substf_free by intuition.
    eapply star_map_impl with (f := fun t => lam (closeb 0 y t)); [|intuition].
    + intros t3 t4 Hbeta1.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros z Hz; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
      apply beta_subst; [constructor | auto].
Qed.

*)
