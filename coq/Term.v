Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.

(** Terms *)

Inductive term :=
| bvar : nat -> term
| fvar : freevar -> term
| lam : term -> term
| app : term -> term -> term
| constr : nat -> list term -> term
| switch : term -> list (nat * term) -> term.

Fixpoint term_ind2 (P : term -> Prop)
         (Hbvar : forall n, P (bvar n))
         (Hfvar : forall f, P (fvar f))
         (Hlam : forall t, P t -> P (lam t))
         (Happ : forall t1 t2, P t1 -> P t2 -> P (app t1 t2))
         (Hconstr : forall p l, Forall P l -> P (constr p l))
         (Hswitch : forall t m, P t -> Forall (fun '(p, t2) => P t2) m -> P (switch t m))
         (t : term) : P t :=
  match t with
  | bvar n => Hbvar n
  | fvar f => Hfvar f
  | lam t => Hlam t (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t)
  | app t1 t2 =>
    Happ t1 t2
      (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t1)
      (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t2)
  | constr p l =>
    Hconstr p l
            ((fix H (l : _) : Forall P l :=
              match l with
              | nil => @Forall_nil _ _
              | cons t l => @Forall_cons _ _ t l (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t) (H l)
              end) l)
  | switch t m =>
    Hswitch t m
            (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t)
            ((fix H (m : _) : Forall (fun '(p, t2) => P t2) m :=
              match m with
              | nil => @Forall_nil _ _
              | cons (p, t2) m => @Forall_cons _ _ (p, t2) m (term_ind2 P Hbvar Hfvar Hlam Happ Hconstr Hswitch t2) (H m)
              end) m)
  end.

Fixpoint substb k u t :=
  match t with
  | bvar i => if Nat.eq_dec i k then u else bvar i
  | fvar x => fvar x
  | lam t => lam (substb (S k) u t)
  | app t1 t2 => app (substb k u t1) (substb k u t2)
  | constr p l => constr p (map (substb k u) l)
  | switch t m => switch (substb k u t) (map (fun '(p, t2) => (p, substb (p + k) u t2)) m)
  end.

Fixpoint closeb k x t :=
  match t with
  | bvar i => bvar i
  | fvar y => if freevar_eq_dec x y then bvar k else fvar y
  | lam t => lam (closeb (S k) x t)
  | app t1 t2 => app (closeb k x t1) (closeb k x t2)
  | constr p l => constr p (map (closeb k x) l)
  | switch t m => switch (closeb k x t) (map (fun '(p, t2) => (p, closeb (p + k) x t2)) m)
  end.

Notation "t [ k <- u ]" := (substb k u t) (at level 67).
Notation "t ^^ u" := (t [ 0 <- u ]) (at level 67).
Notation "t ^ x" := (t ^^ (fvar x)).

Fixpoint substf x u t :=
  match t with
  | bvar i => bvar i
  | fvar y => if freevar_eq_dec x y then u else fvar y
  | lam t => lam (substf x u t)
  | app t1 t2 => app (substf x u t1) (substf x u t2)
  | constr p l => constr p (map (substf x u) l)
  | switch t m => switch (substf x u t) (map (fun '(p, t2) => (p, substf x u t2)) m)
  end.

Notation "t [ x := u ]" := (substf x u t) (at level 67).

Fixpoint fv t :=
  match t with
  | bvar i => nil
  | fvar x => x :: nil
  | lam t => fv t
  | app t1 t2 => fv t1 ++ fv t2
  | constr p l => concat (map fv l)
  | switch t m => fv t ++ concat (map (fun '(p, t2) => fv t2) m)
  end.

Lemma substf_fv :
  forall t u x, x \notin fv t -> t [ x := u ] = t.
Proof.
  induction t using term_ind2; intros u x Hx; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; intuition congruence.
  - f_equal; apply IHt; auto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
  - f_equal. erewrite map_ext_in; [apply map_id|].
    intros t Ht. simpl. rewrite Forall_forall in H. apply H; [assumption|].
    rewrite concat_In in Hx. intros Hx2; apply Hx. eexists.
    split; [eassumption|]. apply in_map. assumption.
  - rewrite in_app_iff in Hx.
    f_equal; [apply IHt; tauto|].
    erewrite map_ext_in; [apply map_id|]. intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. apply (H (p, t2)); [assumption|].
    rewrite concat_In in Hx. intros Hx2; apply Hx; right; eexists.
    split; [eassumption|]. rewrite in_map_iff; eexists; split; [|eassumption]; reflexivity.
Qed.

Fixpoint substb_list k l t :=
  match l with
  | nil => t
  | u :: l => substb k u (substb_list (S k) l t)
  end.

Fixpoint closeb_list k l t :=
  match l with
  | nil => t
  | x :: l => closeb_list (S k) l (closeb k x t)
  end.

Inductive lc : term -> Prop :=
| lc_var : forall v, lc (fvar v)
| lc_app : forall t1 t2, lc t1 -> lc t2 -> lc (app t1 t2)
| lc_lam : forall t L, (forall x, ~ In x L -> lc (t ^ x)) -> lc (lam t)
| lc_constr : forall p l, (forall t, In t l -> lc t) -> lc (constr p l)
| lc_switch : forall t m L, lc t -> (forall p t2 l, In (p, t2) m -> distinct L p l -> lc (substb_list 0 (map fvar l) t2)) -> lc (switch t m).

Definition body t := exists L, forall x, x \notin L -> lc (t ^ x).
Definition bodies n t := exists L, forall l, distinct L n l -> lc (substb_list 0 (map fvar l) t).

Lemma lc_lam_body : forall t, lc (lam t) <-> body t.
Proof.
  intros t. split.
  - intros H; inversion H; exists L; auto.
  - intros [L H]; econstructor; eauto.
Qed.

Lemma Forall_ex_mono_exchange :
  forall (A B : Type) (P : A -> list B -> Prop) (Hmono : forall x L1 L2, L1 \subseteq L2 -> P x L1 -> P x L2) l,
    Forall (fun x => exists L, P x L) l -> exists L, Forall (fun x => P x L) l.
Proof.
  intros A B P Hmono l H. induction H.
  - exists nil. constructor.
  - destruct H as [L1 H1].
    destruct IHForall as [L2 H2].
    exists (L1 ++ L2). constructor.
    + eapply Hmono; [|eassumption]. prove_list_inc.
    + eapply Forall_impl; [|eassumption]. simpl. intros a.
      apply Hmono. prove_list_inc.
Qed.

Lemma lc_switch_bodies :
  forall t m, lc (switch t m) <-> lc t /\ Forall (fun '(p, t2) => bodies p t2) m.
Proof.
  intros t m. split.
  - intros H; inversion H; subst. split; [assumption|].
    eapply Forall_impl; [|rewrite Forall_forall; intros pt2 Hin; refine (fun l => _); exact (H3 (fst pt2) (snd pt2) l ltac:(destruct pt2; simpl in *; assumption))].
    intros [p t2] Hbody. simpl in *. exists L. assumption.
  - intros [H1 H2]. assert (H3 : Forall (fun pt2 => bodies (fst pt2) (snd pt2)) m).
    { eapply Forall_impl; [|eassumption]. intros [p t2]. simpl. tauto. }
    apply Forall_ex_mono_exchange in H3.
    + destruct H3 as [L H3]. apply lc_switch with (L := L); [assumption|].
      rewrite Forall_forall in H3. intros p t2 l Hin Hdistinct.
      apply (H3 (p, t2)); assumption.
    + intros [p t2] L1 L2 Hinc H l Hl. apply H. simpl in *.
      eapply distinct_incl; eassumption.
Qed.

Lemma substb_lc_id_core :
  forall t u v k1 k2, k1 <> k2 -> t [ k2 <- v ] [ k1 <- u ] = t [ k2 <- v ] -> t [ k1 <- u ] = t.
Proof.
  induction t using term_ind2; intros u v k1 k2 Hk Heq; simpl in *; inversion Heq; try (f_equal; eauto).
  - repeat ( destruct Nat.eq_dec; simpl in * ); congruence.
  - erewrite map_ext_in; [apply map_id|rewrite <- Forall_forall].
    apply Forall2_map_eq in H1. rewrite Forall2_map_left, Forall2_map_same in H1.
    eapply Forall_impl; [|rewrite <- Forall_and; split; [apply H | apply H1]]. intros t.
    simpl. intros [Ht1 Ht2]; eapply Ht1; eassumption.
  - erewrite map_ext_in; [apply map_id|rewrite <- Forall_forall].
    apply Forall2_map_eq in H2. rewrite Forall2_map_left, Forall2_map_same in H2.
    eapply Forall_impl; [|rewrite <- Forall_and; split; [apply H | apply H2]]. intros [p t2].
    simpl. intros [H3 H4]; injection H4 as H4. f_equal; eapply H3; [|apply H4]. lia.
Qed.

Lemma substb_list_lc_id_core :
  forall t u l k1 k2, (k1 < k2 \/ k2 + length l <= k1) ->
                 (substb_list k2 l t) [ k1 <- u ] = substb_list k2 l t -> t [ k1 <- u ] = t.
Proof.
  intros t u l. revert t. induction l as [|v l]; intros t.
  - intros. simpl in *. assumption.
  - intros. simpl in *. eapply substb_lc_id_core in H0; [|lia].
    eapply IHl; [|eassumption]. lia.
Qed.

Lemma substb_lc_id : forall t u, lc t -> forall k, t [ k <- u ] = t.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - intros; simpl; rewrite IHlc1, IHlc2; reflexivity.
  - intros k. simpl. f_equal. pick x \notin L as Hx.
    eapply substb_lc_id_core with (k2 := 0); eauto.
  - intros k. simpl. f_equal.
    erewrite map_ext_in; [apply map_id|]. simpl.
    intros; apply H0; assumption.
  - intros k. simpl. f_equal.
    + apply IHlc.
    + erewrite map_ext_in; [apply map_id|]. simpl.
      intros [p t3] Hin. simpl. f_equal.
      pickn p distinct l \notin L as Hl.
      eapply H1 in Hin; [|eassumption].
      eapply substb_list_lc_id_core; [|eassumption].
      erewrite map_length, distinct_length by eassumption.
      lia.
Qed.

Lemma substb_substf :
  forall t u v k x, lc u -> t [ k <- v ] [ x := u ] = t [ x := u ] [ k <- v [ x := u ]].
Proof.
  induction t using term_ind2.
  - intros; simpl. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl. destruct freevar_eq_dec; [|reflexivity].
    rewrite substb_lc_id; auto.
  - intros; simpl. f_equal. apply IHt; auto.
  - intros; simpl. f_equal; auto.
  - intros; simpl. f_equal. rewrite !map_map.
    apply map_ext_in; rewrite <- Forall_forall. eapply Forall_impl; [|eassumption].
    simpl. intros t Ht. apply Ht. assumption.
  - intros; simpl. f_equal; [apply IHt; assumption|].
    rewrite !map_map. apply map_ext_in; rewrite <- Forall_forall. eapply Forall_impl; [|eassumption].
    intros [p t2] Hpt2. simpl in *. f_equal. apply Hpt2. assumption.
Qed.

Lemma substb_list_substf :
  forall vs t u k x, lc u -> (substb_list k vs t) [ x := u ] = substb_list k (map (substf x u) vs) (t [ x := u ]).
Proof.
  induction vs as [|v vs]; intros t u k x Hlc.
  - reflexivity.
  - simpl. rewrite substb_substf by assumption.
    f_equal. apply IHvs. assumption.
Qed.

Lemma substf_substb_free :
  forall t u v k x, x ∉ fv v -> lc u -> t [x := u] [k <- v] = t [k <- v] [x := u].
Proof.
  intros. rewrite substb_substf; [|assumption].
  f_equal. rewrite substf_fv; auto.
Qed.

Lemma substf_substb_list_free :
  forall t u l k x, (forall v, v \in l -> x ∉ fv v) -> lc u -> substb_list k l (t [x := u]) = (substb_list k l t) [ x := u ].
Proof.
  intros t u l. revert t; induction l as [|v l]; intros t k x Hl Hlc.
  - reflexivity.
  - simpl. rewrite IHl; [|intros v2 Hv2; apply Hl; simpl; right; assumption|assumption].
    apply substf_substb_free; [apply Hl; simpl; tauto|assumption].
Qed.

Lemma substf_substb_free2 :
  forall t u v k x, x ∉ fv t -> t [k <- v] [x := u] = t [k <- v [x := u]].
Proof.
  induction t using term_ind2.
  - intros; simpl in *. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl in *. destruct freevar_eq_dec; intuition congruence.
  - intros; simpl in *. f_equal. auto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
  - intros u v k x Hx. simpl in *. f_equal. rewrite map_map.
    apply map_ext_in; rewrite Forall_forall in H. intros t Ht; apply H; [assumption|].
    rewrite concat_In in Hx. intros Hx2; apply Hx. exists (fv t). split; [assumption|apply in_map; assumption].
  - intros u v k x Hx. simpl in *. rewrite in_app_iff in Hx. f_equal.
    + apply IHt. tauto.
    + rewrite map_map. apply map_ext_in; rewrite Forall_forall in H.
      intros [p t2] Hin. f_equal; apply (H (p, t2)); [assumption|].
      intros Hx2; apply Hx; right. rewrite concat_In. exists (fv t2). split; [assumption|].
      rewrite in_map_iff. exists (p, t2); simpl. tauto.
Qed.

Lemma closeb_id :
  forall t k x, x \notin fv t -> closeb k x t = t.
Proof.
  intros t. induction t using term_ind2.
  - intros; reflexivity.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in*; f_equal; auto.
  - intros; simpl in *. f_equal. erewrite map_ext_in; [apply map_id|].
    intros t Ht. simpl. rewrite Forall_forall in H. apply H; [assumption|].
    intros Hx. apply H0. rewrite concat_In. exists (fv t); split; [assumption|apply in_map; assumption].
  - intros; simpl in *. f_equal.
    + apply IHt. rewrite in_app_iff in H0; tauto.
    + erewrite map_ext_in; [apply map_id|]. intros [p t2] Hpt2; simpl; f_equal.
      rewrite Forall_forall in H; apply (H (p, t2)); [assumption|].
      rewrite in_app_iff in H0; intros Hx; apply H0; right.
      rewrite concat_In. exists (fv t2); split; [assumption|].
      rewrite in_map_iff; exists (p, t2); simpl; tauto.
Qed.

Lemma closeb_substf_free :
  forall t u k x y, x <> y -> x \notin fv u -> (closeb k x t) [y := u] = closeb k x (t [y := u]).
Proof.
  intros t. induction t using term_ind2.
  - intros; simpl; reflexivity.
  - intros; simpl; repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite closeb_id; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal. rewrite !map_map.
    apply map_ext_in. intros t Ht. rewrite Forall_forall in H; apply H; assumption.
  - intros; simpl in *; f_equal.
    + apply IHt; auto.
    + rewrite !map_map. apply map_ext_in. intros [p t2] Hpt2. f_equal.
      rewrite Forall_forall in H; apply (H (p, t2)); assumption.
Qed.

Lemma substf_lc : forall t, lc t -> forall u x, lc u -> lc (t [x := u]).
Proof.
  intros t Ht. induction Ht; intros u x Hu.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; auto.
  - simpl. apply lc_lam with (L := x :: L). intros y Hy.
    rewrite substf_substb_free; [|simpl in *; intuition congruence|assumption].
    apply H0; simpl in *; tauto.
  - simpl. constructor.
    intros t Ht. rewrite in_map_iff in Ht. destruct Ht as (t1 & <- & Ht1).
    apply H0; assumption.
  - simpl. apply lc_switch with (L := x :: L).
    + apply IHHt. assumption.
    + intros p t2 l Hpt2 Hl.
      rewrite in_map_iff in Hpt2. destruct Hpt2 as ([p2 t3] & Heq & Hpt3).
      injection Heq as -> <-.
      rewrite substf_substb_list_free; [| |assumption].
      * eapply H0; [eassumption| |assumption].
        eapply distinct_incl; [|eassumption]. prove_list_inc.
      * intros v Hv. rewrite in_map_iff in Hv. destruct Hv as (x1 & <- & Hx1).
        simpl. intros [-> | []]. eapply distinct_distinct; [eassumption| |eassumption]; simpl; tauto.
Qed.

Lemma substb_is_substf :
  forall t u x, x ∉ fv t -> t ^^ u = t ^ x [x := u].
Proof.
  intros t u x Hx.
  rewrite substf_substb_free2; [|assumption].
  simpl. destruct freevar_eq_dec; tauto.
Qed.

Lemma substb_lc : forall t u, body t -> lc u -> lc (t ^^ u).
Proof.
  intros t u [L Ht] Hu.
  pick fresh x as Hx.
  rewrite substb_is_substf with (x := x) by (use_fresh x).
  apply substf_lc; [apply Ht; use_fresh x | apply Hu].
Unshelve. all: exact nil.
Qed.

Lemma lc_open_gen :
  forall t x, body t -> lc (t ^ x).
Proof.
  intros.
  apply substb_lc; [assumption | constructor].
Qed.

Lemma substb_fv :
  forall t k u, fv (t [ k <- u ]) \subseteq fv t ++ fv u.
Proof.
  induction t using term_ind2; intros k u.
  - simpl. destruct Nat.eq_dec; simpl; prove_list_inc.
  - simpl. prove_list_inc.
  - simpl. apply IHt.
  - simpl. rewrite IHt1, IHt2. prove_list_inc.
  - simpl. rewrite map_map. intros x Hx.
    rewrite in_app_iff, concat_map_In. rewrite concat_map_In in Hx. destruct Hx as (t & Hx & Ht).
    rewrite Forall_forall in H. eapply H in Hx; [|assumption]. rewrite in_app_iff in Hx; destruct Hx.
    + left. exists t. tauto.
    + tauto.
  - simpl. rewrite map_map. rewrite IHt. intros x Hx.
    rewrite !in_app_iff in *; destruct Hx as [Hx | Hx]; [tauto|].
    rewrite concat_map_In in *. destruct Hx as ([p t2] & Hx & Hpt2).
    rewrite Forall_forall in H. eapply (H (p, t2)) in Hx; [|assumption].
    rewrite in_app_iff in Hx; destruct Hx.
    + left. right. exists (p, t2). tauto.
    + tauto.
Qed.

Lemma substb_fv2 :
  forall t k u, fv t \subseteq fv (t [ k <- u ]).
Proof.
  induction t using term_ind2.
  - intros; simpl. prove_list_inc.
  - intros; simpl. reflexivity.
  - intros; simpl. apply IHt.
  - intros; simpl. rewrite <- IHt1, <- IHt2. reflexivity.
  - intros; simpl. intros x Hx. rewrite concat_map_In in *. destruct Hx as (t & Hx & Ht). exists (substb k u t).
    split; [|apply in_map; assumption].
    rewrite Forall_forall in H; apply H; assumption.
  - intros; simpl. intros x Hx. rewrite in_app_iff, concat_map_In in *.
    destruct Hx as [Hx | ([p t2] & Hx & Hpt2)].
    + left. apply IHt. assumption.
    + right. exists (p, substb (p + k) u t2). split; [|rewrite in_map_iff; exists (p, t2); tauto].
      rewrite Forall_forall in H; apply (H (p, t2)); assumption.
Qed.

Lemma substb_list_fv :
  forall us t k x, (forall u, u \in us -> x \notin fv u) -> x \notin fv t -> x \notin fv (substb_list k us t).
Proof.
  induction us as [|u us].
  - intros. simpl. assumption.
  - intros. simpl. rewrite substb_fv, notin_app_iff. split; [|apply H; simpl; tauto].
    apply IHus; [intros; apply H; simpl; tauto|assumption].
Qed.

Lemma substb_list_fv2 :
  forall us t k, fv t \subseteq fv (substb_list k us t).
Proof.
  induction us as [|u us].
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHus. apply substb_fv2.
Qed.


Lemma close_open :
  forall t k x, x \notin fv t -> closeb k x (t [k <- fvar x]) = t.
Proof.
  intros t. induction t using term_ind2.
  - intros; simpl; destruct Nat.eq_dec; simpl; try destruct freevar_eq_dec; congruence.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
  - intros; simpl in *.
    f_equal. erewrite map_map, map_ext_in; [apply map_id|].
    intros t Ht. simpl. rewrite Forall_forall in H; apply H; [assumption|].
    rewrite concat_map_In in H0. intros Hx; apply H0; exists t; tauto.
  - intros; simpl in *; rewrite in_app_iff in *. f_equal.
    + apply IHt. tauto.
    + erewrite map_map, map_ext_in; [apply map_id|].
      intros [p t2] Hpt2. simpl. f_equal.
      rewrite Forall_forall in H; apply (H (p, t2)); [assumption|].
      intros Hx; apply H0; right. rewrite concat_map_In. exists (p, t2); simpl; tauto.
Qed.

Lemma close_open_list :
  forall xs t k p, distinct (fv t) p xs -> closeb_list k xs (substb_list k (map fvar xs) t) = t.
Proof.
  induction xs as [|x xs].
  - intros. simpl. reflexivity.
  - intros t k p H. simpl. inversion H; subst. rewrite close_open.
    + eapply IHxs. eapply distinct_incl; [|eassumption]. prove_list_inc.
    + apply substb_list_fv; [|assumption].
      rewrite forall_map. intros y Hy [->|[]]. eapply distinct_distinct; [| |apply Hy]; [eassumption|].
      simpl. tauto.
Qed.

Lemma open_inj :
  forall x t1 t2, x \notin fv t1 -> x \notin fv t2 -> t1 ^ x = t2 ^ x -> t1 = t2.
Proof.
  intros.
  rewrite <- (close_open t1 0 x), <- (close_open t2 0 x); auto; congruence.
Qed.

Lemma open_close_core :
  forall t i j x y u, i <> j -> x <> y -> lc u -> y \notin fv t -> (closeb j x t) [j <- u] [i <- fvar y] = (closeb j x (t [i <- fvar y])) [j <- u].
Proof.
  intros t. induction t using term_ind2.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite substb_lc_id; auto.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite substb_lc_id; auto.
  - intros; simpl. f_equal.
    apply IHt; simpl in *; auto.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; tauto.
  - intros; simpl in *. f_equal.
    rewrite !map_map. apply map_ext_in. intros t Ht.
    rewrite Forall_forall in H. apply H; try tauto.
    intros Hy. apply H3. rewrite concat_map_In. exists t; tauto.
  - intros; simpl in *. rewrite in_app_iff in *. f_equal.
    + apply IHt; tauto.
    + rewrite !map_map. apply map_ext_in. intros [p t2] Hpt2. f_equal.
      rewrite Forall_forall in H; apply (H (p, t2)); try tauto.
      * lia.
      * intros Hy. apply H3. right. rewrite concat_map_In. exists (p, t2); simpl; tauto.
Qed.


Lemma open_list_inj :
  forall l k n t1 t2, distinct (fv t1 ++ fv t2) n l -> substb_list k (map fvar l) t1 = substb_list k (map fvar l) t2 -> t1 = t2.
Proof.
  induction l as [|x l].
  - intros; simpl in *. assumption.
  - intros; simpl in *. inversion H; subst.
    eapply IHl; [eapply distinct_incl; [|eassumption]; prove_list_inc|].
    erewrite <- close_open with (t := substb_list _ _ _), H0, close_open; [reflexivity| |].
    + apply substb_list_fv; [|rewrite in_app_iff in *; tauto].
      intros u Hu; rewrite in_map_iff in Hu; destruct Hu as (y & <- & Hy); apply notin_one; intros ->.
      eapply distinct_distinct; [| |eassumption]; [eassumption|]; simpl; tauto.
    + apply substb_list_fv; [|rewrite in_app_iff in *; tauto].
      intros u Hu; rewrite in_map_iff in Hu; destruct Hu as (y & <- & Hy); apply notin_one; intros ->.
      eapply distinct_distinct; [| |eassumption]; [eassumption|]; simpl; tauto.
Qed.

Lemma open_close_core_list :
  forall t i j p x ys u, (j < i \/ i + p <= j) -> distinct (x :: fv t) p ys -> lc u ->
                    substb_list i (map fvar ys) ((closeb j x t) [j <- u]) =
                    (closeb j x (substb_list i (map fvar ys) t)) [j <- u].
Proof.
  intros t i j p x ys u. revert t i j p x u; induction ys as [|y ys]; intros t i j p x u Hij Hys Hlc.
  - simpl. reflexivity.
  - simpl. inversion Hys; subst.
    erewrite IHys; [| |eapply distinct_incl; [|eassumption]; prove_list_inc|assumption]; [|lia].
    apply open_close_core.
    + lia.
    + intros ->; simpl in *; tauto.
    + assumption.
    + apply substb_list_fv; [|simpl in *; tauto].
      intros v Hv; rewrite in_map_iff in Hv; destruct Hv as (z & <- & Hz); apply notin_one; intros ->.
      eapply distinct_distinct; [| |eassumption]; [eassumption|]; simpl; tauto.
Qed.

Lemma open_close :
  forall t, lc t -> forall k x u, lc u -> substb k u (closeb k x t) = t [x := u].
Proof.
  intros t H. induction H; intros k x u Hu.
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    pick fresh y.
    apply (open_inj y); try use_fresh y.
    rewrite open_close_core by (use_fresh y || tauto || discriminate).
    rewrite substf_substb_free by (assumption || apply notin_one; use_fresh y).
    apply H0; [use_fresh y | assumption].
  - simpl. f_equal. rewrite map_map. apply map_ext_in.
    intros t Ht. apply H0; assumption.
  - simpl. f_equal.
    + apply IHlc. assumption.
    + rewrite map_map. apply map_ext_in.
      intros [p t2] Hpt2. f_equal.
      pickn p distinct xs \notin (x :: L ++ fv t2 ++ fv (closeb (p + k) x t2 [p + k <- u]) ++ fv (t2 [x := u])) as Hxs.
      apply open_list_inj with (l := xs) (k := 0) (n := p); [eapply distinct_incl; [|eassumption]; prove_list_inc|].
      specialize (H1 p t2 xs Hpt2 ltac:(eapply distinct_incl; [|eassumption]; prove_list_inc) (p + k) x u Hu).
      rewrite substf_substb_list_free; [| |assumption].
      * rewrite <- H1. eapply open_close_core_list; [|eapply distinct_incl; [|eassumption]|]; [lia|prove_list_inc|assumption].
      * intros v Hv; rewrite in_map_iff in Hv; destruct Hv as (y & <- & Hy).
        intros [-> | []]. eapply distinct_distinct; [eassumption| |eassumption]. simpl. tauto.
Unshelve. all: exact nil.
Qed.

Lemma substf_id :
  forall x t, t [x := fvar x] = t.
Proof.
  intros x t; induction t using term_ind2; simpl; try congruence.
  - destruct freevar_eq_dec; congruence.
  - f_equal. erewrite map_ext_in; [apply map_id|]. intros t Ht.
    rewrite Forall_forall in H; apply H. assumption.
  - f_equal; [assumption|].
    erewrite map_ext_in; [apply map_id|]. intros [p t2] Hpt2.
    f_equal. rewrite Forall_forall in H; apply (H (p, t2)). assumption.
Qed.

Lemma open_close_var :
  forall t, lc t -> forall k x, substb k (fvar x) (closeb k x t) = t.
Proof.
  intros. rewrite open_close, substf_id; auto.
  constructor.
Qed.

Lemma fv_substf_iff :
  forall t x y u, y \in fv (t [ x := u ]) <-> (y \in fv t /\ y <> x) \/ (x \in fv t /\ y \in fv u).
Proof.
  induction t using term_ind2.
  - intros; simpl in *; tauto.
  - intros; simpl in *. destruct freevar_eq_dec.
    + subst. intuition congruence.
    + simpl. intuition congruence.
  - intros; simpl in *; apply IHt.
  - intros; simpl in *; rewrite !in_app_iff, IHt1, IHt2. tauto.
  - intros; simpl in *. rewrite map_map, !concat_map_In.
    rewrite Forall_forall in H. split.
    + intros (t & Hy & Ht). rewrite H in Hy by assumption.
      destruct Hy; [left | right]; split; try (exists t); tauto.
    + intros [[(t & Hy1 & Ht) Hy2] | [(t & Hx & Ht) Hy]]; exists t; rewrite H; tauto.
  - intros; simpl in *. rewrite map_map, !in_app_iff, !concat_map_In.
    rewrite Forall_forall in H. rewrite IHt. split.
    + intros [Hy | ([p t2] & Hy & Hpt2)]; [tauto|].
      specialize (H (p, t2) Hpt2). simpl in H. rewrite H in Hy.
      destruct Hy; [left | right]; split; try (right; exists (p, t2)); tauto.
    + intros [[[Hy1 | ([p t2] & Hy1 & Hpt2)] Hy2] | [[Hx | ([p t2] & Hx & Hpt2)] Hy]];
        try tauto; specialize (H (p, t2) Hpt2); simpl in H; right; exists (p, t2); rewrite H; tauto.
Qed.

Lemma fv_substf :
  forall x t u, fv (t [ x := u ]) \subseteq fv t ++ fv u.
Proof.
  intros x t u y. rewrite fv_substf_iff, in_app_iff. tauto.
Qed.

Lemma fv_substf2 :
  forall t x u, fv t \subseteq x :: fv (t [ x := u ]).
Proof.
  intros t x u y. simpl. rewrite fv_substf_iff.
  destruct (freevar_eq_dec x y); intuition congruence.
Qed.

Lemma fv_substf3 :
  forall t x u, list_remove x (fv t) \subseteq fv (t [ x := u ]).
Proof.
  intros t x u y. rewrite list_remove_correct, fv_substf_iff.
  intuition congruence.
Qed.

Lemma fv_substf4 :
  forall t x u, x \in fv t -> fv u \subseteq fv (t [ x := u ]).
Proof.
  intros t x u Hx y. rewrite fv_substf_iff. tauto.
Qed.

Lemma substf_substf :
  forall t x1 x2 u1 u2, x1 <> x2 -> x1 \notin fv u2 -> t [ x1 := u1 ] [ x2 := u2 ] = t [ x2 := u2 ] [ x1 := u1 [ x2 := u2 ] ].
Proof.
  induction t using term_ind2.
  - intros; simpl in *; reflexivity.
  - intros; simpl in *.
    repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite substf_fv; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal.
    rewrite !map_map. apply map_ext_in.
    rewrite Forall_forall in H. intros t Ht; apply H; assumption.
  - intros; simpl in *; f_equal.
    + apply IHt; assumption.
    + rewrite !map_map; apply map_ext_in.
      rewrite Forall_forall in H. intros [p t2] Hpt2; f_equal; apply (H (p, t2)); assumption.
Qed.

Lemma substf_exchange :
  forall t u v x y, x <> y -> x \notin fv v \/ y \notin fv u -> t [ x := u ] [ y := v [ x := u ] ] = t [ y := v ] [ x := u [ y := v ] ].
Proof.
  intros t u v x y Hxy [Hx | Hy].
  - rewrite substf_fv with (x := x) (t := v) by assumption.
    rewrite substf_substf with (u1 := u) by assumption. reflexivity.
  - rewrite substf_fv with (x := y) (t := u) by assumption.
    rewrite substf_substf with (u1 := v) by congruence.
    reflexivity.
Qed.

Lemma closeb_fv_eq :
  forall x k t, fv (closeb k x t) == list_remove x (fv t).
Proof.
  intros x k t y. rewrite list_remove_correct. revert k; induction t using term_ind2; intros k; simpl in *.
  - tauto.
  - destruct freevar_eq_dec; simpl in *; intuition congruence.
  - rewrite IHt. tauto.
  - rewrite !in_app_iff, IHt1, IHt2. tauto.
  - rewrite map_map, !concat_map_In. rewrite Forall_forall in H. split.
    + intros (t & Hy & Ht); rewrite H in Hy by assumption; split; [exists t|]; tauto.
    + intros [(t & Hy & Ht) Hxy]; exists t; rewrite H; tauto.
  - rewrite !in_app_iff, map_map, !concat_map_In, IHt. rewrite Forall_forall in H. split.
    + intros [Hy | ([p t2] & Hy & Hpt2)]; [tauto|].
      specialize (H (p, t2) Hpt2); simpl in H; rewrite H in Hy. split; [|tauto].
      right; exists (p, t2); tauto.
    + intros [[Hy | ([p t2] & Hy & Hpt2)] Hxy]; [tauto|]. right.
      specialize (H (p, t2) Hpt2); simpl in H. exists (p, t2); rewrite H. tauto.
Qed.

Lemma fv_closeb :
  forall t k x, fv (closeb k x t) \subseteq fv t.
Proof.
  intros. rewrite closeb_fv_eq. intros y Hy; rewrite list_remove_correct in Hy; tauto.
Qed.

Lemma closeb_var_free :
  forall x k t, x \notin fv (closeb k x t).
Proof.
  intros. rewrite closeb_fv_eq. rewrite list_remove_correct. tauto.
Qed.


Inductive lc_at : term -> nat -> Prop :=
| lc_at_fvar : forall x k, lc_at (fvar x) k
| lc_at_bvar : forall n k, n < k -> lc_at (bvar n) k
| lc_at_lam : forall t k, lc_at t (S k) -> lc_at (lam t) k
| lc_at_app : forall t1 t2 k, lc_at t1 k -> lc_at t2 k -> lc_at (app t1 t2) k
| lc_at_constr : forall p l k, (forall t, t \in l -> lc_at t k) -> lc_at (constr p l) k
| lc_at_switch : forall t m k, lc_at t k -> (forall p t2, (p, t2) \in m -> lc_at t2 (p + k)) -> lc_at (switch t m) k.

Lemma lc_at_substb_id :
  forall t k1 k2 u, lc_at t k1 -> k1 <= k2 -> t [ k2 <- u ] = t.
Proof.
  induction t using term_ind2; intros k1 k2 u H1 H2.
  - simpl. inversion H1; subst. destruct Nat.eq_dec; [lia|reflexivity].
  - reflexivity.
  - simpl. f_equal. inversion H1; subst.
    eapply IHt; [eassumption|]. lia.
  - simpl. inversion H1; subst. f_equal; eauto.
  - simpl. f_equal. erewrite map_ext_in; [apply map_id|].
    intros t Ht. simpl.
    inversion H1; subst.
    rewrite Forall_forall in H; eapply H; [eassumption|apply H5; assumption|assumption].
  - simpl. inversion H1; subst. f_equal.
    + eapply IHt; eassumption.
    + erewrite map_ext_in; [apply map_id|].
      intros [p t2] Hpt2. f_equal. rewrite Forall_forall in H.
      eapply (H (p, t2) Hpt2); [eapply H6; eassumption|]. lia.
Qed.

Lemma lc_at_inc :
  forall t k1 k2, lc_at t k1 -> k1 <= k2 -> lc_at t k2.
Proof.
  intros t k1 k2 H; revert k2; induction H; intros k2 Hk.
  - constructor.
  - constructor; lia.
  - constructor. apply IHlc_at. lia.
  - constructor; [apply IHlc_at1|apply IHlc_at2]; assumption.
  - constructor. intros t Ht; apply H0; assumption.
  - constructor; [apply IHlc_at; assumption|].
    intros p t2 Hpt2; eapply H1; [eassumption|]; lia.
Qed.

Lemma lc_at_substb_lc_at :
  forall t k u, lc_at u 0 -> lc_at t (S k) -> lc_at (t [ k <- u ]) k.
Proof.
  induction t using term_ind2; intros k u H1 H2.
  - simpl. destruct Nat.eq_dec.
    + eapply lc_at_inc; [eassumption|lia].
    + inversion H2. constructor. lia.
  - simpl; constructor.
  - simpl. inversion H2; subst. constructor.
    apply IHt; assumption.
  - simpl. inversion H2; subst.
    constructor; [apply IHt1 | apply IHt2]; assumption.
  - simpl. constructor.
    intros t2 Ht2; rewrite in_map_iff in Ht2; destruct Ht2 as (t & <- & Ht).
    inversion H2; subst.
    rewrite Forall_forall in H. apply H; [assumption|assumption|apply H5; assumption].
  - simpl. inversion H2; subst. constructor.
    + apply IHt; assumption.
    + intros p2 t3 Hpt3; rewrite in_map_iff in Hpt3; destruct Hpt3 as ([p t2] & [= <- <-] & Hpt2).
      rewrite Forall_forall in H. apply (H (p, t2)); try assumption.
      replace (S (p + k)) with (p + S k) by lia. apply H6; assumption.
Qed.

Lemma lc_at_substb_list_lc_at :
  forall t k us, (forall u, In u us -> lc_at u 0) -> lc_at t (length us + k) -> lc_at (substb_list k us t) k.
Proof.
  intros t k us. revert t k; induction us as [|u us]; intros t k.
  - intros; simpl in *. assumption.
  - intros; simpl in *. apply lc_at_substb_lc_at; [apply H; tauto|].
    apply IHus; [intros u1 Hu1; apply H; tauto|].
    replace (length us + S k) with (S (length us + k)) by lia; assumption.
Qed.

Lemma lc_at_substb_lc_at2 :
  forall t k u, lc_at (t [ k <- u ]) k -> lc_at t (S k).
Proof.
  induction t using term_ind2; intros k u Hlc.
  - simpl in *. destruct Nat.eq_dec.
    + constructor. lia.
    + inversion Hlc. constructor. lia.
  - simpl; constructor.
  - simpl. inversion Hlc; subst. constructor.
    eapply IHt; eassumption.
  - simpl. inversion Hlc; subst.
    constructor; [eapply IHt1 | eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor.
    rewrite Forall_forall in H. intros t Ht. eapply H; [eassumption|].
    apply H3. apply in_map. assumption.
  - inversion Hlc; subst. constructor; [eapply IHt; eassumption|].
    intros p t2 Hpt2. rewrite Forall_forall in H. specialize (H (p, t2) Hpt2).
    simpl in H. replace (p + S k) with (S (p + k)) by lia.
    eapply H. apply H4. rewrite in_map_iff; exists (p, t2); split; [reflexivity|assumption].
Qed.

Lemma lc_at_substb_list_lc_at2 :
  forall t k us, lc_at (substb_list k us t) k -> lc_at t (length us + k).
Proof.
  intros t k us. revert t k; induction us as [|u us]; intros t k.
  - intros; simpl in *. assumption.
  - intros; simpl in *.
    replace (S (length us + k)) with (length us + S k) by lia.
    apply IHus. eapply lc_at_substb_lc_at2. eassumption.
Qed.

Fixpoint size t :=
  match t with
  | bvar _ => 0
  | fvar _ => 0
  | lam t => S (size t)
  | app t1 t2 => S (Nat.max (size t1) (size t2))
  | constr p l => smallest_above (map size l)
  | switch t m => Nat.max (S (size t)) (smallest_above (map (fun pt2 => size (snd pt2)) m))
  end.

Lemma open_size :
  forall t k x, size (t [ k <- fvar x ]) = size t.
Proof.
  induction t using term_ind2; intros k x; unfold size, substb; fold size; fold substb.
  - destruct Nat.eq_dec; reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite map_map. f_equal.
    apply map_ext_in. rewrite Forall_forall in H. intros t Ht; apply H; assumption.
  - rewrite IHt. f_equal. rewrite map_map. f_equal.
    apply map_ext_in. rewrite Forall_forall in H. intros [p t2] Hpt2; apply (H (p, t2)); assumption.
Qed.

Lemma open_list_size :
  forall t k xs, size (substb_list k (map fvar xs) t) = size t.
Proof.
  intros t k xs; revert t k; induction xs as [|x xs]; intros t k.
  - reflexivity.
  - simpl. rewrite open_size. apply IHxs.
Qed.

Lemma lc_at_lc :
  forall t, lc t <-> lc_at t 0.
Proof.
  intros t. split.
  - intros H. induction H.
    + constructor.
    + constructor; assumption.
    + constructor. pick x \notin L as Hx. eapply lc_at_substb_lc_at2. apply H0; eassumption.
    + constructor. assumption.
    + constructor; [assumption|].
      intros p t2 Hpt2. pickn p distinct xs \notin L as Hxs.
      specialize (H1 _ _ _ Hpt2 Hxs).
      apply lc_at_substb_list_lc_at2 in H1. rewrite map_length in H1.
      erewrite distinct_length in H1; eassumption.
  - remember (size t) as n. revert t Heqn. refine (lt_wf_ind n (fun n => _) _). clear n. intros n Hrec t Hsize H.
    destruct t.
    + inversion H; lia.
    + constructor.
    + simpl in Hsize. subst.
      inversion H; subst.
      apply lc_lam with (L := nil).
      intros x _. eapply Hrec; [|reflexivity|]; [rewrite open_size; lia|].
      apply lc_at_substb_lc_at; [constructor|assumption].
    + simpl in Hsize. subst. inversion H; subst.
      constructor.
      all: eapply Hrec; [|reflexivity|]; [lia|assumption].
    + simpl in Hsize. subst. inversion H; subst.
      constructor. intros t Ht. eapply Hrec; [|reflexivity|apply H3; assumption].
      apply smallest_above_map_gt. exists t. split; [reflexivity|assumption].
    + unfold size in Hsize. fold size in Hsize. subst. inversion H; subst.
      apply lc_switch with (L := nil).
      * eapply Hrec; [|reflexivity|assumption]. lia.
      * intros p t2 xs Hpt2 Hxs.
        eapply Hrec; [|reflexivity|]; [rewrite open_list_size, Nat.max_lt_iff; right; apply smallest_above_map_gt;
                                       exists (p, t2); simpl; split; [reflexivity|assumption]|].
        apply lc_at_substb_list_lc_at; [|erewrite map_length, distinct_length; [|eassumption]; apply H4; assumption].
        intros u Hu; rewrite in_map_iff in Hu; destruct Hu as (x & <- & Hx). constructor.
Qed.

Lemma substf_lc2 :
  forall t x u, lc (t [ x := u ]) -> lc t.
Proof.
  intros. rewrite lc_at_lc in *.
  remember 0 as k. clear Heqk.
  revert k H. induction t using term_ind2; intros k Hlc; simpl in *.
  - assumption.
  - constructor.
  - constructor. apply IHt. inversion Hlc; subst; assumption.
  - inversion Hlc; subst. constructor; [apply IHt1 | apply IHt2]; assumption.
  - inversion Hlc; subst. constructor. intros t Ht.
    rewrite Forall_forall in H. apply H; [assumption|]. apply H3, in_map. assumption.
  - inversion Hlc; subst. constructor.
    + apply IHt. assumption.
    + intros p t2 Hpt2. rewrite Forall_forall in H; apply (H (p, t2)); [assumption|].
      apply H4. rewrite in_map_iff; exists (p, t2); simpl; tauto.
Qed.

Lemma substb_list_lc : forall us t, bodies (length us) t -> (forall u, u \in us -> lc u) -> lc (substb_list 0 us t).
Proof.
  intros us t Hbodies Hlc.
  rewrite lc_at_lc. apply lc_at_substb_list_lc_at; [intros u Hu; rewrite <- lc_at_lc; apply Hlc; assumption|].
  destruct Hbodies as [L Ht]. pickn (length us) distinct xs \notin L as Hxs. specialize (Ht xs Hxs).
  rewrite lc_at_lc in Ht. apply lc_at_substb_list_lc_at2 in Ht.
  erewrite map_length, distinct_length in Ht; eassumption.
Qed.


Lemma body_substf :
  forall t u x, lc u -> body (t [x := u]) <-> body t.
Proof.
  intros. split.
  - intros [L HL]. exists (x :: L). intros y Hy. simpl in *. specialize (HL y ltac:(tauto)).
    rewrite substf_substb_free in HL by (simpl; intuition congruence).
    eapply substf_lc2; eassumption.
  - intros [L HL]. exists (x :: L). intros y Hy. simpl in *. specialize (HL y ltac:(tauto)).
    rewrite substf_substb_free by (simpl; intuition congruence).
    apply substf_lc; assumption.
Qed.

Lemma bodies_lc_at :
  forall n t, bodies n t <-> lc_at t n.
Proof.
  intros n t. split.
  - intros [L HL]. pickn n distinct xs \notin L as Hxs.
    specialize (HL xs Hxs). rewrite lc_at_lc in HL.
    apply lc_at_substb_list_lc_at2 in HL.
    erewrite map_length, distinct_length, plus_0_r in HL; [|eassumption]. assumption.
  - intros H. exists nil. intros xs Hxs. rewrite lc_at_lc.
    apply lc_at_substb_list_lc_at; [rewrite forall_map; intros; constructor|].
    erewrite map_length, distinct_length, plus_0_r; eassumption.
Qed.

Lemma bodies_substf :
  forall n t u x, lc u -> bodies n (t [x := u]) <-> bodies n t.
Proof.
  intros. split.
  - intros Ht. exists (x :: nil). intros ys Hys.
    eapply substf_lc2. rewrite <- substf_substb_list_free.
    + apply substb_list_lc; [erewrite map_length, distinct_length; eassumption|].
      rewrite forall_map; intros; constructor.
    + rewrite forall_map. simpl. intros y Hy [->|[]].
      eapply distinct_distinct; [eassumption| |eassumption]; simpl; tauto.
    + assumption.
  - intros Ht. exists (x :: nil). intros ys Hys.
    rewrite substf_substb_list_free.
    + apply substf_lc; [|assumption].
      apply substb_list_lc; [erewrite map_length, distinct_length; eassumption|].
      rewrite forall_map. intros; constructor.
    + rewrite forall_map. simpl. intros y Hy [->|[]].
      eapply distinct_distinct; [eassumption| |eassumption]; simpl; tauto.
    + assumption.
Qed.

Lemma open_close_at :
  forall t k x u, lc_at t k -> lc u -> substb k u (closeb k x t) = t [x := u].
Proof.
  intros t. induction t using term_ind2; intros k x u Hlct Hlcu.
  - simpl. inversion Hlct; subst. destruct Nat.eq_dec; [lia | reflexivity].
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. inversion Hlct; subst. f_equal; auto.
  - simpl. inversion Hlct; subst. f_equal; auto.
  - simpl. inversion Hlct; subst. f_equal. rewrite map_map. apply map_ext_in.
    intros t Ht. rewrite Forall_forall in H; apply H; auto.
  - simpl. inversion Hlct; subst. f_equal.
    + apply IHt; assumption.
    + rewrite map_map. apply map_ext_in.
      intros [p t2] Hpt2. f_equal.
      rewrite Forall_forall in H; apply (H (p, t2)); auto.
Qed.

Lemma open_close_var_at :
  forall t k x, lc_at t k -> substb k (fvar x) (closeb k x t) = t.
Proof.
  intros. rewrite open_close_at, substf_id; auto.
  constructor.
Qed.

Lemma open_close_var_list_at :
  forall xs k t, lc_at t k -> substb_list k (map fvar xs) (closeb_list k xs t) = t.
Proof.
  induction xs as [|x xs]; intros k t Hlc; [reflexivity|].
  simpl. rewrite IHxs.
  - apply open_close_var_at. assumption.
  - eapply lc_at_substb_lc_at2. rewrite open_close_var_at; assumption.
Qed.

Lemma open_close_var_list :
  forall xs k t, lc t -> substb_list k (map fvar xs) (closeb_list k xs t) = t.
Proof.
  intros. apply open_close_var_list_at.
  apply lc_at_lc in H. eapply lc_at_inc; [eassumption|]. lia.
Qed.

Lemma substb_list_app :
  forall us1 us2 k t, substb_list k (us1 ++ us2) t = substb_list k us1 (substb_list (length us1 + k) us2 t).
Proof.
  induction us1 as [|u us1].
  - intros; reflexivity.
  - intros; simpl; rewrite IHus1; f_equal; f_equal; f_equal; lia.
Qed.

Lemma closeb_list_app :
  forall xs1 xs2 k t, closeb_list k (xs1 ++ xs2) t = closeb_list (length xs1 + k) xs2 (closeb_list k xs1 t).
Proof.
  induction xs1 as [|x xs1].
  - intros; reflexivity.
  - intros; simpl; rewrite IHxs1; f_equal; lia.
Qed.

Lemma closeb_list_substf :
  forall ys k t x u, (forall y, y \in ys -> y \notin (x :: fv u)) -> closeb_list k ys (t [x := u]) = closeb_list k ys t [x := u].
Proof.
  induction ys as [|y ys]; intros k t x u Hys.
  - reflexivity.
  - simpl. rewrite <- IHys by (intros; apply Hys; simpl; tauto).
    f_equal. rewrite closeb_substf_free; [reflexivity| |].
    + intros ->. eapply Hys; simpl; left; reflexivity.
    + intros H. eapply Hys; [simpl; left; reflexivity|]. simpl. tauto.
Qed.

Lemma distinct_swap :
  forall L p x1 x2 xs, distinct L p (x1 :: x2 :: xs) <-> distinct L p (x2 :: x1 :: xs).
Proof.
  intros; revert x1 x2.
  enough (H : forall x1 x2, distinct L p (x1 :: x2 :: xs) -> distinct L p (x2 :: x1 :: xs)) by (intros; split; apply H).
  intros x1 x2 Hdistinct. inversion Hdistinct; subst.
  inversion H4; subst. constructor; [|constructor].
  - intros Hx2; apply H5; simpl; tauto.
  - intros [-> | H]; [|apply H3; assumption]. simpl in *; tauto.
  - eapply distinct_incl; [|eassumption]. prove_list_inc.
Qed.

Lemma distinct_app_cons :
  forall L p x xs1 xs2, distinct L p (x :: xs1 ++ xs2) <-> distinct L p (xs1 ++ x :: xs2).
Proof.
  intros L p x xs1; revert L p x; induction xs1 as [|y xs1]; intros L p x xs2; [reflexivity|].
  simpl. rewrite distinct_swap.
  split; intros H; inversion H; subst; constructor; try assumption; rewrite IHxs1 in *; assumption.
Qed.

Lemma distinct_app :
  forall L p xs1 xs2, distinct L p (xs1 ++ xs2) <-> distinct L p (xs2 ++ xs1).
Proof.
  intros L p.
  enough (H : forall xs1 xs2, distinct L p (xs1 ++ xs2) -> distinct L p (xs2 ++ xs1)) by (intros; split; apply H).
  intros xs1; revert L p; induction xs1 as [|x xs1]; intros L p xs2 H.
  - simpl in *. rewrite app_nil_r. assumption.
  - simpl in *. inversion H; subst. apply IHxs1 in H5.
    rewrite <- distinct_app_cons. constructor; assumption.
Qed.

Lemma closeb_list_fv_incl :
  forall xs k t, fv (closeb_list k xs t) \subseteq fv t.
Proof.
  induction xs as [|x xs].
  - reflexivity.
  - intros; simpl. rewrite IHxs. apply fv_closeb.
Qed.

Lemma closeb_list_vars_free :
  forall xs k t x, x \in xs -> x \notin fv (closeb_list k xs t).
Proof.
  induction xs as [|y xs]; intros k t x; [intros [] | intros [-> | Hx]]; simpl.
  - rewrite closeb_list_fv_incl. apply closeb_var_free.
  - apply IHxs. assumption.
Qed.

(** Multicontexts *)

Definition multicontext := (freevar * term)%type.

Definition fill_mctx (K : multicontext) (t : term) := (snd K) [ fst K := t ].
Definition empty_mctx (t : term) : multicontext := (proj1_sig (fresh (fv t)), t).
Definition app_mctx (K1 K2 : multicontext) : multicontext :=
  let x := proj1_sig (fresh (fv (snd K1) ++ (fv (snd K2)))) in (x, app (fill_mctx K1 (fvar x)) (fill_mctx K2 (fvar x))).
Definition lam_mctx (K : multicontext) : multicontext := (fst K, lam (snd K)).
Definition constr_mctx (p : nat) (Ks : list multicontext) : multicontext :=
  let x := proj1_sig (fresh (concat (map (fun K => fv (snd K)) Ks))) in
  (x, constr p (map (fun K => fill_mctx K (fvar x)) Ks)).
Definition switch_mctx (K : multicontext) (m : list (nat * multicontext)) : multicontext :=
  let x := proj1_sig (fresh (fv (snd K) ++ concat (map (fun '(p, K2) => fv (snd K2)) m))) in
  (x, switch (fill_mctx K (fvar x)) (map (fun '(p, K2) => (p, fill_mctx K2 (fvar x))) m)).

Lemma fill_empty : forall t1 t2, fill_mctx (empty_mctx t1) t2 = t1.
Proof.
  intros t1 t2. unfold fill_mctx, empty_mctx. simpl.
  apply substf_fv. apply proj2_sig.
Qed.

Lemma fill_fill : forall K x t, x \notin fv (snd K) -> fill_mctx (x, fill_mctx K (fvar x)) t = fill_mctx K t.
Proof.
  intros K x t Hx. destruct K as [y u]; simpl in *. unfold fill_mctx; simpl.
  induction u using term_ind2.
  - simpl. reflexivity.
  - simpl. destruct freevar_eq_dec.
    + simpl. destruct freevar_eq_dec; congruence.
    + simpl in *. destruct freevar_eq_dec; intuition congruence.
  - simpl in *. f_equal. apply IHu. assumption.
  - simpl in *. rewrite in_app_iff in Hx. f_equal.
    + apply IHu1. tauto.
    + apply IHu2. tauto.
  - simpl in *. f_equal. rewrite map_map. apply map_ext_in.
    intros u Hu. rewrite Forall_forall in H. apply H; [assumption|].
    rewrite concat_map_In in Hx. intros Hx2; apply Hx; exists u; tauto.
  - simpl in *. rewrite in_app_iff, concat_map_In in Hx. f_equal.
    + apply IHu. tauto.
    + rewrite map_map. apply map_ext_in.
      intros [p t2] Hpt2. f_equal. rewrite Forall_forall in H. apply (H (p, t2)); [assumption|].
      intros Hx2; apply Hx; right; exists (p, t2); tauto.
Qed.

Lemma fill_app : forall K1 K2 t, fill_mctx (app_mctx K1 K2) t = app (fill_mctx K1 t) (fill_mctx K2 t).
Proof.
  intros K1 K2 t. unfold app_mctx. simpl.
  destruct fresh as [x Hx]; simpl; rewrite in_app_iff in Hx.
  unfold fill_mctx. simpl.
  f_equal; apply fill_fill; tauto.
Qed.

Lemma fill_lam : forall K t, fill_mctx (lam_mctx K) t = lam (fill_mctx K t).
Proof.
  intros K t. unfold fill_mctx, lam_mctx. reflexivity.
Qed.

Lemma fill_constr : forall p Ks t, fill_mctx (constr_mctx p Ks) t = constr p (map (fun K => fill_mctx K t) Ks).
Proof.
  intros p Ks t. unfold constr_mctx. simpl.
  destruct fresh as [x Hx]; simpl; rewrite concat_map_In in Hx.
  unfold fill_mctx. simpl. rewrite map_map.
  f_equal. apply map_ext_in. intros K HK; simpl.
  apply fill_fill. intros Hx2; apply Hx; exists K; tauto.
Qed.

Lemma fill_switch :
  forall K m t, fill_mctx (switch_mctx K m) t = switch (fill_mctx K t) (map (fun '(p, K2) => (p, fill_mctx K2 t)) m).
Proof.
  intros K m t. unfold switch_mctx. simpl.
  destruct fresh as [x Hx]; simpl; rewrite in_app_iff, concat_map_In in Hx.
  unfold fill_mctx. simpl. rewrite map_map.
  f_equal.
  - apply fill_fill. tauto.
  - apply map_ext_in. intros [p t2] Hpt2; f_equal. apply fill_fill.
    intros Hx2; apply Hx; right; exists (p, t2); tauto.
Qed.

Definition lc_mctx (K : multicontext) := lc (snd K).

Definition hole : multicontext := (let x := proj1_sig (fresh nil) in (x, fvar x)).
Lemma fill_hole : forall t, fill_mctx hole t = t.
Proof.
  intros t. unfold hole, fill_mctx. simpl.
  destruct freevar_eq_dec; congruence.
Qed.

Definition closeb_mctx k x (K : multicontext) : multicontext :=
  let y := proj1_sig (fresh (x :: fv (snd K))) in (y, closeb k x (fill_mctx K (fvar y))).

Lemma closeb_fill :
  forall k x K t, x \notin fv t -> fill_mctx (closeb_mctx k x K) t = closeb k x (fill_mctx K t).
Proof.
  intros k x [y K] t Hx. unfold closeb_mctx, fill_mctx. simpl.
  destruct fresh as [z Hz]; simpl in *.
  rewrite closeb_substf_free by tauto. f_equal.
  apply fill_fill with (K := (y, K)). simpl. tauto.
Qed.


Lemma body_app :
  forall t1 t2, body t1 -> body t2 -> body (app t1 t2).
Proof.
  intros t1 t2 [L1 H1] [L2 H2]. exists (L1 ++ L2).
  intros x Hx; rewrite in_app_iff in Hx; simpl; constructor; [apply H1 | apply H2]; tauto.
Qed.

Lemma lc_body_one :
  forall t x, lc (t ^ x) -> body t.
Proof.
  intros t x H. exists (fv t). intros y Hy.
  rewrite substb_is_substf with (x := y) in H by assumption.
  apply substf_lc2 in H. assumption.
Qed.

Lemma closeb_body :
  forall t x, lc t -> body (closeb 0 x t).
Proof.
  intros t x H. apply lc_body_one with (x := x). rewrite open_close_var; assumption.
Qed.

Lemma open_close2 :
  forall t k x u, lc u -> (closeb k x t) [ k <- u ] = (t [ x := u ]) [ k <- u ].
Proof.
  induction t using term_ind2; intros k x u Hlc; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; [|reflexivity].
    simpl. destruct Nat.eq_dec; [|tauto].
    rewrite substb_lc_id; [reflexivity|assumption].
  - f_equal. apply IHt. assumption.
  - f_equal; auto.
  - f_equal. rewrite !map_map. apply map_ext_in. intros t Ht.
    rewrite Forall_forall in H; apply H; assumption.
  - f_equal; [apply IHt; tauto|].
    rewrite !map_map. apply map_ext_in. intros [p t2] Hpt2. f_equal.
    rewrite Forall_forall in H. apply (H (p, t2)); tauto.
Qed.

Definition substb_mctx (K1 K2 : multicontext) k : multicontext :=
  let z := proj1_sig (fresh (fv (snd K1) ++ fv (snd K2))) in
  (z, (fill_mctx K1 (fvar z)) [ k <- fill_mctx K2 (fvar z)]).

Lemma fill_substb :
  forall K1 K2 k t, lc t -> fill_mctx (substb_mctx K1 K2 k) t = (fill_mctx K1 t) [ k <- fill_mctx K2 t ].
Proof.
  intros [x K1] [y K2] k t Hlc. unfold substb_mctx, fill_mctx in *; simpl in *.
  destruct fresh as [z Hz]; simpl in *.
  rewrite substb_substf by assumption.
  f_equal; apply fill_fill with (K := (_, _)); simpl; rewrite in_app_iff in Hz; tauto.
Qed.

Definition substf_mctx (K1 K2 : multicontext) x : multicontext :=
  let z := proj1_sig (fresh (x :: fv (snd K1) ++ fv (snd K2))) in
  (z, (fill_mctx K1 (fvar z)) [ x := fill_mctx K2 (fvar z)]).

Lemma fill_substf :
  forall K1 K2 x t, x \notin fv t -> fill_mctx (substf_mctx K1 K2 x) t = (fill_mctx K1 t) [ x := fill_mctx K2 t ].
Proof.
  intros [x K1] [y K2] w t Hw. unfold substf_mctx, fill_mctx in *; simpl in *.
  destruct fresh as [z Hz]; simpl in *; rewrite in_app_iff in Hz.
  rewrite substf_substf by tauto.
  f_equal; apply fill_fill with (K := (_, _)); simpl; tauto.
Qed.

Lemma fill_substf2 :
  forall K1 t2 x t, (fill_mctx K1 t) [ x := t2 ] = fill_mctx (substf_mctx K1 (empty_mctx t2) x) (t [ x := t2 ]).
Proof.
  intros [x K] t2 w t.
  unfold substf_mctx in *; simpl in *. rewrite fill_empty in *.
  unfold fill_mctx in *; simpl in *.
  destruct fresh as [z Hz]; simpl in *. rewrite in_app_iff in Hz.
  rewrite <- substf_substf with (x1 := z) by intuition congruence.
  f_equal. symmetry; apply fill_fill with (K := (_, _)). simpl. tauto.
Qed.


Lemma fill_open :
  forall K t1 t2, lc t1 -> (fill_mctx K t1) ^^ t2 = fill_mctx (substb_mctx K (empty_mctx t2) 0) t1.
Proof.
  intros K t1 t2 H. rewrite fill_substb by assumption.
  f_equal. rewrite fill_empty. reflexivity.
Qed.
