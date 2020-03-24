Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.

(* Terms *)

Inductive term :=
| bvar : nat -> term
| fvar : freevar -> term
| lam : term -> term
| app : term -> term -> term.

Fixpoint substb k u t :=
  match t with
  | bvar i => if Nat.eq_dec i k then u else bvar i
  | fvar x => fvar x
  | lam t => lam (substb (S k) u t)
  | app t1 t2 => app (substb k u t1) (substb k u t2)
  end.

Fixpoint closeb k x t :=
  match t with
  | bvar i => bvar i
  | fvar y => if freevar_eq_dec x y then bvar k else fvar y
  | lam t => lam (closeb (S k) x t)
  | app t1 t2 => app (closeb k x t1) (closeb k x t2)
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
  end.

Notation "t [ x := u ]" := (substf x u t) (at level 67).

Fixpoint fv t :=
  match t with
  | bvar i => nil
  | fvar x => x :: nil
  | lam t => fv t
  | app t1 t2 => fv t1 ++ fv t2
  end.

Lemma substf_fv :
  forall t u x, x \notin fv t -> t [ x := u ] = t.
Proof.
  induction t; intros u x Hx; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; intuition congruence.
  - f_equal; apply IHt; auto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
Qed.

Inductive lc : term -> Prop :=
| lc_var : forall v, lc (fvar v)
| lc_app : forall t1 t2, lc t1 -> lc t2 -> lc (app t1 t2)
| lc_lam : forall t L, (forall x, ~ In x L -> lc (t ^ x)) -> lc (lam t).

Definition body t := exists L, forall x, x \notin L -> lc (t ^ x).
Lemma lc_lam_body : forall t, lc (lam t) <-> body t.
Proof.
  intros t. split.
  - intros H; inversion H; exists L; auto.
  - intros [L H]; econstructor; eauto.
Qed.

Lemma substb_lc_id_core :
  forall t u v k1 k2, k1 <> k2 -> t [ k2 <- v ] [ k1 <- u ] = t [ k2 <- v ] -> t [ k1 <- u ] = t.
Proof.
  induction t; intros u v k1 k2 Hk Heq; simpl in *; inversion Heq; try (f_equal; eauto).
  repeat ( destruct Nat.eq_dec; simpl in * ); congruence.
Qed.

Lemma substb_lc_id : forall t u, lc t -> forall k, t [ k <- u ] = t.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - intros; simpl; rewrite IHlc1, IHlc2; reflexivity.
  - intros k. simpl. f_equal. pick x \notin L as Hx.
    eapply substb_lc_id_core with (k2 := 0); eauto.
Qed.

Lemma substb_substf :
  forall t u v k x, lc u -> t [ k <- v ] [ x := u ] = t [ x := u ] [ k <- v [ x := u ]].
Proof.
  induction t.
  - intros; simpl. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl. destruct freevar_eq_dec; [|reflexivity].
    rewrite substb_lc_id; auto.
  - intros; simpl. f_equal. apply IHt; auto.
  - intros; simpl. f_equal; auto.
Qed.

Lemma substf_substb_free :
  forall t u v k x, x ∉ fv v -> lc u -> t [x := u] [k <- v] = t [k <- v] [x := u].
Proof.
  intros. rewrite substb_substf; [|assumption].
  f_equal. rewrite substf_fv; auto.
Qed.

Lemma substf_substb_free2 :
  forall t u v k x, x ∉ fv t -> t [k <- v] [x := u] = t [k <- v [x := u]].
Proof.
  induction t.
  - intros; simpl in *. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl in *. destruct freevar_eq_dec; intuition congruence.
  - intros; simpl in *. f_equal. auto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
Qed.

Lemma closeb_id :
  forall t k x, x \notin fv t -> closeb k x t = t.
Proof.
  intros t. induction t.
  - intros; reflexivity.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in*; f_equal; auto.
Qed.

Lemma closeb_substf_free :
  forall t u k x y, x <> y -> x \notin fv u -> (closeb k x t) [y := u] = closeb k x (t [y := u]).
Proof.
  intros t. induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite closeb_id; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
Qed.

Lemma substf_lc : forall t, lc t -> forall u x, lc u -> lc (t [x := u]).
Proof.
  intros t Ht. induction Ht; intros u x Hu.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; auto.
  - simpl. apply lc_lam with (L := x :: L). intros y Hy.
    rewrite substf_substb_free; [|simpl in *; intuition congruence|assumption].
    apply H0; simpl in *; tauto.
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
  pick x ∉ (L ++ fv t).
  rewrite in_app_iff in *.
  rewrite substb_is_substf with (x := x); [|tauto].
  apply substf_lc; intuition.
Qed.

Lemma lc_open_gen :
  forall t x, body t -> lc (t ^ x).
Proof.
  intros.
  apply substb_lc; [assumption | constructor].
Qed.

Lemma close_open :
  forall t k x, x \notin fv t -> closeb k x (t [k <- fvar x]) = t.
Proof.
  intros t. induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; try destruct freevar_eq_dec; congruence.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
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
  intros t. induction t.
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
Qed.

Lemma open_close :
  forall t, lc t -> forall k x u, lc u -> substb k u (closeb k x t) = t [x := u].
Proof.
  intros t H. induction H; intros k x u Hu.
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    match goal with [ |- ?t1 = ?t2 ] => pick y \notin (x :: L ++ fv t1 ++ fv t2 ++ fv t) end.
    simpl in *; rewrite !in_app_iff in *.
    apply (open_inj y); try tauto.
    rewrite open_close_core by (tauto || discriminate).
    rewrite substf_substb_free by (simpl; intuition).
    intuition.
Qed.

Lemma substf_id :
  forall x t, t [x := fvar x] = t.
Proof.
  intros x t; induction t; simpl; try congruence.
  destruct freevar_eq_dec; congruence.
Qed.

Lemma open_close_var :
  forall t, lc t -> forall k x, substb k (fvar x) (closeb k x t) = t.
Proof.
  intros. rewrite open_close, substf_id; auto.
  constructor.
Qed.

Lemma fv_substf :
  forall x t u, fv (t [ x := u ]) \subseteq fv t ++ fv u.
Proof.
  intros x t u. induction t.
  - simpl. prove_list_inc.
  - simpl. destruct freevar_eq_dec; simpl; prove_list_inc.
  - simpl. assumption.
  - simpl. rewrite list_inc_app_left.
    rewrite IHt1, IHt2.
    split; prove_list_inc.
Qed.

Lemma fv_substf2 :
  forall t x u, fv t \subseteq x :: fv (t [ x := u ]).
Proof.
  induction t.
  - intros; simpl in *. prove_list_inc.
  - intros; simpl in *. destruct freevar_eq_dec.
    + subst. prove_list_inc.
    + simpl. prove_list_inc.
  - intros; simpl in *. apply IHt.
  - intros; simpl in *.
    rewrite (IHt1 x u). rewrite (IHt2 x u).
    prove_list_inc.
Qed.

Lemma fv_substf3 :
  forall t x u, list_remove x (fv t) \subseteq fv (t [ x := u ]).
Proof.
  induction t.
  - intros; simpl in *. prove_list_inc.
  - intros; simpl in *. destruct freevar_eq_dec.
    + subst. prove_list_inc.
    + simpl. prove_list_inc.
  - intros; simpl in *. apply IHt.
  - intros; simpl in *.
    rewrite list_remove_app, (IHt1 x u), (IHt2 x u).
    prove_list_inc.
Qed.

Lemma fv_substf4 :
  forall t x u, x \in fv t -> fv u \subseteq fv (t [ x := u ]).
Proof.
  induction t.
  - intros; simpl in *. prove_list_inc.
  - intros; simpl in *. destruct freevar_eq_dec.
    + subst. prove_list_inc.
    + simpl. intuition congruence.
  - intros; simpl in *. apply IHt. assumption.
  - intros; simpl in *.
    destruct (in_dec freevar_eq_dec x (fv t1)).
    + rewrite (IHt1 x u); [prove_list_inc|assumption].
    + rewrite (IHt2 x u); [prove_list_inc|].
      rewrite in_app_iff in H; tauto.
Qed.

Lemma fv_substf_iff :
  forall t x y u, y \in fv (t [ x := u ]) <-> (y \in fv t /\ y <> x) \/ (x \in fv t /\ y \in fv u).
Proof.
  induction t.
  - intros; simpl in *; tauto.
  - intros; simpl in *. destruct freevar_eq_dec.
    + subst. intuition congruence.
    + simpl. intuition congruence.
  - intros; simpl in *; apply IHt.
  - intros; simpl in *; rewrite !in_app_iff, IHt1, IHt2. tauto.
Qed.

Lemma substf_substf :
  forall t x1 x2 u1 u2, x1 <> x2 -> x1 \notin fv u2 -> t [ x1 := u1 ] [ x2 := u2 ] = t [ x2 := u2 ] [ x1 := u1 [ x2 := u2 ] ].
Proof.
  induction t.
  - intros; simpl in *; reflexivity.
  - intros; simpl in *.
    repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite substf_fv; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
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

Lemma substb_fv :
  forall t k u, fv (t [ k <- u ]) \subseteq fv t ++ fv u.
Proof.
  induction t; intros k u.
  - simpl. destruct Nat.eq_dec; simpl; prove_list_inc.
  - simpl. prove_list_inc.
  - simpl. apply IHt.
  - simpl. rewrite IHt1, IHt2. prove_list_inc.
Qed.

Lemma substb_fv2 :
  forall t k u, fv t \subseteq fv (t [ k <- u ]).
Proof.
  induction t.
  - intros; simpl. prove_list_inc.
  - intros; simpl. reflexivity.
  - intros; simpl. apply IHt.
  - intros; simpl. rewrite <- IHt1, <- IHt2. reflexivity.
Qed.


Lemma closeb_var_free :
  forall x k t, x \notin fv (closeb k x t).
Proof.
  intros x k t. revert k. induction t.
  - simpl; tauto.
  - simpl. destruct freevar_eq_dec; intros k.
    + simpl; tauto.
    + simpl. intuition congruence.
  - simpl. intros k; apply IHt.
  - simpl. intros k.
    rewrite in_app_iff; firstorder.
Qed.

Lemma fv_closeb :
  forall t k x, fv (closeb k x t) \subseteq fv t.
Proof.
  induction t; intros k x.
  - simpl. reflexivity.
  - simpl. destruct freevar_eq_dec; prove_list_inc.
  - simpl. apply IHt.
  - simpl. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma closeb_fv_eq :
  forall x k t, fv (closeb k x t) == list_remove x (fv t).
Proof.
  intros x k t y. rewrite list_remove_correct.
  split.
  - intros H. split; [rewrite fv_closeb in H; assumption|intros ->; apply closeb_var_free in H; assumption].
  - intros [H1 H2]. revert k; induction t; intros k; simpl in *.
    + assumption.
    + destruct freevar_eq_dec; subst; simpl; tauto.
    + apply IHt. assumption.
    + rewrite in_app_iff in *. destruct H1; [left; apply IHt1 | right; apply IHt2]; assumption.
Qed.




Inductive lc_at : term -> nat -> Prop :=
| lc_at_fvar : forall x k, lc_at (fvar x) k
| lc_at_bvar : forall n k, n < k -> lc_at (bvar n) k
| lc_at_lam : forall t k, lc_at t (S k) -> lc_at (lam t) k
| lc_at_app : forall t1 t2 k, lc_at t1 k -> lc_at t2 k -> lc_at (app t1 t2) k.

Lemma lc_at_substb_id :
  forall t k1 k2 u, lc_at t k1 -> k1 <= k2 -> t [ k2 <- u ] = t.
Proof.
  induction t; intros k1 k2 u H1 H2.
  - simpl. inversion H1; subst. destruct Nat.eq_dec; [lia|reflexivity].
  - reflexivity.
  - simpl. f_equal. inversion H1; subst.
    eapply IHt; [eassumption|]. lia.
  - simpl. inversion H1; subst. f_equal; eauto.
Qed.

Lemma lc_at_inc :
  forall t k1 k2, lc_at t k1 -> k1 <= k2 -> lc_at t k2.
Proof.
  induction t; intros k1 k2 H1 H2.
  - inversion H1; constructor; lia.
  - constructor.
  - inversion H1; subst; constructor.
    eapply IHt; [eassumption|lia].
  - inversion H1; subst; constructor; [eapply IHt1|eapply IHt2]; try eassumption; lia.
Qed.

Lemma lc_at_substb_lc_at :
  forall t k u, lc_at u 0 -> lc_at t (S k) -> lc_at (t [ k <- u ]) k.
Proof.
  induction t; intros k u H1 H2.
  - simpl. destruct Nat.eq_dec.
    + eapply lc_at_inc; [eassumption|lia].
    + inversion H2. constructor. lia.
  - simpl; constructor.
  - simpl. inversion H2; subst. constructor.
    apply IHt; assumption.
  - simpl. inversion H2; subst.
    constructor; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma lc_at_substb_lc_at2 :
  forall t k u, lc_at (t [ k <- u ]) k -> lc_at t (S k).
Proof.
  induction t; intros k u H.
  - simpl in *. destruct Nat.eq_dec.
    + constructor. lia.
    + inversion H. constructor. lia.
  - simpl; constructor.
  - simpl. inversion H; subst. constructor.
    eapply IHt; eassumption.
  - simpl. inversion H; subst.
    constructor; [eapply IHt1 | eapply IHt2]; eassumption.
Qed.

Fixpoint size t :=
  match t with
  | bvar _ => 0
  | fvar _ => 0
  | lam t => S (size t)
  | app t1 t2 => S (size t1 + size t2)
  end.

Lemma open_size :
  forall t k x, size (t [ k <- fvar x ]) = size t.
Proof.
  induction t; intros k x; simpl.
  - destruct Nat.eq_dec; reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma lc_at_lc :
  forall t, lc t <-> lc_at t 0.
Proof.
  intros t. split.
  - intros H. induction H.
    + constructor.
    + constructor; assumption.
    + constructor. pick x \notin L as Hx. eapply lc_at_substb_lc_at2. apply H0; eassumption.
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
Qed.

Lemma substf_lc2 :
  forall t x u, lc (t [ x := u ]) -> lc t.
Proof.
  intros. rewrite lc_at_lc in *.
  remember 0 as k. clear Heqk.
  revert k H. induction t; intros k H; simpl in *.
  - assumption.
  - constructor.
  - constructor. apply IHt. inversion H; subst; assumption.
  - inversion H; subst. constructor; [apply IHt1 | apply IHt2]; assumption.
Qed.

(* Multicontexts *)

Definition multicontext := (freevar * term)%type.

Definition fill_mctx (K : multicontext) (t : term) := (snd K) [ fst K := t ].
Definition empty_mctx (t : term) : multicontext := (proj1_sig (fresh (fv t)), t).
Definition app_mctx (K1 K2 : multicontext) : multicontext :=
  let x := proj1_sig (fresh (fv (snd K1) ++ (fv (snd K2)))) in (x, app (fill_mctx K1 (fvar x)) (fill_mctx K2 (fvar x))).
Definition lam_mctx (K : multicontext) : multicontext := (fst K, lam (snd K)).

Lemma fill_empty : forall t1 t2, fill_mctx (empty_mctx t1) t2 = t1.
Proof.
  intros t1 t2. unfold fill_mctx, empty_mctx. simpl.
  apply substf_fv. apply proj2_sig.
Qed.

Lemma fill_fill : forall K x t, x \notin fv (snd K) -> fill_mctx (x, fill_mctx K (fvar x)) t = fill_mctx K t.
Proof.
  intros K x t Hx. destruct K as [y u]; simpl in *. unfold fill_mctx; simpl.
  induction u.
  - simpl. reflexivity.
  - simpl. destruct freevar_eq_dec.
    + simpl. destruct freevar_eq_dec; congruence.
    + simpl in *. destruct freevar_eq_dec; intuition congruence.
  - simpl in *. f_equal. apply IHu. assumption.
  - simpl in *. rewrite in_app_iff in Hx. f_equal.
    + apply IHu1. tauto.
    + apply IHu2. tauto.
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
  induction t; intros k x u Hlc; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; [|reflexivity].
    simpl. destruct Nat.eq_dec; [|tauto].
    rewrite substb_lc_id; [reflexivity|assumption].
  - f_equal. apply IHt. assumption.
  - f_equal; auto.
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
