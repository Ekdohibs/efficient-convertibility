Require Import List.
Require Import Arith.
Require Import Psatz.

(* List Notations *)

Notation "x '\in' L" := (In x L) (at level 80, only parsing).
Notation "x '\notin' L" := (~ In x L) (at level 80, only parsing).
Notation "x ∈ L" := (x \in L) (at level 80).
Notation "x ∉ L" := (x \notin L) (at level 80).

(* Theorems on Forall *)

Lemma Forall_cons_iff :
  forall A (P : A -> Prop) a L, Forall P (a :: L) <-> P a /\ Forall P L.
Proof.
  intros. split.
  - intros H; inversion H; tauto.
  - intros; constructor; tauto.
Qed.

Lemma Forall_app_iff :
  forall A (P : A -> Prop) L1 L2, Forall P (L1 ++ L2) <-> Forall P L1 /\ Forall P L2.
Proof.
  intros. induction L1.
  - simpl. firstorder.
  - intros; simpl.
    rewrite !Forall_cons_iff, IHL1. tauto.
Qed.

Lemma Forall_map :
  forall A B (f : A -> B) (P : B -> Prop) L, Forall P (map f L) <-> Forall (fun x => P (f x)) L.
Proof.
  intros. induction L.
  - simpl. firstorder.
  - simpl. rewrite !Forall_cons_iff. firstorder.
Qed.


(* Free variables and fresh name generator *)

Definition freevar := nat.
Lemma freevar_eq_dec : forall (v1 v2 : freevar), { v1 = v2 } + { v1 <> v2 }.
Proof.
  apply Nat.eq_dec.
Qed.
Lemma fresh : forall (L : list freevar), { x | x \notin L }.
Proof.
  intros L.
  assert (H : { x | forall y, y \in L -> y < x }).
  - induction L.
    + exists 0. intros y [].
    + destruct IHL as [x IH].
      exists (Nat.max (S a) x); unfold freevar in *.
      intros y [Hy | Hy]; [|specialize (IH y Hy)]; lia.
  - destruct H as [x Hx]; exists x.
    intros H; apply Hx in H; lia.
Qed.
Global Opaque freevar.

Notation "'forall' x '∉' L , P" := (forall (x : freevar), ~ In x L -> P) (at level 200, x ident, only printing).

Tactic Notation "pick" ident(x) "\notin" constr(L) "as" ident(H) := destruct (fresh L) as [x H].
Tactic Notation "pick" ident(x) "\notin" constr(L) := (let H := fresh "H" in pick x \notin L as H).
Tactic Notation "pick" ident(x) "∉" constr(L) "as" ident(H) := destruct (fresh L) as [x H].
Tactic Notation "pick" ident(x) "∉" constr(L) := (let H := fresh "H" in pick x \notin L as H).

(* Transitive reflexive closure *)

Inductive trans_refl_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| trclos_refl : forall x, trans_refl_clos R x x
| trclos_step : forall x y z, R x y -> trans_refl_clos R y z -> trans_refl_clos R x z.

Lemma trans_refl_clos_compose :
  forall (A : Type) (R : A -> A -> Prop) x y z, trans_refl_clos R x y -> trans_refl_clos R y z -> trans_refl_clos R x z.
Proof.
  intros A R x y z H. induction H.
  - intros; assumption.
  - intros; econstructor; [eassumption | firstorder].
Qed.

Lemma trans_refl_clos_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y, RA x y -> RB (f x) (f y)) -> forall x y, trans_refl_clos RA x y -> trans_refl_clos RB (f x) (f y).
Proof.
  intros A B RA RB f HR x y H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma trans_refl_clos_refl_clos :
  forall (A : Type) (R : A -> A -> Prop), forall x y, trans_refl_clos (trans_refl_clos R) x y -> trans_refl_clos R x y.
Proof.
  intros A R x y H. induction H.
  - constructor.
  - eapply trans_refl_clos_compose; eauto.
Qed.


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
    rewrite open_close_core by intuition.
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
  forall t u1 u2 x, beta u1 u2 -> lc t -> trans_refl_clos beta (t [x := u1]) (t [x := u2]).
Proof.
  intros t u1 u2 x Hbeta Ht. induction Ht.
  - simpl. destruct freevar_eq_dec.
    + econstructor; [eassumption|constructor].
    + constructor.
  - simpl. destruct (beta_lc _ _ Hbeta) as [Hlc1 Hlc2]. eapply trans_refl_clos_compose.
    + eapply trans_refl_clos_map_impl with (f := fun t => app t _); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
    + eapply trans_refl_clos_map_impl with (f := fun t => app _ t); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
  - simpl.
    pick y \notin (x :: L ++ fv t ++ fv u1 ++ fv u2) as Hy; simpl in Hy.
    rewrite !in_app_iff in Hy.
    rewrite <- (close_open t 0 y), !closeb_substf_free by intuition.
    eapply trans_refl_clos_map_impl with (f := fun t => lam (closeb 0 y t)); [|intuition].
    + intros t3 t4 Hbeta1.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros z Hz; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
      apply beta_subst; [constructor | auto].
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

Lemma parallel_beta_incl_trans_refl_clos_beta :
  forall t1 t2, parallel_beta t1 t2 -> trans_refl_clos beta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor.
  - apply trans_refl_clos_compose with (y := app t3 t2).
    + eapply trans_refl_clos_map_impl with (f := fun t => app t t2); [|eassumption].
      intros; constructor; firstorder using parallel_beta_lc.
    + eapply trans_refl_clos_map_impl with (f := fun t => app t3 t); [|eassumption].
      intros; constructor; firstorder using parallel_beta_lc.
  - pick x \notin (L ++ fv t1 ++ fv t2).
    rewrite !in_app_iff in *.
    rewrite <- (close_open t1 0 x), <- (close_open t2 0 x) by tauto.
    apply trans_refl_clos_map_impl with (RA := beta) (f := fun t => lam (closeb 0 x t)).
    + intros t3 t4 Hbeta.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros y Hy; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta; tauto).
      apply beta_subst; [constructor | auto].
    + auto.
  - econstructor; constructor; auto.
Qed.

(* D-Terms *)
(* In D-terms, lambdas have two bodies, and the first body must beta-reduce to the second body.
 * Only the first body may be used in beta-reduction, and reduction is only allowed within the second body.
 *)

Inductive dterm :=
| dbvar : nat -> dterm
| dfvar : freevar -> dterm
| dlam : dterm -> dterm -> dterm
| dapp : dterm -> dterm -> dterm.

Fixpoint dsubstb k u t :=
  match t with
  | dbvar i => if Nat.eq_dec i k then u else dbvar i
  | dfvar x => dfvar x
  | dlam t1 t2 => dlam (dsubstb (S k) u t1) (dsubstb (S k) u t2)
  | dapp t1 t2 => dapp (dsubstb k u t1) (dsubstb k u t2)
  end.

Fixpoint dcloseb k x t :=
  match t with
  | dbvar i => dbvar i
  | dfvar y => if freevar_eq_dec x y then dbvar k else dfvar y
  | dlam t1 t2 => dlam (dcloseb (S k) x t1) (dcloseb (S k) x t2)
  | dapp t1 t2 => dapp (dcloseb k x t1) (dcloseb k x t2)
  end.

Notation "t 'd[' k <- u ]" := (dsubstb k u t) (at level 67).
Notation "t 'd^^' u" := (t d[ 0 <- u ]) (at level 67).
Notation "t 'd^' x" := (t d^^ (dfvar x)) (at level 35).

Fixpoint dsubstf x u t :=
  match t with
  | dbvar i => dbvar i
  | dfvar y => if freevar_eq_dec x y then u else dfvar y
  | dlam t1 t2 => dlam (dsubstf x u t1) (dsubstf x u t2)
  | dapp t1 t2 => dapp (dsubstf x u t1) (dsubstf x u t2)
  end.

Notation "t 'd[' x := u ]" := (dsubstf x u t) (at level 67).

Fixpoint dfv t :=
  match t with
  | dbvar i => nil
  | dfvar x => x :: nil
  | dlam t1 t2 => dfv t1 ++ dfv t2
  | dapp t1 t2 => dfv t1 ++ dfv t2
  end.

Lemma dsubstf_dfv :
  forall t u x, x \notin dfv t -> t d[ x := u ] = t.
Proof.
  induction t; intros u x Hx; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; intuition congruence.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
Qed.

Inductive dlc : dterm -> Prop :=
| dlc_var : forall v, dlc (dfvar v)
| dlc_app : forall t1 t2, dlc t1 -> dlc t2 -> dlc (dapp t1 t2)
| dlc_lam : forall t1 t2 L, (forall x, x \notin L -> dlc (t1 d^ x)) -> (forall x, x \notin L -> dlc (t2 d^ x)) -> dlc (dlam t1 t2).

Definition dbody t := exists L, forall x, x \notin L -> dlc (t d^ x).
Lemma dlc_dlam_dbody : forall t1 t2, dlc (dlam t1 t2) <-> dbody t1 /\ dbody t2.
Proof.
  intros t1 t2. split.
  - intros H; inversion H; split; exists L; firstorder.
  - intros [[L1 H1] [L2 H2]].
    apply (dlc_lam t1 t2 (L1 ++ L2)); intros x Hx; rewrite in_app_iff in Hx; firstorder.
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
  - intros k. simpl. pick x \notin L as Hx.
    f_equal; eapply dsubstb_dlc_id_core with (k2 := 0); eauto.
Qed.

Lemma dsubstb_dsubstf :
  forall t u v k x, dlc u -> t d[ k <- v ] d[ x := u ] = t d[ x := u ] d[ k <- v d[ x := u ]].
Proof.
  induction t.
  - intros; simpl. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl. destruct freevar_eq_dec; [|reflexivity].
    rewrite dsubstb_dlc_id; auto.
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
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
Qed.

Lemma dsubstf_dlc : forall t, dlc t -> forall u x, dlc u -> dlc (t d[ x := u ]).
Proof.
  intros t Ht. induction Ht; intros u x Hu.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; auto.
  - simpl.
    apply dlc_lam with (L := x :: L); intros y Hy.
    + rewrite dsubstf_dsubstb_free; [|simpl in *; intuition congruence|assumption].
      firstorder.
    + rewrite dsubstf_dsubstb_free; [|simpl in *; intuition congruence|assumption].
      firstorder.
Qed.

Lemma dsubstb_is_dsubstf :
  forall t u x, x ∉ dfv t -> t d^^ u = (t d^ x) d[ x := u ].
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

Lemma dlc_dopen_gen :
  forall t x, dbody t -> dlc (t d^ x).
Proof.
  intros.
  apply dsubstb_dlc; [assumption | constructor].
Qed.

Lemma dclose_dopen :
  forall t k x, x \notin dfv t -> dcloseb k x (t d[ k <- dfvar x ]) = t.
Proof.
  intros t. induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; try destruct freevar_eq_dec; congruence.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
Qed.

Lemma dopen_inj :
  forall x t1 t2, x \notin dfv t1 -> x \notin dfv t2 -> t1 d^ x = t2 d^ x -> t1 = t2.
Proof.
  intros.
  rewrite <- (dclose_dopen t1 0 x), <- (dclose_dopen t2 0 x); auto; congruence.
Qed.

Lemma dopen_dclose_core :
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
    f_equal; [apply IHt1 | apply IHt2]; simpl; auto.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; tauto.
Qed.

Lemma dopen_dclose :
  forall t, dlc t -> forall k x u, dlc u -> dsubstb k u (dcloseb k x t) = t d[ x := u ].
Proof.
  intros t H. induction H; intros k x u Hu.
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. f_equal; auto.
  - simpl.
    f_equal; match goal with [ |- ?t3 = ?t4 ] => pick y \notin (x :: L ++ dfv t1 ++ dfv t2 ++ dfv t3 ++ dfv t4) end.
    + simpl in *; rewrite !in_app_iff in *.
      apply (dopen_inj y); try tauto.
      rewrite dopen_dclose_core by intuition.
      rewrite dsubstf_dsubstb_free by (simpl; intuition).
      intuition.
    + simpl in *; rewrite !in_app_iff in *.
      apply (dopen_inj y); try tauto.
      rewrite dopen_dclose_core by intuition.
      rewrite dsubstf_dsubstb_free by (simpl; intuition).
      intuition.
Qed.

Lemma dsubstf_id :
  forall x t, t d[ x := dfvar x ] = t.
Proof.
  intros x t; induction t; simpl; try congruence.
  destruct freevar_eq_dec; congruence.
Qed.

Lemma dopen_dclose_var :
  forall t, dlc t -> forall k x, dsubstb k (dfvar x) (dcloseb k x t) = t.
Proof.
  intros. rewrite dopen_dclose, dsubstf_id; auto.
  constructor.
Qed.

Lemma dsubstf_dsubstf :
  forall t x1 x2 u1 u2, x1 <> x2 -> x1 \notin dfv u2 -> t d[ x1 := u1 ] d[ x2 := u2 ] = t d[ x2 := u2 ] d[ x1 := u1 d[ x2 := u2 ] ].
Proof.
  induction t.
  - intros; simpl in *; reflexivity.
  - intros; simpl in *.
    repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite dsubstf_dfv; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
Qed.

(* Dbeta *)

Inductive dbeta : dterm -> dterm -> Prop :=
| dbeta_redex : forall t1 t2 t3, dbody t1 -> dbody t2 -> dlc t3 -> dbeta (dapp (dlam t1 t2) t3) (t1 d^^ t3)
| dbeta_app_left : forall t1 t2 t3, dbeta t1 t2 -> dlc t3 -> dbeta (dapp t1 t3) (dapp t2 t3)
| dbeta_app_right : forall t1 t2 t3, dbeta t1 t2 -> dlc t3 -> dbeta (dapp t3 t1) (dapp t3 t2)
| dbeta_lam : forall t1 t2 t3 L, dbody t1 -> (forall x, x ∉ L -> dbeta (t2 d^ x) (t3 d^ x)) -> dbeta (dlam t1 t2) (dlam t1 t3).

Lemma dbeta_dlc : forall t1 t2, dbeta t1 t2 -> dlc t1 /\ dlc t2.
Proof.
  intros t1 t2 H. induction H.
  - split.
    + constructor; [apply dlc_dlam_dbody; split|]; assumption.
    + apply dsubstb_dlc; assumption.
  - split; constructor; tauto.
  - split; constructor; tauto.
  - destruct H as [L1 H].
    split; apply dlc_lam with (L := L ++ L1); intros x Hx; rewrite in_app_iff in Hx; firstorder.
Qed.

Lemma dbeta_subst :
  forall t1 t2 x u, dlc u -> dbeta t1 t2 -> dbeta (t1 d[ x := u ]) (t2 d[ x := u ]).
Proof.
  intros t1 t2 x u Hu Hbeta. induction Hbeta.
  - simpl. rewrite dsubstb_dsubstf by auto.
    assert (Hbody : dlc ((dlam t1 t2) d[ x := u ])) by (apply dsubstf_dlc; [rewrite dlc_dlam_dbody|]; auto).
    simpl in Hbody; rewrite dlc_dlam_dbody in Hbody.
    constructor; [| |apply dsubstf_dlc]; tauto.
  - intros; simpl; constructor; auto using dsubstf_dlc.
  - intros; simpl; constructor; auto using dsubstf_dlc.
  - intros; simpl; apply dbeta_lam with (L := x :: L).
    + exists (x :: nil).
      intros y Hy.
      rewrite dsubstf_dsubstb_free by (simpl in *; intuition).
      apply dsubstf_dlc; [|auto].
      apply dlc_dopen_gen; auto.
    + intros y Hy; simpl in Hy.
      specialize (H1 y (ltac:(tauto))).
      rewrite !dsubstb_dsubstf in H1 by auto.
      simpl in H1. destruct freevar_eq_dec; tauto.
Qed.


Inductive dwf : dterm -> Prop :=
| dwf_var : forall x, dwf (dfvar x)
| dwf_app : forall t1 t2, dwf t1 -> dwf t2 -> dwf (dapp t1 t2)
| dwf_lam : forall L t1 t2,
    (forall x, x \notin L -> dwf (t1 d^ x)) ->
    (forall x, x \notin L -> dwf (t2 d^ x)) ->
    (forall x, x \notin L -> trans_refl_clos dbeta (t1 d^ x) (t2 d^ x)) ->
    dwf (dlam t1 t2).

Lemma dwf_dlc :
  forall t, dwf t -> dlc t.
Proof.
  intros t Ht. induction Ht.
  - constructor.
  - constructor; auto.
  - econstructor; eauto.
Qed.

Lemma dwf_app_inv :
  forall {t1 t2}, dwf (dapp t1 t2) -> dwf t1 /\ dwf t2.
Proof.
  intros t1 t2 H; inversion H; auto.
Qed.

Lemma dwf_lam_inv :
  forall {t1 t2},
    dwf (dlam t1 t2) ->
    exists L, (forall x, x \notin L -> dwf (t1 d^ x)) /\
         (forall x, x \notin L -> dwf (t2 d^ x)) /\
         (forall x, x \notin L -> trans_refl_clos dbeta (t1 d^ x) (t2 d^ x)).
Proof.
  intros t1 t2 H; inversion H; eauto.
Qed.

Lemma dsubstf_dwf :
  forall x t u, dwf u -> dwf t -> dwf (t d[ x := u ]).
Proof.
  intros x t u Hwfu Hwft. induction Hwft.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; assumption.
  - simpl. apply dwf_lam with (L := x :: L).
    + intros y Hy. rewrite dsubstf_dsubstb_free; simpl in *; firstorder using dwf_dlc.
    + intros y Hy. rewrite dsubstf_dsubstb_free; simpl in *; firstorder using dwf_dlc.
    + intros y Hy.
      rewrite !dsubstf_dsubstb_free by (firstorder using dwf_dlc).
      eapply trans_refl_clos_map_impl with (f := fun t => t d[ x := u]); [|apply H3; simpl in Hy; auto].
      firstorder using dbeta_subst, dwf_dlc.
Qed.

Lemma dbeta_dwf :
  forall t1 t2, dbeta t1 t2 -> dwf t1 -> dwf t2.
Proof.
  intros t1 t2 Hbeta. induction Hbeta.
  - intros Hwf.
    destruct (dwf_app_inv Hwf) as [Hwf1 Hwf2].
    destruct (dwf_lam_inv Hwf1) as [L (Hwf3 & _ & _)].
    pick x \notin (L ++ dfv t1); rewrite in_app_iff in *.
    rewrite dsubstb_is_dsubstf with (x := x) by auto.
    apply dsubstf_dwf; auto.
  - intros Hwf. inversion_clear Hwf.
    constructor; auto.
  - intros Hwf. inversion_clear Hwf.
    constructor; auto.
  - intros Hwf.
    destruct (dwf_lam_inv Hwf) as [L1 (Hwf1 & Hwf2 & Hwf3)].
    apply dwf_lam with (L := L ++ L1).
    + intros x Hx; rewrite in_app_iff in *; auto.
    + intros x Hx; rewrite in_app_iff in *; intuition.
    + intros x Hx; rewrite in_app_iff in *.
      eapply trans_refl_clos_compose; [apply Hwf3; auto|].
      econstructor; [|constructor].
      auto.
Qed.

Lemma dlc_lam_inv_strong :
  forall {t1 t2},
    dlc (dlam t1 t2) -> (forall x, dlc (t1 d^ x)) /\ (forall x, dlc (t2 d^ x)).
Proof.
  intros t1 t2 Hlc. rewrite dlc_dlam_dbody in Hlc.
  split; intros x; apply dlc_dopen_gen; tauto.
Qed.

Lemma dwf_lam_inv_strong :
  forall {t1 t2},
    dwf (dlam t1 t2) -> (forall x, dwf (t1 d^ x)) /\ (forall x, dwf (t2 d^ x)) /\
         (forall x, trans_refl_clos dbeta (t1 d^ x) (t2 d^ x)).
Proof.
  intros t1 t2 Hwf.
  apply dwf_lam_inv in Hwf; destruct Hwf as [L (H1 & H2 & H3)].
  pick x \notin (L ++ dfv t1 ++ dfv t2) as Hx.
  rewrite !in_app_iff in Hx.
  split; [|split].
  - intros y.
    rewrite dsubstb_is_dsubstf with (x := x) by tauto.
    apply dsubstf_dwf; [|auto].
    constructor.
  - intros y.
    rewrite dsubstb_is_dsubstf with (x := x) by tauto.
    apply dsubstf_dwf; [|auto].
    constructor.
  - intros y.
    rewrite dsubstb_is_dsubstf with (t := t1) (x := x) by tauto.
    rewrite dsubstb_is_dsubstf with (t := t2) (x := x) by tauto.
    eapply trans_refl_clos_map_impl with (f := fun t => t d[ x := dfvar y ]); [|apply H3; tauto].
    intros t3 t4 Hbeta.
    apply dbeta_subst; [constructor | auto].
Qed.


Fixpoint dterm_read1 (t : dterm) :=
  match t with
  | dbvar k => bvar k
  | dfvar x => fvar x
  | dapp t1 t2 => app (dterm_read1 t1) (dterm_read1 t2)
  | dlam t1 t2 => lam (dterm_read1 t1)
  end.

Lemma dsubstb_substb :
  forall t u k, dterm_read1 (dsubstb k u t) = substb k (dterm_read1 u) (dterm_read1 t).
Proof.
  induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl; reflexivity.
  - intros; simpl; f_equal; apply IHt1.
  - intros; simpl; f_equal; auto.
Qed.

Lemma dsubstf_substf :
  forall t u x, dterm_read1 (dsubstf x u t) = substf x (dterm_read1 u) (dterm_read1 t).
Proof.
  induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; destruct freevar_eq_dec; simpl; reflexivity.
  - intros; simpl; f_equal; apply IHt1.
  - intros; simpl; f_equal; auto.
Qed.

Lemma dcloseb_closeb :
  forall t x k, dterm_read1 (dcloseb k x t) = closeb k x (dterm_read1 t).
Proof.
  induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; destruct freevar_eq_dec; simpl; reflexivity.
  - intros; simpl; f_equal; apply IHt1.
  - intros; simpl; f_equal; auto.
Qed.

Lemma dlc_lc :
  forall t, dlc t -> lc (dterm_read1 t).
Proof.
  intros t Ht. induction Ht.
  - simpl; constructor.
  - simpl; constructor; auto.
  - simpl; apply lc_lam with (L := L).
    intros x Hx; specialize (H0 x Hx).
    rewrite dsubstb_substb in H0; exact H0.
Qed.

Lemma dbody_body :
  forall t, dbody t -> body (dterm_read1 t).
Proof.
  intros t [L Ht].
  exists L. intros x Hx; specialize (Ht x Hx).
  apply dlc_lc in Ht. rewrite dsubstb_substb in Ht.
  exact Ht.
Qed.

Lemma dbeta_beta :
  forall t1 t2, dbeta t1 t2 -> trans_refl_clos beta (dterm_read1 t1) (dterm_read1 t2).
Proof.
  intros t1 t2 Hbeta. induction Hbeta.
  - simpl. rewrite dsubstb_substb.
    econstructor; [|constructor].
    constructor; [apply dbody_body | apply dlc_lc]; assumption.
  - simpl.
    eapply trans_refl_clos_map_impl with (f := fun t => app t _); [|eassumption].
    intros; constructor; auto using dlc_lc.
  - simpl.
    eapply trans_refl_clos_map_impl with (f := fun t => app _ t); [|eassumption].
    intros; constructor; auto using dlc_lc.
  - simpl. constructor.
Qed.

Fixpoint dterm_read2 (t : dterm) :=
  match t with
  | dbvar k => bvar k
  | dfvar x => fvar x
  | dapp t1 t2 => app (dterm_read2 t1) (dterm_read2 t2)
  | dlam t1 t2 => lam (dterm_read2 t2)
  end.

Lemma dsubstb_substb2 :
  forall t u k, dterm_read2 (dsubstb k u t) = substb k (dterm_read2 u) (dterm_read2 t).
Proof.
  induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl; reflexivity.
  - intros; simpl; f_equal; apply IHt2.
  - intros; simpl; f_equal; auto.
Qed.

Lemma dcloseb_closeb2 :
  forall t x k, dterm_read2 (dcloseb k x t) = closeb k x (dterm_read2 t).
Proof.
  induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; destruct freevar_eq_dec; simpl; reflexivity.
  - intros; simpl; f_equal; apply IHt2.
  - intros; simpl; f_equal; auto.
Qed.

Lemma dlc_lc2 :
  forall t, dlc t -> lc (dterm_read2 t).
Proof.
  intros t Ht. induction Ht.
  - simpl; constructor.
  - simpl; constructor; auto.
  - simpl; apply lc_lam with (L := L).
    intros x Hx; specialize (H2 x Hx).
    rewrite dsubstb_substb2 in H2; exact H2.
Qed.

Lemma dbody_body2 :
  forall t, dbody t -> body (dterm_read2 t).
Proof.
  intros t [L Ht].
  exists L. intros x Hx; specialize (Ht x Hx).
  apply dlc_lc2 in Ht. rewrite dsubstb_substb2 in Ht.
  exact Ht.
Qed.

Lemma beta_dterm_read12 :
  forall t, dwf t -> trans_refl_clos beta (dterm_read1 t) (dterm_read2 t).
Proof.
  intros t Ht. induction Ht.
  - simpl; constructor.
  - simpl.
    eapply trans_refl_clos_compose.
    + eapply trans_refl_clos_map_impl with (f := fun t => app _ t); [|eassumption].
      intros; constructor; auto using dlc_lc, dwf_dlc.
    + eapply trans_refl_clos_map_impl with (f := fun t => app t _); [|eassumption].
      intros; constructor; auto using dlc_lc2, dwf_dlc.
  - simpl.
    pick x \notin (L ++ dfv t1 ++ dfv t2).
    rewrite !in_app_iff in *.
    rewrite <- (dclose_dopen t1 0 x), <- (dclose_dopen t2 0 x) by tauto.
    rewrite dcloseb_closeb, dcloseb_closeb2.
    apply trans_refl_clos_map_impl with (RA := beta) (f := fun t => lam (closeb 0 x t)).
    + intros t3 t4 Hbeta.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros y Hy; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta; tauto).
      apply beta_subst; [constructor | auto].
    + eapply trans_refl_clos_compose; [|eauto].
      apply trans_refl_clos_refl_clos.
      eapply trans_refl_clos_map_impl; [|eauto].
      intros t3 t4 Hbeta; apply dbeta_beta; auto.
Qed.

Lemma dbeta_beta_subst :
  forall x t t1 t2, dlc t -> dbeta t1 t2 ->
               trans_refl_clos beta (dterm_read1 (t d[ x := t1 ])) (dterm_read1 (t d[ x := t2 ])).
Proof.
  intros x t t1 t2 Ht Hdbeta.
  rewrite !dsubstf_substf.
  apply trans_refl_clos_refl_clos.
  eapply trans_refl_clos_map_impl with (f := fun t1 => dterm_read1 t [ x := t1 ]); [|apply dbeta_beta; assumption].
  intros t3 t4 Hbeta. apply beta_subst2; [assumption|].
  apply dlc_lc. assumption.
Qed.

Inductive parallel_dbeta : dterm -> dterm -> Prop :=
| pdbeta_var : forall x, parallel_dbeta (dfvar x) (dfvar x)
| pdbeta_app : forall t1 t2 t3 t4, parallel_dbeta t1 t3 -> parallel_dbeta t2 t4 -> parallel_dbeta (dapp t1 t2) (dapp t3 t4)
| pdbeta_lam : forall t1 t2 t3 L,
    dbody t1 -> (forall x, x \notin L -> parallel_dbeta (t2 d^ x) (t3 d^ x)) -> parallel_dbeta (dlam t1 t2) (dlam t1 t3)
| pdbeta_redex : forall t1 t2 t3, dbody t1 -> dbody t2 -> dlc t3 -> parallel_dbeta (dapp (dlam t1 t2) t3) (t1 d^^ t3).

Lemma parallel_dbeta_dlc : forall t1 t2, parallel_dbeta t1 t2 -> dlc t1 /\ dlc t2.
Proof.
  intros t1 t2 H. induction H.
  - split; constructor.
  - split; constructor; tauto.
  - rewrite !dlc_dlam_dbody. split; split; (assumption || exists L; firstorder).
  - split.
    + constructor; [apply dlc_dlam_dbody|]; tauto.
    + apply dsubstb_dlc; assumption.
Qed.

Lemma parallel_dbeta_refl : forall t, dlc t -> parallel_dbeta t t.
Proof.
  intros t H. induction H.
  - constructor.
  - constructor; assumption.
  - econstructor; [exists L|]; eassumption.
Qed.

Lemma dbeta_incl_parallel_dbeta :
  forall t1 t2, dbeta t1 t2 -> parallel_dbeta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor; assumption.
  - constructor; [|apply parallel_dbeta_refl]; assumption.
  - constructor; [apply parallel_dbeta_refl|]; assumption.
  - econstructor; eassumption.
Qed.

Lemma parallel_dbeta_incl_trans_refl_clos_dbeta :
  forall t1 t2, parallel_dbeta t1 t2 -> trans_refl_clos dbeta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor.
  - apply trans_refl_clos_compose with (y := dapp t3 t2).
    + eapply trans_refl_clos_map_impl with (f := fun t => dapp t t2); [|eassumption].
      intros; constructor; firstorder using parallel_dbeta_dlc.
    + eapply trans_refl_clos_map_impl with (f := fun t => dapp t3 t); [|eassumption].
      intros; constructor; firstorder using parallel_dbeta_dlc.
  - pick x \notin (L ++ dfv t2 ++ dfv t3).
    rewrite !in_app_iff in *.
    rewrite <- (dclose_dopen t2 0 x), <- (dclose_dopen t3 0 x) by tauto.
    apply trans_refl_clos_map_impl with (RA := dbeta) (f := fun t => dlam _ (dcloseb 0 x t)).
    + intros t4 t5 Hbeta.
      apply dbeta_lam with (L := dfv t4 ++ dfv t5); [assumption|].
      intros y Hy; rewrite in_app_iff in *.
      rewrite !dopen_dclose by (constructor || apply dbeta_dlc in Hbeta; tauto).
      apply dbeta_subst; [constructor | auto].
    + auto.
  - econstructor; constructor; auto.
Qed.



(* S-terms : lambda-calculus with explicit substitutions *)

(*
Inductive sterm :=
| sbvar : nat -> sterm
| sfvar : freevar -> sterm
| slam : sterm -> sterm
| sapp : sterm -> sterm -> sterm
| slet : sterm -> sterm -> sterm (* t1 [x := t2] *).

Fixpoint ssubstb k u t :=
  match t with
  | sbvar i => if Nat.eq_dec i k then u else sbvar i
  | sfvar x => sfvar x
  | slam t => slam (ssubstb (S k) u t)
  | sapp t1 t2 => sapp (ssubstb k u t1) (ssubstb k u t2)
  | slet t1 t2 => slet (ssubstb (S k) u t1) (ssubstb k u t2)
  end.

Fixpoint scloseb k x t :=
  match t with
  | sbvar i => sbvar i
  | sfvar y => if freevar_eq_dec x y then sbvar k else sfvar y
  | slam t => slam (scloseb (S k) x t)
  | sapp t1 t2 => sapp (scloseb k x t1) (scloseb k x t2)
  | slet t1 t2 => slet (scloseb (S k) x t1) (scloseb k x t2)
  end.

Notation "t 's[' k <- u ]" := (ssubstb k u t) (at level 67).
Notation "t 's^^' u" := (t s[ 0 <- u ]) (at level 67).
Notation "t 's^' x" := (t s^^ (sfvar x)) (at level 35).

Fixpoint ssubstf x u t :=
  match t with
  | sbvar i => sbvar i
  | sfvar y => if freevar_eq_dec x y then u else sfvar y
  | slam t => slam (ssubstf x u t)
  | sapp t1 t2 => sapp (ssubstf x u t1) (ssubstf x u t2)
  | slet t1 t2 => slet (ssubstf x u t1) (ssubstf x u t2)
  end.

Notation "t 's[' x := u ]" := (ssubstf x u t) (at level 67).

Fixpoint sfv t :=
  match t with
  | sbvar i => nil
  | sfvar x => x :: nil
  | slam t => sfv t
  | sapp t1 t2 => sfv t1 ++ sfv t2
  | slet t1 t2 => sfv t1 ++ sfv t2
  end.

Lemma ssubstf_fv :
  forall t u x, x \notin sfv t -> t s[ x := u ] = t.
Proof.
  induction t; intros u x Hx; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; intuition congruence.
  - f_equal; apply IHt; auto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; rewrite in_app_iff in Hx; tauto.
Qed.

Inductive slc : sterm -> Prop :=
| slc_var : forall v, slc (sfvar v)
| slc_app : forall t1 t2, slc t1 -> slc t2 -> slc (sapp t1 t2)
| slc_lam : forall t L, (forall x, x \notin L -> slc (t s^ x)) -> slc (slam t)
| slc_let : forall t1 t2 L, (forall x, x \notin L -> slc (t1 s^ x)) -> slc t2 -> slc (slet t1 t2).

Definition sbody t := exists L, forall x, x \notin L -> slc (t s^ x).
Lemma slc_lam_body : forall t, slc (slam t) <-> sbody t.
Proof.
  intros t. split.
  - intros H; inversion H; exists L; auto.
  - intros [L H]; econstructor; eauto.
Qed.

Lemma slc_let_body : forall t1 t2, slc (slet t1 t2) <-> sbody t1 /\ slc t2.
Proof.
  intros t. split.
  - intros H; inversion H; split; [exists L|]; auto.
  - intros [[L H1] H2]; econstructor; eauto.
Qed.

Lemma ssubstb_lc_id_core :
  forall t u v k1 k2, k1 <> k2 -> t s[ k2 <- v ] s[ k1 <- u ] = t s[ k2 <- v ] -> t s[ k1 <- u ] = t.
Proof.
  induction t; intros u v k1 k2 Hk Heq; simpl in *; inversion Heq; try (f_equal; eauto).
  repeat ( destruct Nat.eq_dec; simpl in * ); congruence.
Qed.

Lemma ssubstb_lc_id : forall t u, slc t -> forall k, t s[ k <- u ] = t.
Proof.
  intros t1 t2 H. induction H.
  - reflexivity.
  - intros; simpl; rewrite IHslc1, IHslc2; reflexivity.
  - intros k. simpl. f_equal. pick x \notin L as Hx.
    eapply ssubstb_lc_id_core with (k2 := 0); eauto.
  - intros k. simpl. f_equal.
    + pick x \notin L as Hx.
      eapply ssubstb_lc_id_core with (k2 := 0); eauto.
    + auto.
Qed.

Lemma ssubstb_substf :
  forall t u v k x, slc u -> t s[ k <- v ] s[ x := u ] = t s[ x := u ] s[ k <- v s[ x := u ]].
Proof.
  induction t.
  - intros; simpl. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl. destruct freevar_eq_dec; [|reflexivity].
    rewrite ssubstb_lc_id; auto.
  - intros; simpl. f_equal. apply IHt; auto.
  - intros; simpl. f_equal; auto.
  - intros; simpl. f_equal; auto.
Qed.

Lemma ssubstf_substb_free :
  forall t u v k x, x ∉ sfv v -> slc u -> t s[ x := u ] s[ k <- v ] = t s[ k <- v ] s[ x := u ].
Proof.
  intros. rewrite ssubstb_substf; [|assumption].
  f_equal. rewrite ssubstf_fv; auto.
Qed.

Lemma ssubstf_substb_free2 :
  forall t u v k x, x ∉ sfv t -> t s[ k <- v ] s[ x := u ] = t s[ k <- v s[ x := u ] ].
Proof.
  induction t.
  - intros; simpl in *. destruct Nat.eq_dec; simpl; reflexivity.
  - intros; simpl in *. destruct freevar_eq_dec; intuition congruence.
  - intros; simpl in *. f_equal. auto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
  - intros; simpl in *.
    f_equal; [apply IHt1 | apply IHt2]; rewrite !in_app_iff in *; tauto.
Qed.

Lemma scloseb_id :
  forall t k x, x \notin sfv t -> scloseb k x t = t.
Proof.
  intros t. induction t.
  - intros; reflexivity.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in*; f_equal; auto.
  - intros; simpl in *; rewrite in_app_iff in*; f_equal; auto.
Qed.

Lemma scloseb_substf_free :
  forall t u k x y, x <> y -> x \notin sfv u -> (scloseb k x t) s[ y := u ] = scloseb k x (t s[ y := u ]).
Proof.
  intros t. induction t.
  - intros; simpl; reflexivity.
  - intros; simpl; repeat (destruct freevar_eq_dec; simpl in * ); try congruence.
    rewrite scloseb_id; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
  - intros; simpl in *; f_equal; auto.
Qed.

Lemma ssubstf_lc : forall t, slc t -> forall u x, slc u -> slc (t s[ x := u ]).
Proof.
  intros t Ht. induction Ht; intros u x Hu.
  - simpl. destruct freevar_eq_dec; [assumption | constructor].
  - simpl. constructor; auto.
  - simpl. apply slc_lam with (L := x :: L). intros y Hy.
    rewrite ssubstf_substb_free; [|simpl in *; intuition congruence|assumption].
    apply H0; simpl in *; tauto.
  - simpl. apply slc_let with (L := x :: L).
    + intros y Hy.
      rewrite ssubstf_substb_free; [|simpl in *; intuition congruence|assumption].
      apply H0; simpl in *; tauto.
    + auto.      
Qed.

Lemma ssubstb_is_substf :
  forall t u x, x ∉ sfv t -> t s^^ u = t s^ x s[ x := u ].
Proof.
  intros t u x Hx.
  rewrite ssubstf_substb_free2; [|assumption].
  simpl. destruct freevar_eq_dec; tauto.
Qed.

Lemma ssubstb_lc : forall t u, sbody t -> slc u -> slc (t s^^ u).
Proof.
  intros t u [L Ht] Hu.
  pick x ∉ (L ++ sfv t).
  rewrite in_app_iff in *.
  rewrite ssubstb_is_substf with (x := x); [|tauto].
  apply ssubstf_lc; intuition.
Qed.

Lemma slc_open_gen :
  forall t x, sbody t -> slc (t s^ x).
Proof.
  intros.
  apply ssubstb_lc; [assumption | constructor].
Qed.

Lemma sclose_open :
  forall t k x, x \notin sfv t -> scloseb k x (t s[ k <- sfvar x ]) = t.
Proof.
  intros t. induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; try destruct freevar_eq_dec; congruence.
  - intros; simpl in *; destruct freevar_eq_dec; firstorder congruence.
  - intros; simpl in *; rewrite IHt; auto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
  - intros; simpl in *; rewrite in_app_iff in *; rewrite IHt1, IHt2; tauto.
Qed.

Lemma sopen_inj :
  forall x t1 t2, x \notin sfv t1 -> x \notin sfv t2 -> t1 s^ x = t2 s^ x -> t1 = t2.
Proof.
  intros.
  rewrite <- (sclose_open t1 0 x), <- (sclose_open t2 0 x); auto; congruence.
Qed.

Lemma sopen_close_core :
  forall t i j x y u, i <> j -> x <> y -> slc u -> y \notin sfv t -> (scloseb j x t) s[ j <- u ] s[ i <- sfvar y ] = (scloseb j x (t s[ i <- sfvar y ])) s[ j <- u ].
Proof.
  intros t. induction t.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite ssubstb_lc_id; auto.
  - intros; simpl.
    repeat ((destruct Nat.eq_dec || destruct freevar_eq_dec); simpl); try congruence.
    rewrite ssubstb_lc_id; auto.
  - intros; simpl. f_equal.
    apply IHt; simpl in *; auto.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; tauto.
  - intros; simpl in *.
    rewrite in_app_iff in *.
    f_equal; [apply IHt1 | apply IHt2]; auto.
Qed.

Lemma sopen_close :
  forall t, slc t -> forall k x u, slc u -> ssubstb k u (scloseb k x t) = t s[ x := u ].
Proof.
  intros t H. induction H; intros k x u Hu.
  - simpl. destruct freevar_eq_dec; simpl; try destruct Nat.eq_dec; simpl; congruence.
  - simpl. f_equal; auto.
  - simpl. f_equal.
    match goal with [ |- ?t1 = ?t2 ] => pick y \notin (x :: L ++ sfv t1 ++ sfv t2 ++ sfv t) end.
    simpl in *; rewrite !in_app_iff in *.
    apply (sopen_inj y); try tauto.
    rewrite sopen_close_core by intuition.
    rewrite ssubstf_substb_free by (simpl; intuition).
    intuition.
  - simpl. f_equal; [|auto].
    match goal with [ |- ?t3 = ?t4 ] => pick y \notin (x :: L ++ sfv t3 ++ sfv t4 ++ sfv t1) end.
    simpl in *; rewrite !in_app_iff in *.
    apply (sopen_inj y); try tauto.
    rewrite sopen_close_core by intuition.
    rewrite ssubstf_substb_free by (simpl; intuition).
    intuition.
Qed.

Lemma ssubstf_id :
  forall x t, t s[ x := sfvar x ] = t.
Proof.
  intros x t; induction t; simpl; try congruence.
  destruct freevar_eq_dec; congruence.
Qed.

Lemma sopen_close_var :
  forall t, slc t -> forall k x, ssubstb k (sfvar x) (scloseb k x t) = t.
Proof.
  intros. rewrite sopen_close, ssubstf_id; auto.
  constructor.
Qed.

(* Beta and parallel beta *)

Inductive distant_beta_redex : sterm -> sterm -> sterm -> Prop :=
| distant_beta_lam : forall t1 t2, sbody t1 -> slc t2 -> distant_beta_redex (slam t1) t2 (slet t1 t2)
| distant_beta_let : forall t1 t2 t3 t4 L,
    (forall x, x \notin L -> distant_beta_redex (t1 s^ x) t3 (t4 s^ x)) -> slc t2 -> distant_beta_redex (slet t1 t2) t3 (slet t4 t2).

Inductive sbeta : sterm -> sterm -> Prop :=
| sbeta_redex : forall t1 t2 t3, distant_beta_redex t1 t2 t3 -> sbeta (sapp t1 t2) t3
| sbeta_app_left : forall t1 t2 t3, sbeta t1 t2 -> slc t3 -> sbeta (sapp t1 t3) (sapp t2 t3)
| sbeta_app_right : forall t1 t2 t3, sbeta t1 t2 -> slc t3 -> sbeta (sapp t3 t1) (sapp t3 t2)
| sbeta_lam : forall t1 t2 L, (forall x, x ∉ L -> sbeta (t1 s^ x) (t2 s^ x)) -> sbeta (slam t1) (slam t2)
| sbeta_let_left : forall t1 t2 t3 L,
    (forall x, x \notin L -> sbeta (t1 s^ x) (t2 s^ x)) -> slc t3 -> sbeta (slet t1 t3) (slet t2 t3)
| sbeta_let_right : forall t1 t2 t3, sbeta t1 t2 -> sbody t3 -> sbeta (slet t3 t1) (slet t3 t2).

Lemma distant_beta_redex_lc :
  forall t1 t2 t3, distant_beta_redex t1 t2 t3 -> slc t1 /\ slc t2 /\ slc t3.
Proof.
  intros t1 t2 t3 H. induction H.
  - firstorder using slc_lam_body, slc_let_body.
  - assert (sbody t1) by firstorder.
    assert (sbody t4) by firstorder.
    pick x \notin L.
    split; [|split]; try (apply slc_let_body; tauto).
    firstorder.
Qed.

Lemma sbeta_lc : forall t1 t2, sbeta t1 t2 -> slc t1 /\ slc t2.
Proof.
  intros t1 t2 H. induction H.
  - apply distant_beta_redex_lc in H.
    split; [constructor|]; tauto.
  - split; constructor; tauto.
  - split; constructor; tauto.
  - split; apply slc_lam with (L := L); firstorder.
  - split; apply slc_let with (L := L); firstorder.
  - split; apply slc_let_body; tauto.
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
  forall t u1 u2 x, beta u1 u2 -> lc t -> trans_refl_clos beta (t [x := u1]) (t [x := u2]).
Proof.
  intros t u1 u2 x Hbeta Ht. induction Ht.
  - simpl. destruct freevar_eq_dec.
    + econstructor; [eassumption|constructor].
    + constructor.
  - simpl. destruct (beta_lc _ _ Hbeta) as [Hlc1 Hlc2]. eapply trans_refl_clos_compose.
    + eapply trans_refl_clos_map_impl with (f := fun t => app t _); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
    + eapply trans_refl_clos_map_impl with (f := fun t => app _ t); [|eauto].
      intros; constructor; [assumption | apply substf_lc; assumption].
  - simpl.
    pick y \notin (x :: L ++ fv t ++ fv u1 ++ fv u2) as Hy; simpl in Hy.
    rewrite !in_app_iff in Hy.
    rewrite <- (close_open t 0 y), !closeb_substf_free by intuition.
    eapply trans_refl_clos_map_impl with (f := fun t => lam (closeb 0 y t)); [|intuition].
    + intros t3 t4 Hbeta1.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros z Hz; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
      apply beta_subst; [constructor | auto].
Qed.
*)


















(* Stores *)

Definition ref := nat.
Definition store := list.
Axiom fresh_store : forall {A : Type}, store A -> ref -> Prop.
Axiom add_store : forall {A : Type}, ref -> A -> store A -> store A.
Axiom get_store : forall {A : Type}, ref -> store A -> option A.
Opaque ref store.

(* List inclusion *)

Definition list_inc (L1 L2 : list freevar) := forall x, In x L1 -> In x L2.

Lemma list_inc_trans :
  forall L1 L2 L3, list_inc L1 L2 -> list_inc L2 L3 -> list_inc L1 L3.
Proof.
  intros; unfold list_inc in *; firstorder.
Qed.

Lemma list_inc_app_left :
  forall L1 L2 L3, list_inc (L1 ++ L2) L3 <-> list_inc L1 L3 /\ list_inc L2 L3.
Proof.
  intros; unfold list_inc in *.
  firstorder using in_app_iff.
  rewrite in_app_iff in *; firstorder.
Qed.

(* Global environments and "dual" expressions *)

Definition gterm := (dterm * (list (freevar * dterm)))%type.

Fixpoint gterm_env_fv (e : list (freevar * dterm)) :=
  match e with
  | nil => nil
  | (x, t) :: e => x :: dfv t ++ gterm_env_fv e
  end.

Definition gterm_fv (t : gterm) := dfv (fst t) ++ gterm_env_fv (snd t).

Ltac prove_list_inc := (let x := fresh "x" in intros x; unfold gterm_fv; simpl; try repeat (rewrite in_app_iff; simpl); tauto).

Fixpoint gterm_read t (e : list (freevar * dterm)) :=
  match e with
  | nil => t
  | (x, t1) :: e => gterm_read (t d[ x := t1 ]) e
  end.

Lemma gterm_read_app :
  forall e t1 t2, gterm_read (dapp t1 t2) e = dapp (gterm_read t1 e) (gterm_read t2 e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

Lemma gterm_read_lam :
  forall e t1 t2, gterm_read (dlam t1 t2) e = dlam (gterm_read t1 e) (gterm_read t2 e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

Fixpoint gterm_env_find x (e : list (freevar * dterm)) :=
  match e with
  | nil => None
  | (y, t) :: e => if freevar_eq_dec x y then Some t else gterm_env_find x e
  end.

Lemma gterm_env_find_fv :
  forall e x t, gterm_env_find x e = Some t -> list_inc (dfv t) (gterm_env_fv e).
Proof.
  induction e as [|[x u] e]; intros; simpl in *.
  - congruence.
  - destruct freevar_eq_dec; simpl in *.
    + replace u with t by congruence. prove_list_inc.
    + eapply list_inc_trans; [eapply IHe; apply H|]. prove_list_inc.
Qed.

Inductive gterm_redt : list freevar -> gterm -> gterm -> Prop :=
| gterm_redt_app1 : forall L t1 t2 t3 e1 e2,
    gterm_redt L (t1, e1) (t2, e2) -> gterm_redt L (dapp t1 t3, e1) (dapp t2 t3, e2)
| gterm_redt_app2 : forall L t1 t2 t3 e1 e2,
    gterm_redt L (t1, e1) (t2, e2) -> gterm_redt L (dapp t3 t1, e1) (dapp t3 t2, e2)
| gterm_redt_lam : forall L L1 t1 t2 t3 e1 e2,
    (forall x, x \notin L1 -> gterm_redt (x :: L) (t1 d^ x, e1) (t2 d^ x, e2)) ->
    gterm_redt L (dlam t3 t1, e1) (dlam t3 t2, e2)
| gterm_redt_redex : forall L t1 t2 t3 e x,
    x \notin L ->
    gterm_redt L (dapp (dlam t1 t2) t3, e) (t1 d^ x, (x, t3) :: e)
| gterm_redt_var : forall L t e x,
    gterm_env_find x e = Some t -> gterm_redt L (dfvar x, e) (t, e)
.

Inductive gterm_red : list freevar -> gterm -> gterm -> Prop :=
| gterm_red_env : forall L t t1 t2 e1 e2 x,
    gterm_red L (t1, e1) (t2, e2) ->
    gterm_red L (t, (x, t1) :: e1) (t, (x, t2) :: e2)
| gterm_red_redt : forall L t1 t2 e1 e2, gterm_redt L (t1, e1) (t2, e2) -> gterm_red L (t1, e1) (t2, e2)
.

Lemma gterm_inc_redt :
  forall t1 t2 L1, gterm_redt L1 t1 t2 -> forall L2, list_inc L2 L1 -> gterm_redt L2 t1 t2.
Proof.
  intros t1 t2 L1 Hred. induction Hred.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; apply gterm_redt_lam with (L1 := L1). firstorder.
  - intros; constructor; auto.
  - intros; constructor; auto.
Qed.


Lemma gterm_inc_red :
  forall t1 t2 L1, gterm_red L1 t1 t2 -> forall L2, list_inc L2 L1 -> gterm_red L2 t1 t2.
Proof.
  intros t1 t2 L1 Hred.
  induction Hred; intros; constructor; eauto using gterm_inc_redt.
Qed.

Definition disjoint (L1 L2 : list freevar) := forall x1 x2, In x1 L1 -> In x2 L2 -> x1 <> x2.

Definition gterm_red1 L t1 t2 := gterm_red (L ++ gterm_fv t1) t1 t2.

Inductive gterm_env_wf : list (freevar * dterm) -> Prop :=
| gterm_env_wf_nil : gterm_env_wf nil
| gterm_env_fv_cons :
    forall x t e,
      gterm_env_wf e ->
      dlc t -> x \notin (dfv t ++ gterm_env_fv e) ->
      gterm_env_wf ((x, t) :: e).

Lemma gterm_env_wf_inv :
  forall {x t e}, gterm_env_wf ((x, t) :: e) ->
             gterm_env_wf e /\ dlc t /\
             x \notin (dfv t ++ gterm_env_fv e).
Proof.
  intros x t e H. inversion H; tauto.
Qed.

Definition gterm_wf (t : gterm) := dlc (fst t) /\ gterm_env_wf (snd t).

Lemma dsubstf_dlc2 :
  forall t x u, dlc (t d[ x := u ]) -> dlc t.
Proof.
Admitted.
(*
  intros t x u H.
  remember (t d[ x := u ]) as v. revert t u x Heqv.
  induction H; intros t u x.
  - destruct t; simpl; try congruence. intros; constructor.
  - destruct t; simpl; try congruence; [intros; constructor|].
    intros Happ. injection Happ; intros; constructor; eauto.
  - destruct t; simpl; try congruence; [intros; constructor|].
    intros Hlam. injection Hlam; intros.
    apply dlc_lam with (L := x :: L); intros y Hy; simpl in Hy.
    + apply (H0 y ltac:(tauto) _ u x). rewrite H4.

    + eapply IHdlc1; congruence.
    eapply dlc_dlam_dbody in H.
    destruct H as [[L1 H1] [L2 H2]].
    apply dlc_lam with (L := x :: L1 ++ L2); intros y Hy; simpl in Hy; rewrite in_app_iff in Hy.
*)

Lemma gterm_read_wf_lc_rec :
  forall e t, dlc (gterm_read t e) -> gterm_env_wf e -> dlc t.
Proof.
  induction e as [|[x v] e]; intros t Hlc He; simpl in *.
  - tauto.
  - apply gterm_env_wf_inv in He.
    specialize (IHe _ Hlc ltac:(tauto)).
    apply dsubstf_dlc2 in IHe. assumption.
Qed.

Lemma gterm_read_wf_lc :
  forall e t, gterm_wf (t, e) -> dlc t.
Proof.
  intros e t H; apply H.
  (*
  intros.
  unfold gterm_wf in *; simpl in *.
  eapply gterm_read_wf_lc_rec; [|apply H].
  apply H. *)
Qed.

Lemma gterm_read_dsubstb :
  forall e t k u, gterm_env_wf e -> gterm_read (dsubstb k u t) e = dsubstb k (gterm_read u e) (gterm_read t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - rewrite dsubstb_dsubstf, IHe.
    + reflexivity.
    + eapply gterm_env_wf_inv; eassumption.
    + apply gterm_env_wf_inv in H.
      eapply gterm_read_wf_lc; split; simpl; apply H.
Qed.

Lemma gterm_read_dsubstf :
  forall e x t u, x \notin gterm_env_fv e -> gterm_read (dsubstf x u t) e = dsubstf x (gterm_read u e) (gterm_read t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - rewrite in_app_iff in *. rewrite dsubstf_dsubstf, IHe.
    + reflexivity.
    + tauto.
    + firstorder congruence.
    + tauto.
Qed.

Lemma gwf_app_inv :
  forall {t1 t2 e}, gterm_wf (dapp t1 t2, e) -> gterm_wf (t1, e) /\ gterm_wf (t2, e).
Proof.
  intros t1 t2 e [H1 H2]; simpl in *.
  (* rewrite gterm_read_app in H1. *)
  inversion H1.
  unfold gterm_wf; simpl; tauto.
Qed.

(*
Lemma gterm_wf_read_wf :
  forall {e t}, gterm_wf (t, e) -> dwf (gterm_read t e).
Proof.
  (*
  induction e as [|[x t] e].
  - intros; unfold gterm_wf in *; simpl in *. tauto.
  - intros t1 [H1 H2]; unfold gterm_wf in *; simpl in *.
    apply gterm_env_wf_inv in H2.
    apply IHe; split; [|tauto].
    apply dsubstf_dwf; tauto. *)
  intros e t [H _]; exact H.
Qed.
 *)

Lemma gterm_wf_read_lc :
  forall {e t}, gterm_wf (t, e) -> dlc (gterm_read t e).
Proof.
  induction e as [|[x t] e].
  - intros; unfold gterm_wf in *; simpl in *. tauto.
  - intros t1 [H1 H2]; unfold gterm_wf in *; simpl in *.
    apply gterm_env_wf_inv in H2.
    apply IHe; split; [|tauto].
    apply dsubstf_dlc; tauto.
  (* intros t e H. (* apply dwf_dlc, gterm_wf_read_wf; assumption. *) apply H. *)
Qed.


Lemma gterm_read_var :
  forall x e, x \notin gterm_env_fv e -> gterm_read (dfvar x) e = dfvar x.
Proof.
  intros x e. induction e as [|[y t] e].
  - reflexivity.
  - intros; simpl in *.
    destruct freevar_eq_dec; try tauto.
    apply IHe; rewrite !in_app_iff in *; tauto.
Qed.

Lemma gterm_wf_read_body :
  forall {t e}, dbody t -> gterm_env_wf e -> dbody (gterm_read t e).
Proof.
  intros t e [L Hlc] He.
  exists (L ++ gterm_env_fv e). intros x Hx; rewrite in_app_iff in Hx.
  replace (dfvar x) with (gterm_read (dfvar x) e) by (apply gterm_read_var; tauto).
  rewrite <- gterm_read_dsubstb by tauto.
  apply gterm_wf_read_lc; split; firstorder.
Qed.


Lemma gterm_env_find_fv2 :
  forall e x t, gterm_env_wf e -> gterm_env_find x e = Some t -> x \notin dfv t.
Proof.
  induction e as [|[x u] e]; intros; simpl in *.
  - congruence.
  - apply gterm_env_wf_inv in H; rewrite in_app_iff in *.
    destruct freevar_eq_dec; simpl in *; try congruence.
    + firstorder congruence.
    + firstorder.
Qed.


Lemma gterm_env_find_read :
  forall e x t, gterm_env_wf e -> gterm_env_find x e = Some t -> gterm_read (dfvar x) e = gterm_read t e.
Proof.
  induction e as [|[x u] e]; intros; simpl in *.
  - congruence.
  - repeat (destruct freevar_eq_dec); simpl in *; try congruence.
    + replace t with u by congruence.
      apply gterm_env_wf_inv in H; rewrite in_app_iff in *.
      rewrite dsubstf_dfv; firstorder congruence.
    + apply gterm_env_wf_inv in H; rewrite in_app_iff in *.
      erewrite IHe; try eassumption; [|apply H].
      rewrite dsubstf_dfv; [reflexivity|].
      assert (H2 := gterm_env_find_fv _ _ _ H0). firstorder.
Qed.


Lemma gterm_env_find_dlc :
  forall e x t, gterm_env_wf e -> gterm_env_find x e = Some t -> dlc t.
Proof.
  induction e as [|[x u] e]; intros; simpl in *.
  - congruence.
  - repeat (destruct freevar_eq_dec); simpl in *; try congruence.
    + replace t with u by congruence.
      apply gterm_env_wf_inv in H. tauto.
    + apply gterm_env_wf_inv in H.
      firstorder.
Qed.


(*
Lemma lc_app_inv : forall {t1 t2}, lc (app t1 t2) -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H; inversion H; auto.
Qed.
 *)


Lemma trans_refl_clos_beta_lc :
  forall t1 t2, trans_refl_clos beta t1 t2 -> lc t1 -> lc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using beta_lc.
Qed.

Lemma trans_refl_clos_dbeta_dlc :
  forall t1 t2, trans_refl_clos dbeta t1 t2 -> dlc t1 -> dlc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using dbeta_dlc.
Qed.

Lemma trans_refl_clos_beta_app :
  forall t1 t2 t3 t4,
    lc t1 -> lc t2 ->
    trans_refl_clos beta t1 t3 -> trans_refl_clos beta t2 t4 -> trans_refl_clos beta (app t1 t2) (app t3 t4).
Proof.
  intros t1 t2 t3 t4 Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply trans_refl_clos_compose.
  - eapply trans_refl_clos_map_impl with (f := fun t => app _ t); [|eassumption].
    intros t5 t6 Hbeta; constructor; assumption.
  - eapply trans_refl_clos_map_impl with (f := fun t => app t _); [|eassumption].
    intros t5 t6 Hbeta; constructor; [|eapply trans_refl_clos_beta_lc]; eassumption.
Qed.

Lemma trans_refl_clos_dbeta_app :
  forall t1 t2 t3 t4,
    dlc t1 -> dlc t2 ->
    trans_refl_clos dbeta t1 t3 -> trans_refl_clos dbeta t2 t4 -> trans_refl_clos dbeta (dapp t1 t2) (dapp t3 t4).
Proof.
  intros t1 t2 t3 t4 Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply trans_refl_clos_compose.
  - eapply trans_refl_clos_map_impl with (f := fun t => dapp _ t); [|eassumption].
    intros t5 t6 Hbeta; constructor; assumption.
  - eapply trans_refl_clos_map_impl with (f := fun t => dapp t _); [|eassumption].
    intros t5 t6 Hbeta; constructor; [|eapply trans_refl_clos_dbeta_dlc]; eassumption.
Qed.

Lemma trans_refl_clos_beta_lam :
  forall t1 t2 x,
    x \notin fv t1 -> x \notin fv t2 -> trans_refl_clos beta (t1 ^ x) (t2 ^ x) ->
    trans_refl_clos beta (lam t1) (lam t2).
Proof.
  intros t1 t2 x Hx1 Hx2 Hbeta.
  rewrite <- (close_open t1 0 x), <- (close_open t2 0 x) by tauto.
  eapply trans_refl_clos_map_impl with (f := fun t => lam (closeb 0 x t)); [|eassumption].
  intros t3 t4 Hbeta1.
  apply beta_lam with (L := fv t1 ++ fv t2).
  intros y Hy; rewrite in_app_iff in *.
  rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
  apply beta_subst; [constructor | auto].
Qed.

Lemma trans_refl_clos_dbeta_dlam :
  forall t1 t2 t3 x,
    x \notin dfv t1 -> x \notin dfv t2 -> trans_refl_clos dbeta (t1 d^ x) (t2 d^ x) -> dbody t3 ->
    trans_refl_clos dbeta (dlam t3 t1) (dlam t3 t2).
Proof.
  intros t1 t2 t3 x Hx1 Hx2 Hbeta Hbody.
  rewrite <- (dclose_dopen t1 0 x), <- (dclose_dopen t2 0 x) by tauto.
  eapply trans_refl_clos_map_impl with (f := fun t => dlam t3 (dcloseb 0 x t)); [|eassumption].
  intros t4 t5 Hbeta1.
  apply dbeta_lam with (L := dfv t1 ++ dfv t2); [assumption|].
  intros y Hy; rewrite in_app_iff in *.
  rewrite !dopen_dclose by (constructor || apply dbeta_dlc in Hbeta1; tauto).
  apply dbeta_subst; [constructor | auto].
Qed.

Lemma dsubstb_dfv1 :
  forall t k u, list_inc (dfv (dsubstb k u t)) (dfv t ++ dfv u).
Proof.
  induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; firstorder.
  - intros; simpl; firstorder.
  - intros; simpl in *.
    intros x.
    specialize (IHt1 (S k) u x); specialize (IHt2 (S k) u x).
    rewrite !in_app_iff in *; tauto.
  - intros; simpl in *.
    intros x.
    specialize (IHt1 k u x); specialize (IHt2 k u x).
    rewrite !in_app_iff in *; tauto.
Qed.

Lemma dsubstb_dfv2 :
  forall t k u, list_inc (dfv t) (dfv (dsubstb k u t)).
Proof.
  induction t.
  - intros; simpl; destruct Nat.eq_dec; simpl; firstorder.
  - intros; simpl; firstorder.
  - intros; simpl in *.
    intros x; rewrite !in_app_iff; firstorder.
  - intros; simpl in *.
    intros x; rewrite !in_app_iff; firstorder.
Qed.

Lemma gterm_redt_newvars :
  forall L t1 t2, gterm_redt L t1 t2 -> forall x, In x (gterm_fv t2) -> In x L -> In x (gterm_fv t1).
Proof.
  intros L t1 t2 Hred. induction Hred; intros y Hy2 HyL.
  - unfold gterm_fv in *; simpl in *.
    specialize (IHHred y).
    rewrite !in_app_iff in *; firstorder.
  - unfold gterm_fv in *; simpl in *.
    specialize (IHHred y).
    rewrite !in_app_iff in *; firstorder.
  - unfold gterm_fv in *; simpl in *.
    pick x \notin (y :: L1) as Hx. specialize (H0 x ltac:(firstorder) y).
    simpl in Hx; rewrite !in_app_iff in *.
    destruct Hy2 as [[Hy2 | Hy2] | Hy2].
    + tauto.
    + destruct H0 as [H0 | H0]; [left; apply dsubstb_dfv2; assumption|tauto| |tauto].
      apply dsubstb_dfv1 in H0; rewrite !in_app_iff in *; simpl in *.
      firstorder congruence.
    + destruct H0 as [H0 | H0]; [tauto|tauto| |tauto].
      apply dsubstb_dfv1 in H0; rewrite !in_app_iff in *; simpl in *.
      firstorder congruence.
  - unfold gterm_fv in *; simpl in *.
    repeat (rewrite in_app_iff in *; simpl in * ).
    destruct Hy2 as [Hy2 | [Hy2 | [Hy2 | Hy2]]]; try firstorder congruence.
    apply dsubstb_dfv1 in Hy2.
    rewrite !in_app_iff in *; simpl in *.
    firstorder congruence.
  - unfold gterm_fv in *; simpl in *.
    rewrite in_app_iff in *.
    destruct Hy2 as [Hy2 | Hy2]; [|tauto].
    right. eapply gterm_env_find_fv; eauto.
Qed.

Lemma gterm_red_newvars :
  forall L t1 t2, gterm_red L t1 t2 -> forall x, In x (gterm_fv t2) -> In x L -> In x (gterm_fv t1).
Proof.
  intros L t1 t2 Hred. induction Hred; intros y Hy2 HyL.
  - unfold gterm_fv in *; simpl in *.
    specialize (IHHred y).
    repeat (rewrite in_app_iff in *; simpl in * ).
    firstorder congruence.
  - eauto using gterm_redt_newvars.
Qed.

Lemma dwf_lam_one :
  forall x t1 t2, x \notin dfv t1 -> x \notin dfv t2 ->
             dwf (t1 d^ x) -> dwf (t2 d^ x) -> trans_refl_clos dbeta (t1 d^ x) (t2 d^ x) -> dwf (dlam t1 t2).
Proof.
  intros x t1 t2 Hx1 Hx2 Hwf1 Hwf2 Hbeta.
  apply dwf_lam with (L := dfv t1 ++ dfv t2);
    intros y Hy; rewrite in_app_iff in Hy;
      try rewrite dsubstb_is_dsubstf with (t := t1) (x := x) by tauto;
      try rewrite dsubstb_is_dsubstf with (t := t2) (x := x) by tauto.
  - apply dsubstf_dwf; [constructor | tauto].
  - apply dsubstf_dwf; [constructor | tauto].
  - eapply trans_refl_clos_map_impl; [|eassumption].
    intros t3 t4 H; apply dbeta_subst; [constructor | assumption].
Qed.

Inductive parallel_env_dbeta : list (freevar * dterm) -> list (freevar * dterm) -> Prop :=
| ped_nil : parallel_env_dbeta nil nil
| ped_cons : forall x t1 t2 e1 e2, trans_refl_clos dbeta t1 t2 -> parallel_env_dbeta e1 e2 -> parallel_env_dbeta ((x, t1) :: e1) ((x, t2) :: e2).

Lemma parallel_env_dbeta_refl :
  forall e, parallel_env_dbeta e e.
Proof.
  induction e as [|[x t] e]; constructor; [constructor | assumption].
Qed.

Lemma parallel_env_dbeta_inv_left :
  forall x t1 e1 e, parallel_env_dbeta ((x, t1) :: e1) e -> exists t2 e2, trans_refl_clos dbeta t1 t2 /\ parallel_env_dbeta e1 e2 /\ e = (x, t2) :: e2.
Proof.
  intros x1 t1 e1 e H. inversion_clear H.
  eauto.
Qed.

Lemma parallel_env_dbeta_inv_right :
  forall x t2 e2 e, parallel_env_dbeta e ((x, t2) :: e2) -> exists t1 e1, trans_refl_clos dbeta t1 t2 /\ parallel_env_dbeta e1 e2 /\ e = (x, t1) :: e1.
Proof.
  intros x1 t2 e2 e H. inversion_clear H.
  eauto.
Qed.

Lemma dbeta_fv :
  forall t1 t2, dbeta t1 t2 -> list_inc (dfv t2) (dfv t1).
Proof.
  intros t1 t2 Hbeta. induction Hbeta.
  - simpl.
    eapply list_inc_trans; [apply dsubstb_dfv1|].
    prove_list_inc.
  - simpl. unfold list_inc in *; intros x; rewrite !in_app_iff; firstorder.
  - simpl. unfold list_inc in *; intros x; rewrite !in_app_iff; firstorder.
  - simpl.
    enough (list_inc (dfv t3) (dfv t2)) by (unfold list_inc in *; intros x; rewrite !in_app_iff; firstorder).
    pick x \notin (L ++ dfv t2 ++ dfv t3) as Hx; rewrite !in_app_iff in Hx.
    specialize (H1 x ltac:(tauto)).
    enough (list_inc (dfv t3) (x :: dfv t2)).
    + intros y Hy. specialize (H2 y Hy). simpl in H2.
      destruct H2 as [H2 | H2]; [|exact H2].
      rewrite H2 in *; tauto.
    + eapply list_inc_trans; [eapply dsubstb_dfv2|].
      eapply list_inc_trans; [exact H1|].
      eapply list_inc_trans; [eapply dsubstb_dfv1|].
      simpl; prove_list_inc.
Qed.

Lemma trans_refl_clos_dbeta_fv :
  forall t1 t2, trans_refl_clos dbeta t1 t2 -> list_inc (dfv t2) (dfv t1).
Proof.
  intros t1 t2 H. induction H.
  - prove_list_inc.
  - eapply list_inc_trans; [eassumption|].
    apply dbeta_fv. assumption.
Qed.

Lemma gterm_read_dbeta :
  forall e t1 t2, gterm_env_wf e -> dbeta t1 t2 -> dbeta (gterm_read t1 e) (gterm_read t2 e).
Proof.
  induction e as [|[x t] e].
  - intros; simpl; auto.
  - intros t1 t2 He Hbeta; simpl.
    apply gterm_env_wf_inv in He.
    apply IHe; [apply He|].
    apply dbeta_subst; tauto.
Qed.

Lemma gterm_read_trans_refl_clos_dbeta :
  forall e t1 t2, gterm_env_wf e -> trans_refl_clos dbeta t1 t2 -> trans_refl_clos dbeta (gterm_read t1 e) (gterm_read t2 e).
Proof.
  intros e t1 t2 He Hbeta.
  eapply trans_refl_clos_map_impl with (f := fun t => gterm_read t e).
  + intros; apply gterm_read_dbeta; eassumption.
  + assumption.
Qed.

Lemma parallel_env_dbeta_fv :
  forall e1 e2, parallel_env_dbeta e1 e2 -> list_inc (gterm_env_fv e2) (gterm_env_fv e1).
Proof.
  intros e1 e2 Hbeta. induction Hbeta.
  - firstorder.
  - simpl.
    apply trans_refl_clos_dbeta_fv in H.
    unfold list_inc in *; intros ?; simpl; rewrite !in_app_iff; firstorder.
Qed.

Lemma parallel_env_dbeta_wf :
  forall e1 e2, parallel_env_dbeta e1 e2 -> gterm_env_wf e1 -> gterm_env_wf e2.
Proof.
  intros e1 e2 H. induction H.
  - auto.
  - intros H1. apply gterm_env_wf_inv in H1.
    constructor.
    + tauto.
    + firstorder using trans_refl_clos_dbeta_dlc.
    + apply parallel_env_dbeta_fv in H0.
      apply trans_refl_clos_dbeta_fv in H.
      rewrite !in_app_iff in *; firstorder.
Qed.

Lemma trans_refl_clos_dbeta_dwf :
  forall t1 t2, trans_refl_clos dbeta t1 t2 -> dwf t1 -> dwf t2.
Proof.
  intros t1 t2 H. induction H.
  - auto.
  - intros H1. eapply dbeta_dwf in H1; [|eassumption]. auto.
Qed.


Definition term_wf_in_env t e := forall e2, parallel_env_dbeta e e2 -> dwf (gterm_read t e2).
Lemma term_wf_in_env_wf :
  forall t e, term_wf_in_env t e -> dwf (gterm_read t e).
Proof.
  intros t e H.
  exact (H e (parallel_env_dbeta_refl e)).
Qed.

Lemma term_wf_in_env_app : forall t1 t2 e, term_wf_in_env (dapp t1 t2) e <-> term_wf_in_env t1 e /\ term_wf_in_env t2 e.
Proof.
  intros t1 t2 e. unfold term_wf_in_env.
  split; [intros H; split | intros [H1 H2]]; intros e2 He2.
  - specialize (H e2 He2). rewrite gterm_read_app in H. apply dwf_app_inv in H; apply H.
  - specialize (H e2 He2). rewrite gterm_read_app in H. apply dwf_app_inv in H; apply H.
  - rewrite gterm_read_app. constructor; auto.
Qed.

Lemma term_wf_in_env_lam : forall t1 t2 e L,
    gterm_env_wf e ->
    term_wf_in_env (dlam t1 t2) e <-> forall x, x \notin (L ++ dfv t1 ++ dfv t2 ++ gterm_env_fv e) -> term_wf_in_env (t1 d^ x) e /\ term_wf_in_env (t2 d^ x) e /\ (forall e2, parallel_env_dbeta e e2 -> trans_refl_clos dbeta ((gterm_read t1 e2) d^ x) ((gterm_read t2 e2) d^ x)).
Proof.
  intros t1 t2 e L He. unfold term_wf_in_env.
  split.
  - intros H x Hx. rewrite !in_app_iff in Hx.
    split; [|split]; intros e2 He2; specialize (H e2 He2); rewrite gterm_read_lam in H; apply dwf_lam_inv_strong in H.
    + rewrite gterm_read_dsubstb by (eauto using parallel_env_dbeta_wf).
      rewrite gterm_read_var by (firstorder using parallel_env_dbeta_fv).
      apply H.
    + rewrite gterm_read_dsubstb by (eauto using parallel_env_dbeta_wf).
      rewrite gterm_read_var by (firstorder using parallel_env_dbeta_fv).
      apply H.
    + apply H.
  - intros HL e2 He2.
    rewrite gterm_read_lam.
    apply dwf_lam with (L := gterm_env_fv e2 ++ L ++ dfv t1 ++ dfv t2 ++ gterm_env_fv e).
    + intros x Hx; rewrite in_app_iff in Hx.
      replace (dfvar x) with (gterm_read (dfvar x) e2) by (apply gterm_read_var; tauto).
      rewrite <- gterm_read_dsubstb by (eauto using parallel_env_dbeta_wf).
      apply HL; auto.
    + intros x Hx; rewrite in_app_iff in Hx.
      replace (dfvar x) with (gterm_read (dfvar x) e2) by (apply gterm_read_var; tauto).
      rewrite <- gterm_read_dsubstb by (eauto using parallel_env_dbeta_wf).
      apply HL; auto.
    + intros x Hx; rewrite in_app_iff in Hx.
      apply HL; tauto.
Qed.


Lemma term_wf_in_env_cons_free :
  forall t u x e, x \notin dfv t -> term_wf_in_env t ((x, u) :: e) <-> term_wf_in_env t e.
Proof.
  intros t u x e Hx.
  unfold term_wf_in_env.
  split; intros H e2 He2.
  - specialize (H ((x, u) :: e2)).
    simpl in H. rewrite dsubstf_dfv in H by assumption.
    apply H.
    constructor; [constructor | assumption].
  - inversion_clear He2. simpl.
    rewrite dsubstf_dfv by assumption.
    auto.
Qed.

Lemma gterm_redt_beta_rec :
  forall L t1 t2,
    gterm_redt L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 -> term_wf_in_env (fst t1) (snd t1) ->
    gterm_wf t2 /\ term_wf_in_env (fst t2) (snd t2) /\
    (forall e3, parallel_env_dbeta (snd t2) e3 -> trans_refl_clos dbeta (gterm_read (fst t1) e3) (gterm_read (fst t2) e3)) /\
    (snd t2 = snd t1 \/ exists x t3, x \notin L /\ dlc t3 /\ term_wf_in_env t3 (snd t1) /\ snd t2 = (x, t3) :: snd t1).
Proof.
  intros L t1 t2 Hred. induction Hred; intros HL Hwf Hewf; simpl in *.

  - destruct (gwf_app_inv Hwf) as [Hwf1 Hwf3].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    rewrite term_wf_in_env_app in Hewf.
    specialize (IHHred HL1 Hwf1 ltac:(tauto)).
    destruct IHHred as (Hwf2 & Hewf2 & Hbeta & [He2 | (x & t4 & Hx & Ht4 & Hewf4 & He2)]); rewrite He2 in *;
      split; [|split; [|split]| |split; [|split]]; try eauto.
    + unfold gterm_wf in *; simpl in *.
      (* rewrite gterm_read_app in *. *)
      split; [|tauto].
      constructor; tauto.
    + rewrite term_wf_in_env_app. tauto.
    + intros e3 He3. rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_dbeta_app; eauto.
      admit. admit. constructor.
    + unfold gterm_wf in *; simpl in *.
      (* rewrite dsubstf_dfv with (t := t3).
      2: { unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto. } *)
      split; [|tauto].
      (* rewrite gterm_read_app in *. *)
      constructor; tauto.
    + rewrite term_wf_in_env_app. split; [tauto|].
      rewrite term_wf_in_env_cons_free; [tauto|].
      unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto.
    + intros e3 He3.
      specialize (Hbeta e3 He3).
      apply parallel_env_dbeta_inv_left in He3; destruct He3 as (t5 & e4 & Hbeta45 & Hebeta & He3); rewrite He3 in *.
      simpl in *.
      rewrite !gterm_read_app.
      rewrite dsubstf_dfv with (t := t3).
      2: { unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto. }
      apply trans_refl_clos_dbeta_app; eauto.
      admit. admit. constructor.
    + right. exists x; exists t4; auto.

  - destruct (gwf_app_inv Hwf) as [Hwf3 Hwf1].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    rewrite term_wf_in_env_app in Hewf.
    specialize (IHHred HL1 Hwf1 ltac:(tauto)).
    destruct IHHred as (Hwf2 & Hewf2 & Hbeta & [He2 | (x & t4 & Hx & Ht4 & Hewf4 & He2)]); rewrite He2 in *;
      split; [|split; [|split]| |split; [|split]]; try eauto.
    + unfold gterm_wf in *; simpl in *.
      (* rewrite gterm_read_app in *. *)
      split; [|tauto].
      constructor; tauto.
    + rewrite term_wf_in_env_app. tauto.
    + intros e3 He3. rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_dbeta_app; eauto.
      admit. admit. constructor.
    + unfold gterm_wf in *; simpl in *.
      (* rewrite dsubstf_dfv with (t := t3).
      2: { unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto. } *)
      split; [|tauto].
      (* rewrite gterm_read_app in *. *)
      constructor; tauto.
    + rewrite term_wf_in_env_app. split; [|tauto].
      rewrite term_wf_in_env_cons_free; [tauto|].
      unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto.
    + intros e3 He3.
      specialize (Hbeta e3 He3).
      apply parallel_env_dbeta_inv_left in He3; destruct He3 as (t5 & e4 & Hbeta45 & Hebeta & He3); rewrite He3 in *.
      simpl in *.
      rewrite !gterm_read_app.
      rewrite dsubstf_dfv with (t := t3).
      2: { unfold gterm_fv in *. simpl in *. intro. apply Hx. apply HL. rewrite !in_app_iff; tauto. }
      apply trans_refl_clos_dbeta_app; eauto.
      admit. admit. constructor.
    + right. exists x; exists t4; auto.

  - assert (HL1 : forall x, list_inc (gterm_fv (t1 d^ x, e1)) (x :: L)).
    {
      intros x.
      unfold gterm_fv in *; simpl in *.
      rewrite !list_inc_app_left in *.
      split; [|eapply list_inc_trans; [apply HL|]; prove_list_inc].
      eapply list_inc_trans; [apply dsubstb_dfv1|].
      simpl; rewrite list_inc_app_left; split; [|prove_list_inc].
      eapply list_inc_trans; [apply HL|]; prove_list_inc.
    }
    assert (Hwf1 : forall x, x \notin L -> gterm_wf (t1 d^ x, e1)).
    {
      intros x Hx. unfold gterm_wf in *; simpl in *.
      split; [|apply Hwf].
      destruct Hwf as [Hwfl Hwfe].
      (* rewrite gterm_read_lam in Hwfl. *)
      apply dlc_lam_inv_strong in Hwfl.
      (* rewrite gterm_read_dsubstb; [|assumption].
      rewrite gterm_read_var; [apply Hwfl|].
      unfold list_inc, gterm_fv in *; simpl in *; firstorder. *)
      apply Hwfl.
    }
    rewrite term_wf_in_env_lam with (L := nil) in Hewf by apply Hwf.
    remember (nil ++ dfv t3 ++ dfv t1 ++ gterm_env_fv e1) as L2.
    assert (HL3 : list_inc (dfv t3) L).
    {
      unfold gterm_fv in *; simpl in *.
      eapply list_inc_trans; [|apply HL].
      prove_list_inc.
    }
    split; [|split; [|split]].
    + unfold gterm_wf in *; simpl in *.
      split.
      * (* rewrite gterm_read_lam in *. *)
        apply dlc_lam with (L := L ++ L1 ++ L2 ++ gterm_env_fv e2); intros x Hx;
          rewrite !in_app_iff in *; specialize (H0 x ltac:(tauto) ltac:(auto) ltac:(auto) ltac:(apply Hewf; tauto)).
        -- (* replace (gterm_read t3 e2) with (gterm_read t3 e1). *)
           (* ++ *) destruct Hwf as [Hwfl Hwfe]; apply dlc_lam_inv_strong in Hwfl; apply Hwfl.
(*           ++ destruct H0 as (Hwf2 & Hbeta & [He2 | (y & t4 & Hy & Ht4 & He2)]); rewrite He2 in *; [reflexivity|].
              simpl.
              rewrite dsubstf_dfv; [reflexivity|firstorder]. *)
        -- (* rewrite gterm_read_dsubstb in H0 by tauto. *)
           (* rewrite gterm_read_var in H0 by tauto. *)
           tauto. 
(*        -- destruct Hwf as [Hwfl Hwfe].
           apply dwf_lam_inv_strong in Hwfl.
           destruct H0 as (Hwf2 & Hbeta & [He2 | (y & t4 & Hy & Ht4 & He2)]); rewrite He2 in *.
           ++ eapply trans_refl_clos_compose; [apply Hwfl|].
              rewrite !gterm_read_dsubstb in Hbeta by tauto.
              rewrite gterm_read_var in Hbeta by tauto.
              apply Hbeta.
           ++ simpl in *; rewrite !in_app_iff in *.
              rewrite dsubstf_dfv by firstorder.
              eapply trans_refl_clos_compose; [apply Hwfl|].
              rewrite dsubstb_dsubstf in Hbeta by auto.
              simpl in Hbeta.
              destruct freevar_eq_dec; [intuition congruence|].
              rewrite !gterm_read_dsubstb in Hbeta by tauto.
              rewrite !gterm_read_var in Hbeta by tauto.
              apply Hbeta. *)
      * pick x \notin (L ++ L1 ++ L2); rewrite !in_app_iff in *.
        specialize (H0 x ltac:(tauto) ltac:(auto) ltac:(auto) ltac:(apply Hewf; tauto)).
        tauto.
    + rewrite term_wf_in_env_lam with (L := L ++ L1 ++ L2); [|admit].
      intros x Hx; rewrite !in_app_iff in Hx.
      specialize (H0 x ltac:(tauto) ltac:(auto) ltac:(apply Hwf1; tauto) ltac:(apply Hewf; tauto)).
      destruct H0 as (Hwf2 & Hewf2 & Hbeta & [He2 | (y & t4 & Hy & Ht4 & Hewf4 & He2)]); rewrite He2 in *;
        split; [|split| |split]; try tauto.
      * apply Hewf; tauto.
      * intros e3 He3.
        eapply trans_refl_clos_compose; [apply Hewf; tauto|].
        specialize (Hbeta e3 He3).
        rewrite !gterm_read_dsubstb in Hbeta by (eapply parallel_env_dbeta_wf; [eassumption|apply Hwf]).
        rewrite gterm_read_var in Hbeta; [exact Hbeta|].
        intros Hx3. eapply parallel_env_dbeta_fv in Hx3; [|eassumption].
        specialize (HL x); unfold gterm_fv in HL; simpl in HL; rewrite !in_app_iff in HL. tauto.
      * apply term_wf_in_env_cons_free; [admit|].
        apply Hewf; tauto.
      * intros e3 He3.
        specialize (Hbeta e3 He3).
        apply parallel_env_dbeta_inv_left in He3; destruct He3 as (t5 & e4 & Hbeta45 & Hebeta & He3); rewrite He3 in *.
        simpl in *.
        eapply trans_refl_clos_compose.
        -- simpl.
           rewrite dsubstf_dfv by admit.
           apply Hewf; tauto.
        -- rewrite !dsubstb_dsubstf in Hbeta by (eapply trans_refl_clos_dbeta_dlc; eauto).
           simpl in Hbeta.
           destruct freevar_eq_dec; [intuition congruence|].
           rewrite dsubstf_dfv in Hbeta by (specialize (HL y); unfold gterm_fv in HL; simpl in HL; rewrite !in_app_iff in HL; tauto).
           unfold gterm_wf in Hwf; simpl in Hwf.
           rewrite !gterm_read_dsubstb in Hbeta by (eapply parallel_env_dbeta_wf; [eassumption | apply Hwf]).
           rewrite gterm_read_var in Hbeta; [exact Hbeta|].
           intros Hx4; eapply parallel_env_dbeta_fv in Hx4; [|eassumption].
           specialize (HL x); unfold gterm_fv in HL; simpl in HL; rewrite !in_app_iff in HL. tauto.
    + intros e3 He3.
      rewrite !gterm_read_lam. simpl.
      pick x \notin (L ++ L1 ++ L2 ++ dfv (gterm_read t3 e1) ++ dfv (gterm_read t3 e2) ++ dfv (gterm_read t1 e3) ++ dfv (gterm_read t2 e3) ++ gterm_env_fv e3);
        rewrite !in_app_iff in *.
      specialize (H0 x ltac:(tauto) ltac:(auto) ltac:(auto) ltac:(apply Hewf; tauto)).
      unfold gterm_wf in *; simpl in *.
      destruct H0 as (Hwf2 & Hewf2 & Hbeta & [He2 | (y & t4 & Hy & Ht4 & Hewf4 & He2)]); rewrite He2 in *.
      * apply trans_refl_clos_dbeta_dlam with (x := x); try tauto.
        -- specialize (Hbeta e3 He3).
           rewrite !gterm_read_dsubstb in Hbeta by (eapply parallel_env_dbeta_wf; [eassumption | apply Hwf]).
           rewrite !gterm_read_var in Hbeta by tauto.
           apply Hbeta.
        -- destruct Hwf as [Hwfl Hwfe].
           (* rewrite gterm_read_lam in Hwfl. *) apply dlc_dlam_dbody in Hwfl.
           apply gterm_wf_read_body; [apply Hwfl|].
           eapply parallel_env_dbeta_wf; [eassumption | apply Hwfe].
           (* tauto. *)
(*           destruct Hwfl as [[L3 Hwf3] _].
           exists (L3 ++ gterm_env_fv e1). intros y Hy.
           rewrite in_app_iff in Hy.
           specialize (Hwf3 y ltac:(tauto)).
           replace (dfvar y) with (gterm_read (dfvar y) e1) by (apply gterm_read_var; tauto).
           rewrite <- gterm_read_dsubstb by tauto.
           apply gterm_wf_read_lc. split; auto. *)
      * admit. (*simpl in *.
        rewrite dsubstf_dfv by firstorder.
        apply trans_refl_clos_dbeta_dlam with (x := x); try tauto.
        2: {
          destruct Hwf as [Hwfl Hwfe].
          (* rewrite gterm_read_lam in Hwfl. *) apply dlc_dlam_dbody in Hwfl. (* tauto. *)
          apply gterm_wf_read_body; tauto.
(*          destruct Hwfl as [[L3 Hwf3] _].
          exists (L3 ++ gterm_env_fv e1). intros z Hz.
          rewrite in_app_iff in Hz.
           specialize (Hwf3 z ltac:(tauto)).
           replace (dfvar z) with (gterm_read (dfvar z) e1) by (apply gterm_read_var; tauto).
           rewrite <- gterm_read_dsubstb by tauto.
           apply gterm_wf_read_lc. split; auto. *)
        }
        rewrite dsubstb_dsubstf in Hbeta by auto.
        simpl in Hbeta.
        destruct freevar_eq_dec; [intuition congruence|].
        rewrite !gterm_read_dsubstb in Hbeta by tauto.
        rewrite !gterm_read_var in Hbeta by tauto.
        apply Hbeta. *)
    + pick x \notin (L ++ L1 ++ L2); rewrite !in_app_iff in *.
      specialize (H0 x ltac:(tauto) ltac:(auto) ltac:(auto) ltac:(apply Hewf; tauto)).
      destruct H0 as (Hwf2 & Hewf2 & Hbeta & [He2 | (y & t4 & Hy & Ht4 & Hewf4 & He2)]); rewrite He2 in *.
      * left; reflexivity.
      * right. exists y; exists t4; auto.

  - destruct (gwf_app_inv Hwf) as [Hwfl Hwf3].
    assert (Hx : x \notin gterm_fv (dapp (dlam t1 t2) t3, e)) by firstorder.
    unfold gterm_fv in Hx; simpl in Hx; rewrite !in_app_iff in Hx.
    split; [|split; [|split]].
    + unfold gterm_wf in *; simpl in *. split.
      * (* rewrite gterm_read_dsubstf by tauto.
        apply dsubstf_dlc; [|tauto]. *)
        destruct Hwfl as [Hwfl _].
        (* rewrite gterm_read_lam in Hwfl. *) apply dlc_lam_inv_strong in Hwfl.
        apply Hwfl.
        (* rewrite gterm_read_dsubstb by tauto.
        rewrite gterm_read_var by tauto.
        apply Hwfl. *)
      * constructor; try tauto.
        rewrite in_app_iff; tauto.
    + intros e2 He2.
      apply parallel_env_dbeta_inv_left in He2; destruct He2 as (t4 & e3 & Hbeta34 & Hebeta & He2); rewrite He2 in *.
      simpl. (* rewrite <- dsubstb_is_dsubstf by tauto. *)
      rewrite gterm_read_dsubstf by admit. (* by (eapply parallel_env_dbeta_wf; [eassumption | apply Hwf3]). *)
      rewrite term_wf_in_env_app in Hewf.
      rewrite term_wf_in_env_lam with (L := nil) in Hewf by apply Hwf3.
      apply dsubstf_dwf.
      * eapply trans_refl_clos_dbeta_dwf.
        { apply gterm_read_trans_refl_clos_dbeta; [|eassumption].
          eapply parallel_env_dbeta_wf; [eassumption | apply Hwf3]. }
        apply Hewf. assumption.
      * apply Hewf; [|assumption].
        rewrite !in_app_iff; tauto.
    + intros e2 He2.
      apply parallel_env_dbeta_inv_left in He2; destruct He2 as (t4 & e3 & Hbeta34 & Hebeta & He2); rewrite He2 in *.
      assert (Hewf3 : gterm_env_wf e3) by (eapply parallel_env_dbeta_wf; [eassumption | apply Hwf3]).
      assert (Hbody1 : dbody (gterm_read t1 e3)).
      { destruct Hwfl as [Hwfl Hwfe]; simpl in *. apply dlc_dlam_dbody in Hwfl. apply gterm_wf_read_body; tauto. }
      assert (Hbody2 : dbody (gterm_read t2 e3)).
      { destruct Hwfl as [Hwfl Hwfe]; simpl in *. apply dlc_dlam_dbody in Hwfl. apply gterm_wf_read_body; tauto. }
      assert (Hlc3 : dlc (gterm_read t3 e3)).
      { apply gterm_wf_read_lc. split; [apply Hwf3 | apply Hewf3]. }
      rewrite gterm_read_app, gterm_read_lam. simpl.
      rewrite <- dsubstb_is_dsubstf by tauto.
      rewrite gterm_read_dsubstb by assumption.
      rewrite !dsubstf_dfv by tauto.
      eapply trans_refl_clos_compose.
      { apply trans_refl_clos_dbeta_app; [apply dlc_dlam_dbody; tauto|auto|constructor|].
        apply gterm_read_trans_refl_clos_dbeta; eassumption. }
      econstructor; constructor; [assumption | assumption |].
      apply gterm_wf_read_lc. split; [|assumption]. simpl.
      eapply trans_refl_clos_dbeta_dlc; [eassumption|apply Hwf3].
    + right. exists x; exists t3.
      split; [auto|].
      split; [eauto using gterm_read_wf_lc|].
      split; [|reflexivity].
      apply term_wf_in_env_app in Hewf; apply Hewf.

  - split; [|split; [|split]]; [| | |left; reflexivity].
    + unfold gterm_wf in *; simpl in *.
      split; [|tauto].
      apply gterm_env_find_dlc in H; tauto.
    + admit.
    + intros e3 He3.
      erewrite gterm_env_find_read; try eassumption.
      * constructor.
      * apply Hwf.
Qed.

Lemma gterm_red_beta_rec :
  forall L t1 t2,
    gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 ->
    (gterm_wf t2 /\
     trans_refl_clos beta (dterm_read1 (gterm_read (fst t1) (snd t1))) (dterm_read1 (gterm_read (fst t2) (snd t2)))) /\
    (forall t3, list_inc (dfv t3) L -> gterm_wf (t3, snd t1) ->
           gterm_wf (t3, snd t2) /\
           trans_refl_clos beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
Proof.
  intros L t1 t2 Hred. induction Hred; intros HL Hwf; simpl in *.

  - match goal with [ |- _ /\ ?G ] => enough (H : G) end.
    {
      split; apply H; [|assumption].
      eapply list_inc_trans; [|exact HL].
      unfold gterm_fv; simpl. prove_list_inc.
    } 
    intros t3 HL3 Hwf3.
    destruct Hwf as [Hwf Hwfe]; simpl in *.
    apply gterm_env_wf_inv in Hwfe; destruct Hwfe as (Hwfe1 & Hwf1 & Hx).
    rewrite in_app_iff in Hx.
    rewrite gterm_read_dsubstf by tauto.
    rewrite gterm_read_dsubstf.
    + rewrite !dsubstf_substf.
      split.
      { unfold gterm_wf in *; simpl in *. admit. }
      eapply trans_refl_clos_compose.
      * eapply trans_refl_clos_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|].
           ++ unfold gterm_fv in *; simpl in *.
              eapply list_inc_trans; [|exact HL]. prove_list_inc.
           ++ unfold gterm_wf in *; simpl in *.
              split; [|tauto].
              admit.
      * apply trans_refl_clos_refl_clos.
        eapply trans_refl_clos_map_impl with (f := fun t => _ [x := t]).
        -- intros t4 t5 Hbeta; apply beta_subst2; [exact Hbeta|].
           apply dlc_lc. apply gterm_wf_read_lc. unfold gterm_wf; simpl.

           (* split; [apply Hwf3|].
           apply gterm_red_wf in Hred; [apply Hred| |unfold gterm_wf; simpl; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc. *) admit.
        -- apply IHHred; [|split; assumption].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
    + intros Hx2. apply Hx.
      rewrite <- in_app_iff.
      eapply gterm_red_newvars with (t1 := (t1, e1)); [eassumption| |].
      * unfold gterm_fv; rewrite in_app_iff; tauto.
      * unfold gterm_fv in HL; simpl in HL.
        apply HL; rewrite in_app_iff; simpl; tauto.

  - apply gterm_redt_beta_rec in H; try assumption.
    simpl in *.
    split; [split|].
    + tauto.
    + apply trans_refl_clos_refl_clos.
      eapply trans_refl_clos_map_impl; [|apply H].
      intros; apply dbeta_beta; auto.
    + destruct H as (Hwf2 & Hbeta & [He2 | (x & t3 & Hx & Ht3 & He2)]); intros t4 HL4 Hwf4; rewrite He2 in *.
      * split; [assumption | constructor].
      * split.
        -- unfold gterm_wf in *; simpl in *.
           split; [|tauto].
           (* rewrite dsubstf_dfv by firstorder. *) tauto.
        -- simpl.
           rewrite dsubstf_dfv by firstorder.
           constructor.
Qed.
      


  - destruct (gwf_app_inv Hwf) as [Hwf1 Hwf3].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    specialize (IHHred HL1 Hwf1).
    split; [split|].
    + unfold gterm_wf in *; simpl in *.
      rewrite gterm_read_app in *.
      split; [|tauto].
      constructor; [tauto|].
      apply IHHred; [|assumption].
      eapply list_inc_trans; [|exact HL].
      unfold gterm_fv; simpl. prove_list_inc.
    + rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_beta_app; eauto using dlc_lc.
      * apply IHHred.
      * apply IHHred; [|assumption].
        eapply list_inc_trans; [|exact HL].
        unfold gterm_fv; simpl. prove_list_inc.
    + intros; apply IHHred; assumption.

  - destruct (gwf_app_inv Hwf) as [Hwf3 Hwf1].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    specialize (IHHred HL1 Hwf1).
    split; [split|].
    + unfold gterm_wf in *; simpl in *.
      rewrite gterm_read_app in *.
      split; [|tauto].
      constructor; [|tauto].
      apply IHHred; [|assumption].
      eapply list_inc_trans; [|exact HL].
      unfold gterm_fv; simpl. prove_list_inc.
    + rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_beta_app; eauto using dlc_lc.
      * apply IHHred; [|assumption].
        eapply list_inc_trans; [|exact HL].
        unfold gterm_fv; simpl. prove_list_inc.
      * apply IHHred.
    + intros; apply IHHred; assumption.

  - assert (HL1 : forall x, list_inc (gterm_fv (t1 d^ x, e1)) (x :: L)).
    {
      intros x.
      unfold gterm_fv in *; simpl in *.
      rewrite !list_inc_app_left in *.
      split; [|eapply list_inc_trans; [apply HL|]; prove_list_inc].
      eapply list_inc_trans; [apply dsubstb_dfv1|].
      simpl; rewrite list_inc_app_left; split; [|prove_list_inc].
      eapply list_inc_trans; [apply HL|]; prove_list_inc.
    }
    assert (Hwf1 : forall x, x \notin L -> gterm_wf (t1 d^ x, e1)).
    {
      intros x Hx. unfold gterm_wf in *; simpl in *.
      split; [|apply Hwf].
      destruct Hwf as [Hwfl Hwfe].
      rewrite gterm_read_lam in Hwfl.
      apply dwf_lam_inv_strong in Hwfl.
      rewrite gterm_read_dsubstb; [|assumption].
      admit.
    }
    match goal with [ |- _ /\ ?G ] => enough (H1 : G) end.
    {
      split; [|apply H1].
      unfold gterm_wf in *; simpl in *.
      rewrite !gterm_read_lam in *; simpl in *.
      pick x \notin (L ++ L1 ++ fv (dterm_read1 (gterm_read t3 e1)) ++ fv (dterm_read1 (gterm_read t3 e2))) as Hx.
      rewrite !in_app_iff in *.
      destruct (H0 x) as [H2 H3].
      (* apply trans_refl_clos_beta_lam with (x := x); try tauto. *)
      + firstorder.
      + apply HL1.
      + apply Hwf1; firstorder.
      + specialize (H3 (t3 d^ x)).
        rewrite !gterm_read_dsubstb, !dsubstb_substb in H3 by tauto.
        destruct H3 as [H3a H3b].
        * admit.
        * admit.
        * split.
          -- split; [|tauto].
             apply dwf_lam_one with (x := x); try tauto.
        * apply trans_refl_clos_beta_lam with (x := x); try tauto.
          admit.
        * specialize (H x ltac:(tauto)).
          apply gterm_red_wf in H; [apply H|apply HL1|apply Hwf1].
        * apply Hwf.
    }
    pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
    intros t4 HL4 Hwf4; apply (H0 x); try tauto.
    + apply HL1.
    + apply Hwf1.
    + eapply list_inc_trans; [exact HL4|]. prove_list_inc.
      (*
    split.
    + rewrite !gterm_read_lam; simpl.
      match goal with [ |- trans_refl_clos beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply trans_refl_clos_beta_lam with (x := x); try tauto.
      specialize (H0 x (ltac:(tauto))).
      rewrite <- !gterm_read_dsubstb, <- !dsubstb_substb. in H0; simpl in H0.
      admit.
    + pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
      intros t4 HL4 Hwf4; apply (H0 x); try tauto.
      * admit.
      * admit.
      * eapply list_inc_trans; [exact HL4|]. prove_list_inc. *)

  - destruct (gwf_app_inv Hwf) as [Hwfl Hwf3].
    split.
    + rewrite gterm_read_app, gterm_read_lam. simpl.
      rewrite <- dsubstb_is_dsubstf by admit.
      rewrite gterm_read_dsubstb, dsubstb_substb by (apply Hwf3).
      econstructor; constructor.
      * destruct Hwfl as [Hwfl Hwfe]; simpl in *.
        apply dwf_lam_inv_strong in Hwfl.
        exists L; intros y Hy.
        replace (fvar y) with (dterm_read1 (dfvar y)) by reflexivity.
        rewrite <- dsubstb_substb. apply dlc_lc.
        admit.
      * apply dlc_lc. apply gterm_wf_read_lc; assumption.
    + intros t4 Hinc Hwf4.
      rewrite dsubstf_dfv; [constructor|].
      unfold list_inc in *; firstorder.

  - match goal with [ |- _ /\ ?G ] => enough (H : G) end.
    {
      split; apply H; [|assumption].
      eapply list_inc_trans; [|exact HL].
      unfold gterm_fv; simpl. prove_list_inc.
    } 
    intros t3 HL3 Hwf3.
    destruct Hwf as [Hwf Hwfe]; simpl in *.
    apply gterm_env_wf_inv in Hwfe; destruct Hwfe as (Hwfe1 & Hwf1 & Hx).
    rewrite in_app_iff in Hx.
    rewrite gterm_read_dsubstf by tauto.
    rewrite gterm_read_dsubstf.
    + rewrite !dsubstf_substf.
      eapply trans_refl_clos_compose.
      * eapply trans_refl_clos_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|unfold gterm_wf in *; simpl in *; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
      * apply trans_refl_clos_refl_clos.
        eapply trans_refl_clos_map_impl with (f := fun t => _ [x := t]).
        -- intros t4 t5 Hbeta; apply beta_subst2; [exact Hbeta|].
           apply dlc_lc. apply gterm_wf_read_lc. unfold gterm_wf; simpl.
           split; [apply Hwf3|].
           apply gterm_red_wf in Hred; [apply Hred| |unfold gterm_wf; simpl; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
        -- apply IHHred; [|split; assumption].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
    + intros Hx2. apply Hx.
      rewrite <- in_app_iff.
      eapply gterm_red_newvars with (t1 := (t1, e1)); [eassumption| |].
      * unfold gterm_fv; rewrite in_app_iff; tauto.
      * unfold gterm_fv in HL; simpl in HL.
        apply HL; rewrite in_app_iff; simpl; tauto.

  - split; [|intros; constructor].
    erewrite gterm_env_find_read; try eassumption.
    + constructor.
    + apply Hwf.
Qed.


Lemma gterm_red_wf :
  forall L t1 t2, gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 -> gterm_wf t2.
Proof.
  intros L t1 t2 Hred. induction Hred.

  - intros Hfv [Hwf1 Hwf2]; simpl in *. admit. (*
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    destruct IHHred as [IH1 IH2]; [|split; auto|].
    + unfold gterm_fv, list_inc in *; simpl in *.
      intros; apply Hfv.
      rewrite !in_app_iff in *; tauto.
    + split; simpl in *; [constructor|]; assumption.
*)
  - intros Hfv [Hwf1 Hwf2]; simpl in *. admit. (*
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    destruct IHHred as [IH1 IH2]; [|split; auto|].
    + unfold gterm_fv, list_inc in *; simpl in *.
      intros; apply Hfv.
      rewrite !in_app_iff in *; tauto.
    + split; simpl in *; [constructor|]; assumption.
*)
  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    unfold gterm_wf; simpl.
    rewrite gterm_read_lam in *.
    destruct (dwf_lam_inv_strong Hwf1) as (Hwf3 & Hwf4 & Hwf5).
    enough (forall x, x \notin L1 -> dwf (gterm_read t2 e2 d^ x) /\ gterm_env_wf e2).
    + pick x \notin L1.
      split; [|eapply H1; eauto].
      apply dwf_lam with (L := L1); [firstorder|firstorder|].
      * intros y Hy; simpl in Hy.
        rewrite gterm_read_dsubstb.
        Search gterm_read.
      ; [eauto| |].
      intros y Hy.
    admit.

  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    split.
    + simpl.
      apply (dwf_lam_inv_strong Hwf3).
    + simpl. constructor; try assumption.
      unfold gterm_fv, list_inc in *; simpl in *.
      specialize (Hfv x); rewrite !in_app_iff in *.
      tauto.
      (*
      * constructor.
      * constructor.
      * intros Hx; apply H, Hfv.
        unfold gterm_fv in *; simpl in *.
        rewrite !in_app_iff in *. tauto.
       *)
  
  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    split; simpl; [assumption|].
    destruct (gterm_env_wf_inv Hwf2) as (H0 & H1 & H2). (*  & _ & H2 & H3 & H4). *)
    destruct IHHred as [Hwf3 Hwf4]; [|split; auto|].
    + unfold gterm_fv, list_inc in *; simpl in *.
      intros; apply Hfv.
      repeat (rewrite !in_app_iff in * || simpl in * ); tauto.
    + simpl in *.
      constructor; try assumption.
      admit.

      (*
      * constructor.
      * constructor.
      * admit.
      *)
      (*
  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    split; simpl; [assumption|].
    destruct (gterm_env_wf_inv Hwf2) as (H0 & H1 & H2 & H3 & H4 & H5).
    destruct IHHred as [Hwf3 Hwf4]; [|split; auto|].
    + unfold gterm_fv in *; simpl in *.
      intros; apply Hfv.
      repeat (rewrite !in_app_iff in * || simpl in * ); tauto.
    + simpl in *.
      constructor; try assumption.
      * econstructor. [|eassumption].
  *)
  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    split; simpl; [|assumption].
    admit.
Admitted.      

(*
Lemma gterm_red_beta_id :
  forall L t1 t2,
    gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 ->
    (forall t3, list_inc (dfv t3) L -> gterm_wf (t3, snd t1) ->
           trans_refl_clos beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
Proof.
  intros L t1 t2 Hred. induction Hred; intros HL Hwf; simpl in *.

  - destruct (gwf_app_inv Hwf) as [Hwf1 Hwf3].
    intros; apply IHHred; try assumption.
    eapply list_inc_trans; [|exact HL].
    prove_list_inc.

  - destruct (gwf_app_inv Hwf) as [Hwf3 Hwf1].
    intros; apply IHHred; try assumption.
    eapply list_inc_trans; [|exact HL].
    prove_list_inc.

  - pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
    intros t4 HL4 Hwf4; apply (H0 x); try tauto.
    + admit.
    + admit.
    + eapply list_inc_trans; [exact HL4|]. prove_list_inc.

  - destruct (gwf_app_inv Hwf) as [Hwfl Hwf3].
    intros t4 Hinc Hwf4.
    rewrite dsubstf_dfv; [constructor|].
    unfold list_inc in *; firstorder.

  - intros t3 HL3 Hwf3.
    destruct Hwf as [Hwf Hwfe]; simpl in *.
    apply gterm_env_wf_inv in Hwfe; destruct Hwfe as (Hwfe1 & Hwf1 & Hx).
    rewrite in_app_iff in Hx.
    rewrite gterm_read_dsubstf by tauto.
    rewrite gterm_read_dsubstf.
    + rewrite !dsubstf_substf.
      eapply trans_refl_clos_compose.
      * eapply trans_refl_clos_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. admit.
        -- apply IHHred; admit.
      * apply trans_refl_clos_refl_clos.
        eapply trans_refl_clos_map_impl with (f := fun t => _ [x := t]).
        -- intros t4 t5 Hbeta; apply beta_subst2; [exact Hbeta|].
           apply dlc_lc. apply gterm_wf_read_lc. unfold gterm_wf; simpl.
           split; [apply Hwf3|].
           apply gterm_red_wf in Hred; [apply Hred| |]; admit.
        -- 

  - intros; constructor.
Qed.
*)

Lemma gterm_red_beta_rec :
  forall L t1 t2,
    gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 ->
    trans_refl_clos beta (dterm_read1 (gterm_read (fst t1) (snd t1))) (dterm_read1 (gterm_read (fst t2) (snd t2))) /\
    (forall t3, list_inc (dfv t3) L -> gterm_wf (t3, snd t1) ->
           trans_refl_clos beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
Proof.
  intros L t1 t2 Hred. induction Hred; intros HL Hwf; simpl in *.

  - destruct (gwf_app_inv Hwf) as [Hwf1 Hwf3].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    specialize (IHHred HL1 Hwf1).
    split.
    + rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_beta_app; eauto using dlc_lc.
      * apply IHHred.
      * apply IHHred; [|assumption].
        eapply list_inc_trans; [|exact HL].
        unfold gterm_fv; simpl. prove_list_inc.
    + intros; apply IHHred; assumption.

  - destruct (gwf_app_inv Hwf) as [Hwf3 Hwf1].
    assert (Hlc1 := gterm_wf_read_lc Hwf1).
    assert (Hlc3 := gterm_wf_read_lc Hwf3).
    assert (HL1 : list_inc (gterm_fv (t1, e1)) L). {
      unfold list_inc, gterm_fv in *; simpl in *.
      intros x; specialize (HL x); rewrite !in_app_iff in *; firstorder.
    }
    specialize (IHHred HL1 Hwf1).
    split.
    + rewrite !gterm_read_app; simpl.
      apply trans_refl_clos_beta_app; eauto using dlc_lc.
      * apply IHHred; [|assumption].
        eapply list_inc_trans; [|exact HL].
        unfold gterm_fv; simpl. prove_list_inc.
      * apply IHHred.
    + intros; apply IHHred; assumption.

  - assert (HL1 : forall x, list_inc (gterm_fv (t1 d^ x, e1)) (x :: L)).
    {
      intros x.
      unfold gterm_fv in *; simpl in *.
      rewrite !list_inc_app_left in *.
      split; [|eapply list_inc_trans; [apply HL|]; prove_list_inc].
      eapply list_inc_trans; [apply dsubstb_dfv1|].
      simpl; rewrite list_inc_app_left; split; [|prove_list_inc].
      eapply list_inc_trans; [apply HL|]; prove_list_inc.
    }
    assert (Hwf1 : forall x, gterm_wf (t1 d^ x, e1)).
    {
      intros x. unfold gterm_wf in *; simpl in *.
      split; [|apply Hwf].
      destruct Hwf as [Hwfl Hwfe].
      apply (dwf_lam_inv_strong Hwfl).
    }
    match goal with [ |- _ /\ ?G ] => enough (H1 : G) end.
    {
      split; [|apply H1].
      rewrite !gterm_read_lam; simpl.
      match goal with [ |- trans_refl_clos beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply trans_refl_clos_beta_lam with (x := x); try tauto.
      destruct (H0 x) as [_ H3].
      + firstorder.
      + apply HL1.
      + apply Hwf1.
      + specialize (H3 (t3 d^ x)).
        rewrite !gterm_read_dsubstb, !dsubstb_substb in H3.
        * admit.
        * specialize (H x ltac:(tauto)).
          apply gterm_red_wf in H; [apply H|apply HL1|apply Hwf1].
        * apply Hwf.
    }
    pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
    intros t4 HL4 Hwf4; apply (H0 x); try tauto.
    + apply HL1.
    + apply Hwf1.
    + eapply list_inc_trans; [exact HL4|]. prove_list_inc.
      (*
    split.
    + rewrite !gterm_read_lam; simpl.
      match goal with [ |- trans_refl_clos beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply trans_refl_clos_beta_lam with (x := x); try tauto.
      specialize (H0 x (ltac:(tauto))).
      rewrite <- !gterm_read_dsubstb, <- !dsubstb_substb. in H0; simpl in H0.
      admit.
    + pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
      intros t4 HL4 Hwf4; apply (H0 x); try tauto.
      * admit.
      * admit.
      * eapply list_inc_trans; [exact HL4|]. prove_list_inc. *)

  - destruct (gwf_app_inv Hwf) as [Hwfl Hwf3].
    split.
    + rewrite gterm_read_app, gterm_read_lam. simpl.
      rewrite <- dsubstb_is_dsubstf by admit.
      rewrite gterm_read_dsubstb, dsubstb_substb by (apply Hwf3).
      econstructor; constructor.
      * destruct Hwfl as [Hwfl Hwfe]; simpl in *.
        apply dwf_lam_inv_strong in Hwfl.
        exists L; intros y Hy.
        replace (fvar y) with (dterm_read1 (dfvar y)) by reflexivity.
        rewrite <- dsubstb_substb. apply dlc_lc.
        admit.
      * apply dlc_lc. apply gterm_wf_read_lc; assumption.
    + intros t4 Hinc Hwf4.
      rewrite dsubstf_dfv; [constructor|].
      unfold list_inc in *; firstorder.

  - match goal with [ |- _ /\ ?G ] => enough (H : G) end.
    {
      split; apply H; [|assumption].
      eapply list_inc_trans; [|exact HL].
      unfold gterm_fv; simpl. prove_list_inc.
    } 
    intros t3 HL3 Hwf3.
    destruct Hwf as [Hwf Hwfe]; simpl in *.
    apply gterm_env_wf_inv in Hwfe; destruct Hwfe as (Hwfe1 & Hwf1 & Hx).
    rewrite in_app_iff in Hx.
    rewrite gterm_read_dsubstf by tauto.
    rewrite gterm_read_dsubstf.
    + rewrite !dsubstf_substf.
      eapply trans_refl_clos_compose.
      * eapply trans_refl_clos_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|unfold gterm_wf in *; simpl in *; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
      * apply trans_refl_clos_refl_clos.
        eapply trans_refl_clos_map_impl with (f := fun t => _ [x := t]).
        -- intros t4 t5 Hbeta; apply beta_subst2; [exact Hbeta|].
           apply dlc_lc. apply gterm_wf_read_lc. unfold gterm_wf; simpl.
           split; [apply Hwf3|].
           apply gterm_red_wf in Hred; [apply Hred| |unfold gterm_wf; simpl; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
        -- apply IHHred; [|split; assumption].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
    + intros Hx2. apply Hx.
      rewrite <- in_app_iff.
      eapply gterm_red_newvars with (t1 := (t1, e1)); [eassumption| |].
      * unfold gterm_fv; rewrite in_app_iff; tauto.
      * unfold gterm_fv in HL; simpl in HL.
        apply HL; rewrite in_app_iff; simpl; tauto.

  - split; [|intros; constructor].
    erewrite gterm_env_find_read; try eassumption.
    + constructor.
    + apply Hwf.
Qed.




Inductive db_term :=
| db_var : nat -> db_term
| db_lam : db_term -> db_term
| db_app : db_term -> db_term -> db_term.

Inductive closed_at : db_term -> nat -> Prop :=
| closed_db_var : forall n m, n < m -> closed_at (db_var n) m
| closed_db_lam : forall t n, closed_at t (S n) -> closed_at (db_lam t) n
| closed_db_app : forall t1 t2 n, closed_at t1 n -> closed_at t2 n -> closed_at (db_app t1 t2) n.

Inductive value :=
| Clos : db_term -> list ref -> ref -> value
| Freevar : ref -> value
| StructApp : value -> value -> value
| Lazy : db_term -> list ref -> value.

Notation mem := (store value * store (option value))%type.

Definition fresh_value (m : mem) (a : ref) : Prop := fresh_store (fst m) a.
Definition add_mem_value (a : ref) (v : value) (m : mem) := (add_store a v (fst m), snd m).
Definition get_mem_value (a : ref) (m : mem) := (get_store a (fst m)).
Definition fresh_lam_body (m : mem) (a : ref) : Prop := fresh_store (snd m) a.
Definition add_mem_lam_body (a : ref) (v : option value) (m : mem) := (fst m, add_store a v (snd m)).
Definition get_mem_lam_body (a : ref) (m : mem) := (get_store a (snd m)).

Inductive inert : value -> Prop :=
| inert_freevar : forall x, inert (Freevar x)
| inert_structapp : forall v1 v2, inert (StructApp v1 v2).

Definition is_var t := match t with db_var _ => true | _ => false end.

Inductive eval : db_term -> list ref -> bool -> mem -> value -> mem -> Prop :=
| eval_app_inert :
    forall t1 t2 e deep m1 m2 m3 v1 v2,
      eval t1 e false m1 v1 m2 ->
      eval t2 e true m2 v2 m3 ->
      inert v1 ->
      eval (db_app t1 t2) e deep m1 (StructApp v1 v2) m3
| eval_app_clos_var :
    forall t1 x e deep m1 m2 m3 t0 e0 a v r,
      eval t1 e false m1 (Clos t0 e0 a) m2 ->
      nth_error e x = Some v ->
      eval t0 (v :: e) deep m2 r m3 ->
      eval (db_app t1 (db_var x)) e deep m1 r m3
| eval_app_clos_not_var :
    forall t1 t2 e deep m1 m2 m3 t0 e0 a v r,
      eval t1 e false m1 (Clos t0 e0 a) m2 ->
      fresh_value m2 v ->
      eval t0 (v :: e) deep (add_mem_value v (Lazy t2 e) m2) r m3 ->
      eval (db_app t1 t2) e deep m1 r m3
| eval_lam_shallow :
    forall t e m a,
      fresh_lam_body m a ->
      eval (db_lam t) e false m (Clos t e a) (add_mem_lam_body a None m)
| eval_lam_deep :
    forall t e m1 m2 a v r,
      fresh_lam_body m1 a ->
      fresh_value m1 v ->
      eval t (v :: e) true (add_mem_value v (Freevar a) (add_mem_lam_body a None m1)) r m2 ->
      eval (db_lam t) e true m1 (Clos t e a) (add_mem_lam_body a (Some r) m2)
| eval_var_lazy :
    forall x e deep v m1 m2 t0 e0 r,
      nth_error e x = Some v ->
      get_mem_value v m1 = Some (Lazy t0 e0) ->
      eval t0 e0 deep m1 r m2 ->
      eval (db_var x) e deep m1 r (add_mem_value v r m2)
| eval_var_inert :
    forall x e deep v m r,
      nth_error e x = Some v ->
      get_mem_value v m = Some r ->
      inert r ->
      eval (db_var x) e deep m r m
| eval_var_clos_shallow :
    forall x e v m t0 e0 a,
      nth_error e x = Some v ->
      get_mem_value v m = Some (Clos t0 e0 a) ->
      eval (db_var x) e false m (Clos t0 e0 a) m
| eval_var_clos_deep_compute :
    forall x e v m1 m2 t0 e0 a v0 r,
      nth_error e x = Some v ->
      get_mem_value v m1 = Some (Clos t0 e0 a) ->
      get_mem_lam_body a m1 = Some None ->
      fresh_value m1 v0 ->
      eval t0 (v0 :: e0) true (add_mem_value v0 (Freevar a) m1) r m2 ->
      eval (db_var x) e true m1 (Clos t0 e0 a) (add_mem_lam_body a (Some r) m2)
| eval_var_clos_deep_cache :
    forall x e v m t0 e0 a r,
      nth_error e x = Some v ->
      get_mem_value v m = Some (Clos t0 e0 a) ->
      get_mem_lam_body a m = Some (Some r) ->
      eval (db_var x) e true m (Clos t0 e0 a) m
.

(*
Definition church := forall (A : Type), (A -> A) -> A -> A.
Definition church_succ (n : church) := fun A f x => n A f (f x).
Fixpoint church_from_nat n : church :=
  match n with
  | O => fun A f x => x
  | S n => church_succ (church_from_nat n)
  end.
Definition church_mul (c1 c2 : church) : church :=
  fun A f x => c1 A (c2 A f) x.
Definition church_pow (c1 c2 : church) : church :=
  fun A => c2 (A -> A) (c1 A).

Definition church_100 := Eval compute in church_from_nat 100.
Definition church_300 := Eval compute in church_from_nat 300.
Definition church_10 := Eval compute in church_from_nat 10.
Definition church_4 := Eval compute in church_from_nat 4.
Time Eval cbv in church_pow church_10 church_4.
Time Eval lazy in church_mul church_100 church_300.
*)


*)