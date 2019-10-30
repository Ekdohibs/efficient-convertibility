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

Inductive gterm_red : list freevar -> gterm -> gterm -> Prop :=
| gterm_red_app1 : forall L t1 t2 t3 e1 e2,
    (* dlc t3 -> *) gterm_red L (t1, e1) (t2, e2) -> gterm_red L (dapp t1 t3, e1) (dapp t2 t3, e2)
| gterm_red_app2 : forall L t1 t2 t3 e1 e2,
    (* dlc t3 -> *) gterm_red L (t1, e1) (t2, e2) -> gterm_red L (dapp t3 t1, e1) (dapp t3 t2, e2)
| gterm_red_lam : forall L L1 t1 t2 t3 e1 e2,
    (* dlc t3 -> *) (forall x, x \notin L1 -> gterm_red (x :: L) (t1 d^ x, e1) (t2 d^ x, e2)) ->
    gterm_red L (dlam t3 t1, e1) (dlam t3 t2, e2)
| gterm_red_redex : forall L t1 t2 t3 e x,
    x \notin L -> (* body t1 -> body t2 -> dlc t3 -> *)
    gterm_red L (dapp (dlam t1 t2) t3, e) (t1 d^ x, (x, t3) :: e)
| gterm_red_env : forall L t t1 t2 e1 e2 x,
    (* dlc t -> *) gterm_red L (t1, e1) (t2, e2) ->
    gterm_red L (t, (x, t1) :: e1) (t, (x, t2) :: e2)
| gterm_red_var : forall L t e x,
    gterm_env_find x e = Some t -> gterm_red L (dfvar x, e) (t, e)
.

Lemma gterm_inc_red :
  forall t1 t2 L1, gterm_red L1 t1 t2 -> forall L2, list_inc L2 L1 -> gterm_red L2 t1 t2.
Proof.
  intros t1 t2 L1 Hred. induction Hred.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; apply gterm_red_lam with (L1 := L1). firstorder.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; constructor; auto.
Qed.

Definition disjoint (L1 L2 : list freevar) := forall x1 x2, In x1 L1 -> In x2 L2 -> x1 <> x2.

Definition gterm_red1 L t1 t2 := gterm_red (L ++ gterm_fv t1) t1 t2.

Inductive gterm_env_wf : list (freevar * dterm) -> Prop :=
| gterm_env_wf_nil : gterm_env_wf nil
| gterm_env_fv_cons :
    forall x t e,
      gterm_env_wf e ->
      dwf t -> x \notin (dfv t ++ gterm_env_fv e) ->
      gterm_env_wf ((x, t) :: e).

Lemma gterm_env_wf_inv :
  forall {x t e}, gterm_env_wf ((x, t) :: e) ->
             gterm_env_wf e /\ dwf t /\
             x \notin (dfv t ++ gterm_env_fv e).
Proof.
  intros x t e H. inversion H; tauto.
Qed.

Definition gterm_wf (t : gterm) := dwf (fst t) /\ gterm_env_wf (snd t).

Lemma gterm_read_dsubstb :
  forall e t k u, gterm_env_wf e -> gterm_read (dsubstb k u t) e = dsubstb k (gterm_read u e) (gterm_read t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - rewrite dsubstb_dsubstf, IHe.
    + reflexivity.
    + eapply gterm_env_wf_inv; eassumption.
    + apply dwf_dlc. eapply gterm_env_wf_inv; eassumption.
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
  apply dwf_app_inv in H1.
  unfold gterm_wf; simpl; tauto.
Qed.

Lemma gterm_wf_read_wf :
  forall {e t}, gterm_wf (t, e) -> dwf (gterm_read t e).
Proof.
  induction e as [|[x t] e].
  - intros; unfold gterm_wf in *; simpl in *. tauto.
  - intros t1 [H1 H2]; unfold gterm_wf in *; simpl in *.
    apply gterm_env_wf_inv in H2.
    apply IHe; split; [|tauto].
    apply dsubstf_dwf; tauto.
Qed.

Lemma gterm_wf_read_lc :
  forall {t e}, gterm_wf (t, e) -> dlc (gterm_read t e).
Proof.
  intros t e H. apply dwf_dlc, gterm_wf_read_wf; assumption.
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

(*
Lemma lc_app_inv : forall {t1 t2}, lc (app t1 t2) -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H; inversion H; auto.
Qed.
 *)

Lemma gterm_red_wf :
  forall L t1 t2, gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 -> gterm_wf t2.
Proof.
  intros L t1 t2 Hred. induction Hred.

  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    destruct IHHred as [IH1 IH2]; [|split; auto|].
    + unfold gterm_fv, list_inc in *; simpl in *.
      intros; apply Hfv.
      rewrite !in_app_iff in *; tauto.
    + split; simpl in *; [constructor|]; assumption.

  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    destruct IHHred as [IH1 IH2]; [|split; auto|].
    + unfold gterm_fv, list_inc in *; simpl in *.
      intros; apply Hfv.
      rewrite !in_app_iff in *; tauto.
    + split; simpl in *; [constructor|]; assumption.

  - admit.

  - intros Hfv [Hwf1 Hwf2]; simpl in *.
    destruct (dwf_app_inv Hwf1) as [Hwf3 Hwf4].
    split.
    + simpl. destruct (dwf_lam_inv Hwf3) as [L1 (H1 & H2 & H3)].
      pick y \notin (dfv t1 ++ L1); rewrite in_app_iff in *.
      rewrite dsubstb_is_dsubstf with (x := y); [|auto].
      apply dsubstf_dwf; [constructor | auto].
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

Lemma trans_refl_clos_beta_lc :
  forall t1 t2, trans_refl_clos beta t1 t2 -> lc t1 -> lc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using beta_lc.
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

Lemma gterm_red_newvars :
  forall L t1 t2, gterm_red L t1 t2 -> forall x, In x (gterm_fv t2) -> In x L -> In x (gterm_fv t1).
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
    specialize (IHHred y).
    repeat (rewrite in_app_iff in *; simpl in * ).
    firstorder congruence.
  - unfold gterm_fv in *; simpl in *.
    rewrite in_app_iff in *.
    destruct Hy2 as [Hy2 | Hy2]; [|tauto].
    right. eapply gterm_env_find_fv; eauto.
Qed.

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
      * apply IHHred; [|assumption]. admit.
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
      * apply IHHred; [|assumption]. admit.
      * apply IHHred.
    + intros; apply IHHred; assumption.

  - match goal with [ |- _ /\ ?G ] => enough (H1 : G) end.
    {
      split; [|apply H1].
      rewrite !gterm_read_lam; simpl.
      match goal with [ |- trans_refl_clos beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply trans_refl_clos_beta_lam with (x := x); try tauto.
      destruct (H0 x) as [_ H3]; [firstorder|admit|admit|].
      specialize (H3 (t3 d^ x)).
      rewrite !gterm_read_dsubstb in H3 by admit.
      rewrite !dsubstb_substb in H3.
      admit.
    }
    pick x \notin (L ++ L1) as Hx. rewrite in_app_iff in Hx.
    intros t4 HL4 Hwf4; apply (H0 x); try tauto.
    + admit.
    + admit.
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
      * admit.
      * admit.
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
        -- apply dlc_lc. admit.
        -- apply IHHred; admit.
      * apply trans_refl_clos_refl_clos.
        eapply trans_refl_clos_map_impl with (f := fun t => _ [x := t]).
        -- intros t4 t5 Hbeta; apply beta_subst2; [exact Hbeta|].
           apply dlc_lc. apply gterm_wf_read_lc. unfold gterm_wf; simpl.
           split; [apply Hwf3|].
           apply gterm_red_wf in Hred; [apply Hred| |]; admit.
        -- apply IHHred; [|split; assumption].
           admit.
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