Require Import Freevar.
Require Import List.
Require Import Setoid.
Require Import Morphisms.
Require Import Misc.

Fixpoint env_find {A : Type} (e : list (freevar * A)) (x : freevar) :=
  match e with
  | nil => None
  | (y, r) :: e => if freevar_eq_dec x y then Some r else env_find e x
  end.

Definition env_same {A : Type} (e1 e2 : list (freevar * A)) := forall x, env_find e1 x = env_find e2 x.

Global Instance env_same_Reflexive {A : Type} : Reflexive (@env_same A).
Proof.
  firstorder.
Qed.

Global Instance env_same_Transitive {A : Type} : Transitive (@env_same A).
Proof.
  firstorder congruence.
Qed.

Global Instance env_same_Symmetric {A : Type} : Symmetric (@env_same A).
Proof.
  firstorder congruence.
Qed.

Global Instance env_same_Equivalence {A : Type} : Equivalence (@env_same A).
Proof.
  split; auto with typeclass_instances.
Qed.

Notation "e1 '===' e2" := (env_same e1 e2) (at level 70).

Lemma env_find_app :
  forall A (env1 env2 : list (freevar * A)) x,
    env_find (env1 ++ env2) x = match env_find env1 x with Some t => Some t | None => env_find env2 x end.
Proof.
  intros. induction env1 as [|[y u] env1].
  - reflexivity.
  - simpl. destruct freevar_eq_dec.
    + reflexivity.
    + assumption.
Qed.

Global Instance env_same_app_Proper {A : Type} : Proper (env_same ==> env_same ==> env_same) (@app (freevar * A)).
Proof.
  intros e1 e2 H12 e3 e4 H34 x.
  rewrite !env_find_app.
  rewrite H12, H34.
  reflexivity.
Qed.

Global Instance env_same_cons_Proper {A : Type} : Proper (eq ==> env_same ==> env_same) (@cons (freevar * A)).
Proof.
  intros z1 z2 -> e1 e2 H12 x.
  apply (env_same_app_Proper (z2 :: nil) (z2 :: nil)); [reflexivity | assumption].
Qed.

Fixpoint update_env {A : Type} (env : list (freevar * A)) x v :=
  match env with
  | nil => (x, v) :: nil
  | (y, u) :: env => if freevar_eq_dec x y then (x, v) :: env else (y, u) :: update_env env x v
  end.

Lemma env_find_map_assq :
  forall (B C : Type) (f : freevar -> B -> C) (L : list (freevar * B)) x, env_find (map_assq f L) x = match env_find L x with Some u => Some (f x u) | None => None end.
Proof.
  intros B C f L x. induction L as [|[y a] L].
  - reflexivity.
  - simpl. destruct freevar_eq_dec.
    + subst. reflexivity.
    + assumption.
Qed.

Inductive unique_env {A : Type} : list (freevar * A) -> Prop :=
| unique_env_nil : unique_env nil
| unique_env_cons : forall x t env, env_find env x = None -> unique_env env -> unique_env ((x, t) :: env).

Lemma unique_env_map_assq :
  forall (A B : Type) (f : freevar -> A -> B) env, unique_env (map_assq f env) <-> unique_env env.
Proof.
  intros A B f env. induction env as [|[x u] env].
  - simpl. split; constructor.
  - simpl. split; intros H; constructor; inversion H; subst.
    + rewrite env_find_map_assq in H2; destruct env_find; congruence.
    + tauto.
    + rewrite env_find_map_assq, H2; reflexivity.
    + tauto.
Qed.

Lemma unique_env_inv :
  forall A (env : list (freevar * A)) x t, unique_env ((x, t) :: env) -> unique_env env /\ env_find env x = None.
Proof.
  intros A env x t H; inversion H; subst; tauto.
Qed.

Lemma unique_env_inv_iff :
  forall A (env : list (freevar * A)) x t, unique_env ((x, t) :: env) <-> unique_env env /\ env_find env x = None.
Proof.
  intros. split.
  - apply unique_env_inv.
  - intros [? ?]; constructor; assumption.
Qed.

Lemma unique_env_cons_mid_iff :
  forall A (env1 env2 : list (freevar * A)) x t, unique_env (env1 ++ (x, t) :: env2) <-> unique_env (env1 ++ env2) /\ env_find (env1 ++ env2) x = None.
Proof.
  intros A; induction env1 as [|[y u] env1]; intros env2 x t.
  - simpl. rewrite unique_env_inv_iff. reflexivity.
  - simpl. rewrite !unique_env_inv_iff.
    rewrite IHenv1, !env_find_app; simpl in *.
    repeat destruct env_find; repeat destruct freevar_eq_dec; intuition congruence.
Qed.

Lemma unique_env_cons_mid :
  forall A (env1 env2 : list (freevar * A)) x t, unique_env (env1 ++ (x, t) :: env2) -> unique_env (env1 ++ env2) /\ env_find (env1 ++ env2) x = None.
Proof.
  intros. rewrite <- unique_env_cons_mid_iff. eassumption.
Qed.

Lemma env_cons_mid_eq :
  forall (A : Type) (env1 env2 : list (freevar * A)) x u, env_find env1 x = None -> env1 ++ (x, u) :: env2 === (x, u) :: env1 ++ env2.
Proof.
  intros A env1 env2 x u Hx y. simpl. rewrite !env_find_app; simpl.
  destruct freevar_eq_dec.
  - subst. rewrite Hx. reflexivity.
  - reflexivity.
Qed.

Lemma env_cons_mid_eq2 :
  forall (A : Type) (env1 env2 : list (freevar * A)) x u, env_find (env1 ++ env2) x = None -> env1 ++ (x, u) :: env2 === (x, u) :: env1 ++ env2.
Proof.
  intros. apply env_cons_mid_eq.
  rewrite env_find_app in H. destruct env_find; tauto.
Qed.

Lemma env_find_exists :
  forall A (env : list (freevar * A)) x t, env_find env x = Some t -> exists env1 env2, env = env1 ++ (x, t) :: env2.
Proof.
  intros. induction env as [|[y u] env].
  - simpl in *. congruence.
  - simpl in *. destruct freevar_eq_dec.
    + exists nil. exists env. simpl. congruence.
    + destruct (IHenv H) as (env1 & env2 & IH).
      exists ((y, u) :: env1). exists env2.
      rewrite IH. reflexivity.
Qed.


Lemma env_find_update_env :
  forall A (e : list (freevar * A)) x y v, env_find (update_env e x v) y = if freevar_eq_dec x y then Some v else env_find e y.
Proof.
  intros. induction e as [|[z u] e].
  - simpl. repeat (destruct freevar_eq_dec); congruence.
  - simpl. repeat (destruct freevar_eq_dec; simpl); congruence.
Qed.

Lemma update_env_same :
  forall A (e : list (freevar * A)) x v, update_env e x v === (x, v) :: e.
Proof.
  intros A e x v y. simpl.
  rewrite env_find_update_env.
  repeat destruct freevar_eq_dec; congruence.
Qed.

Lemma update_env_unique :
  forall A (env : list (freevar * A)) x v, unique_env env -> unique_env (update_env env x v).
Proof.
  intros. induction env as [|[y u] env].
  - simpl. constructor; [reflexivity|constructor].
  - simpl. destruct freevar_eq_dec.
    + subst. inversion H; constructor; assumption.
    + inversion H; subst. constructor.
      * rewrite env_find_update_env.
        destruct freevar_eq_dec; congruence.
      * auto.
Qed.

Fixpoint uniquify_env {A : Type} (env : list (freevar * A)) :=
  match env with
  | nil => nil
  | (y, u) :: env => (y, u) :: filter (fun '(x, v) => if freevar_eq_dec x y then false else true) (uniquify_env env)
  end.


Lemma env_find_filter_unique :
  forall (A : Type) (env : list (freevar * A)) P x, unique_env env -> env_find (filter P env) x = match env_find env x with Some u => if P (x, u) then Some u else None | None => None end.
Proof.
  intros A env P x Hunique. induction env as [|[y u] env].
  - reflexivity.
  - simpl in *. destruct (P (y, u)) eqn:HP; simpl.
    + destruct freevar_eq_dec.
      * subst. rewrite HP; simpl. reflexivity.
      * apply IHenv. inversion Hunique; assumption.
    + destruct freevar_eq_dec.
      * subst. rewrite HP; simpl.
        inversion Hunique; subst.
        rewrite IHenv, H1; auto.
      * apply IHenv. inversion Hunique; assumption.
Qed.

Lemma unique_env_filter :
  forall (A : Type) (env : list (freevar * A)) P, unique_env env -> unique_env (filter P env).
Proof.
  intros A env P H. induction H.
  - constructor.
  - simpl. destruct (P (x, t)).
    + constructor.
      * rewrite env_find_filter_unique by assumption.
        rewrite H; reflexivity.
      * assumption.
    + assumption.
Qed.

Lemma uniquify_env_unique :
  forall (A : Type) (env : list (freevar * A)), unique_env (uniquify_env env).
Proof.
  intros. induction env as [|[y u] env].
  - simpl. constructor.
  - simpl. constructor.
    + rewrite env_find_filter_unique by assumption.
      destruct freevar_eq_dec; destruct env_find; congruence.
    + apply unique_env_filter. assumption.
Qed.

Lemma uniquify_env_same :
  forall (A : Type) (env : list (freevar * A)), uniquify_env env === env.
Proof.
  intros. induction env as [|[y u] env].
  - simpl. reflexivity.
  - simpl. intros x. simpl.
    destruct freevar_eq_dec.
    + reflexivity.
    + rewrite env_find_filter_unique by (apply uniquify_env_unique).
      rewrite IHenv. destruct env_find; [|reflexivity].
      destruct freevar_eq_dec; congruence.
Qed.

Lemma sublist_ordered_env_find :
  forall (A : Type) (env1 env2 : list (freevar * A)) x, sublist_ordered env2 env1 -> unique_env env1 -> forall t, env_find env2 x = Some t -> env_find env1 x = Some t.
Proof.
  intros A env1 env2 x H. induction H; intros Hunique t Hfind.
  + assumption.
  + destruct x0 as [y u]. simpl in *.
    destruct freevar_eq_dec; [assumption|].
    apply IHsublist_ordered; [inversion Hunique|]; assumption.
  + destruct x0 as [y u]. simpl in *.
    destruct freevar_eq_dec.
    * subst. apply IHsublist_ordered in Hfind; inversion Hunique; subst; congruence.
    * apply IHsublist_ordered; [inversion Hunique|]; assumption.
Qed.

Lemma sublist_ordered_unique_env :
  forall (A : Type) (env1 env2 : list (freevar * A)), sublist_ordered env2 env1 -> unique_env env1 -> unique_env env2.
Proof.
  intros A env1 env2 H. induction H.
  - intros; assumption.
  - destruct x as [y u]. intros Hunique. inversion Hunique; subst.
    constructor; [|tauto].
    destruct (env_find L1 y) eqn:Hfind; [|reflexivity].
    eapply sublist_ordered_env_find in Hfind; [|eassumption|eassumption]. congruence.
  - intros Hunique. inversion Hunique. tauto.
Qed.

Global Instance map_assq_env_Proper {A B : Type} : Proper ((eq ==> eq ==> eq) ==> env_same ==> env_same) (@map_assq freevar A B).
Proof.
  intros f1 f2 Hf e1 e2 He x.
  rewrite !env_find_map_assq, He. destruct (env_find e2 x); [|reflexivity].
  f_equal. apply Hf; reflexivity.
Qed.

Lemma env_find_In2 :
  forall A x u (env : list (freevar * A)), (x, u) \in env -> exists v, env_find env x = Some v.
Proof.
  intros A x u env Hin. induction env as [|[y v] env].
  - simpl in Hin; tauto.
  - simpl. destruct freevar_eq_dec.
    + subst. exists v. reflexivity.
    + apply IHenv. simpl in Hin. intuition congruence.
Qed.

Lemma uniquify_env_not_in :
  forall A x u (env : list (freevar * A)), env_find env x = None -> uniquify_env ((x, u) :: env) = (x, u) :: uniquify_env env.
Proof.
  intros A x u env Hx.
  simpl. f_equal. apply Forall_filter_eq. rewrite Forall_forall.
  intros [y v] H. destruct freevar_eq_dec; [|congruence]. subst.
  exfalso. apply env_find_In2 in H. destruct H as [w H]; rewrite uniquify_env_same in H; congruence.
Qed.

Lemma env_find_In :
  forall (A : Type) (env : list (freevar * A)) x u, env_find env x = Some u -> In (x, u) env.
Proof.
  induction env as [|[y v] env].
  - intros; simpl in *. congruence.
  - intros; simpl in *.
    destruct freevar_eq_dec.
    + left; congruence.
    + right; apply IHenv. assumption.
Qed.

Lemma update_env_app :
  forall (A : Type) (env1 env2 : list (freevar * A)) x u,
    env_find env1 x = None -> update_env (env1 ++ env2) x u = env1 ++ update_env env2 x u.
Proof.
  intros A env1 env2 x u Hx. induction env1 as [|[y v] env1].
  - reflexivity.
  - simpl in *. destruct freevar_eq_dec; [congruence|].
    f_equal; tauto.
Qed.

Lemma env_move_to_front A (env : list (freevar * A)) x u :
  unique_env env -> env_find env x = Some u ->
  exists env1 env2, env = env1 ++ (x, u) :: env2 /\ env === (x, u) :: env1 ++ env2 /\ unique_env ((x, u) :: env1 ++ env2).
Proof.
  intros Hunique Hfind. apply env_find_exists in Hfind. destruct Hfind as (env1 & env2 & H). exists env1. exists env2.
  split; [assumption|].
  split; subst.
  - intros y. rewrite unique_env_cons_mid_iff in Hunique. simpl.
    rewrite !env_find_app in *. simpl.
    destruct freevar_eq_dec.
    + subst. destruct env_find, Hunique; congruence.
    + reflexivity.
  - rewrite unique_env_cons_mid_iff in Hunique. constructor; tauto.
Qed.

Global Instance update_env_Proper {A : Type} : Proper (env_same ==> eq ==> eq ==> env_same) (@update_env A).
Proof.
  intros env1 env2 He x1 x2 -> u1 u2 ->.
  rewrite !update_env_same. rewrite He. reflexivity.
Qed.
