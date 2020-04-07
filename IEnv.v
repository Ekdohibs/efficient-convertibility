Require Import Misc.
Require Import Arith.
Require Import List.
Require Import Psatz.
Require Import Freevar.
Require Import Term.
Require Import Setoid Morphisms.
Require Import FEnv.
Require Import Red.

Definition acyclic_env env (f : freevar -> nat) :=
  forall x y t, env_find env x = Some t -> y \in fv t -> f y < f x.

Lemma acyclic_env_nil :
  forall f, acyclic_env nil f.
Proof.
  intros f x y t H. simpl in H. congruence.
Qed.

Lemma acyclic_env_same :
  forall env1 env2 f, env1 === env2 -> acyclic_env env1 f -> acyclic_env env2 f.
Proof.
  intros env1 env2 f Henv H x y t. specialize (H x y t).
  rewrite Henv in H. assumption.
Qed.

Lemma acyclic_env_same_iff :
  forall env1 env2 f, env1 === env2 -> acyclic_env env1 f <-> acyclic_env env2 f.
Proof.
  intros env1 env2 f Henv. split.
  - apply acyclic_env_same. assumption.
  - apply acyclic_env_same. symmetry; assumption.
Qed.

Global Instance acyclic_env_Proper : Proper (env_same ==> eq ==> iff) acyclic_env.
Proof.
  intros env1 env2 H12 f1 f2 ->. apply acyclic_env_same_iff. assumption.
Qed.

Lemma acyclic_env_cons2_weak :
  forall env x t f, env_find env x = None -> acyclic_env ((x, t) :: env) f -> acyclic_env env f.
Proof.
  intros env x t f Hx H y z t2 Hy. specialize (H y z t2).
  simpl in H. destruct freevar_eq_dec; [congruence|].
  tauto.
Qed.

Lemma acyclic_env_cons2 :
  forall env x t f, env_find env x = None ->
               acyclic_env ((x, t) :: env) f <-> (forall y, y \in fv t -> f y < f x) /\ acyclic_env env f.
Proof.
  intros env x t f Hx. split.
  - intros H. split; [|eapply acyclic_env_cons2_weak; eassumption].
    intros y Hy. eapply H; [|eassumption]. simpl. destruct freevar_eq_dec; congruence.
  - intros [H1 H2] y z t2 Hy. simpl in Hy. destruct freevar_eq_dec.
    + injection Hy. intros; subst. apply H1. assumption.
    + apply H2. assumption.
Qed.


Fixpoint read_env env t :=
  match env with
  | nil => t
  | (x, t2) :: env =>
    (read_env env t) [ x := read_env env t2 ]
  end.

Lemma read_env_fv :
  forall env t f y, unique_env env -> acyclic_env env f -> y \in fv (read_env env t) -> exists x, x \in fv t /\ f y <= f x.
Proof.
  induction env as [|[z u] env]; intros t f y Hunique Hcycle Hy.
  - simpl in *. exists y. split; [assumption|lia].
  - simpl in *.
    rewrite unique_env_inv_iff in Hunique.
    rewrite acyclic_env_cons2 in Hcycle by tauto.
    destruct Hunique as [Hunique Hz]. destruct Hcycle as [Hu Hcycle].
    rewrite fv_substf_iff in Hy. destruct Hy as [[Hy1 Hy2] | [Hy1 Hy2]].
    + eapply IHenv in Hy1; eassumption.
    + eapply IHenv in Hy1; try eassumption.
      eapply IHenv in Hy2; try eassumption.
      destruct Hy1 as (w & Hw1 & Hw2). exists w; split; [assumption|].
      destruct Hy2 as (p & Hp1 & Hp2). specialize (Hu p Hp1). lia.
Qed.

Lemma read_env_cons_mid :
  forall env1 env2 x t1 t2 f, unique_env (env1 ++ (x, t1) :: env2) -> acyclic_env (env1 ++ (x, t1) :: env2) f -> read_env (env1 ++ (x, t1) :: env2) t2 = read_env (env1 ++ env2) t2 [ x := read_env (env1 ++ env2) t1 ].
Proof.
  induction env1 as [|[y t3] env1].
  - intros; simpl; reflexivity.
  - intros env2 x t1 t2 f Hunique Hcycle. simpl.
    simpl in Hcycle.
    simpl in Hunique. destruct (unique_env_inv _ _ _ _ Hunique) as [Hunique2 Hy].
    rewrite !IHenv1 with (f := f) by (assumption || eapply acyclic_env_cons2_weak; eassumption).
    assert (Hxy : x <> y) by (rewrite env_find_app in Hy; destruct (env_find env1 y); [congruence|]; simpl in Hy; destruct freevar_eq_dec; congruence).
    apply substf_exchange; [assumption|].
    destruct (in_dec freevar_eq_dec x (fv (read_env (env1 ++ env2) t3))) as [Hx1 | ?]; [|tauto]. right. intros Hy1.
    rewrite unique_env_cons_mid_iff in Hunique2.
    rewrite acyclic_env_cons2 in Hcycle by assumption.
    rewrite env_cons_mid_eq2, acyclic_env_cons2 in Hcycle by tauto.
    eapply read_env_fv in Hx1; [|apply Hunique2|apply Hcycle].
    eapply read_env_fv in Hy1; [|apply Hunique2|apply Hcycle].
    destruct Hx1 as (x1 & Hx1a & Hx1b).
    destruct Hy1 as (y1 & Hy1a & Hy1b).
    apply Hcycle in Hx1a. apply Hcycle in Hy1a. lia.
Qed.

Lemma read_env_same :
  forall env1 env2 t f, env1 === env2 -> unique_env env1 -> unique_env env2 -> acyclic_env env1 f -> read_env env1 t = read_env env2 t.
Proof.
  induction env1 as [|[x t1] env1]; intros env2 t f Henv Hunique1 Hunique2 Hcycle.
  - destruct env2 as [|[y t2] env2].
    + reflexivity.
    + specialize (Henv y); simpl in Henv.
      destruct freevar_eq_dec; congruence.
  - simpl.
    assert (Hfind := Henv x).
    simpl in Hfind. destruct freevar_eq_dec; [|congruence]. symmetry in Hfind.
    apply env_find_exists in Hfind. destruct Hfind as (env2a & env2b & Henv2).
    erewrite Henv2, read_env_cons_mid.
    rewrite Henv2 in Hunique2.
    destruct (unique_env_cons_mid _ _ _ _ _ Hunique2) as [Hunique2a Hx].
    + erewrite !IHenv1 with (env2 := env2a ++ env2b).
      * reflexivity.
      * intros y. specialize (Henv y).
        rewrite Henv2, env_find_app in Henv; simpl in Henv.
        destruct freevar_eq_dec.
        -- subst. apply unique_env_inv in Hunique1. intuition congruence.
        -- rewrite env_find_app. assumption.
      * apply unique_env_inv in Hunique1; tauto.
      * assumption.
      * apply acyclic_env_cons2_weak in Hcycle; [eassumption | apply unique_env_inv in Hunique1; tauto].
      * intros y. specialize (Henv y).
        rewrite Henv2, env_find_app in Henv; simpl in Henv.
        destruct freevar_eq_dec.
        -- subst. apply unique_env_inv in Hunique1. intuition congruence.
        -- rewrite env_find_app. assumption.
      * apply unique_env_inv in Hunique1; tauto.
      * assumption.
      * apply acyclic_env_cons2_weak in Hcycle; [eassumption | apply unique_env_inv in Hunique1; tauto].
    + rewrite <- Henv2; assumption.
    + rewrite <- Henv2.
      eapply acyclic_env_same; eassumption.
Qed.

Lemma read_env_app :
  forall env t1 t2, read_env env (app t1 t2) = app (read_env env t1) (read_env env t2).
Proof.
  induction env as [|[x u] env].
  - reflexivity.
  - intros t1 t2. simpl.
    destruct u; simpl; rewrite !IHenv; reflexivity.
Qed.

Lemma read_env_lam :
  forall env t, read_env env (lam t) = lam (read_env env t).
Proof.
  induction env as [|[x u] env].
  - reflexivity.
  - intros t. simpl.
    destruct u; simpl; rewrite !IHenv; reflexivity.
Qed.

Lemma read_env_fvar_free :
  forall env x, env_find env x = None -> read_env env (fvar x) = fvar x.
Proof.
  induction env as [|[y u] env].
  - reflexivity.
  - intros x Hx. simpl in *. destruct freevar_eq_dec; [congruence|].
    rewrite IHenv by assumption. simpl. destruct freevar_eq_dec; congruence.
Qed.

Lemma read_env_fvar_bound :
  forall env x t f, unique_env env -> acyclic_env env f -> env_find env x = Some t -> read_env env (fvar x) = read_env env t.
Proof.
  intros env x t f Hunique Hcycle Hfind.
  induction env as [|[y u] env].
  - simpl in Hfind. congruence.
  - simpl in *. rewrite acyclic_env_cons2 in Hcycle by (inversion Hunique; tauto).
    rewrite unique_env_inv_iff in Hunique.
    destruct freevar_eq_dec.
    + injection Hfind. intro. subst.
      rewrite read_env_fvar_free by tauto. simpl.
      destruct freevar_eq_dec; [|congruence].
      rewrite substf_fv; [reflexivity|].
      intros Hy. eapply read_env_fv in Hy; [|apply Hunique|apply Hcycle].
      destruct Hy as (z & Hz1 & Hz2); apply Hcycle in Hz1. lia.
    + specialize (IHenv ltac:(tauto) ltac:(tauto) Hfind).
      rewrite IHenv. reflexivity.
Qed.



Fixpoint env_fv env :=
  match env with
  | nil => nil
  | (x, t) :: env => x :: fv t ++ env_fv env
  end.

Lemma env_fv_inc :
  forall env, Forall (fun '(x, t) => x :: fv t \subseteq env_fv env) env.
Proof.
  induction env as [|[x t] env].
  - constructor.
  - constructor.
    + simpl. prove_list_inc.
    + simpl. eapply Forall_impl; [|eassumption].
      intros [x1 t1]. intros H; rewrite H; prove_list_inc.
Qed.

Lemma env_find_fv_None :
  forall env x, x \notin env_fv env -> env_find env x = None.
Proof.
  intros env x Hx.
  induction env as [|[y t] env].
  - reflexivity.
  - simpl in *. destruct freevar_eq_dec.
    + subst. tauto.
    + rewrite in_app_iff in *. tauto.
Qed.


Inductive in_fv_rec env : freevar -> term -> Prop :=
| in_fv_rec_in : forall x t, x \in fv t -> in_fv_rec env x t
| in_fv_rec_env : forall x y t1 t2, y \in fv t1 -> env_find env y = Some t2 -> in_fv_rec env x (read_envitem t2) -> in_fv_rec env x t1.

Lemma in_fv_rec_same :
  forall env1 env2 x t, env1 === env2 -> in_fv_rec env1 x t -> in_fv_rec env2 x t.
Proof.
  intros env1 env2 x t Henv12 H. induction H.
  - apply in_fv_rec_in. assumption.
  - rewrite Henv12 in *; eapply in_fv_rec_env; eassumption.
Qed.

Lemma in_fv_rec_same_iff :
  forall env1 env2 x t, env1 === env2 -> in_fv_rec env1 x t <-> in_fv_rec env2 x t.
Proof.
  intros; split.
  - apply in_fv_rec_same; assumption.
  - apply in_fv_rec_same; intuition congruence.
Qed.

Global Instance in_fv_rec_Proper : Proper (env_same ==> eq ==> eq ==> iff) in_fv_rec.
Proof.
  intros env1 env2 H12 x1 x2 -> t1 t2 ->.
  apply in_fv_rec_same_iff. assumption.
Qed.

Lemma in_fv_rec_cons :
  forall env x y ei t, env_find env x = None -> in_fv_rec ((x, ei) :: env) y t <-> (in_fv_rec env y t \/ (in_fv_rec env x t /\ in_fv_rec env y (read_envitem ei))).
Proof.
  intros env x y ei t Hx. split.
  - intros H. induction H.
    + left. apply in_fv_rec_in. assumption.
    + simpl in H0. destruct freevar_eq_dec.
      * subst. injection H0; intro; subst.
        right. split; [|tauto].
        apply in_fv_rec_in. assumption.
      * destruct IHin_fv_rec as [? | [? ?]]; [left; eapply in_fv_rec_env; eassumption|right].
        split; [|assumption].
        eapply in_fv_rec_env; eassumption.
  - intros [H | [H1 H2]].
    + induction H.
      * apply in_fv_rec_in. assumption.
      * eapply in_fv_rec_env; try eassumption.
        simpl. destruct freevar_eq_dec; congruence.
    + induction H1.
      * eapply in_fv_rec_env; [eassumption|simpl; destruct freevar_eq_dec; [reflexivity|congruence]|].
        induction H2.
        -- apply in_fv_rec_in. assumption.
        -- eapply in_fv_rec_env; try eassumption. simpl.
           destruct freevar_eq_dec; [congruence|assumption].
      * eapply in_fv_rec_env; [eassumption| |apply IHin_fv_rec; assumption].
        simpl. destruct freevar_eq_dec; [congruence|assumption].
Qed.

Lemma in_fv_rec_dec_list_unique :
  forall env t, unique_env env -> { L | forall x, in_fv_rec env x t <-> x \in L }.
Proof.
  induction env as [|[y ei] env].
  - intros t Hunique. exists (fv t). intros x.
    split; intros H.
    + inversion H; subst; simpl in *; [assumption|congruence].
    + apply in_fv_rec_in. assumption.
  - intros t Hunique.
    destruct (IHenv t) as [L HL]; [inversion Hunique; auto|].
    destruct (in_dec freevar_eq_dec y L).
    + destruct (IHenv (read_envitem ei)) as [L2 HL2]; [inversion Hunique; auto|].
      exists (L ++ L2). intros x.
      rewrite in_fv_rec_cons, in_app_iff, !HL, HL2; [tauto|].
      inversion Hunique; tauto.
    + exists L. intros x.
      rewrite in_fv_rec_cons, !HL; [tauto|].
      inversion Hunique; tauto.
Qed.

Lemma in_fv_rec_dec_list :
  forall env t, { L | forall x, in_fv_rec env x t <-> x \in L }.
Proof.
  intros env t.
  destruct (in_fv_rec_dec_list_unique (uniquify_env env) t (uniquify_env_unique _ env)) as [L HL].
  exists L. intros x; specialize (HL x).
  rewrite uniquify_env_same in HL. assumption.
Qed.

Lemma in_fv_rec_dec :
  forall env t x, { in_fv_rec env x t } + { ~ in_fv_rec env x t }.
Proof.
  intros env t x.
  destruct (in_fv_rec_dec_list env t) as [L HL].
  destruct (in_dec freevar_eq_dec x L).
  - left. rewrite HL; assumption.
  - right. rewrite HL; assumption.
Qed.

Lemma in_fv_rec_list :
  forall env t, exists L, forall x, in_fv_rec env x t <-> x \in L.
Proof.
  intros env t.
  destruct (in_fv_rec_dec_list env t) as [L HL].
  exists L. assumption.
Qed.

Definition in_fv_recL env t := proj1_sig (in_fv_rec_dec_list env t).
Lemma in_fv_recL_iff :
  forall env t x, x \in in_fv_recL env t <-> in_fv_rec env x t.
Proof.
  intros env t x. unfold in_fv_recL. destruct in_fv_rec_dec_list. simpl.
  firstorder.
Qed.

Global Instance in_fv_recL_Proper : Proper (env_same ==> eq ==> list_same) in_fv_recL.
Proof.
  intros e1 e2 H12 t1 t2 -> z.
  rewrite !in_fv_recL_iff, H12. reflexivity.
Qed.

Lemma in_fv_recL_cons :
  forall env x y ei t, env_find env x = None -> y \in in_fv_recL ((x, ei) :: env) t <-> (y \in in_fv_recL env t \/ (x \in in_fv_recL env t /\ y \in in_fv_recL env (read_envitem ei))).
Proof.
  intros. rewrite !in_fv_recL_iff.
  apply in_fv_rec_cons. assumption.
Qed.

Lemma in_fv_recL_cons_same :
  forall env x ei t, env_find env x = None -> x \in in_fv_recL ((x, ei) :: env) t <-> x \in in_fv_recL env t.
Proof.
  intros. rewrite !in_fv_recL_iff.
  rewrite in_fv_rec_cons by assumption.
  tauto.
Qed.

Lemma in_fv_recL_cons_In :
  forall env x ei t, env_find env x = None -> x \in in_fv_recL env t -> in_fv_recL ((x, ei) :: env) t == in_fv_recL env t ++ in_fv_recL env (read_envitem ei).
Proof.
  intros env x ei t Hx Hfv y.
  rewrite !in_fv_recL_cons, in_app_iff by assumption.
  tauto.
Qed.

Lemma in_fv_recL_cons_notIn :
  forall env x ei t, env_find env x = None -> x \notin in_fv_recL env t -> in_fv_recL ((x, ei) :: env) t == in_fv_recL env t.
Proof.
  intros env x ei t Hx Hfv y.
  rewrite !in_fv_recL_cons by assumption.
  tauto.
Qed.


Lemma read_env_fv_sub :
  forall env1 env2 t x, sublist_ordered env2 env1 -> unique_env env1 -> x \in fv (read_env env2 t) -> x \in fv (read_env env1 t) \/ (env_find env1 x <> None).
Proof.
  intros env1 env2 t x H. revert t x. induction H.
  - intros; left; assumption.
  - destruct x as [x u]. intros t y Hunique Hin.
    simpl in *. destruct freevar_eq_dec; [subst; right; congruence|].
    rewrite fv_substf_iff in *. destruct Hin as [[Hin1 Hin2] | [Hin1 Hin2]].
    + apply IHsublist_ordered in Hin1; [|inversion Hunique; assumption]. tauto.
    + apply IHsublist_ordered in Hin1; [|inversion Hunique; assumption].
      apply IHsublist_ordered in Hin2; [|inversion Hunique; assumption].
      destruct Hin1 as [Hin1 | Hin1]; [tauto|].
      inversion Hunique; subst; congruence.
  - destruct x as [x u]. intros t y Hunique Hin.
    simpl. apply IHsublist_ordered in Hin; [|inversion Hunique; assumption].
    rewrite fv_substf_iff. destruct freevar_eq_dec; [|tauto].
    right; congruence.
Qed.

Lemma acyclic_sub_env_unique :
  forall env1 env2 f, sublist_ordered env2 env1 -> unique_env env1 -> acyclic_env env1 f -> acyclic_env env2 f.
Proof.
  intros env1 env2 f H. induction H.
  - intros; assumption.
  - intros Hunique Hcycle. destruct x as [x u].
    rewrite acyclic_env_cons2 in Hcycle; [|inversion Hunique; tauto].
    rewrite acyclic_env_cons2; [inversion Hunique; tauto|].
    destruct (env_find L1 x) eqn:Hfind; [|reflexivity].
    eapply sublist_ordered_env_find in Hfind; [|eassumption|inversion Hunique; tauto].
    inversion Hunique; congruence.
  - intros Hunique Hcycle. destruct x as [x u].
    rewrite acyclic_env_cons2 in Hcycle by (inversion Hunique; tauto).
    inversion Hunique; tauto.
Qed.


Definition rdei (env : list (freevar * envitem)) := map_assq (fun x ei => read_envitem ei) env.
Global Instance rdei_Proper : Proper (env_same ==> env_same) rdei.
Proof.
  apply map_assq_env_Proper. reflexivity.
Qed.

Definition env_ei_fv env := env_fv (rdei env).
Lemma env_ei_fv_None :
  forall env x, x \notin env_ei_fv env -> env_find env x = None.
Proof.
  intros env x H. unfold env_ei_fv, rdei in *.
  destruct (env_find env x) eqn:Hfind; [|reflexivity].
  exfalso.
  apply env_find_In in Hfind.
  assert (Hinc := env_fv_inc (map_assq (fun _ ei => read_envitem ei) env)).
  rewrite Forall_map_assq, Forall_In in Hinc.
  specialize (Hinc (x, e) Hfind).
  simpl in Hinc. rewrite <- Hinc in H. simpl in H. tauto.
Qed.


Definition elc (env : list (freevar * term)) := forall x u, env_find env x = Some u -> lc u.
Global Instance elc_Proper : Proper (env_same ==> iff) elc.
Proof.
  intros env1 env2 Henv.
  split; intros H x u Hfind; specialize (H x u); rewrite Henv in *; tauto.
Qed.

Lemma elc_cons_inv :
  forall x u env, env_find env x = None -> elc ((x, u) :: env) -> lc u /\ elc env.
Proof.
  intros x u env Hfind H. split.
  - apply (H x u). simpl. destruct freevar_eq_dec; congruence.
  - intros y v H1. apply (H y v).
    simpl. destruct freevar_eq_dec; congruence.
Qed.

Lemma read_env_lc :
  forall env t, unique_env env -> elc env -> lc t -> lc (read_env env t).
Proof.
  induction env as [|[x u] env].
  - intros; simpl; assumption.
  - intros t Hunique Helc Hlc. simpl.
    apply unique_env_inv in Hunique. destruct Hunique as [Hunique Hy].
    apply elc_cons_inv in Helc; [|assumption].
    apply substf_lc; apply IHenv; tauto.
Qed.

Lemma read_env_substb :
  forall env t k u, unique_env env -> elc env -> read_env env (t [ k <- u ]) = read_env env t [ k <- read_env env u ].
Proof.
  intros env t k u Hunique Hlc. induction env as [|[y v] env].
  - reflexivity.
  - simpl.
    apply unique_env_inv in Hunique. destruct Hunique as [Hunique Hy].
    apply elc_cons_inv in Hlc; [|assumption].
    rewrite IHenv by tauto.
    apply substb_substf.
    apply read_env_lc; tauto.
Qed.


Lemma unique_env_rdei : forall env, unique_env (rdei env) <-> unique_env env.
Proof.
  apply unique_env_map_assq.
Qed.

Lemma env_find_rdei : forall env x, env_find (rdei env) x = match env_find env x with Some u => Some (read_envitem u) | None => None end.
Proof.
  apply env_find_map_assq.
Qed.


Definition env_wf env f := elc (rdei env) /\ unique_env env /\ acyclic_env (rdei env) f.
Lemma env_wf_cons_inv :
  forall x ei env f, env_wf ((x, ei) :: env) f <-> env_wf env f /\ env_find env x = None /\ lc (read_envitem ei) /\ (forall y, y \in fv (read_envitem ei) -> f y < f x).
Proof.
  intros x ei env f. split.
  - intros (H1 & H2 & H3).
    simpl in *.
    rewrite acyclic_env_cons2 in H3 by (erewrite <- unique_env_map_assq in H2; inversion H2; eassumption).
    rewrite unique_env_inv_iff in H2; destruct H2 as [H2 Hx].
    apply elc_cons_inv in H1; [|unfold rdei; rewrite env_find_map_assq, Hx; reflexivity].
    unfold env_wf; tauto.
  - intros ((H1 & H2 & H3) & Hx & Hlc & Hx2). unfold env_wf.
    simpl. split; [|split].
    + intros y t Hy. simpl in Hy.
      destruct freevar_eq_dec; [injection Hy; intro; subst; assumption|].
      eapply H1; eassumption.
    + rewrite unique_env_inv_iff. tauto.
    + rewrite acyclic_env_cons2; [tauto|].
      rewrite env_find_rdei, Hx. reflexivity.
Qed.

Lemma env_wf_cons_mid :
  forall f env1 env2 x ei, env_wf (env1 ++ (x, ei) :: env2) f <-> env_wf ((x, ei) :: env1 ++ env2) f.
Proof.
  intros f env1 env2 x ei. split; intros (H1 & H2 & H3).
  - unfold env_wf. rewrite unique_env_cons_mid_iff in H2. rewrite unique_env_inv_iff.
    assert (H : env1 ++ (x, ei) :: env2 === (x, ei) :: env1 ++ env2).
    { apply env_cons_mid_eq. destruct H2 as [H2 H4]; rewrite env_find_app in H4; destruct env_find; congruence. }
    unfold rdei in *. rewrite H in H1, H3. tauto.
  - unfold env_wf. rewrite unique_env_inv_iff in H2. rewrite unique_env_cons_mid_iff.
    assert (H : env1 ++ (x, ei) :: env2 === (x, ei) :: env1 ++ env2).
    { apply env_cons_mid_eq. destruct H2 as [H2 H4]; rewrite env_find_app in H4; destruct env_find; congruence. }
    unfold rdei in *. rewrite H. tauto.
Qed.

Lemma env_wf_move_to_front f env x u :
  env_wf env f -> env_find env x = Some u -> exists env2, env === (x, u) :: env2 /\ env_wf ((x, u) :: env2) f.
Proof.
  intros Hwf Hfind. apply env_move_to_front in Hfind; [|apply Hwf].
  destruct Hfind as (env1 & env2 & H1 & H2 & H3). exists (env1 ++ env2).
  split; [assumption|]. subst. rewrite env_wf_cons_mid in Hwf. assumption.
Qed.

Lemma env_wf_update :
  forall f env x ei1 ei2,
    env_find env x = Some ei1 -> (forall y, y \in fv (read_envitem ei2) -> f y < f x) ->
    lc (read_envitem ei2) -> env_wf env f -> env_wf (update_env env x ei2) f.
Proof.
  intros f env x ei1 ei2 Hfind Hx Hlc Hewf.
  eapply env_wf_move_to_front in Hfind; [|eassumption]. destruct Hfind as (env2 & Heq & Hewf2).
  enough (H : env_wf ((x, ei2) :: env2) f).
  - assert (Heq2 : update_env env x ei2 === (x, ei2) :: env2).
    + rewrite Heq. simpl. destruct freevar_eq_dec; [|tauto]. reflexivity.
    + split; [|split].
      * unfold env_wf, rdei in *. rewrite Heq2 in *. tauto.
      * apply update_env_unique. apply Hewf.
      * unfold env_wf, rdei in *. rewrite Heq2 in *. tauto.
  - rewrite env_wf_cons_inv in *.
    repeat (split; [tauto|]). assumption.
Qed.



Lemma acyclic_fv_recL_read_env :
  forall env t f, acyclic_env (rdei env) f -> unique_env env -> fv (read_env (rdei env) t) \subseteq in_fv_recL env t.
Proof.
  intros env t f Hcycle Hunique x. revert x t. induction env as [|[y u] env]; intros x t.
  - simpl. rewrite in_fv_recL_iff.
    intros H.
    constructor. assumption.
  - simpl in Hcycle.
    rewrite acyclic_env_cons2 in Hcycle; [|rewrite <- unique_env_map_assq in Hunique; inversion Hunique; eassumption].
    apply unique_env_inv in Hunique.
    rewrite in_fv_recL_cons by tauto. simpl.
    rewrite fv_substf_iff.
    firstorder.
Qed.

Lemma acyclic_fv_recL_read_env2 :
  forall env t x f, acyclic_env (rdei env) f -> unique_env env -> env_find env x = None -> x \in in_fv_recL env t -> x \in fv (read_env (rdei env) t).
Proof.
  intros env. induction env as [|[y u] env]; intros t x f Hcycle Hunique Hxenv Hx.
  - simpl. rewrite in_fv_recL_iff in *.
    inversion Hx; subst; [assumption|]. simpl in *; congruence.
  - simpl in Hcycle.
    rewrite acyclic_env_cons2 in Hcycle; [|rewrite <- unique_env_map_assq in Hunique; inversion Hunique; eassumption].
    apply unique_env_inv in Hunique.
    rewrite in_fv_recL_cons in * by tauto. simpl in *.
    rewrite fv_substf_iff.
    destruct freevar_eq_dec; [congruence|].
    firstorder.
Qed.

Lemma in_fv_recL_app :
  forall env t1 t2, in_fv_recL env (app t1 t2) == in_fv_recL env t1 ++ in_fv_recL env t2.
Proof.
  intros env t1 t2 x. rewrite in_app_iff, !in_fv_recL_iff.
  split; intros H; inversion H; subst.
  - simpl in H0. rewrite in_app_iff in H0; destruct H0.
    + left. constructor. assumption.
    + right. constructor. assumption.
  - simpl in H0. rewrite in_app_iff in H0; destruct H0.
    + left. eapply in_fv_rec_env; eassumption.
    + right. eapply in_fv_rec_env; eassumption.
  - inversion H0; subst.
    + constructor. simpl. rewrite in_app_iff. left; assumption.
    + eapply in_fv_rec_env; [simpl; rewrite in_app_iff; left| |]; eassumption.
  - inversion H0; subst.
    + constructor. simpl. rewrite in_app_iff. right; assumption.
    + eapply in_fv_rec_env; [simpl; rewrite in_app_iff; right| |]; eassumption.
Qed.

Lemma in_fv_recL_lam :
  forall env t, in_fv_recL env (lam t) == in_fv_recL env t.
Proof.
  intros env t x. rewrite !in_fv_recL_iff.
  split; intros H; inversion H; subst.
  - simpl in H0. constructor. assumption.
  - simpl in H0. eapply in_fv_rec_env; eassumption.
  - constructor. simpl. assumption.
  - eapply in_fv_rec_env; simpl; eassumption.
Qed.

Lemma in_fv_recL_substb :
  forall env k t u, in_fv_recL env (t [ k <- u ]) \subseteq in_fv_recL env t ++ in_fv_recL env u.
Proof.
  intros env k t u x. rewrite in_app_iff, !in_fv_recL_iff.
  intros H; inversion H; subst.
  - rewrite substb_fv, in_app_iff in H0. destruct H0; [left | right]; constructor; assumption.
  - rewrite substb_fv, in_app_iff in H0. destruct H0; [left | right]; eapply in_fv_rec_env; eassumption.
Qed.

Lemma in_fv_recL_substf :
  forall x y t1 t2 env, x <> y -> env_find env y = None -> x \in in_fv_recL env (t1 [ y := t2 ]) <-> (x \in in_fv_recL env t1) \/ (y \in fv t1 /\ x \in in_fv_recL env t2).
Proof.
  intros. rewrite !in_fv_recL_iff. split.
  - intros H1. inversion H1; subst.
    + rewrite fv_substf_iff in H2. destruct H2.
      * left. constructor; tauto.
      * right. split; [|constructor]; tauto.
    + rewrite fv_substf_iff in H2. destruct H2.
      * left; econstructor; intuition eassumption.
      * right. split; [|econstructor]; intuition eassumption.
  - intros [H1 | [H1 H2]].
    + inversion H1; subst.
      * constructor. rewrite fv_substf_iff; tauto.
      * eapply in_fv_rec_env; try eassumption. rewrite fv_substf_iff.
        left. split; [assumption|]. congruence.
    + inversion H2; subst.
      * constructor. rewrite fv_substf_iff; tauto.
      * eapply in_fv_rec_env; try eassumption. rewrite fv_substf_iff. tauto.
Qed.


Definition closed_in_env {A : Type} (env : list (freevar * A)) t := forall x, x \in fv t -> env_find env x = None.
Lemma closed_in_env_map_assq :
  forall A B (f : freevar -> A -> B) env t, closed_in_env (map_assq f env) t <-> closed_in_env env t.
Proof.
  intros. split; intros H x Hx; specialize (H x Hx); rewrite env_find_map_assq in *; destruct env_find; congruence.
Qed.

Lemma closed_in_env_rdei : forall env t, closed_in_env (rdei env) t <-> closed_in_env env t.
Proof.
  apply closed_in_env_map_assq.
Qed.

Lemma closed_in_env_app : forall A (env : list (freevar * A)) t1 t2,
    closed_in_env env (app t1 t2) <-> closed_in_env env t1 /\ closed_in_env env t2.
Proof.
  intros A env t1 t2. split.
  - intros H; split; intros x Hx; specialize (H x ltac:(simpl; rewrite in_app_iff; tauto)); assumption.
  - intros [H1 H2] x Hx; simpl in Hx; rewrite in_app_iff in Hx.
    specialize (H1 x); specialize (H2 x); tauto.
Qed.

Lemma closed_in_env_lam : forall A (env : list (freevar * A)) t,
    closed_in_env env (lam t) <-> closed_in_env env t.
Proof.
  intros; reflexivity.
Qed.

Lemma closed_in_env_fvar : forall A (env : list (freevar * A)) x, closed_in_env env (fvar x) <-> env_find env x = None.
Proof.
  intros; split.
  - intros H. apply H. simpl. tauto.
  - intros H y [-> | []]. assumption.
Qed.

Lemma closed_in_env_bvar : forall A (env : list (freevar * A)) n, closed_in_env env (bvar n).
Proof.
  intros A env n x [].
Qed.

Lemma closed_in_env_substb : forall A (env : list (freevar * A)) t k u, closed_in_env env t -> closed_in_env env u -> closed_in_env env (t [ k <- u ]).
Proof.
  intros A env t. induction t.
  - intros k u _ Hu. simpl. destruct Nat.eq_dec; [assumption|apply closed_in_env_bvar].
  - intros k u H _. apply H.
  - intros k u H1 H2. simpl. rewrite closed_in_env_lam in *. apply IHt; assumption.
  - intros k u H1 H2. simpl. rewrite closed_in_env_app in *.
    split; [apply IHt1 | apply IHt2]; tauto.
Qed.

Lemma closed_in_env_cons : forall A (env : list (freevar * A)) t x ei,
    closed_in_env ((x, ei) :: env) t <-> closed_in_env env t /\ x \notin fv t.
Proof.
  intros A env t x ei. split.
  - intros H. split.
    + intros y Hy. specialize (H y Hy). simpl in *. destruct freevar_eq_dec; congruence.
    + intros Hx. specialize (H x Hx). simpl in *. destruct freevar_eq_dec; congruence.
  - intros [H1 H2] y Hy. simpl. destruct freevar_eq_dec.
    + congruence.
    + apply H1. assumption.
Qed.

Lemma closed_in_env_closeb : forall A (env : list (freevar * A)) t k x,
    closed_in_env env t -> closed_in_env env (closeb k x t).
Proof.
  intros A env t. induction t.
  - intros; simpl. assumption.
  - intros; simpl. destruct freevar_eq_dec; [apply closed_in_env_bvar|assumption].
  - intros; simpl. rewrite closed_in_env_lam in *. apply IHt; assumption.
  - intros; simpl. rewrite closed_in_env_app in *.
    split; [apply IHt1 | apply IHt2]; tauto.
Qed.

Lemma closed_in_env_update_env :
  forall A (env : list (freevar * A)) t x u, env_find env x <> None ->
                                                 closed_in_env (update_env env x u) t <-> closed_in_env env t.
Proof.
  intros A env t x u Hx. split; intros H y Hy; specialize (H y Hy).
  - rewrite env_find_update_env in H. destruct freevar_eq_dec; congruence.
  - rewrite env_find_update_env. destruct freevar_eq_dec; congruence.
Qed.

Lemma closed_in_env_read_env :
  forall env t, closed_in_env env t -> read_env env t = t.
Proof.
  intros env t. induction env as [|[x u] env].
  - reflexivity.
  - intros Ht. rewrite closed_in_env_cons in Ht. simpl.
    rewrite IHenv by tauto. apply substf_fv. tauto.
Qed.


Lemma read_env_lc2 :
  forall env t, lc (read_env env t) -> lc t.
Proof.
  induction env as [|[y u] env]; intros t.
  + intros; assumption.
  + intros; simpl in *.
    apply IHenv. eapply substf_lc2; eassumption.
Qed.


Lemma env_lc_find :
  forall env x t, elc (rdei env) -> env_find env x = Some t -> lc (read_envitem t).
Proof.
  intros env x t H1 H2. specialize (H1 x). apply H1.
  unfold rdei. rewrite env_find_map_assq, H2. reflexivity.
Qed.

Lemma env_fv_find :
  forall env x t, env_find env x = Some t -> fv (read_envitem t) \subseteq env_ei_fv env.
Proof.
  intros env x t H. induction env as [|[y u] env].
  - simpl in *; congruence.
  - simpl in *. unfold env_ei_fv in *; simpl in *. destruct freevar_eq_dec.
    + injection H; intro; subst. prove_list_inc.
    + rewrite IHenv by assumption. prove_list_inc.
Qed.


Lemma acyclic_env_read_free :
  forall f env x t, unique_env env -> acyclic_env env f -> x \in fv (read_env env t) -> env_find env x = None.
Proof.
  intros f. induction env as [|[y u] env]; intros x t Hunique Hcycle Hx.
  - reflexivity.
  - rewrite unique_env_inv_iff in Hunique.
    rewrite acyclic_env_cons2 in Hcycle by tauto.
    simpl in *. destruct freevar_eq_dec.
    + exfalso. subst. rewrite fv_substf_iff in Hx.
      destruct Hx as [? | [Hx1 Hx2]]; [tauto|].
      eapply read_env_fv in Hx2; [|apply Hunique|apply Hcycle].
      destruct Hx2 as (x & Hx2 & Hx3); apply Hcycle in Hx2. lia.
    + rewrite fv_substf_iff in Hx. destruct Hx as [Hx | Hx].
      * eapply IHenv; [tauto|tauto|]. apply Hx.
      * eapply IHenv; [tauto|tauto|]. apply Hx.
Qed.

Lemma acyclic_env_in_cycle :
  forall f env x t, env_find env x = Some t -> unique_env env -> acyclic_env (rdei env) f -> x \notin in_fv_recL env (read_envitem t).
Proof.
  intros f env x t Hfind Hunique Hcycle.
  apply env_move_to_front in Hfind; [|assumption].
  destruct Hfind as (env1 & env2 & H1 & H2 & H3).
  unfold rdei in *.
  rewrite H2 in Hcycle. simpl in Hcycle.
  rewrite acyclic_env_cons2 in Hcycle; [|erewrite <- unique_env_map_assq in H3; inversion H3; eassumption].
  rewrite H2. rewrite in_fv_recL_cons_same; [|inversion H3; assumption].
  intros H.
  eapply acyclic_fv_recL_read_env2 in H; [|apply Hcycle|inversion H3; assumption|inversion H3; assumption].
  eapply read_env_fv in H; [|rewrite unique_env_rdei; inversion H3; assumption|apply Hcycle].
  destruct H as (y & Hy1 & Hy2). apply Hcycle in Hy1. lia.
Qed.

Lemma in_fv_recL_f :
  forall f env x t, acyclic_env (rdei env) f -> x \in in_fv_recL env t -> exists y, y \in fv t /\ f x <= f y.
Proof.
  intros f env x t Hcycle H. rewrite in_fv_recL_iff in H. induction H.
  - exists x. split; [assumption|lia].
  - destruct IHin_fv_rec as (z & Hz1 & Hz2).
    exists y. split; [assumption|].
    specialize (Hcycle y z (read_envitem t2) ltac:(rewrite env_find_rdei, H0; reflexivity) Hz1).
    lia.
Qed.

Lemma in_fv_recL_inc :
  forall t env, in_fv_recL env t \subseteq fv t ++ env_ei_fv env.
Proof.
  intros t env x H. rewrite in_fv_recL_iff in H. induction H.
  - rewrite in_app_iff. tauto.
  - rewrite in_app_iff in *. right.
    destruct IHin_fv_rec; [|assumption].
    erewrite <- env_fv_find; eassumption.
Qed.

Lemma env_ei_fv_update :
  forall x ei env, env_ei_fv (update_env env x ei) \subseteq x :: fv (read_envitem ei) ++ env_ei_fv env.
Proof.
  intros. induction env as [|[y u] env].
  - simpl. reflexivity.
  - simpl. unfold env_ei_fv in *. destruct freevar_eq_dec.
    + subst. simpl. prove_list_inc.
    + simpl. rewrite IHenv. prove_list_inc.
Qed.

Lemma acyclic_env_change_f :
  forall f1 f2 env, (forall x y, x \in env_fv env -> y \in env_fv env -> f1 x < f1 y -> f2 x < f2 y) -> acyclic_env env f1 -> acyclic_env env f2.
Proof.
  intros f1 f2 env H Hcycle x y t Hx Hy.
  assert (Hx2 := Hx).
  eapply Forall_env_find in Hx2; [|apply env_fv_inc]. simpl in Hx2.
  apply H; [| |eapply Hcycle; eassumption]; rewrite <- Hx2; simpl; tauto.
Qed.


Lemma read_env_fv_inc :
  forall env t, fv (read_env env t) \subseteq fv t ++ env_fv env.
Proof.
  induction env as [|[y u] env]; intros t.
  - simpl. prove_list_inc.
  - simpl. rewrite fv_substf. rewrite !IHenv. prove_list_inc.
Qed.

Lemma read_env_substf :
  forall env t1 t2 x, x \notin env_fv env -> read_env env (t1 [ x := t2 ]) = read_env env t1 [ x := read_env env t2 ].
Proof.
  induction env as [|[y u] env]; intros t1 t2 x Hx.
  - reflexivity.
  - simpl in *. rewrite in_app_iff in Hx. rewrite <- substf_substf.
    + f_equal. apply IHenv. tauto.
    + intros ->. tauto.
    + rewrite read_env_fv_inc, in_app_iff. tauto.
Qed.
