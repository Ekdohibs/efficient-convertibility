Require Import List.
Require Import Arith.
Require Import Psatz.
Require Import Misc.
Require Import Freevar.
Require Import Star.
Require Import Term.
Require Import Beta.
Require Import Setoid.
Require Import Morphisms.
Require Import FEnv.

Inductive nfval :=
| NFFreeVar : freevar -> nfval
| NFStructApp : nfval -> nfval_or_lam -> nfval

with nfval_or_lam :=
| NFVal : nfval -> nfval_or_lam
| NFLam : freevar -> nfval_or_lam -> nfval_or_lam.

Inductive envitem :=
| EVal : nfval -> envitem
| ELazy : term -> envitem
| ELam : term -> freevar -> envitem.

Inductive code :=
| CTerm : term -> code
| CVal : nfval -> code.

Inductive cont :=
| KNil : cont
| KUpdateLazy : freevar -> list term -> cont -> cont
| KUpdateLam : term -> freevar -> cont -> cont
| KApp : nfval -> list term -> cont -> cont.

Record state := mkState {
  st_code : envitem ;
  st_stack : list term ;
  st_env : list (freevar * envitem) ;
  st_cont : cont ;
  st_lamnf : list (freevar * nfval_or_lam) ;
  st_usedvars : list freevar ;
}.

Inductive red : state -> state -> Prop :=
| red_app : forall t u e pi K W L,
    red {| st_code := ELazy (app t u) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy t ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_lam : forall t e pi K W L y,
    y \notin L ->
    red {| st_code := ELazy (lam t) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := y :: L |}
| red_redex : forall t u e pi K W L x y,
    x \notin L ->
    red {| st_code := ELam t y ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy (t ^ x) ; st_stack := pi ; st_env := (x, ELazy u) :: e ; st_cont := K ; st_lamnf := W ; st_usedvars := x :: L |}
| red_var_open : forall x e pi K W L,
    env_find e x = None ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFFreeVar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_var_val : forall x e v pi K W L,
    env_find e x = Some (EVal v) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal v ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_var_lazy : forall x e t pi K W L,
    env_find e x = Some (ELazy t) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy t ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
| red_var_lam : forall x e t y pi K W L,
    env_find e x = Some (ELam t y) ->
    red {| st_code := ELazy (fvar x) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_app_val : forall v e u pi K W L,
    red {| st_code := EVal v ; st_stack := u :: pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy u ; st_stack := nil ; st_env := e ; st_cont := KApp v pi K ; st_lamnf := W ; st_usedvars := L |}
| red_lam_deepen : forall t x e K W L,
    env_find W x = None ->
    red {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELazy (t ^ x) ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t x K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_app_val : forall v1 v2 pi K e W L,
    red {| st_code := EVal v1 ; st_stack := nil ; st_env := e ; st_cont := KApp v2 pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFStructApp v2 (NFVal v1)) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_app_lam : forall t x body v pi K e W L,
    env_find W x = Some body ->
    red {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := KApp v pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal (NFStructApp v (NFLam x body)) ; st_stack := pi ; st_env := e ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_update_lam_val : forall t v x K e W L,
    red {| st_code := EVal v ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t x K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := (x, NFVal v) :: W ; st_usedvars := L |}
| red_cont_update_lam_lam : forall t1 t2 y body x K e W L,
    env_find W y = Some body ->
    red {| st_code := ELam t2 y ; st_stack := nil ; st_env := e ; st_cont := KUpdateLam t1 x K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t1 x ; st_stack := nil ; st_env := e ; st_cont := K ; st_lamnf := (x, NFLam y body) :: W ; st_usedvars := L |}
| red_cont_update_lazy_val : forall v x pi e K W L,
    red {| st_code := EVal v ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := EVal v ; st_stack := pi ; st_env := update_env e x (EVal v) ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
| red_cont_update_lazy_lam : forall t y x pi e K W L,
    red {| st_code := ELam t y ; st_stack := nil ; st_env := e ; st_cont := KUpdateLazy x pi K ; st_lamnf := W ; st_usedvars := L |}
        {| st_code := ELam t y ; st_stack := pi ; st_env := update_env e x (ELam t y) ; st_cont := K ; st_lamnf := W ; st_usedvars := L |}
.



Fixpoint read_nfval (v : nfval) :=
  match v with
  | NFFreeVar x => fvar x
  | NFStructApp v1 v2 => app (read_nfval v1) (read_nfval_or_lam v2)
  end

with read_nfval_or_lam (v : nfval_or_lam) :=
  match v with
  | NFVal v => read_nfval v
  | NFLam x v => lam (closeb 0 x (read_nfval_or_lam v))
  end.

Definition read_envitem (ei : envitem) :=
  match ei with
  | EVal v => read_nfval v
  | ELam t x => lam t
  | ELazy t => t
  end.

Fixpoint read_stack t pi :=
  match pi with
  | nil => t
  | u :: pi => read_stack (app t u) pi
  end.
(*
Fixpoint read_cont cont t env lamnf :=
  match cont with
  | KNil => (t, env, lamnf)
  | KApp v pi K => read_cont K (read_stack (app (read_nfval v) t) pi) env lamnf
  | KUpdateLam t2 x K => read_cont K (lam t2) env ((x, lam (closeb 0 x t)) :: lamnf)
  | KUpdateLazy x pi K => read_cont K (read_stack t pi) ((x, t) :: env) lamnf
  end.
*)
Definition acyclic_env env (f : freevar -> nat) :=
  forall x y t, env_find env x = Some t -> y \in fv t -> f y < f x.

Lemma acyclic_env_nil :
  forall f, acyclic_env nil f.
Proof.
  intros f x y t H. simpl in H. congruence.
Qed.

Fixpoint read_env env t :=
  match env with
  | nil => t
  | (x, t2) :: env =>
    (read_env env t) [ x := read_env env t2 ]
  end.

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


(*
Lemma acyclic_env_cons1 :
  forall env x t, unique_env ((x, t) :: env) -> acyclic_env ((x, t) :: env) <-> x \notin fv t /\ acyclic_env (map_assq (fun y t2 => t2 [ x := t ]) env).
Proof.
  intros env x t Hunique. split.
  - intros H.
    split.
    + intros Hx. remember x as x0 in Hx. specialize (H x0). revert Heqx0 Hx. induction H.
      intros Heq Hx; subst.
      apply (H0 x); try tauto.
      exists t. simpl. destruct freevar_eq_dec; intuition.
    + intros y.
      specialize (H y).
      refine (Acc_ind2 _ _ _ _ _ H). clear H y. intros y Hacc Hrec1 Hrec2.
      constructor. intros z [u [Hu1 Hu2]].
      rewrite env_find_map_assq in Hu1.
      destruct (env_find env y) eqn:Hy; [injection Hu1; intro; subst|congruence].
      destruct (in_dec freevar_eq_dec z (fv t0)).
      * apply Hrec1. exists t0. split; [|assumption].
        simpl. destruct freevar_eq_dec; [|assumption].
        inversion Hunique; subst. congruence.
      * apply (Hrec2 x).
        -- exists t. simpl. destruct freevar_eq_dec; [|congruence].
           split; [reflexivity|]. rewrite fv_substf, in_app_iff in Hu2. tauto.
        -- exists t0. split; [|destruct (in_dec freevar_eq_dec x (fv t0)); [assumption|rewrite substf_fv in Hu2; tauto]].
           simpl. destruct freevar_eq_dec; [|assumption].
           subst. inversion Hunique. congruence.
  - intros [H1 H2].
    enough (forall y, x <> y -> Acc (fun y0 x0 => exists t0, env_find ((x, t) :: env) x0 = Some t0 /\ y0 \in fv t0) y).
    + intros y. destruct (freevar_eq_dec x y); [subst|apply H; assumption].
      constructor. intros z [u [Hu1 Hu2]].
      simpl in Hu1. destruct freevar_eq_dec; [|congruence]. injection Hu1; intro; subst.
      apply H. congruence.
    + intros y Hy. specialize (H2 y).
      induction H2.
      constructor.
      intros y [u [Hu1 Hu2]].
      simpl in Hu1; destruct freevar_eq_dec; [congruence|].
      destruct (freevar_eq_dec x y).
      * subst. constructor.
        intros z [v [Hv1 Hv2]]. 
        simpl in Hv1. destruct freevar_eq_dec; [|congruence]. injection Hv1; intro; subst.
        apply H0; [|congruence].
        exists (u [ y := v ]). rewrite env_find_map_assq, Hu1. split; [reflexivity|].
        rewrite <- fv_substf4; assumption.
      * apply H0; [|assumption]. exists (u [ x := t ]). rewrite env_find_map_assq, Hu1.
        split; [reflexivity|]. rewrite <- fv_substf3, list_remove_correct; tauto.
Qed.
*)
Lemma list_length_ind (A : Type) (P : list A -> Prop) (H0 : P nil) (HS : forall x L, (forall L2, length L = length L2 -> P L2) -> P (x :: L)) : forall L, P L.
Proof.
  intros L. remember (length L) as n. revert L Heqn. induction n.
  - intros L. destruct L.
    + intros; apply H0.
    + simpl; intros; congruence.
  - intros L. destruct L.
    + simpl; intros; congruence.
    + simpl; intros H; injection H; intros; subst. apply HS. apply IHn.
Qed.

Lemma acyclic_env_cons2_weak :
  forall env x t f, env_find env x = None -> acyclic_env ((x, t) :: env) f -> acyclic_env env f.
Proof.
  intros env x t f Hx H y z t2 Hy. specialize (H y z t2).
  simpl in H. destruct freevar_eq_dec; [congruence|].
  tauto.
Qed.

(*
Lemma read_env_cons2 :
  forall env t u x, unique_env ((x, u) :: env) -> acyclic_env ((x, u) :: env) -> read_env ((x, u) :: env) t = read_env (map_assq (fun _ t2 => t2 [ x := u ]) env) (t [ x := u ]).
Proof.
  simpl.
  refine (list_length_ind _ _ _ _).
  - intros t u x Hunique Hcycle. simpl. reflexivity.
  - intros [y v] env Hrec t u x Hunique Hcycle. simpl.
    rewrite !(Hrec env ltac:(reflexivity) _ _ y) by (apply unique_env_inv in Hunique; apply acyclic_env_cons2_weak in Hcycle; tauto).
    rewrite !(Hrec (map_assq _ env) ltac:(rewrite map_assq_length; reflexivity) _ _ _).
    + rewrite !map_assq_compose.
      assert (x <> y /\ (x \notin fv v \/ y \notin fv u)).
      assert (Hxy : x <> y) by (destruct (unique_env_inv _ _ _ Hunique) as [_ Hx]; simpl in Hx; destruct freevar_eq_dec; congruence).
      * split; [assumption|].
        destruct (in_dec freevar_eq_dec x (fv v)) as [Hx | Hx]; [|tauto]. right. intro Hy.
        remember x as x0 in Hx. specialize (Hcycle x0). revert Hx Heqx0.
        refine (Acc_ind2 _ _ (fun x0 => x0 \in fv v -> x0 <> x) _ x0 Hcycle).
        intros x1 H1 H2 H3 Hfv Heq. subst. apply (H3 y x).
        -- exists v. simpl. repeat (destruct freevar_eq_dec; try congruence). split; auto.
        -- exists u. simpl. destruct freevar_eq_dec; [|congruence]. split; auto.
        -- assumption.
        -- reflexivity.
      * f_equal; [|apply substf_exchange; intuition congruence].
        apply map_assq_ext.
        intros _ t2. apply substf_exchange; intuition congruence.
    + destruct (unique_env_inv _ _ _ Hunique) as [Hunique2 Hx].
      eapply unique_env_map_assq in Hunique2; exact Hunique2.
    + rewrite acyclic_env_cons1 in Hcycle by assumption. apply Hcycle.
    + destruct (unique_env_inv _ _ _ Hunique) as [Hunique2 Hx].
      destruct (unique_env_inv _ _ _ Hunique2) as [Hunique3 Hy].
      constructor.
      * simpl in Hx; destruct freevar_eq_dec; [congruence|].
        rewrite env_find_map_assq, Hx; reflexivity.
      * rewrite unique_env_map_assq. assumption.
    + assert (Hcycle2 : acyclic_env ((y, v) :: (x, u) :: env)).
      * eapply acyclic_env_same; [|eassumption].
        intros z; simpl; repeat destruct freevar_eq_dec; subst; try reflexivity.
        destruct (unique_env_inv _ _ _ Hunique) as [_ Hy].
        simpl in Hy; destruct freevar_eq_dec; congruence.
      * rewrite acyclic_env_cons1 in Hcycle2; [apply Hcycle2|].
        destruct (unique_env_inv _ _ _ Hunique) as [Hunique2 Hx].
        destruct (unique_env_inv _ _ _ Hunique2) as [Hunique3 Hy].
        simpl in Hx; destruct freevar_eq_dec; [congruence|].
        constructor; [|constructor; assumption].
        simpl. destruct freevar_eq_dec; congruence.
Qed.
*)
(*
Lemma read_env_substf1 :
  forall env t u x, env_find env x = None -> unique_env env -> acyclic_env (map_assq (fun _ t2 => t2 [ x := u ]) env) ->
               read_env (map_assq (fun _ t2 => t2 [ x := u ]) env) (t [ x := u ]) = read_env env t [ x := read_env env u ].
Proof.
  induction env as [|[y v] env]; intros t u x Hx Hunique Hcycle.
  - simpl. reflexivity.
  - simpl in *.
    destruct freevar_eq_dec; [congruence|].
    destruct (unique_env_inv _ _ _ Hunique) as [Hunique2 Hy].
    assert (Hcycle2 := acyclic_env_cons2_weak _ _ _ ltac:(rewrite env_find_map_assq, Hy; reflexivity) Hcycle). 
    rewrite acyclic_env_cons1 in Hcycle by (constructor; [rewrite env_find_map_assq, Hy; reflexivity|apply unique_env_map_assq; assumption]).
    rewrite !IHenv by tauto.
    rewrite fv_substf_iff in Hx2.
    destruct (in_dec freevar_eq_dec y (fv (read_env (map_assq (fun _ t2 => t2 [ x := u ]) env) (t [ x := u ])))).
    + assert (Heq1 := IHenv t u x Hx1 ltac:(tauto)).
      assert (Heq2 := IHenv v u x Hx1 ltac:(tauto)).
      rewrite Heq1, Heq2 in *.
      rewrite fv_substf_iff in i; destruct i as [[Hy1 Hy2] | [Hx3 Hy]].
      * admit.
      * admit.
    + rewrite substf_fv with (x := y); [|assumption].
      assert (Heq := IHenv t u x Hx1 ltac:(tauto)).
      rewrite Heq in *.
      rewrite fv_substf_iff in n0.
      rewrite substf_fv with (x := y) (t := read_env env t) by intuition congruence.
      destruct (in_dec freevar_eq_dec x (fv (read_env env t))).
      * rewrite substf_fv with (x := y) by tauto. reflexivity.
      * rewrite !substf_fv with (x := x) by tauto. reflexivity.
Admitted.
*)

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


(*
Inductive read_env env : term -> term -> Prop :=
| read_env_app : forall t u t2 u2, read_env env t t2 -> read_env env u u2 -> read_env env (app t u) (app t2 u2)
| read_env_lam : forall t t2 L, (forall x, x \notin L -> read_env env (t ^ x) (t2 ^ x)) -> read_env env (lam t) (lam t2)
| read_env_fvar_free : forall x, env_find env x = None -> read_env env (fvar x) (fvar x)
| read_env_fvar_bound : forall x t t2, env_find env x = Some t -> read_env env t t2 -> read_env env (fvar x) t2.

Lemma read_env_unique :
  forall env t t2 t3, read_env env t t2 -> read_env env t t3 -> t2 = t3.
Proof.
  intros env t t2 t3 H2. revert t3. induction H2; intros t3 H3; inversion H3.
  - f_equal; auto.
  - f_equal. pick x \notin (L ++ L0 ++ fv t1 ++ fv t2) as Hx; rewrite !in_app_iff in *.
    specialize (H2 x ltac:(tauto)).
    specialize (H0 x ltac:(tauto) _ H2).
    erewrite <- close_open with (t := t2), H0, close_open; tauto.
  - reflexivity.
  - congruence.
  - congruence.
  - subst. apply IHread_env. congruence.
Qed.

(*
Definition read_state st t2 :=
  let '(t, env, lamnf) :=
      read_cont (st_cont st)
                (read_stack (read_envitem (st_code st)) (st_stack st))
                (map (fun '(x, ei) => (x, read_envitem ei)) (st_env st))
                (map (fun '(x, nf) => (x, lam (closeb 0 x (read_nfval_or_lam nf)))) (st_lamnf st))
  in
  read_env env t t2.
 *)

Inductive read_env_envitem env : envitem -> term -> Prop :=
| read_env_envitem_val : forall v, read_env_envitem env (EVal v) (read_nfval v)
| read_env_envitem_lam : forall t t2 x, read_env env (lam t) (lam t2) -> read_env_envitem env (ELam t x) (lam t2)
| read_env_envitem_lazy : forall t t2, read_env env t t2 -> read_env_envitem env (ELazy t) t2.

Inductive read_stack_env env : term -> list term -> term -> Prop :=
| read_stack_env_nil : forall t, read_stack_env env t nil t
| read_stack_env_cons : forall t1 t2 t3 t4 pi, read_env env t1 t2 -> read_stack_env env (app t3 t2) pi t4 -> read_stack_env env t3 (t1 :: pi) t4.

Definition read_env2 env L t1 t2 :=
  read_env (map_assq (fun x ei => read_envitem ei) (filter (fun '(x, ei) => if in_dec freevar_eq_dec x L then true else match ei with ELazy _ => false | _ => true end) env)) t1 t2.

*)

Definition read_env_envitem env ei :=
  match ei with
  | EVal v => read_nfval v
  | ELam t x => read_env env (lam t)
  | ELazy t => read_env env t
  end.

Fixpoint read_stack_env env t pi :=
  match pi with
  | nil => t
  | t2 :: pi => read_stack_env env (app t (read_env env t2)) pi
  end.


(*
Definition read_env2 env L t :=
  read_env (map_assq (fun x ei => read_envitem ei) (filter (fun '(x, ei) => if in_dec freevar_eq_dec x L then true else match ei with ELazy _ => false | _ => true end) (uniquify_env env))) t.

*)

Definition read_env2 env t :=
  read_env (map_assq (fun x ei => read_envitem ei) (filter (fun '(x, ei) => match ei with ELazy _ => false | _ => true end) (uniquify_env env))) t.

Inductive read_env3 env : term -> term -> Prop :=
| read_env3_app : forall t1 t2 t3 t4, read_env3 env t1 t2 -> read_env3 env t3 t4 -> read_env3 env (app t1 t3) (app t2 t4)
| read_env3_lam : forall L t1 t2, (forall x, x \notin L -> read_env3 env (t1 ^ x) (t2 ^ x)) -> read_env3 env (lam t1) (lam t2)
| read_env3_fvar_free : forall x, env_find env x = None -> read_env3 env (fvar x) (fvar x)
| read_env3_fvar_bound : forall x ei t, env_find env x = Some ei -> read_env3 env (read_envitem ei) t -> read_env3 env (fvar x) t
| read_env3_fvar_lazy : forall x t, env_find env x = Some (ELazy t) -> read_env3 env (fvar x) (fvar x).


(*
Lemma read_env2_cons_lazy :
  forall env L t1 t2 x t, read_env2 ((x, ELazy t) :: env) L t1 t2 <-> read_env2 env L (t1 [ x := t ]) t2.

Lemma read_env_lc :
  forall env t1 t2, read_env env t1 t2 -> lc t1 /\ lc t2.
Proof.
  intros env t1 t2 H. induction H.
  - split; constructor; tauto.
  - split; econstructor; apply H0.
  - split; constructor.
  - split; [constructor | tauto].
Qed.
*)

(*
Lemma read_env_subst :
  forall env t1 t2 x t3 t4, env_find env x = None -> read_env env t1 t2 -> read_env (map_assq (fun y t => t [ x := t3 ]) env) t3 t4 ->
                       read_env (map_assq (fun y t => t [ x := t3 ]) env) (t1 [ x := t3 ]) (t2 [ x := t4 ]).
Proof.
  intros env t1 t2 x t3 t4 Hx Hread1 Hread2. induction Hread1.
  - simpl. constructor; assumption.
  - simpl. apply read_env_lam with (L := x :: L).
    intros y Hy.
    rewrite !substf_substb_free by ((simpl in *; intuition congruence) || (apply read_env_lc in Hread2; tauto)).
    apply H0. simpl in *; tauto.
  - simpl. destruct freevar_eq_dec.
    + assumption.
    + constructor. rewrite env_find_map_assq, H. reflexivity.
  - simpl.
    destruct freevar_eq_dec.
    + congruence.
    + econstructor.
      * rewrite env_find_map_assq, H. reflexivity.
      * assumption.
Qed.
*)

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

(*
Lemma read_env_read_env2 :
  forall env t1 t2, read_env (map_assq (fun x ei => read_envitem ei) env) t1 t2 -> forall L, exists t3, read_env2 env L t1 t3.
Proof.
  intros env t1 t2 H.
  remember (map (fun x ei => read_envitem ei) env) as env2. revert Heqenv2.
  induction H; intro; subst.
  - intros L.
    destruct (IHread_env1 (eq_refl _) L) as [t3 Ht3].
    destruct (IHread_env2 (eq_refl _) L) as [u3 Hu3].
    exists (app t3 u3).
    constructor; assumption.
  - intros L1.
    pick x \notin (L ++ fv t ++ env_fv (map_assq (fun x ei => read_envitem ei) env)) as Hx; rewrite !in_app_iff in Hx.
    destruct (H0 x ltac:(tauto) (eq_refl _) L1) as [t3 Ht3].
    exists (lam (closeb 0 x t3)).
    apply read_env_lam with (L := L ++ fv t ++ env_fv (map_assq (fun x ei => read_envitem ei) env)).
    intros y Hy; rewrite !in_app_iff in Hy.
    rewrite open_close by (constructor || apply read_env_lc in Ht3; tauto).
    match goal with [ |- read_env ?env _ _ ] => remember env as env2 end.
    assert (Hsub := read_env_subst env2 (t ^ x) t3 x (fvar y) (fvar y)).
    rewrite map_assq_id_forall in Hsub.
    + rewrite <- substb_is_substf in Hsub by tauto.
      apply Hsub.
      * rewrite Heqenv2, env_find_map_assq.
        admit.
      * subst. assumption.
      * constructor.
        rewrite Heqenv2, env_find_map_assq.
        admit.
    + rewrite Heqenv2.
      enough (Forall (fun '(_, u) => u [ x := fvar y ] = u) (map_assq (fun _ u => read_envitem u) env)).
      { rewrite Forall_map_assq, Forall_filter in *. eapply Forall_impl; [|eassumption]. intros [z u]; auto. }
      eapply Forall_impl; [|apply env_fv_inc].
      intros [z u] Hfv. simpl in *.
      apply substf_fv. firstorder.
  - intros L.
    exists (fvar x). constructor.
    rewrite env_find_map_assq in *.
    admit.
  - intros L.
    admit.
Admitted.
 *)

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

Definition check_red env t1 t2 :=
  (* exists L, (forall x, in_fv_rec env x t2 -> ~ in_fv_rec env x t1 -> x \in L) /\ (forall x, x \in L -> ~ in_fv_rec env x t1) /\ star beta (read_env2 env nil t1) (read_env2 env L t2). *)
  (* star beta (read_env2 env nil t1) (read_env2 env (list_diff (in_fv_recL env t2) (in_fv_recL env t1)) t2). *)
  exists t3, star beta (read_env2 env t1) t3 /\ read_env3 env t2 t3.

(*
Lemma check_red_self :
  forall env t1 t2, read_env (map_assq (fun x ei => read_envitem ei) env) t1 t2 -> check_red env t1 t1.
Proof.
  intros env t1 t2 H.
  exists nil.
  apply read_env_read_env2 with (L := nil) in H.
  destruct H as [t3 H]. exists t3. exists t3.
  repeat try split; try assumption.
  - intros x Hx; simpl in *; tauto.
  - constructor.
Qed.
*)

(*
Lemma check_red_self :
  forall env t, check_red env t t.
Proof.
  intros env t.
  exists nil.
  split; [|split].
  - intros; tauto.
  - intros x Hx; simpl in *; tauto.
  - constructor.
Qed.
*)
(*
Lemma check_red_self :
  forall env t, check_red env t t.
Proof.
  intros env t.
  unfold check_red.
  destruct list_diff as [|x L] eqn:Hdiff; [constructor|].
  exfalso.
  assert (H : x \in (x :: L)) by (simpl; tauto).
  rewrite <- Hdiff, list_diff_In_iff in H. tauto.
Qed.
 *)

Inductive is_lazy : envitem -> Prop := is_lazy_lazy : forall t, is_lazy (ELazy t).

(*
Lemma read_env_same :
  forall env1 env2 t1 t2, (forall x, env_find env1 x = env_find env2 x) -> read_env env1 t1 t2 -> read_env env2 t1 t2.
Proof.
  intros env1 env2 t1 t2 Henv H. induction H.
  - constructor; assumption.
  - apply read_env_lam with (L := L). assumption.
  - apply read_env_fvar_free. rewrite <- Henv; assumption.
  - eapply read_env_fvar_bound.
    + rewrite <- Henv; eassumption.
    + assumption.
Qed.

Lemma read_env_same_iff :
  forall env1 env2 t1 t2, (forall x, env_find env1 x = env_find env2 x) -> read_env env1 t1 t2 <-> read_env env2 t1 t2.
Proof.
  intros.
  split; apply read_env_same; firstorder.
Qed.
 *)

(*
Lemma read_env_add :
  forall env t1 t2 x t3 t4, env_find env x = None -> read_env ((x, t3) :: env) t3 t4 -> read_env ((x, t3) :: env) t1 t2 <-> (exists t5, read_env env t1 t5 /\ t2 = t5 [ x := t4 ]).
Proof.
  intros env t1 t2 x t3 t4 Hfind Ht3. split.
  - intros H. induction H.
    + destruct IHread_env1 as [t5 Ht5].
      destruct IHread_env2 as [u5 Hu5].
      exists (app t5 u5). split.
      * constructor; tauto.
      * simpl; f_equal; tauto.
    + pick y \notin (x :: fv t ++ fv t2 ++ fv t4 ++ env_fv env ++ L) as Hy; simpl in Hy; rewrite !in_app_iff in Hy.
      destruct (H0 y ltac:(tauto)) as [t5 [H1 H2]].
      exists (lam (closeb 0 y t5)).
      split.
      * apply read_env_lam with (L := x :: L ++ env_fv env).
        intros z Hz; simpl in *; rewrite in_app_iff in Hz.
        rewrite open_close by (constructor || apply read_env_lc in H1; tauto).
        apply (read_env_subst _ _ _ y (fvar z) (fvar z)) in H1.
        -- rewrite <- substb_is_substf in H1 by tauto.
           rewrite map_assq_id_forall in H1; [assumption|].
           eapply Forall_impl; [|apply env_fv_inc].
           intros [w u] Hwu. apply substf_fv. firstorder.
        -- apply env_find_fv_None. tauto.
        -- constructor. rewrite env_find_map_assq.
           rewrite env_find_fv_None; [reflexivity|tauto].
      * simpl. f_equal.
        rewrite closeb_substf_free by (intuition congruence).
        rewrite <- H2. rewrite close_open; tauto.
    + exists (fvar x0).
      simpl in *.
      destruct freevar_eq_dec; [congruence|].
      split; [constructor; assumption|].
      destruct freevar_eq_dec; congruence.
    + simpl in *.
      destruct freevar_eq_dec.
      * subst. exists (fvar x).
        split; [constructor; assumption|].
        assert (t = t3) by congruence; subst.
        assert (t2 = t4) by (eapply read_env_unique; eassumption); subst.
        simpl. destruct freevar_eq_dec; congruence.
      * destruct IHread_env as [t5 [H1 H2]].
        exists t5. split; [|assumption].
        econstructor; eassumption.
  - intros [t5 [Hread Ht2]]. subst.
    induction Hread.
    + simpl. constructor; assumption.
    + simpl. apply read_env_lam with (L := x :: L).
      intros y Hy; simpl in Hy.
      rewrite substf_substb_free by (apply read_env_lc in Ht3; tauto || simpl; intuition congruence).
      apply H0. tauto.
    + simpl.
      destruct freevar_eq_dec.
      * subst.
        econstructor; [|eassumption].
        simpl. destruct freevar_eq_dec; congruence.
      * constructor. simpl.
        destruct freevar_eq_dec; congruence.
    + econstructor; [|eassumption].
      simpl. destruct freevar_eq_dec; congruence.
Qed.
*)

(*
Lemma read_env2_same_list_strong :
  forall env L1 L2 t, (forall x, env_find env x <> None -> in_fv_rec env x t -> x \in L1 <-> x \in L2) -> read_env2 env L1 t = read_env2 env L2 t.
Proof.
Admitted.

Lemma read_env2_same :
  forall env1 env2 L1 L2 t, env1 === env2 -> L1 == L2 -> read_env2 env1 L1 t = read_env2 env2 L2 t.
Proof.
Admitted.

Global Instance read_env2_Proper : Proper (env_same ==> list_same ==> eq ==> eq) read_env2.
Proof.
  intros e1 e2 He L1 L2 HL t1 t2 ->.
  apply read_env2_same; assumption.
Qed.
*)

Definition rdei (env : list (freevar * envitem)) := map_assq (fun x ei => read_envitem ei) env.


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

Lemma read_env2_same :
  forall env1 env2 t f, env1 === env2 -> acyclic_env (rdei env1) f -> read_env2 env1 t = read_env2 env2 t.
Proof.
  intros env1 env2 t f He Hcycle.
  unfold read_env2.
  eapply read_env_same.
  - intros x.
    rewrite !env_find_map_assq, !env_find_filter_unique, !uniquify_env_same, He by (apply uniquify_env_unique).
    reflexivity.
  - apply unique_env_map_assq. apply unique_env_filter.
    apply uniquify_env_unique.
  - apply unique_env_map_assq. apply unique_env_filter.
    apply uniquify_env_unique.
  - apply acyclic_sub_env_unique with (env1 := rdei (uniquify_env env1)).
    + apply sublist_ordered_map. apply sublist_ordered_filter.
    + apply unique_env_map_assq. apply uniquify_env_unique.
    + unfold rdei. rewrite uniquify_env_same. apply Hcycle.
Qed.

(*
Global Instance read_env2_Proper : Proper (env_same ==> eq ==> eq) read_env2.
Proof.
  intros e1 e2 He t1 t2 ->.
  apply read_env2_same; assumption.
Qed.
*)
Lemma read_env3_same :
  forall env1 env2 t1 t2, env1 === env2 -> read_env3 env1 t1 t2 -> read_env3 env2 t1 t2.
Proof.
  intros env1 env2 t1 t2 Henv Heq. induction Heq.
  - constructor; assumption.
  - eapply read_env3_lam with (L := L). assumption.
  - apply read_env3_fvar_free; rewrite <- Henv; assumption.
  - eapply read_env3_fvar_bound; [|eassumption].
    rewrite <- Henv; assumption.
  - eapply read_env3_fvar_lazy. rewrite <- Henv; eassumption.
Qed.

Global Instance read_env3_Proper : Proper (env_same ==> eq ==> eq ==> iff) read_env3.
Proof.
  intros e1 e2 He t1 t2 -> t3 t4 ->.
  split; eapply read_env3_same; [|symmetry]; eassumption.
Qed.



(*
Lemma check_red_same :
  forall env1 env2 t1 t2, unique_env env1 -> unique_env env2 -> (forall x, env_find env1 x = env_find env2 x) -> check_red env1 t1 t2 -> check_red env2 t1 t2.
Proof.
  intros env1 env2 t1 t2 Hunique1 Hunique2 Henv H.
  destruct H as [L H].
  exists L.
  rewrite !read_env2_same with (env1 := env1) (env2 := env2) in H by tauto.
  split; [|split]; [| |tauto].
  all: intros x; rewrite <- !in_fv_rec_same_iff with (env1 := env1) (env2 := env2) by assumption; apply H.
Qed.
 *)

(*
Lemma check_red_same :
  forall env1 env2 t1 t2, env1 === env2 -> check_red env1 t1 t2 -> check_red env2 t1 t2.
Proof.
  intros env1 env2 t1 t2 Henv H.
  unfold check_red in *.
  rewrite Henv in H.
  assumption.
Qed.
*)

Lemma check_red_same :
  forall env1 env2 t1 t2 f, env1 === env2 -> acyclic_env (rdei env1) f -> check_red env1 t1 t2 -> check_red env2 t1 t2.
Proof.
  intros env1 env2 t1 t2 f Henv Hcycle H.
  destruct H as [t3 H]. exists t3.
  destruct H as [H1 H2]; split; [|rewrite <- Henv; assumption].
  erewrite <- read_env2_same; eassumption.
Qed.

(*
Lemma read_env2_cons_lazy :
  forall env L t1 x t, x \notin L -> read_env2 ((x, ELazy t) :: env) L t1 = read_env2 env L t1.
Proof. Admitted.
(*  intros. unfold read_env2.
  simpl. destruct in_dec; [tauto|].
  reflexivity.
Qed.
*)
Lemma read_env2_cons_not_lazy :
  forall env L t1 x ei, (x \in L \/ ~is_lazy ei) -> read_env2 ((x, ei) :: env) L t1 = read_env2 env L t1 [ x := read_env2 env L (read_envitem ei) ].
Proof. Admitted. (*
  intros. unfold read_env2.
  simpl. destruct in_dec.
  - simpl. reflexivity.
  - destruct ei; simpl; try reflexivity.
    destruct H as [H | H]; [tauto | exfalso; apply H; constructor].
Qed.
                  *)
*)



Lemma read_env2_cons_lazy :
  forall env t1 x t, env_find env x = None -> read_env2 ((x, ELazy t) :: env) t1 = read_env2 env t1.
Proof.
  intros. unfold read_env2.
  rewrite uniquify_env_not_in by assumption.
  simpl. reflexivity.
Qed.

Lemma read_env2_cons_not_lazy :
  forall env t1 x ei, env_find env x = None -> ~ is_lazy ei -> read_env2 ((x, ei) :: env) t1 = read_env2 env t1 [ x := read_env2 env (read_envitem ei) ].
Proof.
  intros env t1 x ei Hx Hlazy. unfold read_env2.
  rewrite uniquify_env_not_in by assumption.
  simpl. destruct ei; try reflexivity.
  exfalso. apply Hlazy. constructor.
Qed.

Lemma read_env3_cons_lazy :
  forall env x t1 t2 t3, lc t2 -> read_env3 ((x, ELazy t3) :: env) t1 t2 -> exists t4 t5, body t4 /\ read_env3 env t3 t5 /\ read_env3 env t1 (t4 ^ x) /\ t2 = t4 ^^ t5.
Proof.
  intros env x t1 t2 t3 Hlc Henv. induction Henv.
  - destruct IHHenv1 as (t5 & t6 & H1); [inversion Hlc; subst; auto|].
    destruct IHHenv2 as (t7 & t8 & H2); [inversion Hlc; subst; auto|].
    exists (app t5 t7).
Abort.

Lemma read_env3_lc_1 :
  forall env t1 t2, read_env3 env t1 t2 -> lc t1.
Proof.
  intros env t1 t2 H. induction H.
  - constructor; assumption.
  - apply lc_lam with (L := L). assumption.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma read_env3_lc_2 :
  forall env t1 t2, read_env3 env t1 t2 -> lc t2.
Proof.
  intros env t1 t2 H. induction H.
  - constructor; assumption.
  - apply lc_lam with (L := L). assumption.
  - constructor.
  - assumption.
  - constructor.
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

Lemma read_env3_subst :
  forall x env t1 t2 t3 t4, x \notin env_ei_fv env -> read_env3 env t1 t2 -> read_env3 env t3 t4 -> read_env3 env (t1 [ x := t3 ]) (t2 [ x := t4 ]).
Proof.
  intros x env t1 t2 t3 t4 Hx Hread1 Hread2; induction Hread1.
  - simpl. constructor; assumption.
  - simpl. apply read_env3_lam with (L := x :: L).
    intros y Hy. simpl in Hy. rewrite !substf_substb_free.
    + apply H0. tauto.
    + simpl; intuition congruence.
    + eapply read_env3_lc_2; eassumption.
    + simpl; intuition congruence.
    + apply read_env3_lc_1 in Hread2; assumption.
  - simpl. destruct freevar_eq_dec.
    + assumption.
    + apply read_env3_fvar_free. assumption.
  - simpl. destruct freevar_eq_dec.
    + apply env_find_fv_None in Hx. unfold rdei in Hx. rewrite env_find_map_assq in Hx.
      subst.
      destruct env_find; congruence.
    + eapply read_env3_fvar_bound; [eassumption|].
      rewrite substf_fv in IHHread1; [assumption|].
      unfold env_ei_fv in Hx.
      assert (Hinc := env_fv_inc (rdei env)). unfold rdei in Hinc.
      rewrite Forall_map_assq, Forall_In in Hinc.
      specialize (Hinc (x0, ei) ltac:(apply env_find_In; assumption)).
      simpl in Hinc. rewrite <- Hinc in Hx.
      simpl in Hx; tauto.
  - simpl. destruct freevar_eq_dec.
    + congruence.
    + eapply read_env3_fvar_lazy; eassumption.
Qed.

Lemma read_env3_lam_one :
  forall x env t1 t2, x \notin fv t1 -> x \notin fv t2 -> x \notin env_ei_fv env ->
                 read_env3 env (t1 ^ x) (t2 ^ x) -> read_env3 env (lam t1) (lam t2).
Proof.
  intros x env t1 t2 Hx1 Hx2 Hx3 Hread.
  apply read_env3_lam with (L := fv t1 ++ fv t2 ++ env_ei_fv env).
  intros y Hy; rewrite !in_app_iff in Hy.
  rewrite substb_is_substf with (x := x) (t := t1) by assumption.
  rewrite substb_is_substf with (x := x) (t := t2) by assumption.
  apply read_env3_subst.
  - assumption.
  - assumption.
  - apply read_env3_fvar_free. apply env_ei_fv_None. tauto.
Qed.


Lemma read_env3_beta1 :
  forall env t1 t2 t3, read_env3 env t1 t2 -> beta t1 t3 -> exists t4, read_env3 env t3 t4 /\ beta t2 t4.
Proof.
  intros env t1 t2 t3 Hread Hbeta. revert t2 Hread. induction Hbeta; intros t5 Hread.
  - inversion Hread; subst.
    inversion H3; subst.
    pick x \notin (L ++ fv t1 ++ fv t4 ++ env_ei_fv env) as Hx; rewrite !in_app_iff in Hx.
    rewrite substb_is_substf with (x := x) by tauto.
    exists (t4 ^^ t6).
    split; [|constructor; apply read_env3_lc_2 in Hread; inversion Hread; subst; [rewrite <- lc_lam_body|]; assumption].
    rewrite substb_is_substf with (x := x) (t := t4) by tauto.
    apply read_env3_subst.
    + tauto.
    + apply H2. tauto.
    + assumption.
  - inversion Hread; subst.
    destruct (IHHbeta _ H2) as (t5 & Ht5a & Ht5b).
    exists (app t5 t7). split; constructor; try assumption.
    eapply read_env3_lc_2; eassumption.
  - inversion Hread; subst.
    destruct (IHHbeta _ H4) as (t5 & Ht5a & Ht5b).
    exists (app t4 t5). split; constructor; try assumption.
    eapply read_env3_lc_2; eassumption.
  - inversion Hread; subst.
    pick x \notin (L ++ L0 ++ fv t3 ++ fv t2 ++ env_ei_fv env) as Hx; rewrite !in_app_iff in Hx.
    specialize (H0 x ltac:(tauto) (t3 ^ x) (H2 x ltac:(tauto))).
    destruct H0 as (t4 & Ht4a & Ht4b).
    exists (lam (closeb 0 x t4)). split.
    + apply read_env3_lam_one with (x := x).
      * tauto.
      * apply closeb_var_free.
      * tauto.
      * rewrite open_close_var by (apply beta_lc in Ht4b; tauto). assumption.
    + apply beta_lam_one with (x := x).
      * tauto.
      * apply closeb_var_free.
      * rewrite open_close_var by (apply beta_lc in Ht4b; tauto). assumption.
Qed.

Lemma read_env3_beta :
  forall env t1 t2 t3, read_env3 env t1 t2 -> star beta t1 t3 -> exists t4, read_env3 env t3 t4 /\ star beta t2 t4.
Proof.
  intros env t1 t2 t3 Hread H. revert t2 Hread. induction H; intros t2 Hread.
  - exists t2; split; [assumption|constructor].
  - eapply read_env3_beta1 in H; [|eassumption].
    destruct H as (t4 & Ht4a & Ht4b).
    specialize (IHstar t4 Ht4a).
    destruct IHstar as (t5 & Ht5a & Ht5b). exists t5.
    split; [assumption|econstructor; eassumption].
Qed.

(*
Lemma read_env3_beta :
  forall env t t1 t2 t3 ei x, read_env3 ((x, ELazy t) :: env) t1 t2 -> star beta (read_env2 env t) t3 -> read_env3 ((x, ei) :: env) (read_envitem ei) t3 -> exists t4, read_env3 ((x, ei) :: env) t1 t4 /\ star beta (t2 [ x := read_env2 env t ]) t4.
Proof.
  intros env t t1 t2 t3 ei x H Hred Hread. induction H.
  - admit.
  - admit.
  - admit.
  - simpl in H.
    destruct freevar_eq_dec.
    + injection H; intro; subst. simpl in *.
Admitted.
 *)

Lemma read_env_app :
  forall env t1 t2, read_env env (app t1 t2) = app (read_env env t1) (read_env env t2).
Proof.
  induction env as [|[x u] env].
  - reflexivity.
  - intros t1 t2. simpl.
    destruct u; simpl; rewrite !IHenv; reflexivity.
Qed.

Lemma read_env2_app :
  forall env t1 t2, read_env2 env (app t1 t2) = app (read_env2 env t1) (read_env2 env t2).
Proof.
  intros env t1 t2. apply read_env_app. 
Qed.

Lemma read_env_lam :
  forall env t, read_env env (lam t) = lam (read_env env t).
Proof.
  induction env as [|[x u] env].
  - reflexivity.
  - intros t. simpl.
    destruct u; simpl; rewrite !IHenv; reflexivity.
Qed.

Lemma read_env2_lam :
  forall env t, read_env2 env (lam t) = lam (read_env2 env t).
Proof.
  intros env t. apply read_env_lam.
Qed.

Lemma read_env_fvar_free :
  forall env x, env_find env x = None -> read_env env (fvar x) = fvar x.
Proof.
  induction env as [|[y u] env].
  - reflexivity.
  - intros x Hx. simpl in *. destruct freevar_eq_dec; [congruence|].
    rewrite IHenv by assumption. simpl. destruct freevar_eq_dec; congruence.
Qed.

Lemma read_env2_fvar_rec :
  forall env x, env_find env x = None -> read_env (map_assq (fun _ ei => read_envitem ei) (filter (fun '(x, u) => match u with ELazy _ => false | _ => true end) env)) (fvar x) = fvar x.
Proof.
  intros env x Hx. induction env as [|[y u] env].
  - simpl. reflexivity.
  - simpl in *.
    destruct freevar_eq_dec; [congruence|].
    destruct u; simpl; rewrite IHenv by assumption; simpl; try destruct freevar_eq_dec; congruence.
Qed.

Lemma read_env2_fvar_free :
  forall env x, env_find env x = None -> read_env2 env (fvar x) = fvar x.
Proof.
  intros env x Hx. unfold read_env2.
  remember (uniquify_env env) as env2.
  assert (Hx2 : env_find env2 x = None) by (rewrite Heqenv2, uniquify_env_same; assumption).
  rewrite read_env2_fvar_rec; tauto.
Qed.

Lemma read_env2_fvar_lazy :
  forall env x t, env_find env x = Some (ELazy t) -> read_env2 env (fvar x) = fvar x.
Proof.
  intros env x t Hx. unfold read_env2.
  remember (uniquify_env env) as env2.
  assert (Hx2 : env_find env2 x = Some (ELazy t)) by (rewrite Heqenv2, uniquify_env_same; assumption).
  assert (Hunique : unique_env env2) by (rewrite Heqenv2; apply uniquify_env_unique).
  clear env Hx Heqenv2. induction env2 as [|[y u] env2].
  - simpl. reflexivity.
  - simpl in *. destruct (unique_env_inv _ _ _ _ Hunique) as [Hy Hunique2].
    destruct freevar_eq_dec.
    + subst. injection Hx2; intro; subst.
      rewrite read_env2_fvar_rec; tauto.
    + destruct u; simpl; rewrite IHenv2 by assumption; simpl; try destruct freevar_eq_dec; congruence.
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

Lemma read_env2_fvar_bound :
  forall env x ei f, acyclic_env (rdei env) f -> env_find env x = Some ei -> ~is_lazy ei -> read_env2 env (fvar x) = read_env2 env (read_envitem ei).
Proof.
  intros env x ei f Hcycle Hx Hlazy. unfold read_env2.
  remember (uniquify_env env) as env2.
  assert (Hx2 : env_find env2 x = Some ei) by (rewrite Heqenv2, uniquify_env_same; assumption).
  assert (Hunique : unique_env env2) by (rewrite Heqenv2; apply uniquify_env_unique).
  unfold rdei in Hcycle. rewrite <- uniquify_env_same with (env := env), <- Heqenv2 in Hcycle.
  clear env Hx Heqenv2. induction env2 as [|[y u] env2].
  - simpl in Hx2. congruence.
  - simpl in *.
    rewrite acyclic_env_cons2 in Hcycle by (erewrite <- unique_env_map_assq in Hunique; inversion Hunique; eassumption).
    destruct (unique_env_inv _ _ _ _ Hunique) as [Hunique2 Hy].
    destruct freevar_eq_dec.
    + subst. injection Hx2; intro; subst.
      destruct ei; simpl.
      * rewrite read_env2_fvar_rec by assumption.
        simpl; destruct freevar_eq_dec; [|congruence].
        symmetry; apply substf_fv.
        intros H.
        eapply read_env_fv_sub in H;
          [|apply sublist_ordered_map_assq; apply sublist_ordered_filter|apply unique_env_map_assq; assumption].
        destruct H as [H | H]; [|rewrite env_find_map_assq, Hy in H; congruence].
        simpl in *.
        eapply read_env_fv in H; [|erewrite <- unique_env_map_assq in Hunique2; apply Hunique2|apply Hcycle].
        destruct H as (z & Hz1 & Hz2); apply Hcycle in Hz1. lia.
      * exfalso; apply Hlazy; constructor.
      * rewrite read_env2_fvar_rec by assumption.
        simpl; destruct freevar_eq_dec; [|congruence].
        symmetry; apply substf_fv.
        intros H.
        eapply read_env_fv_sub in H;
          [|apply sublist_ordered_map_assq; apply sublist_ordered_filter|apply unique_env_map_assq; assumption].
        destruct H as [H | H]; [|rewrite env_find_map_assq, Hy in H; congruence].
        simpl in *.
        eapply read_env_fv in H; [|erewrite <- unique_env_map_assq in Hunique2; apply Hunique2|apply Hcycle].
        destruct H as (z & Hz1 & Hz2); apply Hcycle in Hz1. lia.
    + destruct u; simpl; rewrite IHenv2 by tauto; reflexivity.
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

Lemma read_env2_lc :
  forall env t, elc (rdei env) -> lc t -> lc (read_env2 env t).
Proof.
  intros env t Helc Hlc. apply read_env_lc.
  - apply unique_env_map_assq. apply unique_env_filter. apply uniquify_env_unique.
  - intros x v H.
    rewrite env_find_map_assq, env_find_filter_unique, uniquify_env_same in H by (apply uniquify_env_unique).
    specialize (Helc x v). apply Helc. unfold rdei; rewrite env_find_map_assq.
    destruct (env_find env x) as [ei|]; [|congruence].
    destruct ei; congruence.
  - assumption.
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

Lemma read_env2_substb :
  forall env t k u, elc (rdei env) -> read_env2 env (t [ k <- u ]) = read_env2 env t [ k <- read_env2 env u ].
Proof.
  intros env t k u Hlc.
  apply read_env_substb.
  - apply unique_env_map_assq. apply unique_env_filter. apply uniquify_env_unique.
  - intros x v H.
    rewrite env_find_map_assq, env_find_filter_unique, uniquify_env_same in H by (apply uniquify_env_unique).
    specialize (Hlc x v). apply Hlc. unfold rdei; rewrite env_find_map_assq.
    destruct (env_find env x) as [ei|]; [|congruence].
    destruct ei; congruence.
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

Lemma read_env3_read_env2_left :
  forall env t1 t2 f, env_wf env f -> read_env3 env t1 t2 -> read_env3 env (read_env2 env t1) t2.
Proof.
  intros env t1 t2 f Hewf H. induction H.
  - rewrite read_env2_app. constructor; assumption.
  - rewrite read_env2_lam. apply read_env3_lam with (L := L ++ env_ei_fv env).
    intros x Hx. rewrite in_app_iff in Hx. specialize (H0 x ltac:(tauto)).
    rewrite read_env2_substb in H0 by apply Hewf.
    rewrite read_env2_fvar_free in H0 by (apply env_ei_fv_None; tauto).
    assumption.
  - rewrite read_env2_fvar_free; [apply read_env3_fvar_free|]; assumption.
  - destruct ei.
    + erewrite read_env2_fvar_bound; try eassumption; [apply Hewf|]. intros Hlazy; inversion Hlazy.
    + erewrite read_env2_fvar_lazy; [|eassumption].
      eapply read_env3_fvar_bound; eassumption.
    + erewrite read_env2_fvar_bound; try eassumption; [apply Hewf|]. intros Hlazy; inversion Hlazy.
  - erewrite read_env2_fvar_lazy; [|eassumption].
    eapply read_env3_fvar_lazy. eassumption.
Qed.

Lemma read_env3_cons_subst :
  forall env t1 t2 t3 ei x, env_find env x = None -> read_env3 env t1 t2 -> read_env3 ((x, ei) :: env) (read_envitem ei) t3 -> read_env3 ((x, ei) :: env) t1 (t2 [ x := t3 ]).
Proof.
  intros env t1 t2 t3 ei x Hx Hread Hread2. induction Hread.
  - simpl. constructor; assumption.
  - simpl. apply read_env3_lam with (L := x :: L).
    intros y Hy. rewrite substf_substb_free; [|simpl in *; intuition congruence|eapply read_env3_lc_2; eassumption].
    apply H0. simpl in *; tauto.
  - simpl. destruct freevar_eq_dec.
    + subst. eapply read_env3_fvar_bound; [|eassumption].
      simpl. destruct freevar_eq_dec; congruence.
    + apply read_env3_fvar_free. simpl.
      destruct freevar_eq_dec; congruence.
  - eapply read_env3_fvar_bound; [|eassumption].
    simpl. destruct freevar_eq_dec; congruence.
  - simpl. destruct freevar_eq_dec; [congruence|].
    eapply read_env3_fvar_lazy. simpl; destruct freevar_eq_dec; [congruence|eassumption].
Qed.

Lemma read_env3_cons_lazy :
  forall env t1 t2 t x, env_find env x = None -> read_env3 env t1 t2 -> read_env3 ((x, ELazy t) :: env) t1 t2.
Proof.
  intros env t1 t2 t x Hx Hread. induction Hread.
  - simpl. constructor; assumption.
  - simpl. apply read_env3_lam with (L := L). assumption.
  - simpl. destruct (freevar_eq_dec x x0).
    + subst. eapply read_env3_fvar_lazy.
      simpl. destruct freevar_eq_dec; [reflexivity|congruence].
    + apply read_env3_fvar_free.
      simpl. destruct freevar_eq_dec; congruence.
  - eapply read_env3_fvar_bound; [|eassumption].
    simpl. destruct freevar_eq_dec; congruence.
  - eapply read_env3_fvar_lazy. simpl.
    destruct freevar_eq_dec; [congruence|eassumption].
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


Lemma read_env3_cons_notin :
  forall env t1 t2 ei x, x \notin in_fv_recL env t1 -> read_env3 ((x, ei) :: env) t1 t2 <-> read_env3 env t1 t2.
Proof.
  intros env t1 t2 ei x Hx. split; intros H; induction H.
  - rewrite in_fv_recL_app, in_app_iff in Hx. constructor; tauto.
  - apply read_env3_lam with (L := x :: L ++ env_ei_fv env); intros y Hy; simpl in Hy; rewrite in_app_iff in Hy.
    apply H0; [tauto|].
    rewrite in_fv_recL_lam in Hx. rewrite in_fv_recL_substb, in_app_iff.
    intros [H2 | H2]; [tauto|].
    rewrite in_fv_recL_iff in H2. inversion H2; subst.
    + simpl in *; intuition congruence.
    + simpl in *. rewrite env_ei_fv_None in * by intuition congruence. congruence.
  - apply read_env3_fvar_free. simpl in H.
    destruct freevar_eq_dec; congruence.
  - eapply read_env3_fvar_bound; [|apply IHread_env3].
    + simpl in *. destruct freevar_eq_dec; [|assumption].
      subst. exfalso; apply Hx. rewrite in_fv_recL_iff. constructor. simpl; tauto.
    + intros H1. apply Hx. rewrite in_fv_recL_iff in *. eapply in_fv_rec_env; [simpl; left; reflexivity| |eassumption].
      simpl in H. destruct freevar_eq_dec; [|congruence]. subst.
      exfalso; apply Hx. constructor; simpl; tauto.
  - eapply read_env3_fvar_lazy. simpl in H.
    destruct freevar_eq_dec; [|eassumption].
    subst. exfalso. apply Hx. rewrite in_fv_recL_iff. constructor. simpl; tauto.
  - rewrite in_fv_recL_app, in_app_iff in Hx. constructor; tauto.
  - apply read_env3_lam with (L := x :: L ++ env_ei_fv env); intros y Hy; simpl in Hy; rewrite in_app_iff in Hy.
    apply H0; [tauto|].
    rewrite in_fv_recL_lam in Hx. rewrite in_fv_recL_substb, in_app_iff.
    intros [H2 | H2]; [tauto|].
    rewrite in_fv_recL_iff in H2. inversion H2; subst.
    + simpl in *; intuition congruence.
    + simpl in *. rewrite env_ei_fv_None in * by intuition congruence. congruence.
  - apply read_env3_fvar_free. simpl.
    destruct freevar_eq_dec; [|assumption].
    subst. exfalso; apply Hx. rewrite in_fv_recL_iff. constructor. simpl; tauto.
  - eapply read_env3_fvar_bound; [|apply IHread_env3].
    + simpl in *. destruct freevar_eq_dec; [|assumption].
      subst. exfalso; apply Hx. rewrite in_fv_recL_iff. constructor. simpl; tauto.
    + intros H1. apply Hx. rewrite in_fv_recL_iff in *. eapply in_fv_rec_env; [simpl; left; reflexivity| |eassumption].
      assumption.
  - eapply read_env3_fvar_lazy. simpl.
    destruct freevar_eq_dec; [|eassumption].
    subst. exfalso. apply Hx. rewrite in_fv_recL_iff. constructor. simpl; tauto.
Qed.

Lemma read_env3_read_env2_right :
  forall env t f, elc (rdei env) -> unique_env env -> acyclic_env (rdei env) f -> lc t -> read_env3 env t (read_env2 env t).
Proof.
  intros env. induction env as [|[x u] env]; intros t f Helc Hunique Hcycle Hlc.
  - unfold read_env2. simpl. induction Hlc.
    + apply read_env3_fvar_free. reflexivity.
    + constructor; assumption.
    + apply read_env3_lam with (L := L). assumption.
  - simpl in Hcycle.
    rewrite acyclic_env_cons2 in Hcycle; [|erewrite <- unique_env_map_assq in Hunique; inversion Hunique; eassumption].
    destruct Hcycle as [Hxcycle Hcycle].
    apply unique_env_inv in Hunique; destruct Hunique as [Hunique Hx].
    simpl in Helc.
    apply elc_cons_inv in Helc; [|unfold rdei; rewrite env_find_map_assq, Hx; reflexivity]; destruct Helc as [Hlcu Helc].
    destruct u.
    + rewrite read_env2_cons_not_lazy; [|assumption|intros H; inversion H].
      apply read_env3_cons_subst.
      * assumption.
      * eapply IHenv; eassumption.
      * rewrite read_env3_cons_notin; [eapply IHenv; eassumption|].
        intros Hx2; eapply acyclic_fv_recL_read_env2 in Hx2; try eassumption.
        eapply read_env_fv in Hx2; [|rewrite unique_env_rdei; assumption|eassumption].
        destruct Hx2 as (y & Hy1 & Hy2); apply Hxcycle in Hy1. lia.
    + rewrite read_env2_cons_lazy by assumption.
      apply read_env3_cons_lazy; [assumption|].
      eapply IHenv; eassumption.
    + rewrite read_env2_cons_not_lazy; [|assumption|intros H; inversion H].
      apply read_env3_cons_subst.
      * assumption.
      * eapply IHenv; eassumption.
      * rewrite read_env3_cons_notin; [eapply IHenv; eassumption|].
        intros Hx2; eapply acyclic_fv_recL_read_env2 in Hx2; try eassumption.
        eapply read_env_fv in Hx2; [|rewrite unique_env_rdei; assumption|eassumption].
        destruct Hx2 as (y & Hy1 & Hy2); apply Hxcycle in Hy1. lia.
Qed.

Lemma read_env3_compose :
  forall env t1 t2 t3, read_env3 env t1 t2 -> read_env3 env t2 t3 -> read_env3 env t1 t3.
Proof.
  intros env t1 t2 t3 H. revert t3. induction H.
  - intros t5 H2. inversion H2; subst; constructor; auto.
  - intros t3 H2. inversion H2; subst.
    apply read_env3_lam with (L := L ++ L0).
    intros x Hx; rewrite in_app_iff in Hx; apply H0; auto.
  - intros t3 H2. inversion H2; congruence.
  - intros t3 H2. econstructor; [eassumption|].
    apply IHread_env3. assumption.
  - intros; assumption.
Qed.

Lemma check_red_lc_2 :
  forall env t1 t2, check_red env t1 t2 -> lc t2.
Proof.
  intros env t1 t2 [t3 [H1 H2]].
  eapply read_env3_lc_1; eassumption.
Qed.

Lemma read_env3_fv :
  forall env t1 t2, read_env3 env t1 t2 -> fv t2 \subseteq in_fv_recL env t1.
Proof.
  intros env t1 t2 H. induction H.
  - simpl. rewrite in_fv_recL_app, IHread_env3_1, IHread_env3_2. reflexivity.
  - simpl. pick x \notin (L ++ fv t2 ++ env_ei_fv env) as Hx; rewrite !in_app_iff in Hx.
    specialize (H0 x ltac:(tauto)).
    rewrite <- substb_fv2 in H0.
    intros y Hy. specialize (H0 y Hy).
    rewrite in_fv_recL_substb in H0.
    rewrite in_fv_recL_lam.
    rewrite in_app_iff in H0; destruct H0 as [H0 | H0]; [assumption|].
    rewrite in_fv_recL_iff in H0. inversion H0; subst.
    + simpl in H1. intuition congruence.
    + simpl in H1. destruct H1 as [-> | []].
      rewrite env_ei_fv_None in H2 by tauto. congruence.
  - intros y Hy; destruct Hy as [-> | []].
    rewrite in_fv_recL_iff. constructor. simpl; tauto.
  - etransitivity; [eassumption|].
    intros y Hy; rewrite in_fv_recL_iff in *.
    eapply in_fv_rec_env; try eassumption. simpl; tauto.
  - intros y Hy; destruct Hy as [-> | []].
    rewrite in_fv_recL_iff. constructor. simpl; tauto.
Qed.

Lemma check_red_update_env_helper :
  forall f env t1 t2 t ei2 x, env_wf env f -> env_find env x = None -> lc t -> (forall y, y \in fv t -> f y < f x) -> (forall y, y \in fv (read_envitem ei2) -> f y < f x) -> read_env3 ((x, ELazy t) :: env) t1 t2 -> check_red ((x, ELazy t) :: env) t (read_envitem ei2) -> ~is_lazy ei2 -> exists t3, star beta (t2 [ x := read_env2 env (read_envitem ei2) ]) t3 /\ read_env3 ((x, ei2) :: env) t1 t3.
Proof.
  intros f env t1 t2 t ei2 x Hewf Hx Hlc Htcycle Heicycle H Hred Hlazy. induction H.
  - destruct IHread_env3_1 as (t5 & Ht5a & Ht5b).
    destruct IHread_env3_2 as (t6 & Ht6a & Ht6b).
    exists (app t5 t6). split; [apply star_beta_app; try assumption; apply substf_lc|constructor; assumption].
    + eapply read_env3_lc_2; eassumption.
    + eapply read_env2_lc; [|eapply check_red_lc_2; eassumption].
      apply Hewf.
    + eapply read_env3_lc_2; eassumption.
    + eapply read_env2_lc; [|eapply check_red_lc_2; eassumption].
      apply Hewf.
  - pick y \notin (x :: L ++ fv (t2 [ x := read_env2 env (read_envitem ei2) ]) ++ fv t1 ++ env_ei_fv ((x, ei2) :: env)) as Hy.
    simpl in Hy; rewrite !in_app_iff in Hy.
    specialize (H0 y ltac:(tauto)).
    destruct H0 as (t3 & Ht3a & Ht3b).
    exists (lam (closeb 0 y t3)). split.
    + apply star_beta_lam with (x := y).
      * tauto.
      * apply closeb_var_free.
      * rewrite open_close_var; [|eapply read_env3_lc_2; eassumption].
        rewrite substf_substb_free; [assumption|simpl; intuition congruence|].
        apply read_env2_lc; [|eapply check_red_lc_2; eassumption].
        apply Hewf.
    + apply read_env3_lam_one with (x := y).
      * tauto.
      * apply closeb_var_free.
      * tauto.
      * rewrite open_close_var; [|eapply read_env3_lc_2; eassumption].
        assumption.
  - exists (fvar x0). split; [simpl in *; repeat destruct freevar_eq_dec; try congruence; constructor|].
    apply read_env3_fvar_free.
    simpl in *. destruct freevar_eq_dec; congruence.
  - simpl in H. destruct freevar_eq_dec.
    + subst. injection H; intro; subst. simpl in *.
      destruct Hred as (t2 & Ht2a & Ht2b).
      rewrite read_env2_cons_lazy in Ht2a by assumption.
      assert (H1 := H0).
      eapply read_env3_read_env2_left in H1; [|rewrite env_wf_cons_inv; simpl; split; [eassumption|tauto]].
      eapply read_env3_beta in H1; [|rewrite read_env2_cons_lazy; eassumption].
      destruct H1 as (t4 & Ht4a & Ht4b). exists t4.
      split.
      * rewrite substf_fv; [assumption|].
        rewrite read_env3_fv; [|eassumption].
        rewrite in_fv_recL_cons by tauto.
        enough (x \notin in_fv_recL env t) by tauto.
        intros H2.
        eapply acyclic_fv_recL_read_env2 in H2; try apply Hewf; [|assumption].
        eapply read_env_fv in H2; [|rewrite unique_env_rdei; apply Hewf|apply Hewf].
        destruct H2 as (y & Hy1 & Hy2); apply Htcycle in Hy1; lia.
      * eapply read_env3_fvar_bound; [simpl; destruct freevar_eq_dec; [reflexivity|congruence]|].
        assert (Hx2 : x \notin in_fv_recL env (read_envitem ei2)).
        -- intros H2. eapply acyclic_fv_recL_read_env2 in H2; try apply Hewf; [|assumption].
           eapply read_env_fv in H2; [|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           destruct H2 as (y & Hy1 & Hy2); apply Heicycle in Hy1; lia.
        -- rewrite read_env3_cons_notin by (exact Hx2).
           rewrite <- read_env3_cons_notin by (exact Hx2).
           eapply read_env3_compose; eassumption.
    + destruct IHread_env3 as (t3 & Ht3a & Ht3b).
      exists t3. split; [assumption|].
      eapply read_env3_fvar_bound; [simpl; destruct freevar_eq_dec; [congruence|eassumption]|].
      assumption.
  - simpl in H. destruct freevar_eq_dec.
    + subst. injection H; intro; subst. simpl in *.
      destruct freevar_eq_dec; [|congruence].
      exists (read_env2 env (read_envitem ei2)).
      split; [constructor|].
      eapply read_env3_fvar_bound; [simpl; destruct freevar_eq_dec; [reflexivity|congruence]|].
      erewrite read_env3_cons_notin.
      * eapply read_env3_read_env2_right; try apply Hewf. eapply check_red_lc_2; eassumption.
      * intros H2.
        eapply acyclic_fv_recL_read_env2 in H2; try apply Hewf; [|assumption].
        eapply read_env_fv in H2; [|rewrite unique_env_rdei; apply Hewf|apply Hewf].
        destruct H2 as (y & Hy1 & Hy2); apply Heicycle in Hy1; lia.
    + exists (fvar x0).
      simpl; destruct freevar_eq_dec; [congruence|].
      split; [constructor|].
      eapply read_env3_fvar_lazy.
      simpl. destruct freevar_eq_dec; [congruence|]. eassumption.
Qed.

Lemma star_beta_lc_left :
  forall t1 t2, star beta t1 t2 -> lc t2 -> lc t1.
Proof.
  intros t1 t2 H. destruct H.
  - intros; assumption.
  - intros _. apply beta_lc in H. tauto.
Qed.


Lemma check_red_update_env_easy :
  forall f env t1 t2 ei1 ei2 x,
    env_wf ((x, ei1) :: env) f -> (forall y, y \in fv (read_envitem ei2) -> f y < f x) ->
    check_red ((x, ei1) :: env) t1 t2 -> check_red ((x, ei1) :: env) (read_envitem ei1) (read_envitem ei2) ->
    is_lazy ei1 -> ~ is_lazy ei2 -> check_red ((x, ei2) :: env) t1 t2.
Proof.
  intros f env t1 t2 ei1 ei2 x Hewf Hcycle Ht Hei Hlazy1 Hlazy2.
  destruct ei1; try solve [inversion Hlazy1].
  simpl in *.
  rewrite env_wf_cons_inv in Hewf.
  assert (Hx : env_find env x = None) by tauto.
  destruct Ht as [t3 [Ht1 Ht2]].
  eapply check_red_update_env_helper in Ht2; try eassumption; try apply Hewf.
  destruct Ht2 as (t4 & Ht4a & Ht4b).
  exists t4. split; [|eassumption].
  rewrite read_env2_cons_lazy in Ht1 by assumption. rewrite read_env2_cons_not_lazy by assumption.
  eapply star_compose; [|eassumption].
  eapply star_beta_substf.
  - eapply star_beta_lc_left; [eassumption|].
    eapply substf_lc2; eapply star_beta_lc_left; [eassumption|].
    eapply read_env3_lc_2; eassumption.
  - apply read_env2_lc; [|eapply check_red_lc_2; eassumption]. apply Hewf.
  - assumption.
  - constructor.
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


Lemma check_red_update_env :
  forall f env t1 t2 ei1 ei2 x,
    env_wf env f -> env_find env x = Some ei1 -> (forall y, y \in fv (read_envitem ei2) -> f y < f x) ->
    check_red env t1 t2 -> check_red env (read_envitem ei1) (read_envitem ei2) ->
    is_lazy ei1 -> ~ is_lazy ei2 -> check_red (update_env env x ei2) t1 t2.
Proof.
  intros f env t1 t2 ei1 ei2 x Hewf Hin Hx Hred1 Hred2 Hlazy1 Hlazy2.
  eapply env_wf_move_to_front in Hin; [|eassumption]. destruct Hin as (env2 & Heq & Hewf2).
  eapply check_red_same in Hred1; [|eassumption|apply Hewf].
  eapply check_red_same in Hred2; [|eassumption|apply Hewf].
  eapply check_red_update_env_easy in Hred1; [|eassumption| |eassumption|eassumption|eassumption].
  - eapply check_red_same; [| |eassumption].
    + rewrite Heq. simpl. destruct freevar_eq_dec; [|congruence]. reflexivity.
    + apply env_wf_cons_inv in Hewf2. simpl; apply acyclic_env_cons2.
      * destruct Hewf2 as (H2 & H3 & H4 & H5). rewrite env_find_rdei, H3. reflexivity.
      * split; [|apply Hewf2]. assumption.
  - apply env_wf_cons_inv in Hewf2.
    assumption.
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

Lemma read_env3_read_env :
  forall f env t1 t2, env_wf env f -> read_env3 env t1 t2 -> read_env (rdei env) t1 = read_env (rdei env) t2.
Proof.
  intros f env t1 t2 Hewf H. induction H.
  - rewrite !read_env_app. f_equal; assumption.
  - pick x \notin (L ++ env_ei_fv env ++ fv (read_env (rdei env) t1) ++ fv (read_env (rdei env) t2)) as Hx.
    rewrite !in_app_iff in Hx. specialize (H0 x ltac:(tauto)).
    rewrite !read_env_lam. f_equal.
    rewrite !read_env_substb in H0 by (apply Hewf || unfold rdei; rewrite unique_env_map_assq; apply Hewf).
    rewrite !read_env_fvar_free in H0 by (unfold rdei; rewrite env_find_map_assq, env_ei_fv_None; tauto).
    apply open_inj in H0; tauto.
  - reflexivity.
  - erewrite read_env_fvar_bound.
    + eassumption.
    + unfold rdei. rewrite unique_env_map_assq; apply Hewf.
    + apply Hewf.
    + unfold rdei. rewrite env_find_map_assq, H. reflexivity.
  - reflexivity.
Qed.

Lemma star_beta_read_env :
  forall env t1 t2, unique_env env -> elc env -> star beta t1 t2 -> star beta (read_env env t1) (read_env env t2).
Proof.
  induction env as [|[x v] env]; intros t1 t2 Hunique Helc H.
  - assumption.
  - simpl. rewrite unique_env_inv_iff in Hunique. apply elc_cons_inv in Helc; [|tauto].
    eapply star_map_impl; [|apply IHenv; tauto].
    intros t3 t4 H34; apply beta_subst; [|assumption].
    apply read_env_lc; tauto.
Qed.

Lemma is_lazy_dec :
  forall u, { is_lazy u } + { ~is_lazy u }.
Proof.
  intros; destruct u; simpl.
  - right; intros H; inversion H.
  - left; constructor.
  - right; intros H; inversion H.
Qed.

Lemma read_env_read_env2 :
  forall f env t, lc t -> env_wf env f -> read_env (rdei env) (read_env2 env t) = read_env (rdei env) t.
Proof.
  intros f env t Hlc Hewf. symmetry. eapply read_env3_read_env; [eassumption|].
  eapply read_env3_read_env2_right; try apply Hewf; assumption.
Qed.


Lemma read_env_lc2 :
  forall env t, lc (read_env env t) -> lc t.
Proof.
  induction env as [|[y u] env]; intros t.
  + intros; assumption.
  + intros; simpl in *.
    apply IHenv. eapply substf_lc2; eassumption.
Qed.

Lemma read_env2_lc2 :
  forall env t, lc (read_env2 env t) -> lc t.
Proof.
  intros. eapply read_env_lc2. exact H.
Qed.

Lemma check_red_lc_1 :
  forall env t1 t2, check_red env t1 t2 -> lc t1.
Proof.
  intros env t1 t2 (t3 & H1 & H2).
  apply read_env3_lc_2 in H2. apply star_beta_lc_left in H1; [|assumption].
  eapply read_env2_lc2; eassumption.
Qed.


Lemma check_red_fv_inc :
  forall f env t1 t2, env_wf env f ->
                 check_red env t1 t2 -> fv (read_env (rdei env) t2) \subseteq fv (read_env (rdei env) t1).
Proof.
  intros f env t1 t2 Hewf Hred.
  assert (Hlc1 : lc t1) by (eapply check_red_lc_1; eassumption).
  destruct Hred as (t3 & H1 & H2).
  eapply read_env3_read_env in H2; [|eassumption]. rewrite H2.
  eapply star_beta_read_env in H1; [| |apply Hewf]; [|unfold rdei; rewrite unique_env_map_assq; apply Hewf].
  apply star_beta_fv in H1.
  erewrite read_env_read_env2 in H1; eassumption.
Qed.


(*
Admitted.
  revert t1 Ht1 Hei.
  induction Ht2; intros t5 Ht5 [t6 [Hei1 Hei2]].
  - admit.
  - admit.
  - exists (fvar x0). admit.
  - destruct (IHHt2 Ht1) as [t5 [Ht5a Ht5b]].
    destruct (freevar_eq_dec x x0).
    + subst.
      simpl in H. destruct freevar_eq_dec; [|congruence].
      injection H; intro; subst. simpl in *.
      exists t4. split.
      * eapply star_compose; [eassumption|].
        admit.
      * eapply read_env3_fvar_bound; [simpl in *; destruct freevar_eq_dec; [reflexivity|congruence]|].
        admit.
    + exists t5. split; [assumption|].
      eapply read_env3_fvar_bound; simpl in *; [|eassumption].
      destruct freevar_eq_dec; congruence.
  - simpl in H. destruct freevar_eq_dec.
    + subst. injection H; intro; subst.
      exists t4. 

  exists (t3 [ x := t4 ]).
  split.
  - rewrite read_env2_cons_not_lazy by assumption.
    apply star_beta_substf.
    + admit.
    + admit.
    + admit.
    + admit.
  - 
  unfold check_red in *.
  rewrite read_env2_cons_lazy in Ht by (simpl; tauto).
  destruct (in_dec freevar_eq_dec x (in_fv_recL env t1)).
  - rewrite !read_env2_cons_not_lazy by tauto.
    apply star_beta_substf.
    + admit.
    + admit.
    + rewrite read_env2_cons_lazy in Ht.
      * eapply star_compose; [apply Ht|].
        rewrite !in_fv_recL_cons_In with (t := t1) by assumption. simpl.
        apply star_beta_same. apply read_env2_same_list_strong.
        intros z Hz1 Hz2.
        rewrite !list_diff_In_iff, !in_fv_recL_cons, !in_app_iff by assumption.
        rewrite <- in_fv_recL_iff in Hz2. simpl.
        admit.
      * rewrite list_diff_In_iff. rewrite in_fv_recL_cons_In with (t := t1), in_app_iff by assumption.
        tauto.
    + rewrite in_fv_recL_cons_In with (t := t1) by assumption.
      apply star_beta_same. apply read_env2_same_list_strong.
      intros z Hz1 Hz2.
      rewrite list_diff_In_iff, in_app_iff, !in_fv_recL_iff. simpl. tauto.
  - rewrite !read_env2_cons_not_lazy by tauto.
    rewrite substf_fv with (x := x) (u := read_env2 env nil (read_envitem ei2)) by admit.
    eapply star_compose; [apply Ht|].
    destruct (in_dec freevar_eq_dec x (in_fv_recL env t2)).
    + rewrite read_env2_cons_not_lazy; [|left; rewrite list_diff_In_iff, !in_fv_recL_cons_same; tauto].
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite !in_fv_recL_cons_In with (t := t2) by assumption.
        rewrite !in_fv_recL_cons_notIn with (t := t1) by assumption. simpl.
        apply star_beta_same. apply read_env2_same_list_strong.
        intros z Hz1 Hz2.
        rewrite !list_diff_In_iff, !in_app_iff. rewrite <- in_fv_recL_iff in Hz2.
        tauto.
      * rewrite !in_fv_recL_cons_In with (t := t2) by assumption.
        rewrite !in_fv_recL_cons_notIn with (t := t1) by assumption. simpl.
        rewrite !in_fv_recL_cons_notIn with (t := t) in Hei by admit.
        rewrite !in_fv_recL_cons_notIn with (t := read_envitem ei2) in Hei by admit.
        simpl in Hei.
        rewrite read_env2_cons_lazy in Hei by (simpl; tauto).
        rewrite read_env2_cons_lazy in Hei by admit.
        admit.
    + rewrite substf_fv by admit.
      rewrite read_env2_cons_lazy by (rewrite list_diff_In_iff, !in_fv_recL_cons_same; tauto).
      rewrite !in_fv_recL_cons_notIn by assumption.
      constructor.
    split; [|split].
    + admit. (* intros y Hy1 Hy2. rewrite in_app_iff.
      rewrite in_fv_rec_cons in * by assumption.
      destruct (in_fv_rec_dec env t1 x); [apply Ht in i; rewrite in_fv_rec_cons in i by assumption; tauto|].
      left. apply Ht; rewrite in_fv_rec_cons by assumption; simpl; [|tauto].
      destruct Hy1; [tauto|].
      destruct Hy1 as [Hy1 | Hy1].
      * left. admit.
      * right. apply Hei.
        -- rewrite in_fv_rec_cons by assumption. tauto.
        -- rewrite in_fv_rec_cons in * by assumption; simpl in *. *)
    + intros y Hy. rewrite in_app_iff in Hy. destruct Hy as [Hy | Hy].
      * apply Ht in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        tauto.
      * apply Hei in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        simpl in *.
        intros [H | H]; [|tauto].
        assert (~ in_fv_rec env y t) by tauto.
        assert (~ in_fv_rec env x t1) by tauto.
        admit.
      * rewrite in_fv_rec_cons by (inversion Hunique; assumption).
        admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * admit.
      * admit.
  - exists L. split.
    + intros y Hy.
      rewrite in_fv_rec_cons by (inversion Hunique; assumption).
      apply Ht in Hy. rewrite in_fv_rec_cons in Hy by (inversion Hunique; assumption). tauto.
      intros [H | H].
      * 
      * 
      rewrite fv_substf, in_app_iff.
      admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite !read_env2_cons_lazy in Ht by (simpl; tauto). apply Ht.
      * admit.
Admitted.


Lemma check_red_update_env_easy :
  forall env t1 t2 ei1 ei2 x,
    unique_env ((x, ei1) :: env) -> check_red ((x, ei1) :: env) t1 t2 ->
    check_red ((x, ei1) :: env) (read_envitem ei1) (read_envitem ei2) -> is_lazy ei1 -> ~ is_lazy ei2 -> check_red ((x, ei2) :: env) t1 t2.
Proof.
  intros env t1 t2 ei1 ei2 x Hunique Ht Hei Hlazy1 Hlazy2.
  destruct ei1; try solve [inversion Hlazy1].
  simpl in *.
  assert (Hx : env_find env x = None) by (inversion Hunique; assumption).
  unfold check_red in *.
  rewrite read_env2_cons_lazy in Ht by (simpl; tauto).
  destruct (in_dec freevar_eq_dec x (in_fv_recL env t1)).
  - rewrite !read_env2_cons_not_lazy by tauto.
    apply star_beta_substf.
    + admit.
    + admit.
    + rewrite read_env2_cons_lazy in Ht.
      * eapply star_compose; [apply Ht|].
        rewrite !in_fv_recL_cons_In with (t := t1) by assumption. simpl.
        apply star_beta_same. apply read_env2_same_list_strong.
        intros z Hz1 Hz2.
        rewrite !list_diff_In_iff, !in_fv_recL_cons, !in_app_iff by assumption.
        rewrite <- in_fv_recL_iff in Hz2. simpl.
        admit.
      * rewrite list_diff_In_iff. rewrite in_fv_recL_cons_In with (t := t1), in_app_iff by assumption.
        tauto.
    + rewrite in_fv_recL_cons_In with (t := t1) by assumption.
      apply star_beta_same. apply read_env2_same_list_strong.
      intros z Hz1 Hz2.
      rewrite list_diff_In_iff, in_app_iff, !in_fv_recL_iff. simpl. tauto.
  - rewrite !read_env2_cons_not_lazy by tauto.
    rewrite substf_fv with (x := x) (u := read_env2 env nil (read_envitem ei2)) by admit.
    eapply star_compose; [apply Ht|].
    destruct (in_dec freevar_eq_dec x (in_fv_recL env t2)).
    + rewrite read_env2_cons_not_lazy; [|left; rewrite list_diff_In_iff, !in_fv_recL_cons_same; tauto].
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite !in_fv_recL_cons_In with (t := t2) by assumption.
        rewrite !in_fv_recL_cons_notIn with (t := t1) by assumption. simpl.
        apply star_beta_same. apply read_env2_same_list_strong.
        intros z Hz1 Hz2.
        rewrite !list_diff_In_iff, !in_app_iff. rewrite <- in_fv_recL_iff in Hz2.
        tauto.
      * rewrite !in_fv_recL_cons_In with (t := t2) by assumption.
        rewrite !in_fv_recL_cons_notIn with (t := t1) by assumption. simpl.
        rewrite !in_fv_recL_cons_notIn with (t := t) in Hei by admit.
        rewrite !in_fv_recL_cons_notIn with (t := read_envitem ei2) in Hei by admit.
        simpl in Hei.
        rewrite read_env2_cons_lazy in Hei by (simpl; tauto).
        rewrite read_env2_cons_lazy in Hei by admit.
        admit.
    + rewrite substf_fv by admit.
      rewrite read_env2_cons_lazy by (rewrite list_diff_In_iff, !in_fv_recL_cons_same; tauto).
      rewrite !in_fv_recL_cons_notIn by assumption.
      constructor.
    split; [|split].
    + admit. (* intros y Hy1 Hy2. rewrite in_app_iff.
      rewrite in_fv_rec_cons in * by assumption.
      destruct (in_fv_rec_dec env t1 x); [apply Ht in i; rewrite in_fv_rec_cons in i by assumption; tauto|].
      left. apply Ht; rewrite in_fv_rec_cons by assumption; simpl; [|tauto].
      destruct Hy1; [tauto|].
      destruct Hy1 as [Hy1 | Hy1].
      * left. admit.
      * right. apply Hei.
        -- rewrite in_fv_rec_cons by assumption. tauto.
        -- rewrite in_fv_rec_cons in * by assumption; simpl in *. *)
    + intros y Hy. rewrite in_app_iff in Hy. destruct Hy as [Hy | Hy].
      * apply Ht in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        tauto.
      * apply Hei in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        simpl in *.
        intros [H | H]; [|tauto].
        assert (~ in_fv_rec env y t) by tauto.
        assert (~ in_fv_rec env x t1) by tauto.
        admit.
      * rewrite in_fv_rec_cons by (inversion Hunique; assumption).
        admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * admit.
      * admit.
  - exists L. split.
    + intros y Hy.
      rewrite in_fv_rec_cons by (inversion Hunique; assumption).
      apply Ht in Hy. rewrite in_fv_rec_cons in Hy by (inversion Hunique; assumption). tauto.
      intros [H | H].
      * 
      * 
      rewrite fv_substf, in_app_iff.
      admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite !read_env2_cons_lazy in Ht by (simpl; tauto). apply Ht.
      * admit.
Admitted.
*)

(*
Lemma check_red_update_env_easy :
  forall env t1 t2 ei1 ei2 x,
    unique_env ((x, ei1) :: env) -> check_red ((x, ei1) :: env) t1 t2 ->
    check_red ((x, ei1) :: env) (read_envitem ei1) (read_envitem ei2) -> is_lazy ei1 -> ~ is_lazy ei2 -> check_red ((x, ei2) :: env) t1 t2.
Proof.
  intros env t1 t2 ei1 ei2 x Hunique Ht Hei Hlazy1 Hlazy2.
  destruct Ht as [L Ht].
  destruct Hei as [L2 Hei].
  destruct ei1; try solve [inversion Hlazy1].
  simpl in *.
  assert (Hx : env_find env x = None) by (inversion Hunique; assumption).
  destruct (in_dec freevar_eq_dec x L).
  - exists (L ++ L2).
    split; [|split].
    + admit. (* intros y Hy1 Hy2. rewrite in_app_iff.
      rewrite in_fv_rec_cons in * by assumption.
      destruct (in_fv_rec_dec env t1 x); [apply Ht in i; rewrite in_fv_rec_cons in i by assumption; tauto|].
      left. apply Ht; rewrite in_fv_rec_cons by assumption; simpl; [|tauto].
      destruct Hy1; [tauto|].
      destruct Hy1 as [Hy1 | Hy1].
      * left. admit.
      * right. apply Hei.
        -- rewrite in_fv_rec_cons by assumption. tauto.
        -- rewrite in_fv_rec_cons in * by assumption; simpl in *. *)
    + intros y Hy. rewrite in_app_iff in Hy. destruct Hy as [Hy | Hy].
      * apply Ht in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        tauto.
      * apply Hei in Hy.
        apply Ht in i.
        rewrite in_fv_rec_cons in * by assumption.
        simpl in *.
        intros [H | H]; [|tauto].
        assert (~ in_fv_rec env y t) by tauto.
        assert (~ in_fv_rec env x t1) by tauto.
        admit.
      * rewrite in_fv_rec_cons by (inversion Hunique; assumption).
        admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * admit.
      * admit.
  - exists L. split.
    + intros y Hy.
      rewrite in_fv_rec_cons by (inversion Hunique; assumption).
      apply Ht in Hy. rewrite in_fv_rec_cons in Hy by (inversion Hunique; assumption). tauto.
      intros [H | H].
      * 
      * 
      rewrite fv_substf, in_app_iff.
      admit.
    + rewrite !read_env2_cons_not_lazy by tauto.
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite !read_env2_cons_lazy in Ht by (simpl; tauto). apply Ht.
      * admit.
Admitted.
*)

Lemma check_red_self :
  forall f env t, lc t -> env_wf env f -> check_red env t t.
Proof.
  intros f env t Hlc Hewf. exists (read_env2 env t).
  split; [constructor|].
  eapply read_env3_read_env2_right; try apply Hewf; assumption.
Qed.


Inductive cont_wf (L : list freevar) : cont -> Prop :=
| cont_wf_nil : cont_wf L KNil
| cont_wf_app : forall v pi K, lc (read_nfval v) -> Forall lc pi -> fv (read_nfval v) \subseteq L -> Forall (fun t => fv t \subseteq L) pi -> cont_wf L K -> cont_wf L (KApp v pi K)
| cont_wf_update_lam : forall x t K, body t -> fv t \subseteq L -> x \in L -> cont_wf L K -> cont_wf L (KUpdateLam t x K)
| cont_wf_update_lazy : forall x pi K, Forall lc pi -> Forall (fun t => fv t \subseteq L) pi -> x \in L -> cont_wf L K -> cont_wf L (KUpdateLazy x pi K).


Fixpoint bound_update_lazy K :=
  match K with
  | KNil => nil
  | KApp _ _ K => bound_update_lazy K
  | KUpdateLam _ _ K => bound_update_lazy K
  | KUpdateLazy x _ K => x :: bound_update_lazy K
  end.


Inductive check_cont_f f : list freevar -> cont -> Prop :=
| check_cont_f_nil : forall L, check_cont_f f L KNil
| check_cont_f_app : forall v pi L K,
    check_cont_f f (concat (map fv pi) ++ fv (read_nfval v) ++ L) K -> check_cont_f f L (KApp v pi K)
| check_cont_f_update_lam : forall x t L K,
    (* smallest_above (map f (L ++ fv t)) <= S (f x) -> *)
    check_cont_f f (x :: fv t ++ L) K -> check_cont_f f L (KUpdateLam t x K)
| check_cont_f_update_lazy : forall x pi L K,
    smallest_above (map f L) <= f x ->
    check_cont_f f (x :: concat (map fv pi) ++ L) K -> check_cont_f f L (KUpdateLazy x pi K).

Lemma check_cont_L_change :
  forall f L1 L2 K, smallest_above (map f L2) <= smallest_above (map f L1) ->
               check_cont_f f L1 K -> check_cont_f f L2 K.
Proof.
  intros f L1 L2 K HfL H. revert L2 HfL. induction H; intros L2 HfL.
  - constructor.
  - constructor. apply IHcheck_cont_f.
    rewrite !map_app, !smallest_above_app. lia.
  - constructor.
(*    + rewrite map_app, smallest_above_app in *. lia. *)
    + apply IHcheck_cont_f. simpl. rewrite !map_app, !smallest_above_app. lia.
  - constructor.
    + lia.
    + apply IHcheck_cont_f. simpl. rewrite !map_app, !smallest_above_app. lia.
Qed.

Lemma concat_In :
  forall {A : Type} (L : list (list A)) x, In x (concat L) <-> exists l, In x l /\ In l L.
Proof.
  intros A L x. induction L.
  - simpl. firstorder.
  - simpl. rewrite in_app_iff.
    split.
    + intros [H | H]; [|firstorder]. exists a. tauto.
    + intros (l & H1 & [H2 | H2]); [subst; tauto|].
      right. apply IHL. exists l. tauto.
Qed.

Lemma concat_incl :
  forall (L : list (list freevar)) L2, concat L \subseteq L2 <-> Forall (fun L3 => L3 \subseteq L2) L.
Proof.
  induction L.
  - intros L2. simpl. split.
    + intros. constructor.
    + intros _ y Hy. simpl in Hy. tauto.
  - intros L2. simpl. rewrite list_inc_app_left. rewrite Forall_cons_iff. f_equiv. apply IHL.
Qed.

Lemma check_cont_f_change :
  forall f1 f2 L1 L2 Z K,
    (forall x y, x \in Z -> y \in Z -> f1 x < f1 y -> f2 x < f2 y) ->
    (forall x, x \in Z -> smallest_above (map f1 L1) <= f1 x -> smallest_above (map f2 L2) <= f2 x) ->
    cont_wf Z K -> check_cont_f f1 L1 K -> check_cont_f f2 L2 K.
Proof.
  intros f1 f2 L1 L2 Z K Hfm HfL Hwf H.
  assert (Hfm3 : forall x L, x \in Z -> L \subseteq Z -> smallest_above (map f1 L) <= f1 x -> smallest_above (map f2 L) <= f2 x).
  { intros x L Hx HL H1. rewrite smallest_above_map_le in *.
    intros y Hy. apply Hfm; [rewrite <- HL| |apply H1]; assumption. }
  revert L2 HfL. induction H; intros L2 HfL.
  - constructor.
  - constructor.
    inversion Hwf; subst.
    apply IHcheck_cont_f; [assumption|].
    rewrite !app_assoc.
    intros x Hx1 Hx2.
    rewrite map_app, smallest_above_app, Nat.max_lub_iff in *.
    destruct Hx2 as [Hx2 Hx3]. split; [|apply HfL; assumption].
    apply Hfm3; try assumption.
    rewrite list_inc_app_left, concat_incl, Forall_map. tauto.
  - inversion Hwf; subst.
    constructor.
    apply IHcheck_cont_f; [assumption| ].
    intros y Hy1 Hy2; simpl in *.
    rewrite map_app, smallest_above_app, !Nat.max_lub_iff in *.
    split; [|simpl; apply Hfm; tauto].
    split; [|apply HfL; tauto].
    apply Hfm3; tauto.
  - inversion Hwf; subst.
    constructor.
    + apply HfL; assumption.
    + apply IHcheck_cont_f; [assumption| ].
      intros y Hy1 Hy2; simpl in *.
      rewrite map_app, smallest_above_app, !Nat.max_lub_iff in *.
      split; [|simpl; apply Hfm; tauto].
      split; [|apply HfL; tauto].
      apply Hfm3; try tauto. rewrite concat_incl, Forall_map. assumption.
Qed.




Inductive check_reds env : term -> cont -> Prop :=
| check_reds_nil : forall t, check_reds env t KNil
| check_reds_app : forall v pi t K,
(*    (forall x, x \in bound_update_lazy K ->
                x \notin in_fv_recL env (read_nfval v) /\
                Forall (fun t => x \notin in_fv_recL env t) pi) -> *)
    check_reds env (read_stack (app (read_nfval v) t) pi) K -> check_reds env t (KApp v pi K)
| check_reds_update_lam : forall x t1 t2 K,
(*    (forall x, x \in bound_update_lazy K -> x \notin in_fv_recL env t2) ->*)
    env_find env x = None -> (* x \notin (in_fv_recL env t2) -> *) check_red env (t2 ^ x) t1 -> check_reds env (lam t2) K -> check_reds env t1 (KUpdateLam t2 x K)
| check_reds_update_lazy : forall x pi t1 t2 K,
    env_find env x = Some (ELazy t1) -> check_red env t1 t2 -> (* x \notin bound_update_lazy K ->
    (forall x, x \in bound_update_lazy K -> Forall (fun t => x \notin in_fv_recL env t) pi) -> *)
    (* x \notin in_fv_recL env t2 -> *)
    check_reds env (read_stack (fvar x) pi) K -> check_reds env t2 (KUpdateLazy x pi K).




Fixpoint check_last_update_lazy env t1 K :=
  match K with
  | KNil => True
  | KApp v pi K => check_last_update_lazy env (read_stack (app (read_nfval v) t1) pi) K
  | KUpdateLam t x K => check_last_update_lazy env (lam t) K
  | KUpdateLazy y pi K => (exists t, env_find env y = Some (ELazy t) /\ fv t1 \subseteq in_fv_recL env t) /\ check_last_update_lazy env (read_stack (fvar y) pi) K
  end.

Lemma cont_wf_incl :
  forall L1 L2 K, L1 \subseteq L2 -> cont_wf L1 K -> cont_wf L2 K.
Proof.
  intros L1 L2 K Hsub H. induction H.
  - constructor.
  - constructor; try tauto.
    + rewrite <- Hsub. assumption.
    + eapply Forall_impl; [|eassumption]. intros t; simpl.
      rewrite Hsub. tauto.
  - constructor; try tauto.
    + rewrite <- Hsub. assumption.
    + rewrite <- Hsub. assumption.
  - constructor; try tauto.
    + eapply Forall_impl; [|eassumption]. intros t; simpl.
      rewrite Hsub. tauto.
    + rewrite <- Hsub. assumption.
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

Lemma check_red_ctx :
  forall f env t1 t2 K, env_wf env f -> lc_mctx K -> check_red env t1 t2 -> check_red env (fill_mctx K t1) (fill_mctx K t2).
Proof.
  intros f env t1 t2 K Hewf Hlc Hred. destruct K as [x K]. unfold lc_mctx, fill_mctx in *. simpl in *.
  induction Hlc.
  - simpl. destruct freevar_eq_dec.
    + assumption.
    + eapply check_red_self; [constructor|eassumption].
  - simpl.
    destruct IHHlc1 as [u1 Hu1].
    destruct IHHlc2 as [u2 Hu2].
    exists (app u1 u2). split.
    + rewrite read_env2_app. apply star_beta_app.
      * eapply star_beta_lc_left; [apply Hu1|]. eapply read_env3_lc_2; apply Hu1.
      * eapply star_beta_lc_left; [apply Hu2|]. eapply read_env3_lc_2; apply Hu2.
      * apply Hu1.
      * apply Hu2.
    + constructor; [apply Hu1 | apply Hu2].
  - simpl. pick y \notin (x :: L ++ fv (read_env2 env (t [ x := t1 ])) ++ env_ei_fv env ++ fv (t [ x := t2 ])) as Hy; simpl in Hy; rewrite !in_app_iff in Hy.
    specialize (H0 y ltac:(tauto)). destruct H0 as [u Hu].
    exists (lam (closeb 0 y u)). split.
    + rewrite read_env2_lam. apply star_beta_lam with (x := y).
      * tauto.
      * apply closeb_var_free.
      * rewrite open_close_var by (eapply read_env3_lc_2; apply Hu).
        rewrite substb_substf in Hu by (eapply check_red_lc_1; eassumption).
        simpl in Hu. destruct freevar_eq_dec; [tauto|].
        rewrite read_env2_substb in Hu by apply Hewf.
        rewrite read_env2_fvar_free in Hu by (apply env_ei_fv_None; tauto).
        apply Hu.
    + apply read_env3_lam_one with (x := y).
      * tauto.
      * apply closeb_var_free.
      * tauto.
      * rewrite open_close_var by (eapply read_env3_lc_2; apply Hu).
        rewrite substb_substf with (u := t2) in Hu by (eapply check_red_lc_2; eassumption).
        simpl in Hu; destruct freevar_eq_dec; tauto.
Qed.

Lemma read_env3_nil_refl :
  forall t, lc t -> read_env3 nil t t.
Proof.
  intros t H. induction H.
  - constructor. reflexivity.
  - constructor; assumption.
  - apply read_env3_lam with (L := L). assumption.
Qed.

Lemma check_red_read_same :
  forall f env t1 t2, env_wf env f -> read_env3 env t2 t1 -> check_red env t1 t2.
Proof.
  intros f env t1 t2 Hewf Hread. exists (read_env2 env t1). split; [constructor|].
  eapply read_env3_compose; [eassumption|].
  eapply read_env3_read_env2_right; try apply Hewf.
  eapply read_env3_lc_2; eassumption.
Qed.

Lemma read_env3_ctx_left :
  forall env t1 t2 t3 K, read_env3 env t1 t2 -> read_env3 env (fill_mctx K t2) t3 -> read_env3 env (fill_mctx K t1) t3.
Proof.
  intros env t1 t2 t3 K Hread1 Hread2. remember (fill_mctx K t2) as t4.
  revert K Heqt4. induction Hread2; intros [y K] Heq; unfold fill_mctx in *; destruct K; simpl in *; try destruct freevar_eq_dec; try congruence.
  - eapply read_env3_compose; [eassumption|]. subst. constructor; assumption.
  - constructor; [apply (IHHread2_1 (y, K1)) | apply (IHHread2_2 (y, K2))]; simpl; congruence.
  - subst. eapply read_env3_compose; [eassumption|]. apply read_env3_lam with (L := L); assumption.
  - apply read_env3_lam with (L := y :: L); intros x Hx; simpl in Hx. specialize (H0 x ltac:(tauto) (y, K ^ x)).
    simpl in *. injection Heq; intros; subst.
    rewrite !substb_substf in H0 by ((eapply read_env3_lc_1; eassumption) || (eapply read_env3_lc_2; eassumption)).
    simpl in *. destruct freevar_eq_dec; [tauto|]. tauto.
  - injection Heq. intros; subst. constructor. assumption.
  - subst. eapply read_env3_compose; [eassumption|].
    eapply read_env3_fvar_bound; eassumption.
  - injection Heq. intros; subst. eapply read_env3_fvar_bound; eassumption.
  - injection Heq. intros; subst. eapply read_env3_fvar_lazy; eassumption.
Qed.

Lemma check_red_read_in_ctx :
  forall env t1 t2 t3 K, check_red env t1 (fill_mctx K t2) -> read_env3 env t3 t2 -> check_red env t1 (fill_mctx K t3).
Proof.
  intros env t1 t2 t3 K (t4 & H1 & H2) Hread. exists t4.
  split; [assumption|].
  eapply read_env3_ctx_left; eassumption.
Qed.

Lemma check_red2 :
  forall f env t1 t2 t3 K, env_wf env f -> check_red env t1 (fill_mctx K t2) -> check_red env t2 t3 -> check_red env t1 (fill_mctx K t3).
Proof.
  intros f env t1 t2 t3 (x, K) Hewf (t4 & H1 & H2) (t5 & H3 & H4).
  unfold lc_mctx, fill_mctx in *; simpl in *.
  assert (Hlc := read_env3_lc_1 _ _ _ H2). apply substf_lc2 in Hlc.
  enough (H : exists t6, star beta t4 t6 /\ read_env3 env (K [x := t3]) t6).
  { destruct H as (t6 & H5 & H6). exists t6. split; [|assumption]. eapply star_compose; eassumption. }
  clear t1 H1. revert t4 H2. induction Hlc; intros t4 H2; simpl in *.
  - destruct freevar_eq_dec.
    + eapply read_env3_read_env2_left in H2; [|eassumption].
      eapply read_env3_beta in H3; [|eassumption].
      destruct H3 as (t7 & H5 & H6).
      exists t7. split; [assumption|].
      eapply read_env3_compose; eassumption.
    + exists t4. split; [constructor|assumption].
  - inversion H2; subst.
    destruct (IHHlc1 _ ltac:(eassumption)) as (t10 & H7 & H8).
    destruct (IHHlc2 _ ltac:(eassumption)) as (t11 & H9 & H10).
    exists (app t10 t11). split.
    + apply star_beta_app.
      * eapply read_env3_lc_2; eassumption.
      * eapply read_env3_lc_2; eassumption.
      * assumption.
      * assumption.
    + constructor; assumption.
  - inversion H2; subst.
    pick y \notin (x :: L ++ L0 ++ fv t0 ++ fv (t [ x := t3 ]) ++ env_ei_fv env) as Hy;
      simpl in Hy; rewrite !in_app_iff in Hy.
    specialize (H0 y ltac:(tauto)). specialize (H5 y ltac:(tauto)).
    rewrite substf_substb_free in H5.
    + specialize (H0 _ H5). destruct H0 as (t6 & H6 & H7). exists (lam (closeb 0 y t6)).
      split.
      * apply star_beta_lam with (x := y); [tauto|apply closeb_var_free|].
        rewrite open_close_var by (eapply read_env3_lc_2; eassumption).
        assumption.
      * apply read_env3_lam_one with (x := y); [tauto|apply closeb_var_free|tauto|].
        rewrite open_close_var by (eapply read_env3_lc_2; eassumption).
        rewrite substf_substb_free; [assumption|simpl; intuition congruence|eapply read_env3_lc_1; eassumption].
    + simpl. intuition congruence.
    + apply star_beta_lc_left in H3; [|eapply read_env3_lc_2; eassumption].
      apply read_env2_lc2 in H3. assumption.
Qed.


Fixpoint stack_mctx pi K :=
  match pi with
  | nil => K
  | t :: pi => stack_mctx pi (app_mctx K (empty_mctx t))
  end.

Lemma stack_mctx_fill :
  forall pi K t, fill_mctx (stack_mctx pi K) t = read_stack (fill_mctx K t) pi.
Proof.
  induction pi.
  - intros; simpl. reflexivity.
  - intros; simpl. rewrite IHpi. rewrite fill_app, fill_empty. reflexivity.
Qed.


Lemma read_env3_open_gen :
  forall env t1 t2 x, env_find env x = None -> read_env3 env (lam t1) (lam t2) -> read_env3 env (t1 ^ x) (t2 ^ x).
Proof.
  intros env t1 t2 x Hx H. inversion H; subst.
  pick y \notin (L ++ env_ei_fv env ++ fv t1 ++ fv t2) as Hy; rewrite !in_app_iff in Hy.
  specialize (H2 y ltac:(tauto)).
  apply read_env3_subst with (x := y) (t3 := fvar x) (t4 := fvar x) in H2.
  - rewrite <- !substb_is_substf in H2 by tauto.
    assumption.
  - tauto.
  - apply read_env3_fvar_free. assumption.
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

Lemma check_reds_read_in_ctx :
  forall f env t1 t2 K L C, env_wf env f -> check_reds env (fill_mctx C t1) K -> check_red env t1 t2 -> cont_wf L K -> check_reds env (fill_mctx C t2) K.
Proof.
  intros f env t1 t2 K L C Hewf H1 H2 Hkwf.
  remember (fill_mctx C t1) as t3. revert C t1 H2 Heqt3. induction H1; intros C t4 Ht4 Heq3; subst.
  - constructor.
  - inversion Hkwf; subst. constructor.
    specialize (IHcheck_reds ltac:(assumption) (stack_mctx pi (app_mctx (empty_mctx (read_nfval v)) C)) t4 Ht4).
    rewrite !stack_mctx_fill, !fill_app, !fill_empty in *.
    apply IHcheck_reds. reflexivity.
  - constructor; try assumption.
    eapply check_red2; eassumption.
  - econstructor; [eassumption| |].
    + eapply check_red2; eassumption.
    + assumption.
Qed.

Definition closed_in_env {A : Type} (env : list (freevar * A)) t := forall x, x \in fv t -> env_find env x = None.
Lemma closed_in_env_map_assq :
  forall {A B : Type} (f : freevar -> A -> B) env t, closed_in_env (map_assq f env) t <-> closed_in_env env t.
Proof.
  intros. split; intros H x Hx; specialize (H x Hx); rewrite env_find_map_assq in *; destruct env_find; congruence.
Qed.

Lemma closed_in_env_rdei : forall env t, closed_in_env (rdei env) t <-> closed_in_env env t.
Proof.
  apply closed_in_env_map_assq.
Qed.

Lemma closed_in_env_app : forall {A : Type} (env : list (freevar * A)) t1 t2,
    closed_in_env env (app t1 t2) <-> closed_in_env env t1 /\ closed_in_env env t2.
Proof.
  intros A env t1 t2. split.
  - intros H; split; intros x Hx; specialize (H x ltac:(simpl; rewrite in_app_iff; tauto)); assumption.
  - intros [H1 H2] x Hx; simpl in Hx; rewrite in_app_iff in Hx.
    specialize (H1 x); specialize (H2 x); tauto.
Qed.

Lemma closed_in_env_lam : forall {A : Type} (env : list (freevar * A)) t,
    closed_in_env env (lam t) <-> closed_in_env env t.
Proof.
  intros; reflexivity.
Qed.

Lemma closed_in_env_fvar : forall {A : Type} (env : list (freevar * A)) x, closed_in_env env (fvar x) <-> env_find env x = None.
Proof.
  intros; split.
  - intros H. apply H. simpl. tauto.
  - intros H y [-> | []]. assumption.
Qed.

Lemma closed_in_env_bvar : forall {A : Type} (env : list (freevar * A)) n, closed_in_env env (bvar n).
Proof.
  intros A env n x [].
Qed.

Lemma closed_in_env_substb : forall {A : Type} (env : list (freevar * A)) t k u, closed_in_env env t -> closed_in_env env u -> closed_in_env env (t [ k <- u ]).
Proof.
  intros A env t. induction t.
  - intros k u _ Hu. simpl. destruct Nat.eq_dec; [assumption|apply closed_in_env_bvar].
  - intros k u H _. apply H.
  - intros k u H1 H2. simpl. rewrite closed_in_env_lam in *. apply IHt; assumption.
  - intros k u H1 H2. simpl. rewrite closed_in_env_app in *.
    split; [apply IHt1 | apply IHt2]; tauto.
Qed.

Lemma closed_in_env_cons : forall {A : Type} (env : list (freevar * A)) t x ei,
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

Lemma closed_in_env_closeb : forall {A : Type} (env : list (freevar * A)) t k x,
    closed_in_env env t -> closed_in_env env (closeb k x t).
Proof.
  intros A env t. induction t.
  - intros; simpl. assumption.
  - intros; simpl. destruct freevar_eq_dec; [apply closed_in_env_bvar|assumption].
  - intros; simpl. rewrite closed_in_env_lam in *. apply IHt; assumption.
  - intros; simpl. rewrite closed_in_env_app in *.
    split; [apply IHt1 | apply IHt2]; tauto.
Qed.

Definition check_lam ei bodies :=
  match ei with
  | ELam t x => env_find bodies x = Some t
  | _ => True
  end.

Definition check_val ei (env : list (freevar * envitem)) :=
  match ei with
  | EVal v => closed_in_env env (read_nfval v)
  | _ => True
  end.

Lemma check_val_cons : forall env x ei1 ei2,
    check_val ei1 env -> x \notin fv (read_envitem ei1) -> check_val ei1 ((x, ei2) :: env).
Proof.
  intros env x ei1 ei2 H1 H2. destruct ei1; try tauto.
  simpl in *. rewrite closed_in_env_cons. tauto.
Qed.

Fixpoint check_lam_cont bodies K :=
  match K with
  | KNil => True
  | KApp _ _ K => check_lam_cont bodies K
  | KUpdateLam t x K => env_find bodies x = Some t /\ check_lam_cont bodies K
  | KUpdateLazy _ _ K => check_lam_cont bodies K
  end.

Fixpoint check_val_cont (env : list (freevar * envitem)) K :=
  match K with
  | KNil => True
  | KApp v _ K => closed_in_env env (read_nfval v) /\ check_val_cont env K
  | KUpdateLam _ _ K => check_val_cont env K
  | KUpdateLazy _ _ K => check_val_cont env K
  end.

Lemma check_val_cont_cons : forall env x ei K L,
    x \notin L -> cont_wf L K -> check_val_cont env K -> check_val_cont ((x, ei) :: env) K.
Proof.
  intros env x ei K L Hx Hwf H. induction K.
  - simpl. tauto.
  - simpl. inversion Hwf; subst. tauto.
  - simpl. inversion Hwf; subst. tauto.
  - simpl in *. inversion Hwf; subst.
    split; [|tauto]. rewrite closed_in_env_cons; split; [tauto|].
    rewrite H5. assumption.
Qed.

Definition wf_state st :=
  exists f,
    env_wf (st_env st) f /\
    fv (read_envitem (st_code st)) \subseteq (st_usedvars st) /\
    env_ei_fv (st_env st) \subseteq (st_usedvars st) /\
    Forall (fun t => fv t \subseteq (st_usedvars st)) (st_stack st) /\
    lc (read_envitem (st_code st)) /\
    Forall lc (st_stack st) /\
    cont_wf (st_usedvars st) (st_cont st) /\
    check_reds (st_env st) (read_stack (read_envitem (st_code st)) (st_stack st)) (st_cont st) /\
    check_val (st_code st) (st_env st) /\
    (forall x ei, env_find (st_env st) x = Some ei -> check_val ei (st_env st)) /\
    check_val_cont (st_env st) (st_cont st) /\
    check_cont_f f (match st_code st with ELam _ x => x :: nil | _ => nil end
                      ++ fv (read_envitem (st_code st)) ++ concat (map fv (st_stack st))) (st_cont st) /\
    (forall x t y, env_find (st_env st) x = Some (ELam t y) -> f y < f x) /\
    (* (forall x, x \in bound_update_lazy (st_cont st) -> x \notin in_fv_recL (st_env st) (read_envitem (st_code st)) /\ Forall (fun t => x \notin in_fv_recL (st_env st) t) (st_stack st)) /\ *)
    (* check_last_update_lazy (st_env st) (read_stack (read_envitem (st_code st)) (st_stack st)) (st_cont st) /\ *)
    (exists bodies, check_lam (st_code st) bodies /\
               (forall x ei, env_find (st_env st) x = Some ei -> check_lam ei bodies) /\
               check_lam_cont bodies (st_cont st) /\
               (forall x t, env_find bodies x = Some t ->
                       x \in (st_usedvars st) /\ (forall y, y \in fv t -> f y < f x) (*x \notin in_fv_recL (st_env st) t*) /\
                             env_find (st_env st) x = None /\ fv t \subseteq (st_usedvars st)) /\
               (forall x t1 t2, env_find bodies x = Some t1 -> env_find (st_lamnf st) x = Some t2 ->
                           check_red (st_env st) (t1 ^ x) (read_nfval_or_lam t2)) /\
               (forall x, env_find bodies x = None -> env_find (st_lamnf st) x = None) /\
               (forall x t, env_find (st_lamnf st) x = Some t ->
                       fv (read_nfval_or_lam t) \subseteq (st_usedvars st) /\
                       closed_in_env (st_env st) (read_nfval_or_lam t) /\
                       (forall y, y \in list_remove x (fv (read_nfval_or_lam t)) -> f y < f x))).

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

Lemma closed_in_env_read_env3 :
  forall env t1 t2, closed_in_env env t1 -> read_env3 env t1 t2 -> t1 = t2.
Proof.
  intros env t1 t2 H1 H2. induction H2.
  - rewrite closed_in_env_app in H1. f_equal; tauto.
  - f_equal. pick x \notin (L ++ fv t1 ++ fv t2 ++ env_ei_fv env) as Hx. rewrite !in_app_iff in Hx.
    apply open_inj with (x := x); try tauto.
    apply H0; [tauto|].
    apply closed_in_env_substb; [rewrite closed_in_env_lam in H1; assumption|].
    rewrite closed_in_env_fvar. apply env_ei_fv_None; tauto.
  - reflexivity.
  - rewrite closed_in_env_fvar in H1. congruence.
  - reflexivity.
Qed.

Fixpoint nfval_ind2 (P : nfval -> Prop) (Q : nfval_or_lam -> Prop)
         (Hfree : forall x, P (NFFreeVar x)) (Happ : forall v1 v2, P v1 -> Q v2 -> P (NFStructApp v1 v2))
         (Hval : forall v, P v -> Q (NFVal v)) (Hlam : forall x v, Q v -> Q (NFLam x v)) v : P v :=
  match v with
  | NFFreeVar x => Hfree x
  | NFStructApp v1 v2 => Happ v1 v2 (nfval_ind2 P Q Hfree Happ Hval Hlam v1) (nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v2)
  end

with nfval_or_lam_ind2 (P : nfval -> Prop) (Q : nfval_or_lam -> Prop)
         (Hfree : forall x, P (NFFreeVar x)) (Happ : forall v1 v2, P v1 -> Q v2 -> P (NFStructApp v1 v2))
         (Hval : forall v, P v -> Q (NFVal v)) (Hlam : forall x v, Q v -> Q (NFLam x v)) v : Q v :=
  match v with
  | NFVal v => Hval v (nfval_ind2 P Q Hfree Happ Hval Hlam v)
  | NFLam x v => Hlam x v (nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v)
  end.

Definition nfval_and_lam_ind2 P Q Hfree Happ Hval Hlam :=
  conj (fun v => nfval_ind2 P Q Hfree Happ Hval Hlam v) (fun v => nfval_or_lam_ind2 P Q Hfree Happ Hval Hlam v).


Lemma nfval_and_lam_lc :
  (forall v, lc (read_nfval v)) /\ (forall v, lc (read_nfval_or_lam v)).
Proof.
  apply nfval_and_lam_ind2.
  - intros; simpl; constructor.
  - intros; simpl; constructor; assumption.
  - intros; simpl; assumption.
  - intros; simpl. apply lc_lam_body. apply closeb_body. assumption.
Qed.

Definition nfval_or_lam_lc := proj2 nfval_and_lam_lc.

Lemma nfval_and_lam_nf :
  (forall v t, ~ beta (read_nfval v) t) /\ (forall v t, ~ beta (read_nfval_or_lam v) t).
Proof.
  apply nfval_and_lam_ind2.
  - intros x t H. simpl in H. inversion H.
  - intros v1 v2 H1 H2 t H. simpl in H. inversion H; subst.
    + destruct v1; simpl in *; congruence.
    + eapply H1; eassumption.
    + eapply H2; eassumption.
  - intros v H1 t H. simpl in H. eapply H1; eassumption.
  - intros x v H1 t H. simpl in *.
    inversion H; subst.
    pick y \notin (L ++ fv (closeb 0 x (read_nfval_or_lam v))) as Hy. rewrite in_app_iff in Hy. specialize (H2 y ltac:(tauto)).
    apply beta_subst with (x := y) (u := fvar x) in H2; [|constructor].
    rewrite substb_substf in H2; [|constructor].
    simpl in H2. destruct freevar_eq_dec; [|congruence].
    rewrite substf_fv in H2 by tauto.
    rewrite open_close_var in H2; [|apply nfval_or_lam_lc].
    eapply H1; eassumption.
Qed.

Definition nfval_nf := proj1 nfval_and_lam_nf.

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

Lemma check_reds_update_env :
  forall f env ei1 ei2 x K L t,
    env_wf env f -> env_find env x = Some ei1 ->
    (forall y, y \in fv (read_envitem ei2) -> f y < f x) -> check_cont_f f L K -> x \in L -> 
    is_lazy ei1 -> ~ is_lazy ei2 -> check_red env (read_envitem ei1) (read_envitem ei2) ->
    check_reds env t K -> check_reds (update_env env x ei2) t K.
Proof.
  intros f env ei1 ei2 x K L t Hewf Hfind Hx HfK HxL Hlazy1 Hlazy2 Hred H.
  revert L HxL HfK; induction H; intros L HxL HfK.
  - constructor.
  - constructor. inversion HfK; subst; eapply IHcheck_reds; [|eassumption].
    rewrite !in_app_iff; tauto.
  - assert (Hx0 : x <> x0) by congruence. constructor.
    + rewrite env_find_update_env, H. destruct freevar_eq_dec; congruence.
    + eapply check_red_update_env; eassumption.
    + inversion HfK; subst.
      eapply IHcheck_reds; [|eassumption]. simpl. rewrite in_app_iff; tauto.
  - destruct (freevar_eq_dec x x0).
    + subst. inversion HfK; subst. rewrite smallest_above_map_le in H5. specialize (H5 _ HxL). lia.
    + inversion HfK; subst.
      econstructor; [| |eapply IHcheck_reds; [|eassumption]; simpl; rewrite in_app_iff; tauto].
      * rewrite env_find_update_env; destruct freevar_eq_dec; [congruence|eassumption].
      * eapply check_red_update_env; eassumption.
Qed.



Lemma check_lam_impl :
  forall x t bodies ei, env_find bodies x = None -> check_lam ei bodies -> check_lam ei ((x, t) :: bodies).
Proof.
  intros x t bodies ei Hx H. unfold check_lam in *. destruct ei; try tauto.
  simpl. destruct freevar_eq_dec; congruence.
Qed.

Lemma check_red_cons_lazy :
  forall x u t1 t2 env, env_find env x = None -> check_red env t1 t2 -> check_red ((x, ELazy u) :: env) t1 t2.
Proof.
  intros x u t1 t2 env Hx (t3 & H1 & H2). exists t3.
  split.
  - rewrite read_env2_cons_lazy; assumption.
  - apply read_env3_cons_lazy; assumption.
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

Lemma read_stack_fv :
  forall t pi L, Forall (fun t2 => fv t2 \subseteq L) pi -> fv (read_stack t pi) \subseteq fv t ++ L.
Proof.
  intros t pi. revert t. induction pi; intros t L HL.
  - simpl. prove_list_inc.
  - simpl. rewrite Forall_cons_iff in HL. destruct HL as [HL1 HL2]. rewrite IHpi; [|apply HL2].
    simpl. rewrite HL1. prove_list_inc.
Qed.

Lemma check_reds_cons_lazy :
  forall x u t K L env, x \notin env_ei_fv env -> cont_wf L K -> x \notin L -> x \notin fv t -> check_reds env t K -> check_reds ((x, ELazy u) :: env) t K.
Proof.
  intros x u t K L env Hx Hwf Hx2 Hx3 H. induction H.
  - constructor.
  - constructor. inversion Hwf; subst. eapply IHcheck_reds; [assumption|].
    rewrite read_stack_fv; [|eassumption]. simpl.
    rewrite !in_app_iff, H5. tauto.
  - inversion Hwf; subst. constructor.
    + simpl. destruct freevar_eq_dec; [|assumption]. subst. tauto.
    + apply check_red_cons_lazy; [|assumption]. apply env_ei_fv_None; assumption.
    + eapply IHcheck_reds; [assumption|]. simpl.
      rewrite H6; assumption.
  - inversion Hwf; subst. econstructor.
    + simpl. destruct freevar_eq_dec; [|eassumption]. subst. tauto.
    + apply check_red_cons_lazy; [|assumption]. apply env_ei_fv_None; assumption.
    + apply IHcheck_reds; [assumption|].
      rewrite read_stack_fv; [|eassumption]. simpl.
      intros [-> | ?]; tauto.
Qed.


Lemma closed_in_env_update_env :
  forall {A : Type} (env : list (freevar * A)) t x u, env_find env x <> None ->
                                                 closed_in_env (update_env env x u) t <-> closed_in_env env t.
Proof.
  intros A env t x u Hx. split; intros H y Hy; specialize (H y Hy).
  - rewrite env_find_update_env in H. destruct freevar_eq_dec; congruence.
  - rewrite env_find_update_env. destruct freevar_eq_dec; congruence.
Qed.

Lemma check_val_update_env :
  forall env x u ei, env_find env x <> None -> check_val ei (update_env env x u) <-> check_val ei env.
Proof.
  intros env x u ei Hx. unfold check_val. destruct ei; try reflexivity.
  apply closed_in_env_update_env. assumption.
Qed.

Lemma closed_in_env_read_env3_2 :
  forall env t, lc t -> closed_in_env env t -> read_env3 env t t.
Proof.
  intros env t Ht. induction Ht.
  - intros. apply read_env3_fvar_free. rewrite closed_in_env_fvar in H. assumption.
  - intros H. rewrite closed_in_env_app in H. constructor; tauto.
  - intros H1. apply read_env3_lam with (L := L ++ env_ei_fv env).
    intros x Hx. rewrite in_app_iff in Hx. apply H0; [tauto|].
    apply closed_in_env_substb; [|apply closed_in_env_fvar, env_ei_fv_None; tauto].
    rewrite closed_in_env_lam in H1. assumption.
Qed.

Definition offset_fun f x n y :=
  if freevar_eq_dec x y then n else if (lt_dec (f y) n) then f y else S (f y).

Lemma offset_fun_monotone :
  forall f x n y1 y2, x <> y1 -> x <> y2 -> offset_fun f x n y1 < offset_fun f x n y2 <-> f y1 < f y2.
Proof.
  intros. unfold offset_fun.
  repeat destruct freevar_eq_dec; try congruence.
  repeat destruct lt_dec; lia.
Qed.

Lemma closed_in_env_read_env :
  forall env t, closed_in_env env t -> read_env env t = t.
Proof.
  intros env t. induction env as [|[x u] env].
  - reflexivity.
  - intros Ht. rewrite closed_in_env_cons in Ht. simpl.
    rewrite IHenv by tauto. apply substf_fv. tauto.
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

Lemma check_val_cont_update_env :
  forall env x ei K, env_find env x <> None -> check_val_cont env K -> check_val_cont (update_env env x ei) K.
Proof.
  intros env x ei K Hx H. induction K; simpl in *; try tauto.
  split; [|tauto].
  apply closed_in_env_update_env; tauto.
Qed.

Lemma read_env2_fv :
  forall f env t y, acyclic_env (rdei env) f -> y \in fv (read_env2 env t) -> exists x, x \in fv t /\ f y <= f x.
Proof.
  intros f env t y Hcycle H.
  eapply read_env_fv in H; [eassumption|rewrite unique_env_rdei; apply unique_env_filter, uniquify_env_unique|].
  eapply acyclic_sub_env_unique.
  - apply sublist_ordered_map_assq, sublist_ordered_filter.
  - rewrite unique_env_map_assq. apply uniquify_env_unique.
  - rewrite uniquify_env_same. assumption.
Qed.

Lemma Forall_env_find :
  forall {A : Type} (P : freevar * A -> Prop) L x t, Forall P L -> env_find L x = Some t -> P (x, t).
Proof.
  intros. induction L as [|[y u] L].
  - simpl in *. congruence.
  - simpl in *. destruct freevar_eq_dec.
    + injection H0. intros; subst. rewrite Forall_cons_iff in H. tauto.
    + apply IHL; [rewrite Forall_cons_iff in H; tauto|]. assumption.
Qed.

Lemma acyclic_env_change_f :
  forall f1 f2 env, (forall x y, x \in env_fv env -> y \in env_fv env -> f1 x < f1 y -> f2 x < f2 y) -> acyclic_env env f1 -> acyclic_env env f2.
Proof.
  intros f1 f2 env H Hcycle x y t Hx Hy.
  assert (Hx2 := Hx).
  eapply Forall_env_find in Hx2; [|apply env_fv_inc]. simpl in Hx2.
  apply H; [| |eapply Hcycle; eassumption]; rewrite <- Hx2; simpl; tauto.
Qed.

Lemma env_wf_change_f :
  forall f1 f2 env, (forall x y, x \in env_ei_fv env -> y \in env_ei_fv env -> f1 x < f1 y -> f2 x < f2 y) -> env_wf env f1 -> env_wf env f2.
Proof.
  intros f1 f2 env H1 (H2 & H3 & H4); splits 3; try assumption.
  eapply acyclic_env_change_f; eassumption.
Qed.

Lemma check_lam_cont_cons :
  forall K L x t B, check_lam_cont B K -> cont_wf L K -> x \notin L -> check_lam_cont ((x, t) :: B) K.
Proof.
  intros K L x t B H Hwf Hx. induction K.
  - simpl. tauto.
  - simpl in *. apply IHK; [assumption|]. inversion Hwf; subst. assumption.
  - simpl in *. inversion Hwf; subst.
    destruct freevar_eq_dec; [subst; tauto|]. tauto.
  - simpl in *. inversion Hwf; subst. tauto.
Qed.

Theorem red_wf :
  forall st st2, red st st2 -> wf_state st -> wf_state st2.
Proof.
  intros st st2 Hred Hwf.
  destruct Hwf as (f & Hewf & Hfvc & Hfve & Hfvs & Hlcc & Hlcs & Hkwf & Hchk & Hcvc & Hcve & Hcvk & Hcf & Hfl & bodies & Hbclc & Hbcle & Hbclk & Hbb & Hbbeta & HbW & HW).
  inversion Hred; subst; unfold wf_state; simpl in *.
  - exists f. rewrite list_inc_app_left in Hfvc.
    rewrite <- app_assoc in Hcf. rewrite !Forall_cons_iff. inversion Hlcc; subst.
    splits 14; try tauto; exists bodies; tauto.
  - pose (nf := offset_fun f y (smallest_above (map f (fv t)))).
    exists nf.
    splits 14; try assumption;
      [|rewrite Hfvc|rewrite Hfve|eapply Forall_impl; [|eassumption]; intros t2 H2; simpl in H2; rewrite H2|eapply cont_wf_incl; [|eassumption]| | |]; try prove_list_inc.
    + eapply env_wf_change_f; [|eassumption].
      intros x1 y1 Hx1 Hy1 Hxy1. unfold nf.
      apply offset_fun_monotone; [| |assumption]; intros ->; rewrite Hfve in *; tauto.
    + eapply check_cont_f_change; try eassumption.
      * intros. unfold nf. rewrite offset_fun_monotone; [assumption| |]; intros ->; tauto.
      * intros x Hx1 Hx2. rewrite smallest_above_le in *. intros z Hz. simpl in Hz.
        unfold nf in *.
        destruct Hz as [Hz | Hz]; [subst|].
        -- unfold offset_fun.
           destruct freevar_eq_dec; [|tauto].
           destruct freevar_eq_dec; [subst; tauto|].
           destruct lt_dec; [|lia]. exfalso.
           apply smallest_above_gt in l. destruct l as (m & Hm1 & Hm2).
           rewrite in_map_iff in Hm2. destruct Hm2 as (w & <- & Hw).
           specialize (Hx2 (f w) ltac:(rewrite in_map_iff; exists w; rewrite in_app_iff; tauto)). lia.
        -- rewrite in_map_iff in Hz. destruct Hz as (z1 & <- & Hz).
           rewrite offset_fun_monotone; [apply Hx2; apply in_map; assumption|intros ->|intros ->; tauto].
           rewrite in_app_iff, Hfvc in Hz. destruct Hz as [Hz | Hz]; [tauto|].
           rewrite concat_In in Hz. destruct Hz as (l & Hz1 & Hz2).
           rewrite in_map_iff in Hz2. destruct Hz2 as (t2 & <- & Ht2).
           rewrite Forall_In in Hfvs. apply Hfvs in Ht2. rewrite Ht2 in Hz1. tauto.
(*      * intros x Hx1 Hx2. rewrite smallest_above_le in *. intros z Hz. simpl in Hz.
        unfold nf in *.
        admit. *)
    + intros x1 t1 y1 Hx1. assert (Hx2 := Hfl _ _ _ Hx1).
      unfold nf. rewrite offset_fun_monotone.
      * assumption.
      * intros ->. apply Hbcle in Hx1. simpl in Hx1. apply Hbb in Hx1. tauto.
      * intros ->. rewrite env_ei_fv_None in Hx1; [|rewrite Hfve; tauto]. congruence.
    + exists ((y, t) :: bodies). splits 7; simpl.
      * destruct freevar_eq_dec; congruence.
      * intros x ei Hx. apply check_lam_impl; [|eapply Hbcle; eassumption].
        destruct (env_find bodies y) eqn:Hy; [|reflexivity]; exfalso; apply H.
        specialize (Hbb _ _ Hy). tauto.
      * eapply check_lam_cont_cons; eassumption.
      * intros x t0 Hx. destruct freevar_eq_dec.
        -- injection Hx; intros; subst.
           splits 4; [tauto| |apply env_ei_fv_None; rewrite Hfve; assumption|rewrite Hfvc; prove_list_inc].
        (* rewrite in_fv_recL_inc, in_app_iff, Hfve, Hfvc. tauto. *)
           intros z Hz. unfold nf.
           unfold offset_fun.
           destruct freevar_eq_dec; [subst; rewrite Hfvc in Hz; tauto|].
           destruct freevar_eq_dec; [|tauto].
           destruct lt_dec; [assumption|]. rewrite <- Nat.le_ngt in n0.
           rewrite smallest_above_map_le in n0. apply n0 in Hz. lia.
        -- specialize (Hbb _ _ Hx). splits 4; try tauto; [|transitivity L; [tauto|prove_list_inc]].
           intros z Hz. unfold nf. apply offset_fun_monotone; [|congruence|apply Hbb; assumption].
           apply Hbb in Hz. intros Hyz; subst; tauto.
      * intros x t1 t2 Hx1 Hx2. destruct freevar_eq_dec.
        -- subst. exfalso.
           destruct (env_find bodies y) as [v|] eqn:Hyv.
           ** specialize (Hbb y v Hyv). tauto.
           ** specialize (HbW y Hyv). congruence.
        -- apply Hbbeta; assumption.
      * intros x Hx. destruct freevar_eq_dec; [congruence|].
        apply HbW. assumption.
      * intros x v Hxv. destruct (HW _ _ Hxv) as [HW1 HW2].
        splits 3; [rewrite HW1; prove_list_inc|tauto|].
        intros z Hz. unfold nf.
        apply offset_fun_monotone;
          [rewrite list_remove_correct, HW1 in Hz; intros Hyz; subst; tauto| |apply HW2; assumption].
        intros ->. destruct (env_find bodies x) eqn:Hx.
        -- apply Hbb in Hx. tauto.
        -- apply HbW in Hx. congruence.
  - rewrite Forall_cons_iff in *.
    pose (nf := offset_fun f x (smallest_above (map f (fv u)))).
    assert (Hewf2 : env_wf ((x, ELazy u) :: e) nf).
    {
      rewrite env_wf_cons_inv. simpl.
      splits 4.
      + eapply env_wf_change_f; [|eassumption].
        intros x1 y1 Hx1 Hy1 Hxy1. unfold nf.
        apply offset_fun_monotone; [| |assumption]; intros ->; rewrite Hfve in *; tauto.
      + apply env_ei_fv_None; rewrite Hfve; assumption.
      + tauto.
      + intros z Hz. unfold nf.
        unfold offset_fun.
        destruct freevar_eq_dec; [subst; apply Hfvs in Hz; tauto|].
        destruct freevar_eq_dec; [|tauto].
        destruct lt_dec; [assumption|]. rewrite <- Nat.le_ngt in n0.
        rewrite smallest_above_map_le in n0. apply n0 in Hz. lia.
    }
    exists nf. splits 14.
    + assumption.
    + rewrite substb_fv. simpl. rewrite Hfvc. prove_list_inc.
    + unfold env_ei_fv in *. simpl. rewrite Hfve. destruct Hfvs as [Hfvu Hfvs]; rewrite Hfvu.
      prove_list_inc.
    + eapply Forall_impl; [|apply Hfvs]. intros t2 H2; simpl in H2; rewrite H2; prove_list_inc.
    + apply lc_open_gen. rewrite <- lc_lam_body. assumption.
    + apply Hlcs.
    + eapply cont_wf_incl; [|eassumption]. prove_list_inc.
    + rewrite <- fill_hole with (t := t ^ x), <- stack_mctx_fill.
      eapply check_reds_read_in_ctx with (t1 := app (lam t) u); [|rewrite stack_mctx_fill, fill_hole| |eassumption].
      * eassumption.
      * eapply check_reds_cons_lazy; try eassumption; [rewrite Hfve; assumption|].
        destruct Hfvs as [Hfvs1 Hfvs2].
        rewrite read_stack_fv; [|eassumption]. simpl. rewrite Hfvs1, Hfvc, !in_app_iff. tauto.
      * exists (read_env2 e (t ^^ u)). rewrite read_env2_cons_lazy by (eapply env_ei_fv_None; rewrite Hfve; tauto).
        split.
        -- apply star_beta_read_env; [| |econstructor; constructor; [rewrite <- lc_lam_body|]; tauto].
           { rewrite unique_env_map_assq. apply unique_env_filter, uniquify_env_unique. }
           destruct Hewf as (Helc & Hunique & Hcycle). intros z v Hz; specialize (Helc z v).
           unfold rdei in Helc.
           rewrite env_find_map_assq, env_find_filter_unique, uniquify_env_same in * by apply uniquify_env_unique.
           destruct (env_find e z) as [[? | ? | ?]|]; simpl in *; try tauto; congruence.
        -- pick z \notin (env_ei_fv ((x, ELazy u) :: e) ++ env_ei_fv e ++ fv t ++ fv (read_env2 e t)) as Hz.
           rewrite !in_app_iff in Hz.
           rewrite substb_is_substf with (x := z) (u := fvar x) by tauto.
           rewrite read_env2_substb by apply Hewf.
           rewrite substb_is_substf with (x := z) (u := read_env2 e u) by tauto.
           replace (read_env2 e t ^ z) with (read_env2 e (t ^ z))
             by (rewrite read_env2_substb, read_env2_fvar_free; [reflexivity|apply env_ei_fv_None; tauto|apply Hewf]).
           assert (Hx : env_find e x = None) by (apply env_ei_fv_None; rewrite Hfve; assumption).
           apply read_env3_subst; [tauto|apply read_env3_cons_lazy; [assumption|eapply read_env3_read_env2_right; try apply Hewf; apply lc_open_gen, lc_lam_body; tauto]|].
           eapply read_env3_fvar_bound; [simpl; destruct freevar_eq_dec; [reflexivity|congruence]|].
           simpl; apply read_env3_cons_lazy; [assumption|].
           eapply read_env3_read_env2_right; try apply Hewf. tauto.
    (*  * intros z Hz.
        destruct (freevar_eq_dec x z); [subst; right; assumption|].
        rewrite in_fv_recL_cons in * by (apply env_ei_fv_None; rewrite Hfve; tauto); simpl in *.
        left. left.
        rewrite in_fv_recL_app, in_fv_recL_lam, in_app_iff.
        rewrite in_fv_recL_substb, !in_app_iff in Hz. destruct Hz as [[Hz1 | Hz1] | [_ Hz2]].
        -- tauto.
        -- exfalso. rewrite in_fv_recL_iff in Hz1. inversion Hz1; subst; simpl      specialize (Hu x ltac:(simpl; tauto)).
      replace (fv t) with (fv (lam t)) in Hz by reflexivity.
      eapply Hewf in Hz; [|rewrite env_find_rdei, H; reflexivity].
      lia.
 in *; [tauto|].
           destruct H0 as [-> | []]. rewrite env_ei_fv_None in H1; [congruence|]. rewrite Hfve. assumption.
        -- tauto. *)
    + tauto.
    + intros z ei Hz. destruct freevar_eq_dec.
      * injection Hz. intros; subst. simpl. tauto.
      * apply check_val_cons; [eapply Hcve; eassumption|].
        rewrite env_fv_find; [|eassumption]. rewrite Hfve. assumption.
    + eapply check_val_cont_cons; eassumption.
    + eapply check_cont_f_change; try eassumption.
      * intros x1 y1 Hx1 Hy1 Hxy1.
        unfold nf. apply offset_fun_monotone; [| |tauto]; intros ->; tauto.
      * intros z Hz1 Hz2. rewrite smallest_above_map_le in *. intros w Hw. simpl in Hw.
        unfold nf in *. rewrite substb_fv in Hw. rewrite !in_app_iff in Hw.
        destruct Hw as [[Hw | [Hw | []]] | Hw]; [|subst|].
        -- apply offset_fun_monotone; [| |apply Hz2; simpl; rewrite !in_app_iff; tauto]; intros ->; [|tauto].
           rewrite Hfvc in Hw. tauto.
        -- unfold offset_fun.
           destruct freevar_eq_dec; [|tauto].
           destruct freevar_eq_dec; [subst; tauto|].
           destruct lt_dec; [|lia]. exfalso.
           apply smallest_above_map_gt in l. destruct l as (p & Hp1 & Hp2).
           specialize (Hz2 p ltac:(simpl; rewrite !in_app_iff; tauto)). lia.
        -- rewrite offset_fun_monotone;
             [apply Hz2; simpl; rewrite !in_app_iff; tauto|intros ->|intros ->; tauto].
           eapply concat_incl in Hw; [|rewrite Forall_map; apply Hfvs]. tauto.
    + intros x1 t2 y1 Hx1. destruct freevar_eq_dec; [congruence|].
      unfold nf. apply offset_fun_monotone; [intros ->|congruence|eapply Hfl; eassumption].
      apply Hbcle in Hx1. simpl in Hx1. apply Hbb in Hx1. tauto.
    + exists bodies. splits 7; [tauto| |assumption| | |assumption|].
      * intros z ei Hz; destruct freevar_eq_dec; [|eapply Hbcle; eassumption].
        injection Hz; intros; subst. simpl. tauto.
      * intros z t0 Hz. specialize (Hbb _ _ Hz). splits 4; [tauto| | |].
        -- intros w Hw. unfold nf. apply offset_fun_monotone; [|intros ->; tauto|apply Hbb; assumption].
           apply Hbb in Hw; intros ->; tauto.
(*        -- rewrite in_fv_recL_cons by (apply env_ei_fv_None; rewrite Hfve; assumption).
           intros [Hz1 | [Hz1 Hz2]]; [tauto|].
           rewrite in_fv_recL_inc, in_app_iff, Hfve in Hz1.
           destruct Hz1 as [Hz1 | Hz1]; [|tauto].
           destruct Hbb as (Hbb1 & Hbb2 & Hbb3 & Hbb4); rewrite Hbb4 in Hz1; tauto. *)
        -- destruct freevar_eq_dec; [subst; tauto|tauto].
        -- transitivity L; [tauto|prove_list_inc].
      * intros z t1 t2 Ht1 Ht2.
        apply check_red_cons_lazy; [apply env_ei_fv_None; rewrite Hfve; assumption|].
        apply Hbbeta; assumption.
      * intros z v Hzv. destruct (HW _ _ Hzv) as [HW1 HW2].
        split; [rewrite HW1; prove_list_inc|].
        split; [apply closed_in_env_cons; rewrite HW1; tauto|].
        intros w Hw. unfold nf.
        apply offset_fun_monotone;
          [rewrite list_remove_correct, HW1 in Hw; intros ->; tauto| |apply HW2; assumption].
        intros ->. destruct (env_find bodies z) eqn:Hz.
        -- apply Hbb in Hz; tauto.
        -- apply HbW in Hz; congruence.
  - exists f. splits 14; try assumption.
    + rewrite closed_in_env_fvar. assumption.
    + exists bodies. tauto.
  - exists f. splits 14; try assumption.
    + apply env_fv_find in H. simpl in H. rewrite H. assumption.
    + apply (env_lc_find _ _ _ ltac:(apply Hewf) H).
    + rewrite <- fill_hole with (t := read_nfval v), <- stack_mctx_fill.
      eapply check_reds_read_in_ctx; [eassumption|rewrite stack_mctx_fill, fill_hole; eassumption| |eassumption].
      * exists (read_env2 e (fvar x)); split; [constructor|].
        erewrite read_env2_fvar_bound; [|apply Hewf|apply H|intros Hlazy; inversion Hlazy].
        simpl. eapply read_env3_read_env2_right; try apply Hewf.
        apply nfval_and_lam_lc.
(*      * intros z Hz. left. rewrite in_fv_recL_iff in *.
        eapply in_fv_rec_env; [|eassumption|]; simpl; tauto. *)
    + apply (Hcve _ _ H).
    + eapply check_cont_L_change; [|eassumption].
      simpl. rewrite map_app, smallest_above_app, Nat.max_comm. apply Nat.max_le_compat_l.
      rewrite smallest_above_map_le.
      intros y Hy. enough (f y < f x) by lia.
      eapply Hewf; [rewrite env_find_rdei, H; reflexivity|]. assumption.
(*      intros u Hu y Hy. rewrite in_app_iff in Hy.
      destruct Hy as [Hy | Hy]; [|apply Hu; simpl; tauto].
      specialize (Hu x ltac:(simpl; tauto)).
      eapply Hewf in Hy; [|rewrite env_find_rdei, H; reflexivity].
      lia. *)
    + exists bodies. tauto.
  - exists f. splits 14; try assumption; try solve [constructor].
    + apply env_fv_find in H. simpl in H. rewrite H. assumption.
    + apply (env_lc_find _ _ _ ltac:(apply Hewf) H).
    + constructor; try assumption. apply Hfvc. simpl; tauto.
    + econstructor.
      * eassumption.
      * eapply check_red_self; [|eassumption]. apply (env_lc_find _ _ _ ltac:(apply Hewf) H).
      * eapply acyclic_env_in_cycle in H; [|apply Hewf|apply Hewf]. assumption.
    + constructor.
      * rewrite smallest_above_map_le. intros y Hy. rewrite app_nil_r in Hy.
        eapply Hewf in Hy; [|rewrite env_find_rdei, H; reflexivity].
        assumption.
      * eapply check_cont_L_change; [|eassumption].
        rewrite app_nil_r. rewrite smallest_above_map_le.
        intros y Hy. rewrite smallest_above_map_gt.
        simpl in Hy; rewrite in_app_iff in Hy.
        destruct Hy as [Hy | [Hy | Hy]]; try solve [exists y; simpl; split; [lia|tauto]].
        exists x. split; [|simpl; tauto]. 
        eapply Hewf in Hy; [|rewrite env_find_rdei, H; reflexivity].
        lia.
    + exists bodies. tauto.
  - exists f. splits 14; try assumption; try solve [constructor].
    + apply env_fv_find in H. simpl in H. rewrite H. assumption.
    + apply (env_lc_find _ _ _ ltac:(apply Hewf) H).
    + rewrite <- fill_hole with (t := lam t), <- stack_mctx_fill.
      eapply check_reds_read_in_ctx; [eassumption|rewrite stack_mctx_fill, fill_hole; eassumption| |eassumption].
      exists (read_env2 e (fvar x)); split; [constructor|].
      erewrite read_env2_fvar_bound; [|apply Hewf|apply H|intros Hlazy; inversion Hlazy].
      simpl. eapply read_env3_read_env2_right; try apply Hewf.
      destruct Hewf as (Helc & Hunique & Hcycle).
      eapply Helc. unfold rdei. rewrite env_find_map_assq, H. reflexivity.
(*      * intros z Hz. left. rewrite in_fv_recL_iff in *.
        eapply in_fv_rec_env; [|eassumption|]; simpl; tauto. *)
    + eapply check_cont_L_change; [|eassumption].
      rewrite smallest_above_map_le.
      intros z Hz. rewrite smallest_above_map_gt.
      simpl in Hz; rewrite in_app_iff in Hz.
      destruct Hz as [Hz | [Hz | Hz]]; [| |exists z; simpl; split; [lia|tauto]].
      all: exists x; split; [|simpl; tauto].
      * subst. apply Hfl in H. lia.
      * replace (fv t) with (fv (lam t)) in Hz by reflexivity.
        eapply Hewf in Hz; [|rewrite env_find_rdei, H; reflexivity].
        lia.
    + exists bodies. split; [|tauto].
      specialize (Hbcle _ _ H). apply Hbcle.
  - rewrite Forall_cons_iff in *.
    exists f. splits 14; try tauto; try (constructor; tauto).
    + constructor.
      eapply check_cont_L_change; [|eassumption]. rewrite app_nil_r.
      rewrite !map_app, !smallest_above_app. lia.
    + exists bodies. tauto.
  - exists f. splits 14; try assumption.
    + rewrite substb_fv. simpl.
      rewrite list_inc_app_left; split; [assumption|].
      intros ? [<- | []]. specialize (Hbb _ _ Hbclc). tauto.
    + apply lc_open_gen; rewrite <- lc_lam_body; assumption.
    + constructor.
      * rewrite <- lc_lam_body. assumption.
      * assumption.
      * specialize (Hbb _ _ Hbclc). tauto.
      * assumption.
    + constructor.
      * specialize (Hbb _ _ Hbclc). tauto.
(*      * apply Hbb. assumption. *)
      * eapply check_red_self; [|eassumption]. apply lc_open_gen, lc_lam_body. assumption.
      * assumption.
    + constructor.
      eapply check_cont_L_change; [|eassumption]. rewrite !app_nil_r.
      rewrite smallest_above_map_le. intros y Hy.
      rewrite smallest_above_map_gt. exists y. split; [lia|].
      rewrite substb_fv in Hy. simpl in *. rewrite !in_app_iff in *; simpl in *. tauto.
    + exists bodies. tauto.
  - inversion Hkwf; inversion Hchk; subst.
    exists f. splits 14; try assumption.
    + rewrite list_inc_app_left; tauto.
    + constructor; assumption.
    + rewrite closed_in_env_app. tauto.
    + tauto.
    + inversion Hcf; subst.
      rewrite app_nil_r in *.
      eapply check_cont_L_change; [|eassumption].
      rewrite !map_app, !smallest_above_app; lia.
    + exists bodies. tauto.
  - inversion Hkwf; inversion Hchk; subst.
    exists f. splits 14; try assumption.
    + rewrite list_inc_app_left. split; [assumption|].
      rewrite fv_closeb. eapply HW; eassumption.
    + constructor; [assumption|]. apply nfval_and_lam_lc with (v := NFLam _ _).
    + erewrite <- fill_hole with (t := lam _), <- fill_empty with (t1 := read_nfval _), <- fill_app, <- stack_mctx_fill.
      eapply check_reds_read_in_ctx; [eassumption|rewrite stack_mctx_fill, fill_app, fill_empty, fill_hole; eassumption| |eassumption].
      * exists (lam (closeb 0 x (read_nfval_or_lam body))).
        split; [|apply closed_in_env_read_env3_2;
                 [apply lc_lam_body, closeb_body, nfval_and_lam_lc|
                  eapply closed_in_env_lam, closed_in_env_closeb, HW; eassumption]].
        rewrite read_env2_lam. apply star_beta_lam with (x := x).
        -- specialize (Hbb _ _ Hbclc). intros Hx. eapply read_env2_fv in Hx; [|apply Hewf].
           destruct Hx as (y & Hy1 & Hy2). enough (f y < f x) by lia.
           apply Hbb. assumption.
        -- apply closeb_var_free.
        -- rewrite open_close_var by (apply nfval_and_lam_lc).
           specialize (Hbbeta _ _ _ Hbclc H).
           destruct Hbbeta as (t3 & Ht3a & Ht3b).
           apply closed_in_env_read_env3 in Ht3b; [|eapply HW; eassumption].
           subst.
           rewrite read_env2_substb in Ht3a by apply Hewf.
           rewrite read_env2_fvar_free in Ht3a; [assumption|].
           specialize (Hbb _ _ Hbclc). tauto.
(*      * intros z Hz. left.
        specialize (Hbbeta _ _ _ Hbclc H).
        eapply acyclic_fv_recL_read_env; try apply Hewf.
        eapply check_red_fv_inc in Hbbeta; [|apply Hewf].
        admit. *)
    + rewrite closed_in_env_app. split; [tauto|].
      rewrite closed_in_env_lam. apply closed_in_env_closeb.
      specialize (HW _ _ H). tauto.
    + tauto.
    + inversion Hcf; subst. rewrite app_nil_r in *. eapply check_cont_L_change; [|eassumption].
      rewrite smallest_above_map_le.
      intros y Hy. rewrite smallest_above_map_gt.
      simpl in Hy; rewrite !in_app_iff in Hy.
      destruct Hy as [[Hy | Hy] | Hy]; try solve [exists y; simpl; split; [lia|rewrite !in_app_iff; tauto]].
      exists x. split; [|rewrite !in_app_iff; simpl; tauto].
      assert (Hy2 : y \in list_remove x (fv (read_nfval_or_lam body))).
      { rewrite list_remove_correct. split; [|intros ->; apply closeb_var_free in Hy; tauto].
        apply fv_closeb in Hy. assumption. }
      apply HW in Hy2; [|eassumption]. lia.
    + exists bodies. tauto.
  - inversion Hkwf; inversion Hchk; inversion Hcf; subst.
    exists f. splits 14; try assumption.
    + rewrite lc_lam_body. assumption.
    + eapply check_cont_L_change; [|eassumption]. rewrite !app_nil_r in *.
      simpl. rewrite map_app, smallest_above_app. lia.
    + exists bodies. splits 7.
      * tauto.
      * assumption.
      * tauto.
      * assumption.
      * intros y t1 t2 Ht1 Ht2.
        destruct freevar_eq_dec.
        -- subst. injection Ht2. intros; subst. simpl.
           assert (t = t1) by (destruct Hbclk; congruence). subst.
           assumption.
        -- apply Hbbeta; assumption.
      * intros y Hy. destruct freevar_eq_dec; [|apply HbW; assumption].
        subst. destruct Hbclk; congruence.
      * intros y w Hy. destruct freevar_eq_dec.
        -- subst. injection Hy; intros; subst. simpl.
           splits 3; try tauto.
           eapply check_red_fv_inc in H11; [|eassumption].
           rewrite closed_in_env_read_env in H11; [|rewrite closed_in_env_rdei; assumption].
           clear Hy.
           intros y Hy. rewrite list_remove_correct in Hy. destruct Hy as [Hy1 Hy2].
           rewrite H11 in Hy1.
           rewrite read_env_substb, read_env_fvar_free in Hy1; [|rewrite env_find_rdei, H10; reflexivity|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           rewrite substb_fv, in_app_iff in Hy1; simpl in Hy1; destruct Hy1 as [Hy1 | [Hy1 | []]]; [|congruence].
           eapply read_env_fv in Hy1; [|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           destruct Hy1 as (z & Hz1 & Hz2).
           specialize (Hbb x t ltac:(tauto)). assert (f z < f x) by (eapply Hbb; eassumption). lia.
        -- eapply HW; eassumption.
  - inversion Hkwf; inversion Hchk; inversion Hcf; subst.
    exists f. splits 14; try assumption.
    + rewrite lc_lam_body. assumption.
    + eapply check_cont_L_change; [|eassumption]. rewrite !app_nil_r in *.
      simpl. rewrite map_app, smallest_above_app. lia.
    + exists bodies. splits 7.
      * tauto.
      * assumption.
      * tauto.
      * assumption.
      * intros z t3 t4 Ht3 Ht4.
        destruct freevar_eq_dec.
        -- subst. injection Ht4. intros; subst. simpl.
           assert (t1 = t3) by (destruct Hbclk; congruence). subst.
           destruct H12 as (t5 & Ht5a & Ht5b).
           exists ((lam (closeb 0 y (read_nfval_or_lam body)))).
           split; [|apply closed_in_env_read_env3_2;
                 [apply lc_lam_body, closeb_body, nfval_and_lam_lc|
                  eapply closed_in_env_lam, closed_in_env_closeb, HW; eassumption]].
           eapply star_compose; [eassumption|].
           specialize (Hbbeta _ _ _ Hbclc H).
           destruct (Hbb _ _ Hbclc) as [Hy1 Hy2].
           eapply read_env3_read_env2_left in Ht5b; [|apply Hewf].
           destruct Hbbeta as (t6 & Ht6a & Ht6b).
           apply closed_in_env_read_env3 in Ht6b; [|eapply HW; eassumption]. subst.
           rewrite read_env2_substb in Ht6a by apply Hewf.
           rewrite read_env2_fvar_free in Ht6a by tauto.
           rewrite <- open_close_var with (t := read_nfval_or_lam body) (x := y) (k := 0) in Ht6a
             by apply nfval_and_lam_lc.
           apply star_beta_lam in Ht6a; [| |apply closeb_var_free].
           2: {
             intros Hy. eapply read_env2_fv in Hy; [|apply Hewf].
             destruct Hy as (z & Hz1 & Hz2). enough (f z < f y) by lia. eapply Hbb; eassumption.
           }
           rewrite read_env2_lam in Ht5b.
           eapply read_env3_beta in Ht6a; [|eassumption].
           destruct Ht6a as (t4 & Ht4a & Ht4b).
           eapply closed_in_env_read_env3 in Ht4a; [subst; assumption|].
           rewrite closed_in_env_lam. apply closed_in_env_closeb.
           specialize (HW _ _ H). tauto.
        -- apply Hbbeta; assumption.
      * intros z Hz. destruct freevar_eq_dec; [|apply HbW; assumption].
        subst. destruct Hbclk; congruence.
      * intros z w Hz. destruct freevar_eq_dec.
        -- subst. injection Hz; intros; subst. simpl.
           specialize (HW _ _ H).
           splits 3;
             [rewrite fv_closeb; eapply HW; eassumption|apply closed_in_env_lam, closed_in_env_closeb; tauto|].
           eapply check_red_fv_inc in H12; [|eassumption].
           clear Hz; intros z Hz. rewrite list_remove_correct in Hz.
           specialize (Hbbeta _ _ _ ltac:(eassumption) ltac:(eassumption)).
           eapply check_red_fv_inc in Hbbeta; [|eassumption].
           rewrite closed_in_env_read_env in Hbbeta; [|rewrite closed_in_env_rdei; tauto].
           rewrite closeb_fv_eq, list_remove_correct, Hbbeta in Hz.
           assert (Hy : env_find e y = None) by (eapply Hbb; eassumption).
           rewrite read_env_substb, read_env_fvar_free in Hz;
             [|rewrite env_find_rdei, Hy; reflexivity|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           rewrite substb_fv, in_app_iff in Hz. simpl in Hz.
           rewrite read_env_lam in H12; simpl in H12. rewrite H12 in Hz.
           rewrite read_env_substb, read_env_fvar_free in Hz;
             [|rewrite env_find_rdei, H11; reflexivity|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           rewrite substb_fv, in_app_iff in Hz. simpl in Hz.
           destruct Hz as [[[[Hz | Hz] | Hz] Hyz] Hxz]; [|tauto|tauto].
           eapply read_env_fv in Hz; [|rewrite unique_env_rdei; apply Hewf|apply Hewf].
           destruct Hz as (w & Hw1 & Hw2).
           specialize (Hbb x t1 ltac:(tauto)). assert (f w < f x) by (eapply Hbb; eassumption). lia.
        -- eapply HW; eassumption.
  - inversion Hkwf; inversion Hchk; inversion Hcf; subst. rewrite app_nil_r in *.
    assert (Hewf2 : env_wf (update_env e x (EVal v)) f) by (eapply env_wf_update; try rewrite <- smallest_above_map_le; eassumption).
    exists f. splits 14; try assumption.
    + rewrite env_ei_fv_update. rewrite list_inc_cons_left, list_inc_app_left. simpl. tauto.
    + erewrite <- fill_hole with (t := read_nfval _), <- stack_mctx_fill.
      eapply check_reds_read_in_ctx; [|rewrite stack_mctx_fill, fill_hole| |eassumption].
      * eassumption.
      * eapply check_reds_update_env; try eassumption.
        -- simpl. rewrite <- smallest_above_map_le. assumption.
        -- simpl. tauto.
        -- constructor.
        -- intros Hlazy; inversion Hlazy.
      * exists (read_env2 (update_env e x (EVal v)) (fvar x)). split; [constructor|].
        erewrite read_env2_fvar_bound; [|apply Hewf2|rewrite env_find_update_env; destruct freevar_eq_dec; [reflexivity|congruence]|intros Hlazy; inversion Hlazy].
        eapply read_env3_read_env2_right; try apply Hewf2. simpl. assumption.
(*       * intros z Hz. left. rewrite in_fv_recL_iff in *.
        apply in_fv_rec_env with (y := x) (t2 := EVal v);
          [simpl; tauto|rewrite env_find_update_env; destruct freevar_eq_dec; congruence|assumption]. *)
    + rewrite closed_in_env_update_env; [|congruence]. assumption.
    + intros z zi Hz. rewrite check_val_update_env; [|congruence].
      rewrite env_find_update_env in Hz; destruct freevar_eq_dec.
      * injection Hz; intros; subst. simpl. assumption.
      * eapply Hcve; eassumption.
    + apply check_val_cont_update_env; [|assumption]. congruence.
    + eapply check_cont_L_change; [|eassumption].
      simpl; rewrite !map_app, !smallest_above_app; lia.
    + intros x1 t y1 Hx1. rewrite env_find_update_env in Hx1.
      destruct freevar_eq_dec; [congruence|].
      eapply Hfl; eassumption.
    + exists bodies. splits 7.
      * tauto.
      * intros y ei H. rewrite env_find_update_env in H.
        destruct freevar_eq_dec; [injection H; intros; subst|eapply Hbcle; eassumption].
        simpl. tauto.
      * tauto.
      * intros z t Hz. specialize (Hbb _ _ Hz).
        splits 4; try tauto.
        rewrite env_find_update_env. destruct freevar_eq_dec; subst; [|tauto].
        destruct Hbb as (Hbb1 & Hbb2 & Hbb3 & Hbb4); congruence.
      * intros z t2 t3 Hz1 Hz2.
        eapply check_red_update_env; try eassumption; [|apply Hbbeta; assumption|constructor|intros Hlazy; inversion Hlazy].
        rewrite <- smallest_above_map_le. assumption.
      * assumption.
      * intros z t Hz. specialize (HW _ _ Hz). rewrite closed_in_env_update_env; [|congruence]. assumption.
  - inversion Hkwf; inversion Hchk; inversion Hcf; subst. rewrite app_nil_r in *.
    assert (Hewf2 : env_wf (update_env e x (ELam t y)) f)
      by (eapply env_wf_update; try eassumption; rewrite <- smallest_above_map_le; simpl in *; lia).
    exists f. splits 14; try assumption.
    + rewrite env_ei_fv_update. rewrite list_inc_cons_left, list_inc_app_left. simpl. tauto.
    + erewrite <- fill_hole with (t := lam _), <- stack_mctx_fill.
      eapply check_reds_read_in_ctx; [|rewrite stack_mctx_fill, fill_hole| |eassumption].
      * eassumption.
      * eapply check_reds_update_env; try eassumption.
        -- simpl. rewrite <- smallest_above_map_le. simpl in *; lia.
        -- simpl; tauto.
        -- constructor.
        -- intros Hlazy; inversion Hlazy.
      * exists (read_env2 (update_env e x (ELam t y)) (fvar x)). split; [constructor|].
        erewrite read_env2_fvar_bound; [|apply Hewf2|rewrite env_find_update_env; destruct freevar_eq_dec; [reflexivity|congruence]|intros Hlazy; inversion Hlazy].
        eapply read_env3_read_env2_right; try apply Hewf2; simpl; assumption.
(*      * intros z Hz. left. rewrite in_fv_recL_iff in *.
        apply in_fv_rec_env with (y := x) (t2 := ELam t y);
          [simpl; tauto|rewrite env_find_update_env; destruct freevar_eq_dec; congruence|assumption]. *)
    + intros z zi Hz. rewrite check_val_update_env; [|congruence].
      rewrite env_find_update_env in Hz; destruct freevar_eq_dec.
      * injection Hz; intros; subst. simpl. assumption.
      * eapply Hcve; eassumption.
    + apply check_val_cont_update_env; [|assumption]. congruence.
    + eapply check_cont_L_change; [|eassumption].
      simpl; rewrite !map_app, !smallest_above_app; simpl. lia.
    + intros x1 t2 y1 Hx1. rewrite env_find_update_env in Hx1.
      destruct freevar_eq_dec; [|eapply Hfl; eassumption]. injection Hx1. intros; subst.
      simpl in *. lia.
    + exists bodies. splits 7.
      * tauto.
      * intros z ei H. rewrite env_find_update_env in H.
        destruct freevar_eq_dec; [injection H; intros; subst|eapply Hbcle; eassumption].
        simpl. assumption.
      * tauto.
      * intros z t2 Hz. specialize (Hbb _ _ Hz).
        splits 4; try tauto.
        rewrite env_find_update_env. destruct freevar_eq_dec; subst; [|tauto].
        destruct Hbb as (Hbb1 & Hbb2 & Hbb3 & Hbb4); congruence.
      * intros z t2 t3 Hz1 Hz2.
        eapply check_red_update_env; try eassumption; [| |constructor|intros Hlazy; inversion Hlazy].
        -- simpl. rewrite <- smallest_above_map_le. simpl in *; lia.
        -- apply Hbbeta; assumption.
      * assumption.
      * intros z t2 Hz. specialize (HW _ _ Hz). rewrite closed_in_env_update_env; [|congruence]. assumption.
Qed.

Theorem init_wf :
  forall t, lc t ->
       wf_state {| st_code := ELazy t ; st_env := nil ; st_stack := nil ; st_cont := KNil ; st_lamnf := nil ; st_usedvars := fv t |}.
Proof.
  intros t Ht. exists (fun _ => 0). simpl. splits 14; try solve [tauto | constructor | intros; congruence].
  - splits 3; simpl.
    + intros x u Hxu. simpl in *. congruence.
    + constructor.
    + apply acyclic_env_nil.
  - unfold env_ei_fv. simpl. intros x Hx; simpl in *; tauto.
  - exists nil. simpl. splits 7; solve [tauto | intros; congruence].
Qed.

Definition is_st_nf st :=
  st_stack st = nil /\ st_cont st = KNil /\
  ((exists v, st_code st = EVal v) \/ (exists t v x, st_code st = ELam t x /\ env_find (st_lamnf st) x = Some v)).

Lemma red_not_blocked :
  forall st, lc (read_envitem (st_code st)) -> is_st_nf st \/ exists st2, red st st2.
Proof.
  intros st Hlc. destruct st as [t pi e K W L].
  destruct t as [v | t | body x].
  - destruct pi; [|right; eexists; constructor].
    destruct K.
    + left. unfold is_st_nf; simpl. splits 3; try reflexivity.
      left. exists v. reflexivity.
    + right; eexists; constructor.
    + right; eexists; constructor.
    + right; eexists; constructor.
  - destruct t.
    + simpl in Hlc. inversion Hlc.
    + destruct (env_find e f) as [[| |]|] eqn:Henv.
      * right; eexists; apply red_var_val; eassumption.
      * right; eexists; apply red_var_lazy; eassumption.
      * right; eexists; apply red_var_lam; eassumption.
      * right; eexists; apply red_var_open; assumption.
    + right. pick y \notin L.
      eexists; econstructor; eassumption.
    + right; eexists; constructor.
  - destruct pi; [|right; pick y \notin L; eexists; econstructor; eassumption].
    destruct K.
    + destruct (env_find W x) eqn:Henv.
      * left. unfold is_st_nf; simpl. splits 3; try reflexivity.
        right. repeat eexists. eassumption.
      * right. eexists. apply red_lam_deepen. assumption.
    + right; eexists. apply red_cont_update_lazy_lam.
    + right.
      destruct (env_find W x) eqn:HWx.
      * eexists; apply red_cont_update_lam_lam; eassumption.
      * eexists; apply red_lam_deepen; assumption.
    + right.
      destruct (env_find W x) eqn:HWx.
      * eexists; apply red_cont_app_lam; eassumption.
      * eexists; apply red_lam_deepen; assumption.
Qed.

Fixpoint read_cont t K :=
  match K with
  | KNil => t
  | KApp v pi K => read_cont (read_stack (app (read_nfval v) t) pi) K
  | KUpdateLam t1 x K => read_cont (lam t1) K
  | KUpdateLazy x pi K => read_cont (read_stack (fvar x) pi) K
  end.

Lemma read_stack_star_beta :
  forall e t1 t2 pi, unique_env e -> elc e -> Forall lc pi -> star beta (read_env e t1) (read_env e t2) -> star beta (read_env e (read_stack t1 pi)) (read_env e (read_stack t2 pi)).
Proof.
  intros e t1 t2 pi Hunique Hlc Hpi Hred. revert t1 t2 Hred; induction pi; intros t1 t2 Hred.
  - simpl. assumption.
  - simpl. rewrite Forall_cons_iff in Hpi. apply IHpi; [tauto|]. rewrite !read_env_app.
    eapply star_map_impl with (f := fun t => app t (read_env e a)); [|eassumption].
    intros x y H; apply beta_app_left; [assumption|].
    apply read_env_lc; tauto.
Qed.

Lemma read_cont_star_beta :
  forall e t1 t2 K L,
    unique_env e -> elc e -> cont_wf L K ->
    star beta (read_env e t1) (read_env e t2) -> star beta (read_env e (read_cont t1 K)) (read_env e (read_cont t2 K)).
Proof.
  intros e t1 t2 K L Hunique Helc Hwf Hred. revert L t1 t2 Hred Hwf; induction K; intros L t1 t2 Hred Hwf.
  - simpl. assumption.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. inversion Hwf; subst.
    eapply IHK; [|eassumption].
    apply read_stack_star_beta; try assumption.
    rewrite !read_env_app.
    eapply star_map_impl with (f := fun t => app _ t); [|eassumption].
    intros x y H; apply beta_app_right; [assumption|].
    apply read_env_lc; assumption.
Qed.

Global Instance rdei_Proper : Proper (env_same ==> env_same) rdei.
Proof.
  apply map_assq_env_Proper. reflexivity.
Qed.

Lemma read_update_env :
  forall f e x t1 t2 t,
    env_wf e f -> lc t -> env_find e x = Some t1 -> (forall y, y \in fv (read_envitem t2) -> f y < f x) ->
    star beta (read_env (rdei e) (read_envitem t1)) (read_env (rdei e) (read_envitem t2)) ->
    star beta (read_env (rdei e) t) (read_env (rdei (update_env e x t2)) t).
Proof.
  intros f e x t1 t2 t Hwf Hlc1 Hx Ht2.
  assert (Hwf2 := Hwf).
  eapply env_wf_move_to_front in Hwf2; [|eassumption]. destruct Hwf2 as (e2 & Heq & Hwf2).
  repeat (erewrite read_env_same with (env1 := rdei e); [|rewrite Heq; reflexivity|rewrite unique_env_rdei; apply Hwf|rewrite unique_env_rdei; apply Hwf2|apply Hwf]).
  erewrite <- read_env_same with (env2 := rdei (update_env e x t2)); [|rewrite Heq; reflexivity| | |].
  - intros Hred.
    simpl. destruct freevar_eq_dec; [|tauto]. simpl.
    apply star_beta_substf.
    + rewrite env_wf_cons_inv in Hwf2.
      apply read_env_lc; [rewrite unique_env_rdei; apply Hwf2|apply Hwf2|assumption].
    + rewrite env_wf_cons_inv in Hwf2.
      apply read_env_lc; [rewrite unique_env_rdei; apply Hwf2|apply Hwf2|tauto].
    + constructor.
    + simpl in Hred. rewrite !substf_fv in Hred; [assumption| |].
      * intros Hx2. rewrite env_wf_cons_inv in Hwf2.
        eapply read_env_fv in Hx2; [|rewrite unique_env_rdei; apply Hwf2|apply Hwf2].
        destruct Hx2 as (y & Hy1 & Hy2). apply Ht2 in Hy1. lia.
      * intros Hx2. rewrite env_wf_cons_inv in Hwf2.
        eapply read_env_fv in Hx2; [|rewrite unique_env_rdei; apply Hwf2|apply Hwf2].
        destruct Hx2 as (y & Hy1 & Hy2). apply Hwf2 in Hy1. lia.
  - rewrite unique_env_rdei. apply update_env_unique. apply Hwf2.
  - rewrite unique_env_rdei. apply update_env_unique. apply Hwf.
  - simpl. destruct freevar_eq_dec; [|tauto]. simpl.
    rewrite env_wf_cons_inv in Hwf2.
    rewrite acyclic_env_cons2; [split|]; [eassumption|apply Hwf2|]. rewrite env_find_rdei.
    destruct Hwf2 as (? & Hx2 & ?); rewrite Hx2; reflexivity.
Qed.

Definition st_read1 st := read_env (rdei (st_env st)) (read_cont (read_stack (read_envitem (st_code st)) (st_stack st)) (st_cont st)).

Theorem init_st_read1 :
  forall t, st_read1 {| st_code := ELazy t ; st_env := nil ; st_stack := nil ; st_cont := KNil ; st_lamnf := nil ; st_usedvars := fv t |} = t.
Proof.
  reflexivity.
Qed.


Lemma read_stack_substf_free :
  forall pi x t1 t2, Forall (fun t => x \notin fv t) pi -> read_stack t1 pi [ x := t2 ] = read_stack (t1 [ x := t2 ]) pi.
Proof.
  induction pi; intros x t1 t2 Hpi.
  - reflexivity.
  - simpl. rewrite Forall_cons_iff in Hpi. rewrite IHpi by tauto.
    f_equal. simpl. f_equal. apply substf_fv. tauto.
Qed.

Lemma read_cont_substf_free :
  forall K L x t1 t2, x \notin L -> cont_wf L K -> read_cont t1 K [ x := t2 ] = read_cont (t1 [ x := t2 ]) K.
Proof.
  induction K; intros L x t1 t2 Hx Hwf.
  - reflexivity.
  - simpl. inversion Hwf; subst.
    erewrite IHK by eassumption. erewrite read_stack_substf_free.
    + simpl. destruct freevar_eq_dec; [subst|]; tauto.
    + eapply Forall_impl; [|eassumption]. simpl; intros t Ht; rewrite Ht; assumption.
  - simpl. inversion Hwf; subst.
    erewrite IHK by eassumption. f_equal. simpl. f_equal.
    apply substf_fv. rewrite H3; assumption.
  - simpl. inversion Hwf; subst. erewrite IHK by eassumption. f_equal.
    erewrite read_stack_substf_free.
    + simpl. rewrite substf_fv; [|rewrite H4; assumption]. reflexivity.
    + eapply Forall_impl; [|eassumption]. simpl; intros t Ht; rewrite Ht; assumption.
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

Lemma read_stack_lc :
  forall pi t, lc t -> Forall lc pi -> lc (read_stack t pi).
Proof.
  induction pi; intros t Ht Hpi.
  - assumption.
  - rewrite Forall_cons_iff in Hpi. simpl. apply IHpi.
    + constructor; tauto.
    + tauto.
Qed.

Lemma read_cont_lc :
  forall K t L, lc t -> cont_wf L K -> lc (read_cont t K).
Proof.
  induction K; intros t2 L Ht2 HK.
  - assumption.
  - simpl. inversion HK; subst. eapply IHK; [|eassumption].
    apply read_stack_lc; [constructor|assumption].
  - simpl. inversion HK; subst. eapply IHK; [|eassumption].
    rewrite lc_lam_body. assumption.
  - simpl. inversion HK; subst. eapply IHK; [|eassumption].
    apply read_stack_lc; [constructor; assumption|assumption].
Qed.

Theorem red_beta2 :
  forall st t x body, wf_state st -> st_code st = ELam t x -> env_find (st_lamnf st) x = Some body ->
                 star beta (read_env (rdei (st_env st)) (lam t)) (lam (closeb 0 x (read_nfval_or_lam body))).
Proof.
  intros st t x body Hwf Hcode Hfind.
  destruct st as [code pi env K W L].
  destruct Hwf as (f & Hewf & Hfvc & Hfve & Hfvs & Hlcc & Hlcs & Hkwf & Hchk & Hcvc & Hcve & Hcvk & Hcf & Hfl & bodies & Hbclc & Hbcle & Hbclk & Hbb & Hbbeta & HbW & HW).
  subst; simpl in *; subst; simpl in *.
  specialize (Hbbeta _ _ _ Hbclc Hfind).
  destruct Hbbeta as (t3 & Ht3a & Ht3b).
  eapply read_env3_read_env in Ht3b; [|eassumption].
  eapply star_beta_read_env in Ht3a; [erewrite read_env_read_env2 in Ht3a| |];
    [|apply lc_open_gen, lc_lam_body; assumption|eassumption|rewrite unique_env_rdei; apply Hewf|apply Hewf].
  rewrite <- Ht3b in Ht3a.
  rewrite !read_env_lam.
  apply star_beta_lam with (x := x).
  - intros Hx. eapply read_env_fv in Hx; [|apply unique_env_rdei; apply Hewf|apply Hewf].
    destruct Hx as (y & Hy1 & Hy2).
    enough (f y < f x) by lia. eapply Hbb; eassumption.
  - apply closeb_var_free.
  - rewrite open_close_var by apply nfval_and_lam_lc.
    rewrite read_env_substb, read_env_fvar_free in Ht3a.
    + rewrite closed_in_env_read_env with (t := read_nfval_or_lam _) in Ht3a; [assumption|].
      rewrite closed_in_env_rdei; eapply HW; eassumption.
    + rewrite env_find_rdei. replace (env_find env x) with (@None envitem) by (symmetry; eapply Hbb; eassumption).
      reflexivity.
    + rewrite unique_env_rdei; apply Hewf.
    + apply Hewf.
Qed.

Theorem red_beta :
  forall st st2, wf_state st -> red st st2 -> star beta (st_read1 st) (st_read1 st2).
Proof.
  intros st st2 Hwf Hred.
  assert (Hwf2 := Hwf).
  destruct Hwf as (f & Hewf & Hfvc & Hfve & Hfvs & Hlcc & Hlcs & Hkwf & Hchk & Hcvc & Hcve & Hcvk & Hcf & Hfl & bodies & Hbclc & Hbcle & Hbclk & Hbb & Hbbeta & HbW & HW).
  inversion Hred; subst; unfold st_read1; simpl in *; try solve [constructor].
  - rewrite <- read_env_substf; [|rewrite Hfve; assumption].
    erewrite read_cont_substf_free by eassumption.
    eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    rewrite Forall_cons_iff in Hfvs. destruct Hfvs as [Hfvs1 Hfvs2].
    erewrite read_stack_substf_free
      by (eapply Forall_impl; [|eassumption]; simpl; intros t3 Ht3; rewrite Ht3; assumption).
    apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|rewrite Forall_cons_iff in Hlcs; tauto|].
    apply star_beta_read_env; [rewrite unique_env_rdei; apply Hewf|apply Hewf|].
    rewrite <- substb_is_substf by (rewrite Hfvc; assumption).
    econstructor; [|constructor]. constructor.
    + rewrite <- lc_lam_body. assumption.
    + rewrite Forall_cons_iff in Hlcs. tauto.
  - eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    erewrite read_env_fvar_bound.
    + constructor.
    + rewrite unique_env_rdei; apply Hewf.
    + apply Hewf.
    + rewrite env_find_rdei, H. reflexivity.
  - eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    erewrite read_env_fvar_bound.
    + constructor.
    + rewrite unique_env_rdei; apply Hewf.
    + apply Hewf.
    + rewrite env_find_rdei, H. reflexivity.
  - inversion Hkwf; subst.
    eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
    rewrite !read_env_app.
    eapply star_map_impl with (f := fun t => app _ t).
    + intros ? ? ?; apply beta_app_right; [eassumption|].
      apply read_env_lc; [rewrite unique_env_rdei; apply Hewf|apply Hewf|assumption].
    + rewrite read_env_lam with (t := closeb _ _ _).
      rewrite closed_in_env_read_env with (t := closeb _ _ _)
        by (apply closed_in_env_closeb; rewrite closed_in_env_rdei; eapply HW; eassumption).
      lazymatch goal with [ Hwf2 : wf_state ?st |- _ ] => pose (st2 := st) end.
      eapply red_beta2 with (st := st2); unfold st2; simpl; tauto.
  - inversion Hchk; inversion Hkwf; subst.
    assert (lc t1) by (apply check_red_lc_1 in H4; assumption).
    destruct H4 as (t3 & Ht3a & Ht3b). eapply read_env3_read_env in Ht3b; [|eassumption].
    eapply star_beta_read_env in Ht3a; [erewrite read_env_read_env2 in Ht3a| |];
      [|assumption|eassumption|rewrite unique_env_rdei; apply Hewf|apply Hewf].
    rewrite <- Ht3b in Ht3a.
    eapply star_compose; [|eapply read_update_env; try eassumption].
    + eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
      apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
      erewrite read_env_fvar_bound; [eassumption|rewrite unique_env_rdei; apply Hewf|apply Hewf|rewrite env_find_rdei; rewrite H3; reflexivity].
    + eapply read_cont_lc; [|eassumption]. apply read_stack_lc; assumption.
    + inversion Hcf; subst. rewrite <- smallest_above_map_le. simpl.
      rewrite app_nil_r in *. assumption.
  - inversion Hchk; inversion Hkwf; subst.
    assert (lc t1) by (apply check_red_lc_1 in H4; assumption).
    destruct H4 as (t3 & Ht3a & Ht3b). eapply read_env3_read_env in Ht3b; [|eassumption].
    eapply star_beta_read_env in Ht3a; [erewrite read_env_read_env2 in Ht3a| |];
      [|assumption|eassumption|rewrite unique_env_rdei; apply Hewf|apply Hewf].
    rewrite <- Ht3b in Ht3a.
    eapply star_compose; [|eapply read_update_env; try eassumption].
    + eapply read_cont_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
      apply read_stack_star_beta; [rewrite unique_env_rdei; apply Hewf|apply Hewf|eassumption|].
      erewrite read_env_fvar_bound; [eassumption|rewrite unique_env_rdei; apply Hewf|apply Hewf|rewrite env_find_rdei; rewrite H3; reflexivity].
    + eapply read_cont_lc; [|eassumption]. apply read_stack_lc; assumption.
    + inversion Hcf; subst. rewrite <- smallest_above_map_le. simpl.
      rewrite app_nil_r in *. simpl in H4. lia.
Qed.





(*)
Fixpoint readf t K :=
  match K with
  | KNil => 
  H5 : cont_wf L K
  t1 : term
Inductive readf (lamnf : list (freevar * nfval_or_lam)) (env : list (freevar * envitem)) : term -> cont -> term -> Prop :=
| readf_nil : forall t, readf lamnf env t KNil t
| readf_app : forall v pi K t1 t3,
    readf lamnf env (read_stack (app (read_nfval v) t1) pi) K t3 -> readf lamnf env t1 (KApp v pi K) t3
| readf_update_lam : forall t1 x K t2 t3,
    env_find lamnf x = None -> check_red env (lam t2) (lam (closeb 0 x t1)) ->
    readf lamnf env (lam t2) K t3 -> readf lamnf env t1 (KUpdateLam t2 x K) t3
| readf_update_lazy : forall x pi K t1 t2 t4,
    env_find env x = Some (ELazy t4) -> check_red env t4 t1 ->
    readf lamnf env (read_stack t1 pi) K t2 -> readf lamnf env t1 (KUpdateLazy x pi K) t2.

Definition check_lam f ei :=
  match ei with
  | ELam t x => t = f x
  | _ => True
  end.

Definition read_state st t2 :=
  (exists t3, readf (st_lamnf st) (st_env st) (read_stack (read_envitem (st_code st)) (st_stack st)) (st_cont st) t3 /\ t2 = read_env (rdei (st_env st)) t3)
  /\ (exists f, check_lam f (st_code st) /\ Forall (fun '(x, ei) => check_lam f ei) (st_env st) /\ forall x body, env_find (st_lamnf st) x = Some body -> star beta (read_env (rdei (st_env st)) (lam (f x))) (lam (closeb 0 x (read_nfval_or_lam body)))).
(*
Lemma read_stack_env_unique :
  forall env pi t1 t2 t3, read_stack_env env t1 pi t2 -> read_stack_env env t1 pi t3 -> t2 = t3.
Proof.
  intros env pi. induction pi; intros t1 t2 t3 H1 H2.
  - inversion H1; inversion H2; subst.
    reflexivity.
  - inversion H1; inversion H2; subst.
    assert (t4 = t8) by (eapply read_env_unique; eassumption). subst.
    eapply IHpi; eassumption.
Qed.

Lemma readf_unique :
  forall lamnf t K env t2 t3, readf lamnf t K env t2 -> readf lamnf t K env t3 -> t2 = t3.
Proof.
  intros lamnf t K env t2 t3 H. revert t3. induction H; intros t6 H6; inversion H6; subst.
  - eauto using read_env_unique.
  - apply IHreadf. assumption. (* assert (t2 = t4) by (eapply read_stack_env_unique; eassumption). subst; assumption. *)
  - apply IHreadf. assumption.
  - apply IHreadf. assumption. (* assert (t3 = t7) by (eapply read_stack_env_unique; eassumption). subst; assumption. *)
Qed.
 *)

Lemma readf_unique :
  forall lamnf t K env t2 t3, readf lamnf t K env t2 -> readf lamnf t K env t3 -> t2 = t3.
Proof.
  intros lamnf t K env t2 t3 H. revert t3. induction H; intros t6 H6; inversion H6; subst.
  - reflexivity.
  - apply IHreadf. assumption.
  - apply IHreadf. assumption.
  - apply IHreadf. assumption.
Qed.

Lemma split_left : forall (A B : Prop), A /\ (A -> B) -> A /\ B.
Proof.
  intros; tauto.
Qed.

Lemma split_right : forall (A B : Prop), B /\ (B -> A) -> A /\ B.
Proof.
  intros; tauto.
Qed.

Ltac split_left := apply split_left; split; [|intro].
Ltac split_right := apply split_right; split; [|intro].
Tactic Notation "split_left" "as" ident(H) := apply split_left; split; [|intro H].
Tactic Notation "split_right" "as" ident(H) := apply split_right; split; [|intro H].

Lemma red_beta :
  forall st st2 t, read_state st t -> red st st2 -> exists t2, read_state st2 t2 /\ star beta t t2.
Proof.
  intros st st2 t Hread1 Hred.
  inversion Hred; subst; unfold read_state in *; simpl in *.
  - exists t. split; [assumption|constructor].
  - exists t. split; [|constructor].
    split; [apply Hread1|].
    destruct Hread1 as [Hreadf1 [f Hf]].
    exists (fun x => if freevar_eq_dec x y then t0 else f x).
    split; [|split].
    + destruct freevar_eq_dec; tauto.
    + admit.
    + admit.
  - admit.
  - exists t. split; [assumption|constructor].
  - exists t; split; [|constructor].
    split; [|apply Hread1].
    admit.
  - exists t. split; [|constructor].
    split; [|apply Hread1].
    admit.
    (* econstructor.
    + eassumption.
    + eapply check_red_self. admit.
    + *)
  - exists t. split; [|constructor].
    destruct Hread1 as [Hreadf1 [f Hf]].
    assert (t0 = f y) by admit.
    split; [|exists f; tauto].
    admit.
  - exists t. split; [|constructor].
    split; [|apply Hread1].
    destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] Hf].
    exists t3. split; [|assumption].
    constructor. apply Hreadf1.
  - exists t. split; [|constructor].
    destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    split; [|exists f; tauto].
    exists t3; split; [|assumption].
    econstructor.
    + assumption.
    + rewrite close_open by admit. apply check_red_self; admit.
    + assumption.
  - exists t. split; [|constructor].
    destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    split; [exists t3; split; [assumption|reflexivity]|].
    exists f. tauto.
  - destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    admit.
  - destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    exists (read_env (rdei e) t3). split; [|constructor].
    assert (t0 = f x) by admit.
    split.
    + exists t3. split; [|reflexivity]. admit.
    + exists f.
      split; [assumption|].
      split; [tauto|].
      intros x1 body1.
      destruct freevar_eq_dec.
      * intro Hbody1; injection Hbody1; intro; subst. simpl.
        unfold check_red in H5.
        admit.
      * apply Hf.
  - destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    exists (read_env (rdei e) t3). split; [|constructor].
    assert (t1 = f x) by admit.
    split.
    + exists t3. split; [|reflexivity]. admit.
    + exists f.
      split; [assumption|].
      split; [tauto|].
      intros x1 body1.
      destruct freevar_eq_dec.
      * intros Hbody1; injection Hbody1; intro; subst.
        destruct Hf as (Hf1 & Hf2 & Hf3); subst.
        specialize (Hf3 y body0 H).
        apply star_compose with (y := lam (closeb 0 x (read_env (rdei e) (lam (f y)))));
          [|apply star_beta_lam with (x := x); try apply closeb_var_free; try rewrite !open_close_var; [assumption| |]].
        unfold check_red in H6.
        all: admit.
      * apply Hf.
  - destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    exists (read_env (rdei (update_env e x (EVal v))) t3).
    split; [split|].
    + exists t3. split; [|reflexivity]. admit.
    + exists f. admit.
    + admit.
  - destruct Hread1 as [[t3 [Hreadf1 Hreadenv1]] [f Hf]].
    inversion Hreadf1; subst.
    exists (read_env (rdei (update_env e x (ELam t0 y))) t3).
    split; [split|].
    + exists t3. split; [|reflexivity]. admit.
    + exists f. split; [tauto|]. admit.
    + admit.

    admit.
    (* exists t. split; [assumption|constructor]. *)








(* gterm *)

Inductive env_value :=
| Env_term : term -> env_value
| Env_lam : term -> freevar -> term -> env_value.

Definition gterm := (term * list (freevar * env_value))%type.



Inductive elc : env_value -> Prop :=
| elc_term : forall t, lc t -> elc (Env_term t)
| elc_lam : forall x t1 t2, body t1 -> lc t2 -> elc (Env_lam t1 x t2).

Definition efv t :=
  match t with
  | Env_term t => fv t
  | Env_lam t1 x t2 => fv t1 ++ x :: fv t2
  end.

Fixpoint gterm_env_fv (e : list (freevar * env_value)) :=
  match e with
  | nil => nil
  | (x, t) :: e => x :: efv t ++ gterm_env_fv e
  end.

Definition gterm_fv (t : gterm) := fv (fst t) ++ gterm_env_fv (snd t).

Ltac prove_list_inc ::= (let x := fresh "x" in intros x; unfold gterm_fv; simpl; try repeat (rewrite in_app_iff; simpl); tauto).

Definition efv_read1 t :=
  match t with
  | Env_term t => t
  | Env_lam t1 x t2 => lam t1
  end.

(*
Definition efv_read2 t :=
  match t with
  | Env_term t => t
  | Env_lam t1 x t2 => lam t2
  end.
 *)

Fixpoint gterm_read1 t (e : list (freevar * env_value)) :=
  match e with
  | nil => t
  | (x, t1) :: e => gterm_read1 (t [ x := efv_read1 t1 ]) e
  end.

(*
Fixpoint gterm_read2 t (e : list (freevar * env_value)) :=
  match e with
  | nil => t
  | (x, t1) :: e => gterm_read2 (t [ x := efv_read2 t1 ]) e
  end.

Fixpoint gterm_reada t (e : list (freevar * env_value)) :=
  match e with
  | nil => t
  | (x, Env_lam t1 t2) :: e => gterm_reada (t [ x := lam t1 ]) e
  | (x, Env_term (fvar y)) :: e => gterm_reada (t [ x := fvar y ]) e
  | (x, Env_term _) :: e => gterm_reada t e
  end.
 *)

Fixpoint gterm_reade L t e :=
  match e with
  | nil => t
  | (x, t1) :: e =>
    if in_dec freevar_eq_dec x L then
      gterm_reade L t e
    else
      gterm_reade L (t [ x := efv_read1 t1 ]) e
  end.

Lemma gterm_read1_app :
  forall e t1 t2, gterm_read1 (app t1 t2) e = app (gterm_read1 t1 e) (gterm_read1 t2 e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

(*
Lemma gterm_read2_app :
  forall e t1 t2, gterm_read2 (app t1 t2) e = app (gterm_read2 t1 e) (gterm_read2 t2 e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

Lemma gterm_reada_app :
  forall e t1 t2, gterm_reada (app t1 t2) e = app (gterm_reada t1 e) (gterm_reada t2 e).
Proof.
  induction e as [|[x [t|t1 t2]] e]; intros; simpl in *; auto; destruct t; auto.
Qed.
 *)

Lemma gterm_reade_app :
  forall L e t1 t2, gterm_reade L (app t1 t2) e = app (gterm_reade L t1 e) (gterm_reade L t2 e).
Proof.
  induction e as [|[x [t|t1 t2]] e]; intros; simpl in *; try destruct in_dec; auto; destruct t; auto.
Qed.

Lemma gterm_read1_lam :
  forall e t, gterm_read1 (lam t) e = lam (gterm_read1 t e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

(*
Lemma gterm_read2_lam :
  forall e t, gterm_read2 (lam t) e = lam (gterm_read2 t e).
Proof.
  induction e as [|[x t] e]; intros; simpl in *; auto.
Qed.

Lemma gterm_reada_lam :
  forall e t, gterm_reada (lam t) e = lam (gterm_reada t e).
Proof.
  induction e as [|[x [t|t1 t2]] e]; intros; simpl in *; auto; destruct t; auto.
Qed.
 *)

Lemma gterm_reade_lam :
  forall L e t, gterm_reade L (lam t) e = lam (gterm_reade L t e).
Proof.
  induction e as [|[x [t|t1 t2]] e]; intros; simpl in *; try destruct in_dec; auto; destruct t; auto.
Qed.



Lemma substf_lc2 :
  forall t x u, lc (t [ x := u ]) -> lc t.
Proof.
Admitted.


Fixpoint gterm_env_find x (e : list (freevar * env_value)) :=
  match e with
  | nil => None
  | (y, t) :: e => if freevar_eq_dec x y then Some t else gterm_env_find x e
  end.

Lemma gterm_env_find_fv :
  forall e x t, gterm_env_find x e = Some t -> list_inc (efv t) (gterm_env_fv e).
Proof.
  induction e as [|[x u] e]; intros; simpl in *.
  - congruence.
  - destruct freevar_eq_dec; simpl in *.
    + replace u with t by congruence. prove_list_inc.
    + eapply list_inc_trans; [eapply IHe; apply H|]. prove_list_inc.
Qed.


Inductive gterm_redt : list freevar -> gterm -> gterm -> Prop :=
| gterm_redt_app1 : forall L t1 t2 t3 e1 e2,
    gterm_redt L (t1, e1) (t2, e2) -> gterm_redt L (app t1 t3, e1) (app t2 t3, e2)
| gterm_redt_app2 : forall L t1 t2 t3 e1 e2,
    gterm_redt L (t1, e1) (t2, e2) -> gterm_redt L (app t3 t1, e1) (app t3 t2, e2)
| gterm_redt_redex : forall L t1 t2 e x,
    x \notin L ->
    gterm_redt L (app (lam t1) t2, e) (t1 ^ x, (x, Env_term t2) :: e)
| gterm_redt_var_var : forall L e x y,
    gterm_env_find x e = Some (Env_term (fvar y)) -> gterm_redt L (fvar x, e) (fvar y, e)
| gterm_redt_var_lam : forall L e x y t1 t2,
    gterm_env_find x e = Some (Env_lam t1 y t2) -> gterm_redt L (fvar x, e) (lam t1, e)
.

Inductive gterm_red_env : list freevar -> list (freevar * env_value) -> list (freevar * env_value) -> Prop :=
| gterm_red_env_term : forall L t1 t2 e1 e2 x,
    gterm_redt L (t1, e1) (t2, e2) ->
    gterm_red_env L ((x, Env_term t1) :: e1) ((x, Env_term t2) :: e2)
| gterm_red_env_lam : forall L t1 t2 t3 e1 e2 x y,
    gterm_redt L (t1, e1) (t2, e2) ->
    gterm_red_env L ((x, Env_lam t3 y t1) :: e1) ((x, Env_lam t3 y t2) :: e2)
| gterm_red_env_promote_lam : forall L t1 e x y,
    y \notin L ->
    gterm_red_env L ((x, Env_term (lam t1)) :: e) ((x, Env_lam t1 y (t1 ^ y)) :: e)
| gterm_red_env_cons :
    forall L u e1 e2, gterm_red_env L e1 e2 -> gterm_red_env L (u :: e1) (u :: e2)
.

Inductive gterm_red : list freevar -> gterm -> gterm -> Prop :=
| gterm_red_redt : forall L t1 t2 e1 e2, gterm_redt L (t1, e1) (t2, e2) -> gterm_red L (t1, e1) (t2, e2)
| gterm_red_redenv : forall L t e1 e2, gterm_red_env L e1 e2 -> gterm_red L (t, e1) (t, e2)
.

Lemma gterm_inc_redt :
  forall t1 t2 L1, gterm_redt L1 t1 t2 -> forall L2, list_inc L2 L1 -> gterm_redt L2 t1 t2.
Proof.
  intros t1 t2 L1 Hred. induction Hred.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; constructor; auto.
  - intros; econstructor; eauto.
Qed.


Lemma gterm_inc_red :
  forall t1 t2 L1, gterm_red L1 t1 t2 -> forall L2, list_inc L2 L1 -> gterm_red L2 t1 t2.
Proof.
  intros t1 t2 L1 Hred.
  induction Hred; intros; econstructor; eauto using gterm_inc_redt.
  admit.
Admitted.

Definition disjoint (L1 L2 : list freevar) := forall x1 x2, In x1 L1 -> In x2 L2 -> x1 <> x2.

Definition gterm_red1 L t1 t2 := gterm_red (L ++ gterm_fv t1) t1 t2.


Inductive gterm_env_wf : list freevar -> list (freevar * env_value) -> Prop :=
| gterm_env_wf_nil : forall L, gterm_env_wf L nil
| gterm_env_wf_cons_term :
    forall x t e L,
      gterm_env_wf (x :: fv t ++ L) e ->
      lc t -> x \notin (fv t ++ gterm_env_fv e) ->
      gterm_env_wf L ((x, Env_term t) :: e)
| gterm_env_wf_cons_lam :
    forall x y t1 t2 e L,
      gterm_env_wf (x :: fv t1 ++ y :: fv t2 ++ L) e ->
      body t1 -> lc t2 -> x \notin (fv t1 ++ y :: fv t2 ++ gterm_env_fv e) -> y \notin (fv t1 ++ L) ->
      gterm_env_wf L ((x, Env_lam t1 y t2) :: e).

Lemma gterm_env_wf_inv_term :
  forall {x t e L}, gterm_env_wf L ((x, Env_term t) :: e) ->
             gterm_env_wf (x :: fv t ++ L) e /\ lc t /\
             x \notin (fv t ++ gterm_env_fv e).
Proof.
  intros x t e L H. inversion H; tauto.
Qed.

Lemma gterm_env_wf_inv_lam :
  forall {x t1 y t2 e L}, gterm_env_wf L ((x, Env_lam t1 y t2) :: e) ->
             gterm_env_wf (x :: fv t1 ++ y :: fv t2 ++ L) e /\ body t1 /\ lc t2 /\
             x \notin (fv t1 ++ y :: fv t2 ++ gterm_env_fv e) /\ y \notin (fv t1 ++ L).
Proof.
  intros x t1 y t2 e L H. inversion H; tauto.
Qed.

Lemma gterm_env_wf_inv_common :
  forall {x t e L}, gterm_env_wf L ((x, t) :: e) ->
             gterm_env_wf (x :: efv t ++ L) e /\ elc t /\
             x \notin (efv t ++ gterm_env_fv e).
Proof.
  intros x t e L H.
  destruct t.
  - inversion H; subst; simpl in *. repeat (split; try tauto). constructor. assumption.
  - inversion H; subst; simpl in *. repeat (split; try tauto).
    + rewrite <- app_assoc; simpl. assumption.
    + constructor; assumption.
    + rewrite <- app_assoc; simpl. assumption.
Qed.

Definition gterm_wf L (t : gterm) := lc (fst t) /\ gterm_env_wf L (snd t).

Lemma gterm_read1_wf_lc_rec :
  forall e t L, lc (gterm_read1 t e) -> gterm_env_wf L e -> lc t.
Proof.
  induction e as [|[x v] e]; intros t L Hlc He; simpl in *.
  - tauto.
  - apply gterm_env_wf_inv_common in He.
    specialize (IHe _ (x :: efv v ++ L) Hlc ltac:(tauto)).
    apply substf_lc2 in IHe. assumption.
Qed.

Lemma gterm_reade_wf_lc_rec :
  forall e t L1 L2, lc (gterm_reade L1 t e) -> gterm_env_wf L2 e -> lc t.
Proof.
  induction e as [|[x v] e]; intros t L1 L2 Hlc He; simpl in *.
  - tauto.
  - apply gterm_env_wf_inv_common in He.
    destruct (in_dec freevar_eq_dec).
    + eapply IHe; intuition eassumption.
    + destruct v; specialize (IHe _ _ _ Hlc ltac:(apply He));
        apply substf_lc2 in IHe; assumption.
Qed.


Lemma gterm_read1_substb :
  forall e t k u L, gterm_env_wf L e -> gterm_read1 (substb k u t) e = substb k (gterm_read1 u e) (gterm_read1 t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - erewrite substb_substf, IHe.
    + reflexivity.
    + eapply gterm_env_wf_inv_common; eassumption.
    + apply gterm_env_wf_inv_common in H.
      destruct H as (H1 & H2 & H3); inversion H2; subst; simpl in *.
      * assumption.
      * apply lc_lam_body. assumption.
Qed.

Lemma gterm_reade_substb :
  forall e t k u L1 L2, gterm_env_wf L2 e -> gterm_reade L1 (substb k u t) e = substb k (gterm_reade L1 u e) (gterm_reade L1 t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - destruct in_dec.
    + eapply IHe. eapply gterm_env_wf_inv_common; eassumption.
    + erewrite substb_substf, IHe.
      * reflexivity.
      * eapply gterm_env_wf_inv_common; eassumption.
      * apply gterm_env_wf_inv_common in H.
        destruct H as (H1 & H2 & H3); inversion H2; subst; simpl in *.
        -- assumption.
        -- apply lc_lam_body. assumption.
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

Lemma gterm_read1_substf :
  forall e x t u, x \notin gterm_env_fv e -> gterm_read1 (substf x u t) e = substf x (gterm_read1 u e) (gterm_read1 t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - rewrite in_app_iff in *. rewrite substf_substf, IHe.
    + reflexivity.
    + tauto.
    + firstorder congruence.
    + destruct v; simpl in *.
      * tauto.
      * rewrite in_app_iff in *; tauto.
Qed.

Lemma gterm_reade_substf :
  forall e x t u L, x \notin gterm_env_fv e -> gterm_reade L (substf x u t) e = substf x (gterm_reade L u e) (gterm_reade L t e).
Proof.
  induction e as [|[x v] e]; intros; simpl in *.
  - reflexivity.
  - rewrite in_app_iff in *. destruct in_dec.
    + rewrite IHe by tauto. reflexivity.
    + rewrite substf_substf, IHe.
      * reflexivity.
      * tauto.
      * firstorder congruence.
      * destruct v; simpl in *.
        -- tauto.
        -- rewrite in_app_iff in *; tauto.
Qed.

Lemma gterm_redt_env_wf :
  forall t1 t2 L Lwf, gterm_redt L t1 t2 -> gterm_fv t1 \subseteq L -> lc (fst t1) -> gterm_env_wf Lwf (snd t1) -> lc (fst t2) /\ gterm_env_wf Lwf (snd t2).
Proof.
  intros t1 t2 L Lwf H. induction H.
  - intros HL Hlc Hwf; simpl in *. inversion Hlc; subst.
    assert (gterm_fv (t1, e1) \subseteq L) by (rewrite <- HL; simpl in *; prove_list_inc).
    split; [constructor|]; tauto.
  - intros HL Hlc Hwf; simpl in *; inversion Hlc; subst.
    assert (gterm_fv (t1, e1) \subseteq L) by (rewrite <- HL; simpl in *; prove_list_inc).
    split; [constructor|]; tauto.
  - intros HL Hlc Hwf; simpl in *. inversion Hlc; subst.
    split; [|constructor].
    + apply lc_open_gen. apply lc_lam_body. assumption.
    + admit.
    + assumption.
    + rewrite <- HL in H. unfold gterm_fv in H; simpl in *. rewrite !in_app_iff in *; tauto.
  - intros HL Hlc Hwf; simpl in *. split; [constructor|assumption].
  - intros HL Hlc Hwf; simpl in *. split; [|assumption].
Admitted.

(*
Lemma gterm_read1_env_red :
  forall L t1 t2, gterm_red L t1 t2 -> forall t3, list_inc (fv t3) L -> gterm_read1 t3 (snd t1) = gterm_read1 t3 (snd t2).
Proof.
  intros L t1 t2 H. induction H; intros t4 HL; simpl in *.
  - rewrite !gterm_read1_substf. apply IHgterm_red.
*)


Lemma gterm_read1_env_redt :
  forall L t1 t2, gterm_redt L t1 t2 -> forall t3, list_inc (fv t3) L -> gterm_read1 t3 (snd t1) = gterm_read1 t3 (snd t2).
Proof.
  intros L t1 t2 H. induction H; intros t HL; simpl in *; auto.
  rewrite substf_fv; [reflexivity|].
  unfold list_inc in *; firstorder.
Qed.

Lemma gterm_reade_env_redt :
  forall L1 L2 t1 t2, gterm_redt L1 t1 t2 -> forall t3, list_inc (fv t3) L1 -> gterm_reade L2 t3 (snd t1) = gterm_reade L2 t3 (snd t2).
Proof.
  intros L1 L2 t1 t2 H. induction H; intros t HL; simpl in *; auto.
  destruct in_dec.
  - reflexivity.
  - rewrite substf_fv; [reflexivity|].
    unfold list_inc in *; firstorder.
Qed.


Lemma lc_app_inv : forall {t1 t2}, lc (app t1 t2) -> lc t1 /\ lc t2.
Proof.
  intros t1 t2 H; inversion H; auto.
Qed.






Lemma gterm_read1_redt_2 :
  forall L1 L2 t1 t2, gterm_redt L1 t1 t2 -> gterm_wf L2 t1 -> gterm_fv t1 \subseteq L1 -> star beta (gterm_read1 (fst t1) (snd t2)) (gterm_read1 (fst t2) (snd t2)).
Proof.
  intros L1 L2 t1 t2 H. induction H; simpl in *; intros Hwf HL.
  - rewrite !gterm_read1_app.
    eapply star_map_impl with (f := fun t => app t _).
    + intros; constructor; [eassumption|].
      admit.
    + apply IHgterm_redt.
      * destruct Hwf as [Hwft Hwfe]; split; [inversion Hwft|]; simpl in *; subst; assumption.
      * unfold gterm_fv in *; simpl in *.
        intros x; specialize (HL x); rewrite !in_app_iff in *; tauto.
  - rewrite !gterm_read1_app.
    eapply star_map_impl with (f := fun t => app _ t).
    + intros; constructor; [eassumption|].
      admit.
    + apply IHgterm_redt.
      * destruct Hwf as [Hwft Hwfe]; split; [inversion Hwft|]; simpl in *; subst; assumption.
      * unfold gterm_fv in *; simpl in *.
        intros x; specialize (HL x); rewrite !in_app_iff in *; tauto.
  - rewrite <- substb_is_substf by (intros Hx; apply H; apply HL; unfold gterm_fv; simpl; rewrite !in_app_iff; tauto).
    rewrite !substf_fv by (intros Hx; apply H; apply HL; unfold gterm_fv; simpl; rewrite !in_app_iff; tauto).
    (*
    induction e as [|[y u] e].
    + simpl. econstructor; [|constructor].
      destruct Hwf as [Hwft Hwfe]; simpl in *.
      destruct (lc_app_inv Hwft) as [Hwft1 Hwft2].
      constructor; [rewrite <- lc_lam_body|]; assumption.
    + simpl. apply star_beta_substf. *)
    admit.
  - admit.
  - admit.
Admitted.


Lemma fv_efv_read1 :
  forall t, fv (efv_read1 t) \subseteq efv t.
Proof.
  intros t. destruct t.
  - simpl. reflexivity.
  - simpl. prove_list_inc.
Qed.

Lemma gterm_read1_red_env_1 :
  forall L1 e1 e2, gterm_red_env L1 e1 e2 -> forall L2, gterm_env_wf L2 e1 -> gterm_env_fv e1 \subseteq L1 -> (forall t3, fv t3 \subseteq L1 -> star beta (gterm_read1 t3 e1) (gterm_read1 t3 e2)).
Proof.
  intros L1 t1 t2 H. induction H; intros L2 Hwf HL t4 Hinc; simpl in *.
  - rewrite !gterm_read1_substf.
    + apply star_beta_substf.
      * admit.
      * admit.
      * rewrite (gterm_read1_env_redt _ _ _ H) by assumption. simpl.
        constructor.
      * rewrite (gterm_read1_env_redt _ _ _ H) by (rewrite <- HL; prove_list_inc). simpl.
        eapply (gterm_read1_redt_2 _ _ _ _ H).
        -- apply gterm_env_wf_inv_term in Hwf. split; simpl; apply Hwf.
        -- eapply list_inc_trans; [|apply HL]. prove_list_inc.
    + admit.
    + inversion Hwf; subst. rewrite in_app_iff in *. tauto.
  - rewrite (gterm_read1_env_redt _ _ _ H); [constructor|].
    rewrite fv_substf, list_inc_app_left. simpl.
    split; [assumption|].
    rewrite <- HL. prove_list_inc.
  - constructor.
  - destruct u as [x t]. simpl.
    assert (Hwfi := gterm_env_wf_inv_common Hwf).
    apply (IHgterm_red_env _ ltac:(apply Hwfi)).
    + eapply list_inc_trans; [|apply HL]. prove_list_inc.
    + rewrite fv_substf, fv_efv_read1, list_inc_app_left.
      split; [assumption|rewrite <- HL; prove_list_inc].
Admitted.



Inductive env_value_varlam : env_value -> Prop :=
| env_value_varlam_var : forall x, env_value_varlam (Env_term (fvar x))
| env_value_varlam_lam : forall x t1 t2, env_value_varlam (Env_lam t1 x t2).

Lemma env_value_varlam_dec :
  forall u, { env_value_varlam u } + { ~ env_value_varlam u }.
Proof.
  intros u. destruct u as [t | ?].
  - destruct t; (left; constructor) || (right; intro H; inversion H).
  - left. constructor.
Qed.

Definition free_in_rec x t e := forall L, x \notin fv (gterm_reade L t e).

Definition invariant1 L e t :=
  forall z u, (z, u) \in e ->
    (env_value_varlam u /\ z \notin L) \/ (~ env_value_varlam u /\ (z \in L \/ free_in_rec z t e)).

Lemma gterm_reade_free :
  forall L t e x u, x \notin fv t -> gterm_reade L t ((x, u) :: e) = gterm_reade L t e.
Proof.
  intros L t e x u Hx. simpl.
  destruct in_dec.
  - reflexivity.
  - rewrite substf_fv; [reflexivity | assumption].
Qed.

Lemma gterm_reade_fv :
  forall L e t, fv (gterm_reade L t e) \subseteq gterm_fv (t, e).
Proof.
  induction e as [|[x u] e].
  - intros. unfold gterm_fv. simpl.
    rewrite app_nil_r. reflexivity.
  - intros. unfold gterm_fv in *. simpl in *.
    destruct in_dec.
    + rewrite IHe. prove_list_inc.
    + rewrite IHe, fv_substf, fv_efv_read1. prove_list_inc.
Qed.

Lemma gterm_reade_free2 :
  forall L1 L2 e t, (forall x, x \in gterm_env_fv e -> x \in L1 <-> x \in L2) -> gterm_reade L1 t e = gterm_reade L2 t e.
Proof.
  induction e as [|[y u] e].
  - intros. reflexivity.
  - intros t H. simpl.
    assert (Hy := H y).
    destruct (in_dec freevar_eq_dec y (gterm_env_fv ((y, u) :: e))) as [Hy1 | Hy1].
    + specialize (Hy Hy1).
      destruct in_dec; destruct in_dec; try tauto; apply IHe; intros x Hx; apply H; simpl; rewrite in_app_iff; tauto.
    + simpl in Hy1. tauto.
Qed.


Lemma free_in_rec_cons :
  forall x t e y u, x <> y -> y \notin gterm_env_fv e -> free_in_rec x t ((y, u) :: e) <-> free_in_rec x (t [y := efv_read1 u]) e.
Proof.
  intros x t e y u H1 H2. split.
  - intros Hfree L. specialize (Hfree (list_remove y L)).
    simpl in *. destruct in_dec; rewrite list_remove_correct in *; [tauto|].
    erewrite gterm_reade_free2; [eassumption|].
    intros z. rewrite list_remove_correct.
    intuition congruence.
  - intros Hfree L. specialize (Hfree L).
    simpl. destruct in_dec.
    + rewrite gterm_reade_substf in Hfree by assumption.
      rewrite fv_substf2. intros [Hx | Hx]; subst; [|apply Hfree; eassumption].
      congruence.
    + assumption.
Qed.

Lemma free_in_rec_cons_same :
  forall x t e u, x \notin gterm_env_fv e -> free_in_rec x t ((x, u) :: e) <-> x \notin fv t.
Proof.
  intros x t e u Hx. split.
  - intros Hfree. specialize (Hfree (x :: nil)).
    simpl in Hfree. destruct freevar_eq_dec; [|tauto].
    revert t Hfree. induction e as [|[y v] e].
    + simpl in *. intros; assumption.
    + simpl in *. intros t H; destruct freevar_eq_dec; [intuition congruence|].
      apply IHe in H; [|rewrite in_app_iff in *; tauto].
      rewrite fv_substf2. intros [Hx2 | Hx2]; subst; [|apply H; eassumption]. congruence.
  - intros H L. simpl.
    destruct in_dec.
    + rewrite gterm_reade_fv. unfold gterm_fv; simpl. rewrite in_app_iff; tauto.
    + rewrite gterm_reade_fv, substf_fv by assumption. unfold gterm_fv; simpl. rewrite in_app_iff; tauto.
Qed.

Lemma invariant1_cons :
  forall L e t x u, x \notin L -> x \notin gterm_fv (t, e) -> invariant1 L e t -> invariant1 L ((x, u) :: e) t.
Proof.
  intros L e t x u HL Hx Hinv.
  intros z v Hzv.
  destruct Hzv as [Hzv | Hzv].
  - injection Hzv; intros ? ?; subst.
    destruct (env_value_varlam_dec v).
    + left; tauto.
    + right. split; [assumption|].
      right. rewrite free_in_rec_cons_same; unfold gterm_fv in Hx; rewrite in_app_iff in Hx; tauto.
  - specialize (Hinv z v Hzv).
    destruct Hinv as [Hinv | Hinv]; [tauto|].
    right. split; [tauto|].
    destruct Hinv as [? [Hinv | Hinv]]; [tauto|]. right.
    intros L2. rewrite gterm_reade_free by (unfold gterm_fv in *; rewrite in_app_iff in *; tauto).
    apply Hinv.
Qed.


Lemma invariant1_cons_inv :
  forall L e t x u, x \notin gterm_env_fv e -> invariant1 L ((x, u) :: e) t ->
               invariant1 L e t /\ invariant1 L e (t [x := efv_read1 u]) /\ ((env_value_varlam u /\ x \notin L) \/ (~ env_value_varlam u /\ (x \in L \/ (x \notin fv t)))).
Proof.
  intros L e t x u Hx Hinv.
  split; [|split].
  - intros z v Hzv.
    specialize (Hinv z v ltac:(simpl; tauto)).
    destruct Hinv as [Hinv | Hinv]; [tauto|]. right.
    destruct Hinv as [Hvarlam [Hinv | Hinv]]; [tauto|]. split; [assumption|right].
    intros L2. specialize (Hinv (x :: L2)).
    simpl in Hinv. destruct freevar_eq_dec; [|auto].
    erewrite gterm_reade_free2 in Hinv; [eassumption|].
    intros y Hy; simpl in *; intuition congruence.
  - intros z v Hzv.
    specialize (Hinv z v ltac:(simpl; tauto)).
    destruct Hinv as [Hinv | Hinv]; [tauto|]. right.
    destruct Hinv as [Hvarlam [Hinv | Hinv]]; [tauto|]. split; [assumption|right].
    intros L2. specialize (Hinv (list_remove x L2)).
    simpl in Hinv. destruct in_dec; [rewrite list_remove_correct in *; tauto|].
    erewrite gterm_reade_free2 in Hinv; [eassumption|].
    intros y Hy; simpl in *; rewrite list_remove_correct; intuition congruence.
  - specialize (Hinv x u ltac:(simpl; tauto)).
    destruct Hinv as [Hinv | Hinv]; [tauto|]. right.
    split; [tauto|]. destruct Hinv as [Hvarlam [Hinv | Hinv]]; [tauto|].
    right. rewrite free_in_rec_cons_same in Hinv; assumption.
Qed.


Lemma gterm_redt_preserve_invariant1 :
  forall L1 t1 t2, gterm_redt L1 t1 t2 -> forall L2 L3 t3, gterm_wf L2 t1 -> gterm_fv t1 \subseteq L1 -> fv t3 \subseteq L1 -> L3 \subseteq L1 -> invariant1 L3 (snd t1) t3 -> invariant1 L3 (snd t2) t3.
Proof.
  intros L1 t1 t2 H. induction H.
  - intros L2 L3 t4 Hwf HL Hfv3 HL3 Hinv; simpl in *.
    eapply IHgterm_redt; try assumption.
    + destruct Hwf as [Hwft Hwfe]; simpl in *. split; [|eassumption].
      simpl. inversion Hwft; assumption.
    + unfold gterm_fv in *; simpl in *. rewrite <- HL; prove_list_inc.
  - intros L2 L3 t4 Hwf HL Hfv3 HL3 Hinv; simpl in *.
    eapply IHgterm_redt; try assumption.
    + destruct Hwf as [Hwft Hwfe]; simpl in *. split; [|eassumption].
      simpl. inversion Hwft; assumption.
    + unfold gterm_fv in *; simpl in *. rewrite <- HL; prove_list_inc.
  - simpl.
    intros L2 L3 t3 Hwf HL Hfv3 HL3 Hinv.
    apply invariant1_cons.
    + rewrite HL3. assumption.
    + unfold gterm_fv in *; simpl in *.
      rewrite !list_inc_app_left in HL; destruct HL as [[HL1 HL2] HLe].
      rewrite Hfv3, HLe, in_app_iff. tauto.
    + assumption.
  - simpl. intros; assumption.
  - simpl. intros; assumption.
Qed.

Lemma gterm_env_find_In :
  forall e x u, gterm_env_find x e = Some u -> In (x, u) e.
Proof.
  induction e as [|[y v] e].
  - intros; simpl in *. congruence.
  - intros; simpl in *.
    destruct freevar_eq_dec.
    + left; congruence.
    + right; apply IHe. assumption.
Qed.

Lemma gterm_env_In_fv :
  forall e x u, In (x, u) e -> x \in gterm_env_fv e.
Proof.
  induction e as [|[y v] e].
  - intros; simpl in *; tauto.
  - intros; simpl in *. destruct H as [H | H]; rewrite in_app_iff; [|eauto].
    left; congruence.
Qed.

Lemma gterm_env_find_In_iff :
  forall e L x u, gterm_env_wf L e -> gterm_env_find x e = Some u <-> In (x, u) e.
Proof.
  induction e as [|[y v] e].
  - intros; simpl in *. split; [congruence | tauto].
  - intros; simpl in *.
    destruct freevar_eq_dec.
    + split; [intuition congruence|].
      intros [? | Hin2]; [congruence|].
      assert (~ (y \in gterm_env_fv e)) by (inversion H; subst; repeat (simpl in *; rewrite !in_app_iff in * ); tauto).
      subst.
      apply gterm_env_In_fv in Hin2. tauto.
    + apply gterm_env_wf_inv_common in H. split.
      * intros H1; rewrite IHe in H1; [right; apply H1 | apply H].
      * intros [H1 | H1]; [congruence|].
        apply <- IHe; [assumption | apply H].
Qed.


Lemma gterm_reade_var_appears :
  forall e t L x, In x L -> In x (fv t) -> In x (fv (gterm_reade L t e)).
Proof.
  induction e as [|[y v] e].
  - intros; simpl. assumption.
  - intros t L x Hx1 Hx2; simpl in *.
    destruct in_dec.
    + apply IHe; assumption.
    + apply IHe; [assumption|].
      eapply fv_substf2 in Hx2.
      destruct Hx2 as [Hx2 | Hx2]; [|apply Hx2].
      congruence.
Qed.

Lemma gterm_reade_env_find :
  forall e L Lwf t x u, gterm_env_wf Lwf e -> gterm_env_find x e = Some u -> x \notin L -> gterm_reade L (t ^ x) e = gterm_reade L (t ^^ (efv_read1 u)) e.
Proof.
  induction e as [|[y v] e].
  - intros; simpl in *; congruence.
  - intros L Lwf t x w Hwf Hu Hx; simpl in *.
    destruct in_dec.
    + destruct freevar_eq_dec; [congruence|]. apply gterm_env_wf_inv_common in Hwf. eapply IHe; (apply Hwf || assumption).
    + destruct freevar_eq_dec.
      * subst. injection Hu; intro; subst.
        apply gterm_env_wf_inv_common in Hwf.
        rewrite substb_substf; [|destruct Hwf as (? & Hwf & ?); inversion Hwf; simpl; [|apply lc_lam_body]; assumption].
        simpl. destruct freevar_eq_dec; [|tauto].
        rewrite substb_substf; [|destruct Hwf as (? & Hwf & ?); inversion Hwf; simpl; [|apply lc_lam_body]; assumption].
        f_equal. f_equal.
        rewrite substf_fv; [reflexivity|]. rewrite fv_efv_read1. rewrite in_app_iff in *; tauto.
      * apply gterm_env_wf_inv_common in Hwf.
        assert (lc (efv_read1 v)) by (destruct Hwf as (? & Hwf & ?); inversion Hwf; simpl; [|apply lc_lam_body]; assumption).
        rewrite !substb_substf by assumption.
        simpl. destruct freevar_eq_dec; [congruence|].
        erewrite IHe; [|apply Hwf|eassumption|assumption].
        f_equal. f_equal.
        rewrite substf_fv; [reflexivity|].
        rewrite fv_efv_read1. apply gterm_env_find_fv in Hu.
        rewrite in_app_iff in *; firstorder.
Qed.

Lemma gterm_reade_red_env_1 :
  forall L1 e1 e2, gterm_red_env L1 e1 e2 -> forall L2, gterm_env_wf L2 e1 -> gterm_env_fv e1 \subseteq L1 -> (forall t3 L3, lc t3 -> fv t3 \subseteq L1 -> invariant1 L3 e1 t3 -> gterm_reade L3 t3 e1 = gterm_reade L3 t3 e2).
Proof.
  unfold invariant1.
  intros L1 t1 t2 H. induction H; intros L2 Hwf HL t4 L4 Hlc4 Hinc HL4; simpl in *.
  - assert (Heq : gterm_reade L4 t4 e1 = gterm_reade L4 t4 e2).
    { rewrite (gterm_reade_env_redt _ _ _ _ H); [reflexivity | assumption]. }
    destruct in_dec; [assumption|].
    destruct (HL4 x (Env_term t1) ltac:(tauto)) as [[H1 _] | [H1 [H2 | H2]]].
    + inversion H1; subst.
      assert (H2 : e1 = e2 /\ exists u, env_value_varlam u /\ gterm_env_find x0 e2 = Some u /\ t2 = efv_read1 u).
      {
        inversion H; subst.
        all: split; [reflexivity|].
        all: eexists; split; [|split]; [|eassumption|]; [constructor | reflexivity].
      }
      destruct H2 as [Heqe [u H2]]. rewrite Heqe.
      specialize (HL4 x0 u ltac:(right; apply gterm_env_find_In; rewrite Heqe; tauto)).
      destruct HL4 as [[_ H3] | ?]; [|tauto].
      destruct H2 as (Hvarlam & Hfind & ->).
      eapply gterm_redt_env_wf in H; simpl in *.
      * rewrite <- !open_close with (k := 0) (x := x) (t := t4) by (apply H || assumption || constructor).
        eapply gterm_reade_env_find; [|assumption|assumption]. apply H.
      * rewrite <- HL. prove_list_inc.
      * constructor.
      * apply gterm_env_wf_inv_term in Hwf. apply Hwf.
    + tauto.
    + enough (x \notin fv t4) by (rewrite !substf_fv; assumption).
      specialize (H2 (x :: nil)). simpl in *. destruct freevar_eq_dec; [|simpl in *; tauto].
      intros H4; apply H2.
      apply gterm_reade_var_appears; simpl; tauto.
  - destruct in_dec.
    + rewrite (gterm_reade_env_redt _ _ _ _ H); [reflexivity | assumption].
    + rewrite (gterm_reade_env_redt _ _ _ _ H); [reflexivity|].
      rewrite fv_substf, list_inc_app_left. split; [assumption|]. simpl.
      rewrite <- HL. prove_list_inc.
  - reflexivity.
  - destruct u as [x t].
    destruct in_dec.
    + assert (Hwf2 := gterm_env_wf_inv_common Hwf).
      eapply IHgterm_red_env.
      * apply Hwf2.
      * eapply list_inc_trans; [|apply HL]. prove_list_inc.
      * assumption.
      * assumption.
      * intros z u Hu. specialize (HL4 z u ltac:(tauto)).
        destruct HL4 as [? | [? [? | HL4]]]; try tauto.
        right; split; [assumption|]; right.
        intros L5. specialize (HL4 (x :: L5)).
        simpl in HL4. destruct freevar_eq_dec; [|simpl in *; auto].
        rewrite gterm_reade_free2 with (L2 := L5) in HL4; [assumption|].
        intros w Hw; simpl. split; [|tauto].
        intros [-> | ?]; [|tauto].
        rewrite in_app_iff in Hwf2. tauto.
    + assert (Hwf2 := gterm_env_wf_inv_common Hwf).
      eapply IHgterm_red_env.
      * apply Hwf2.
      * eapply list_inc_trans; [|apply HL]. prove_list_inc.
      * apply substf_lc; [assumption|].
        destruct Hwf2 as (? & Hwf2 & ?); inversion Hwf2; simpl; [|apply lc_lam_body]; assumption.
      * rewrite fv_substf, list_inc_app_left, fv_efv_read1. split; [assumption|].
        rewrite <- HL; prove_list_inc.
      * intros z u Hu. specialize (HL4 z u ltac:(tauto)).
        destruct HL4 as [? | [? [? | HL4]]]; try tauto.
        right; split; [assumption|]; right.
        intros L5. specialize (HL4 (list_remove x L5)).
        simpl in HL4. destruct in_dec; [rewrite list_remove_correct in *; tauto|].
        rewrite gterm_reade_free2 with (L2 := L5) in HL4; [assumption|].
        intros w Hw; simpl. rewrite list_remove_correct.
        split; [tauto|]. intros; split; [assumption|].
        intros ->; rewrite in_app_iff in Hwf2. tauto.
Qed.

(*
specialize (HL4 z u ltac:(tauto)).

        destruct HL4 as [? | [? [? | ?]]]; tauto.
Qed.

        right. split; [assumption|]. right.
        ; apply HL4. tauto.
    + inversion H1; subst. inversion H; subst.
      * admit.
      * 
      apply star_beta_substf.
      * admit.
      * admit.
      * rewrite (gterm_read1_env_redt _ _ _ H) by assumption. simpl.
        constructor.
      * rewrite (gterm_read1_env_redt _ _ _ H) by admit. simpl.
        eapply (gterm_read1_redt_2 _ _ _ _ H).
        -- apply gterm_env_wf_inv_term in Hwf. split; simpl; apply Hwf.
        -- eapply list_inc_trans; [|apply HL]. prove_list_inc.
    + admit.
    + admit.
  - rewrite (gterm_read1_env_redt _ _ _ H); [constructor|].
    admit.
  - constructor.
  - destruct u as [x t]. simpl.
    assert (Hwfi := gterm_env_wf_inv_common Hwf).
    apply (IHgterm_red_env _ ltac:(apply Hwfi)).
    + eapply list_inc_trans; [|apply HL]. prove_list_inc.
    + admit.
Admitted.
*)







Inductive env_respects_red : list (freevar * env_value) -> Prop :=
| env_respects_red_nil : env_respects_red nil
| env_respects_red_cons_term :
        
    forall x t e, env_respects_red e -> env_respects_red ((x, Env_term t) :: e)
| env_respects_red_cons_lam :
    forall x y t1 t2 e L,
      env_respects_red e -> invariant1 L e (t1 ^ y) ->
      star beta (gterm_reade L (t1 ^ y) e) (gterm_reade L t2 e) ->
      env_respects_red ((x, Env_lam t1 y t2) :: e).


Lemma env_respects_red_cons_lam_same :
  forall x y t e L, gterm_env_wf L e -> env_respects_red e -> env_respects_red ((x, Env_lam t y (t ^ y)) :: e).
Proof.
  intros x y t e Lwf Hwf He.
  pose (L := map fst (filter (fun p => if env_value_varlam_dec (snd p) then false else true) e)).
  apply env_respects_red_cons_lam with (L := L).
  - assumption.
  - unfold invariant1. intros.
    destruct (in_dec freevar_eq_dec z L) as [Hz | Hz].
    + right. split; [|left; assumption].
      unfold L in Hz. rewrite in_map_iff in Hz.
      destruct Hz as [[? v] [? Hz]]; simpl in *; subst.
      rewrite filter_In in Hz.
      destruct Hz as [Hz1 Hz2]; simpl in *.
      destruct env_value_varlam_dec; [congruence|].
      enough (u = v) by congruence.
      rewrite <- gterm_env_find_In_iff in H, Hz1 by eassumption.
      congruence.
    + left. split; [|assumption].
      unfold L in Hz. rewrite in_map_iff in Hz.
      destruct (env_value_varlam_dec u) as [Hu | Hu]; [assumption|].
      exfalso. apply Hz.
      exists (z, u); simpl.
      split; [reflexivity|].
      rewrite filter_In. split; [assumption|]. simpl.
      destruct env_value_varlam_dec; auto.
  - constructor.
Qed.

Lemma env_respects_red_preserve_redt :
  forall L t1 t2, gterm_redt L t1 t2 -> env_respects_red (snd t1) -> env_respects_red (snd t2).
Proof.
  intros L t1 t2 H. induction H.
  - intros; simpl in *; auto.
  - intros; simpl in *; auto.
  - intros; simpl in *.
    constructor. assumption.
  - intros; simpl in *; auto.
  - intros; simpl in *; auto.
Qed.

Lemma substb_fv :
  forall u k v, fv (u [k <- v]) \subseteq fv u ++ fv v.
Proof.
  induction u; intros; simpl.
  - destruct Nat.eq_dec.
    + reflexivity.
    + simpl. prove_list_inc.
  - prove_list_inc.
  - apply IHu.
  - rewrite IHu1, IHu2. prove_list_inc.
Qed.

Lemma red_env_preserve_invariant1 :
  forall L1 e1 e2, gterm_red_env L1 e1 e2 -> forall L2 L3 t3, gterm_env_wf L2 e1 -> gterm_env_fv e1 \subseteq L1 -> fv t3 \subseteq L1 -> L3 \subseteq L1 -> invariant1 L3 e1 t3 -> exists L4, L4 \subseteq L3 /\ invariant1 L4 e2 t3.
Proof.
  intros L1 e1 e2 H. induction H.
  - intros L2 L3 t3 Hwf HL1 HL2 HL3 Hinv1.
    apply gterm_env_wf_inv_term in Hwf.
    apply invariant1_cons_inv in Hinv1; [|rewrite in_app_iff in Hwf; tauto].

    admit.
  - intros L2 L3 t4 Hwf HL1 HL2 HL3 Hinv1.
    exists L3. split; [reflexivity|]. intros z u Hzu. destruct Hzu as [Hzu | Hzu].
    + inversion Hzu; intros; subst.
      specialize (Hinv1 z (Env_lam t3 y t1) ltac:(simpl; tauto)).
      destruct Hinv1 as [Hinv1 | [Hinv1 ?]]; [|exfalso; apply Hinv1; constructor].
      left. split; [constructor | apply Hinv1].
    + apply gterm_env_wf_inv_lam in Hwf.
      apply invariant1_cons_inv in Hinv1; [|repeat (rewrite !in_app_iff in Hwf; simpl in Hwf); tauto].
      simpl in *.
      assert (Hinv2 := gterm_redt_preserve_invariant1 _ _ _ H _ L3 (t4 [x := lam t3]) ltac:(split; apply Hwf)).
      simpl in Hinv2.
      specialize (Hinv2 ltac:(rewrite <- HL1; prove_list_inc)).
      rewrite fv_substf, list_inc_app_left in Hinv2.
      specialize (Hinv2 ltac:(split; [assumption|rewrite <- HL1; prove_list_inc]) HL3 ltac:(apply Hinv1)).
      specialize (Hinv2 z u Hzu).
      rewrite free_in_rec_cons by admit. simpl.
      assumption.
  - intros L2 L3 t3 Hwf HL1 HL2 HL3 Hinv1.
    exists (list_remove x L3). split; [intros ?; rewrite list_remove_correct; tauto|].
    intros z u Hzu. destruct Hzu as [Hzu | Hzu].
    + left. inversion Hzu; subst.
      split; [constructor|]. rewrite list_remove_correct. tauto.
    + specialize (Hinv1 z u ltac:(simpl; tauto)).
      simpl in *. rewrite list_remove_correct.
      enough (x <> z) by tauto.
      admit.
  - intros L2 L3 t3 Hwf HL1 HL2 HL3 Hinv1.
    destruct u as [y u].
    apply gterm_env_wf_inv_common in Hwf.
    apply invariant1_cons_inv in Hinv1; [|rewrite in_app_iff in Hwf; tauto].
    destruct (IHgterm_red_env (y :: efv u ++ L2) L3 (t3 [y := efv_read1 u])) as [L4 [HLinc HL4]].
    + apply Hwf.
    + rewrite <- HL1. simpl. prove_list_inc.
    + rewrite fv_substf, fv_efv_read1. apply list_inc_app_left. split; [assumption | rewrite <- HL1; prove_list_inc].
    + assumption.
    + apply Hinv1.
    + destruct (in_dec freevar_eq_dec y L3) as [Hy | Hy].
      * exists (y :: L4). split; [intros z [Hz | Hz]; subst; auto|].
        intros z v Hzv. destruct Hzv as [Hzv | Hzv].
        -- inversion Hzv; subst.
           right. simpl; tauto.
        -- specialize (HL4 z v Hzv).
           assert (y <> z) by admit.
           destruct HL4 as [HL4 | HL4]; [left; split; [|intros [? | ?]; subst]; tauto|].
           right. split; [tauto|].
           destruct HL4 as [Hvl [HL4 | HL4]]; [left; simpl; tauto|].
           right. intros L5. specialize (HL4 L5).
           simpl. destruct in_dec; [|assumption].
           rewrite gterm_reade_substf in HL4 by admit.
           rewrite fv_substf2. intros Hz; destruct Hz as [Hz | Hz]; [eauto|apply HL4; apply Hz].
      * exists L4. split; [assumption|].
        intros z v Hzv. destruct Hzv as [Hzv | Hzv].
        -- inversion Hzv; subst.
           destruct Hinv1 as (? & ? & [Hinv1 | Hinv1]).
           ++ left. intuition.
           ++ right. split; [tauto|]. right.
             rewrite free_in_rec_cons_same by admit.
             tauto.
        -- specialize (HL4 z v Hzv).
           rewrite free_in_rec_cons by admit.
           assumption.
Admitted.

Axiom cheat : False. Ltac cheat := exfalso; apply cheat.

Lemma env_respects_red_preserve_red_env :
  forall L e1 e2, gterm_red_env L e1 e2 -> gterm_env_fv e1 \subseteq L -> forall L2, gterm_env_wf L2 e1 -> env_respects_red e1 -> env_respects_red e2.
Proof.
  intros L e1 e2 H HL. induction H.
  - intros L2 Hwf He; simpl in *. constructor.
    apply env_respects_red_preserve_redt in H; simpl in *; [|inversion He]; assumption.
  - intros L2 Hwf He; simpl in *.
    inversion He; subst.
    apply env_respects_red_cons_lam with (L := L0).
    + apply env_respects_red_preserve_redt in H; simpl in *; auto.
    + inversion Hwf; subst.
      eapply (gterm_redt_preserve_invariant1 _ (t1, e1) (t2, e2)); try eassumption.
      * split; simpl; eassumption.
      * rewrite <- HL. unfold gterm_fv; simpl. prove_list_inc.
      * rewrite <- HL, substb_fv; simpl. prove_list_inc.
      * admit.
    + eapply star_compose.
      * erewrite <- (gterm_reade_env_redt _ _ _ _ H); [eassumption|].
        rewrite <- HL, substb_fv; simpl. prove_list_inc.
      * (* erewrite (gterm_reade_env_redt _ _ _ _ H); [|rewrite <- HL; prove_list_inc].
        simpl. apply (gterm_read1_redt_2 _ _ _ _ H). *)
        admit.
  - intros L2 Hwf He; simpl in *.
    eapply env_respects_red_cons_lam_same.
    + inversion Hwf; subst. eassumption.
    + inversion He. assumption.
  - intros L2 Hwf He. inversion He; subst.
    + constructor. eapply IHgterm_red_env; [rewrite <- HL; simpl; prove_list_inc| |assumption].
      inversion Hwf; eassumption.
    + econstructor.
      * eapply IHgterm_red_env; [rewrite <- HL; simpl; prove_list_inc| |assumption]. inversion Hwf; eassumption.
      * admit.
      * erewrite gterm_reade_red_env_1 in H4; try eassumption.
        -- eapply star_compose; [eassumption|].
           admit.
        -- inversion Hwf. eassumption.
        -- rewrite <- HL. simpl. prove_list_inc.
        -- apply gterm_env_wf_inv_lam in Hwf.
           apply lc_open_gen. apply Hwf.
        -- rewrite <- HL. simpl. rewrite substb_fv; simpl. prove_list_inc.
Qed.


    apply (env_respects_red_preserve_redt _ _ _ H).
    simpl. inversion H0. assumption.
  - intros; simpl in *.
    inversion_clear H0.
    apply env_respects_red_cons_lam with (L := L ++ L0 ++ L1).
    + pick y \notin L1 as Hy. apply (env_respects_red_preserve_redt _ _ _ (H y Hy)). assumption.
    + intros y e0 Hy Hr.
      eapply star_compose.
      * apply H2. admit. admit.
      * rewrite !in_app_iff in Hy.
        specialize (H y ltac:(tauto)).
  (* )apply gterm_read1_red_env_1. *)
        admit.
  - intros; simpl in *. apply env_respects_red_cons_lam_same. admit. admit.
  - intros H1. inversion H1; subst.
    + constructor. auto.
    + econstructor; [auto|].
      intros y e0 Hy Hred.

  - intros; simpl in *. apply env_respects_red_cons_lam_same.
    + admit.
    + inversion H; assumption.
  - intros.
    eapply env_respects_red_preserve_redt; eassumption.
Qed.

















Inductive env_respects_red : list (freevar * env_value) -> Prop :=
| env_respects_red_nil : env_respects_red nil
| env_respects_red_cons_term :
    forall x t e, env_respects_red e -> env_respects_red ((x, Env_term t) :: e)
| env_respects_red_cons_lam :
    forall x t1 t2 e L,
      env_respects_red e ->
      (forall y e2, y \notin L -> star (gterm_red_env (y :: L)) e e2 ->
               star beta (gterm_read1 (t1 ^ y) e2) (gterm_read1 (t2 ^ y) e2)) ->
      env_respects_red ((x, Env_lam t1 t2) :: e).


Lemma env_respects_red_cons_lam_same :
  forall x t e, body t -> env_respects_red e -> env_respects_red ((x, Env_lam t t) :: e).
Proof.
  intros x t e Hbody He.
  apply env_respects_red_cons_lam with (L := nil); [assumption|].
  intros y e2 Hy Hred.
  constructor.
(*   remember (t3 ^ y, e2) as g2.
  replace (t3 ^ y) with (fst g2) by (rewrite Heqg2; reflexivity).
  replace e2 with (snd g2) by (rewrite Heqg2; reflexivity).
  clear Heqg2. revert Hred.
  apply star_induction_rev with (P := fun g2 => star beta (gterm_read1 (t ^ y) e) (gterm_read1 (fst g2) (snd g2))).
  - simpl. constructor.
  - intros [t4 e4] [t5 e5]. simpl.
    admit.
Admitted. *)
Qed.

Lemma env_respects_red_preserve_redt :
  forall L t1 t2, gterm_redt L t1 t2 -> env_respects_red (snd t1) -> env_respects_red (snd t2).
Proof.
  intros L t1 t2 H. induction H.
  - intros; simpl in *; auto.
  - intros; simpl in *; auto.
  - intros; simpl in *.
    constructor. assumption.
  - intros; simpl in *; auto.
  - intros; simpl in *; auto.
Qed.

Lemma env_respects_red_preserve_red_env :
  forall L e1 e2, gterm_red_env L e1 e2 -> env_respects_red e1 -> env_respects_red e2.
Proof.
  intros L t1 t2 H. induction H.
  - intros; simpl in *. constructor.
    apply (env_respects_red_preserve_redt _ _ _ H).
    simpl. inversion H0. assumption.
  - intros; simpl in *.
    inversion_clear H0.
    apply env_respects_red_cons_lam with (L := L ++ L0 ++ L1).
    + pick y \notin L1 as Hy. apply (env_respects_red_preserve_redt _ _ _ (H y Hy)). assumption.
    + intros y e0 Hy Hr.
      eapply star_compose.
      * apply H2. admit. admit.
      * rewrite !in_app_iff in Hy.
        specialize (H y ltac:(tauto)).
  (* )apply gterm_read1_red_env_1. *)
        admit.
  - intros; simpl in *. apply env_respects_red_cons_lam_same. admit. admit.
  - intros H1. inversion H1; subst.
    + constructor. auto.
    + econstructor; [auto|].
      intros y e0 Hy Hred.

  - intros; simpl in *. apply env_respects_red_cons_lam_same.
    + admit.
    + inversion H; assumption.
  - intros.
    eapply env_respects_red_preserve_redt; eassumption.
Qed.













Inductive env_respects_red : list (freevar * env_value) -> Prop :=
| env_respects_red_nil : env_respects_red nil
| env_respects_red_cons_term :
    forall x t e, env_respects_red e -> env_respects_red ((x, Env_term t) :: e)
| env_respects_red_cons_lam :
    forall x t1 t2 e L, env_respects_red e -> (forall y, y \notin L -> star beta (gterm_reada (t1 ^ y) e) (gterm_reada (t2 ^ y) e)) -> env_respects_red ((x, Env_lam t1 t2) :: e).

Lemma gterm_redt_beta_rec :
  forall L t1 t2,
    gterm_redt L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 -> env_respects_red (snd t1) ->
    gterm_wf t2 /\ env_respects_red (snd t2) /\
    star beta (gterm_read1 (fst t1) (snd t2)) (gterm_read1 (fst t2) (snd t2)) (* /\
    (snd t2 = snd t1 \/ exists x t3, x \notin L /\ dlc t3 /\ term_wf_in_env t3 (snd t1) /\ snd t2 = (x, t3) :: snd t1). *).
Proof.
  intros L t1 t2 H. induction H; intros HL1 Hwf1 Henv1; simpl in *.
  - split; split.
    + destruct Hwf1 as [Hwf1 Hwfe]. constructor; [|inversion Hwf1; tauto].
      apply IHgterm_redt.
      * admit.
      * split; simpl; [inversion Hwf1|]; tauto.
      * assumption.
    + apply IHgterm_redt; admit.
    + apply IHgterm_redt; admit.
    + admit.

  - admit.

  - split; split.
    + simpl. admit.
    + simpl. constructor; admit.
    + constructor. assumption.
    + rewrite <- substb_is_substf; admit.

  - split; split.
    + constructor.
    + destruct Hwf1 as [Hwf1 Hwfe]; apply Hwfe.
    + assumption.
    + admit.

  - split; split.
    + apply lc_lam_body. admit.
    + apply Hwf1.
    + assumption.
    + admit.
Admitted.

Lemma gterm_red_beta_rec :
  forall L t1 t2,
    gterm_red L t1 t2 -> list_inc (gterm_fv t1) L -> gterm_wf t1 -> env_respects_red (snd t1) ->
    gterm_wf t2 /\ env_respects_red (snd t2) /\
    star beta (gterm_read1 (fst t1) (snd t1)) (gterm_read1 (fst t2) (snd t1)) /\
    (forall t, list_inc (fv t) L -> star beta (gterm_read1 t (snd t1)) (gterm_read1 t (snd t2))).
Proof.
  intros L t1 t2 H. induction H; intros HL1 Hwf1 Henv1; simpl in *.
  - split; split; [| | |split]; simpl.
    + apply Hwf1.
    + constructor; admit.
    + constructor. admit.
    + constructor.
    + intros t3 HL3. rewrite !gterm_read1_substf by admit.
      eapply star_compose.
      * apply star_map_impl with (RA := beta) (f := fun t => t [ x := _ ]).
        { intros; apply beta_subst; [admit | assumption]. }
        admit.
      * apply star_star.
        apply star_map_impl with (RA := beta) (f := fun t => _ [ x := t ]).
        { intros; apply beta_subst2; [assumption | admit]. }
        admit.

  - split; split; [| | |split]; simpl.
    + apply Hwf1.
    + constructor; admit.
    + inversion Henv1; subst. econstructor.


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
    (forall x, x \notin L -> star dbeta (t1 d^ x) (t2 d^ x)) ->
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
         (forall x, x \notin L -> star dbeta (t1 d^ x) (t2 d^ x)).
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
      eapply star_map_impl with (f := fun t => t d[ x := u]); [|apply H3; simpl in Hy; auto].
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
      eapply star_compose; [apply Hwf3; auto|].
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
         (forall x, star dbeta (t1 d^ x) (t2 d^ x)).
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
    eapply star_map_impl with (f := fun t => t d[ x := dfvar y ]); [|apply H3; tauto].
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
  forall t1 t2, dbeta t1 t2 -> star beta (dterm_read1 t1) (dterm_read1 t2).
Proof.
  intros t1 t2 Hbeta. induction Hbeta.
  - simpl. rewrite dsubstb_substb.
    econstructor; [|constructor].
    constructor; [apply dbody_body | apply dlc_lc]; assumption.
  - simpl.
    eapply star_map_impl with (f := fun t => app t _); [|eassumption].
    intros; constructor; auto using dlc_lc.
  - simpl.
    eapply star_map_impl with (f := fun t => app _ t); [|eassumption].
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
  forall t, dwf t -> star beta (dterm_read1 t) (dterm_read2 t).
Proof.
  intros t Ht. induction Ht.
  - simpl; constructor.
  - simpl.
    eapply star_compose.
    + eapply star_map_impl with (f := fun t => app _ t); [|eassumption].
      intros; constructor; auto using dlc_lc, dwf_dlc.
    + eapply star_map_impl with (f := fun t => app t _); [|eassumption].
      intros; constructor; auto using dlc_lc2, dwf_dlc.
  - simpl.
    pick x \notin (L ++ dfv t1 ++ dfv t2).
    rewrite !in_app_iff in *.
    rewrite <- (dclose_dopen t1 0 x), <- (dclose_dopen t2 0 x) by tauto.
    rewrite dcloseb_closeb, dcloseb_closeb2.
    apply star_map_impl with (RA := beta) (f := fun t => lam (closeb 0 x t)).
    + intros t3 t4 Hbeta.
      apply beta_lam with (L := fv t3 ++ fv t4).
      intros y Hy; rewrite in_app_iff in *.
      rewrite !open_close by (constructor || apply beta_lc in Hbeta; tauto).
      apply beta_subst; [constructor | auto].
    + eapply star_compose; [|eauto].
      apply star_star.
      eapply star_map_impl; [|eauto].
      intros t3 t4 Hbeta; apply dbeta_beta; auto.
Qed.

Lemma dbeta_beta_subst :
  forall x t t1 t2, dlc t -> dbeta t1 t2 ->
               star beta (dterm_read1 (t d[ x := t1 ])) (dterm_read1 (t d[ x := t2 ])).
Proof.
  intros x t t1 t2 Ht Hdbeta.
  rewrite !dsubstf_substf.
  apply star_star.
  eapply star_map_impl with (f := fun t1 => dterm_read1 t [ x := t1 ]); [|apply dbeta_beta; assumption].
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

Lemma parallel_dbeta_incl_star_dbeta :
  forall t1 t2, parallel_dbeta t1 t2 -> star dbeta t1 t2.
Proof.
  intros t1 t2 H. induction H.
  - constructor.
  - apply star_compose with (y := dapp t3 t2).
    + eapply star_map_impl with (f := fun t => dapp t t2); [|eassumption].
      intros; constructor; firstorder using parallel_dbeta_dlc.
    + eapply star_map_impl with (f := fun t => dapp t3 t); [|eassumption].
      intros; constructor; firstorder using parallel_dbeta_dlc.
  - pick x \notin (L ++ dfv t2 ++ dfv t3).
    rewrite !in_app_iff in *.
    rewrite <- (dclose_dopen t2 0 x), <- (dclose_dopen t3 0 x) by tauto.
    apply star_map_impl with (RA := dbeta) (f := fun t => dlam _ (dcloseb 0 x t)).
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


Lemma star_beta_lc :
  forall t1 t2, star beta t1 t2 -> lc t1 -> lc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using beta_lc.
Qed.

Lemma star_dbeta_dlc :
  forall t1 t2, star dbeta t1 t2 -> dlc t1 -> dlc t2.
Proof.
  intros t1 t2 H. induction H; firstorder using dbeta_dlc.
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

Lemma star_dbeta_app :
  forall t1 t2 t3 t4,
    dlc t1 -> dlc t2 ->
    star dbeta t1 t3 -> star dbeta t2 t4 -> star dbeta (dapp t1 t2) (dapp t3 t4).
Proof.
  intros t1 t2 t3 t4 Hlc1 Hlc2 Hbeta1 Hbeta2.
  eapply star_compose.
  - eapply star_map_impl with (f := fun t => dapp _ t); [|eassumption].
    intros t5 t6 Hbeta; constructor; assumption.
  - eapply star_map_impl with (f := fun t => dapp t _); [|eassumption].
    intros t5 t6 Hbeta; constructor; [|eapply star_dbeta_dlc]; eassumption.
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
  apply beta_lam with (L := fv t1 ++ fv t2).
  intros y Hy; rewrite in_app_iff in *.
  rewrite !open_close by (constructor || apply beta_lc in Hbeta1; tauto).
  apply beta_subst; [constructor | auto].
Qed.

Lemma star_dbeta_dlam :
  forall t1 t2 t3 x,
    x \notin dfv t1 -> x \notin dfv t2 -> star dbeta (t1 d^ x) (t2 d^ x) -> dbody t3 ->
    star dbeta (dlam t3 t1) (dlam t3 t2).
Proof.
  intros t1 t2 t3 x Hx1 Hx2 Hbeta Hbody.
  rewrite <- (dclose_dopen t1 0 x), <- (dclose_dopen t2 0 x) by tauto.
  eapply star_map_impl with (f := fun t => dlam t3 (dcloseb 0 x t)); [|eassumption].
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
             dwf (t1 d^ x) -> dwf (t2 d^ x) -> star dbeta (t1 d^ x) (t2 d^ x) -> dwf (dlam t1 t2).
Proof.
  intros x t1 t2 Hx1 Hx2 Hwf1 Hwf2 Hbeta.
  apply dwf_lam with (L := dfv t1 ++ dfv t2);
    intros y Hy; rewrite in_app_iff in Hy;
      try rewrite dsubstb_is_dsubstf with (t := t1) (x := x) by tauto;
      try rewrite dsubstb_is_dsubstf with (t := t2) (x := x) by tauto.
  - apply dsubstf_dwf; [constructor | tauto].
  - apply dsubstf_dwf; [constructor | tauto].
  - eapply star_map_impl; [|eassumption].
    intros t3 t4 H; apply dbeta_subst; [constructor | assumption].
Qed.

Inductive parallel_env_dbeta : list (freevar * dterm) -> list (freevar * dterm) -> Prop :=
| ped_nil : parallel_env_dbeta nil nil
| ped_cons : forall x t1 t2 e1 e2, star dbeta t1 t2 -> parallel_env_dbeta e1 e2 -> parallel_env_dbeta ((x, t1) :: e1) ((x, t2) :: e2).

Lemma parallel_env_dbeta_refl :
  forall e, parallel_env_dbeta e e.
Proof.
  induction e as [|[x t] e]; constructor; [constructor | assumption].
Qed.

Lemma parallel_env_dbeta_inv_left :
  forall x t1 e1 e, parallel_env_dbeta ((x, t1) :: e1) e -> exists t2 e2, star dbeta t1 t2 /\ parallel_env_dbeta e1 e2 /\ e = (x, t2) :: e2.
Proof.
  intros x1 t1 e1 e H. inversion_clear H.
  eauto.
Qed.

Lemma parallel_env_dbeta_inv_right :
  forall x t2 e2 e, parallel_env_dbeta e ((x, t2) :: e2) -> exists t1 e1, star dbeta t1 t2 /\ parallel_env_dbeta e1 e2 /\ e = (x, t1) :: e1.
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

Lemma star_dbeta_fv :
  forall t1 t2, star dbeta t1 t2 -> list_inc (dfv t2) (dfv t1).
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

Lemma gterm_read_star_dbeta :
  forall e t1 t2, gterm_env_wf e -> star dbeta t1 t2 -> star dbeta (gterm_read t1 e) (gterm_read t2 e).
Proof.
  intros e t1 t2 He Hbeta.
  eapply star_map_impl with (f := fun t => gterm_read t e).
  + intros; apply gterm_read_dbeta; eassumption.
  + assumption.
Qed.

Lemma parallel_env_dbeta_fv :
  forall e1 e2, parallel_env_dbeta e1 e2 -> list_inc (gterm_env_fv e2) (gterm_env_fv e1).
Proof.
  intros e1 e2 Hbeta. induction Hbeta.
  - firstorder.
  - simpl.
    apply star_dbeta_fv in H.
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
    + firstorder using star_dbeta_dlc.
    + apply parallel_env_dbeta_fv in H0.
      apply star_dbeta_fv in H.
      rewrite !in_app_iff in *; firstorder.
Qed.

Lemma star_dbeta_dwf :
  forall t1 t2, star dbeta t1 t2 -> dwf t1 -> dwf t2.
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
    term_wf_in_env (dlam t1 t2) e <-> forall x, x \notin (L ++ dfv t1 ++ dfv t2 ++ gterm_env_fv e) -> term_wf_in_env (t1 d^ x) e /\ term_wf_in_env (t2 d^ x) e /\ (forall e2, parallel_env_dbeta e e2 -> star dbeta ((gterm_read t1 e2) d^ x) ((gterm_read t2 e2) d^ x)).
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
    (forall e3, parallel_env_dbeta (snd t2) e3 -> star dbeta (gterm_read (fst t1) e3) (gterm_read (fst t2) e3)) /\
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
      apply star_dbeta_app; eauto.
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
      apply star_dbeta_app; eauto.
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
      apply star_dbeta_app; eauto.
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
      apply star_dbeta_app; eauto.
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
           ++ eapply star_compose; [apply Hwfl|].
              rewrite !gterm_read_dsubstb in Hbeta by tauto.
              rewrite gterm_read_var in Hbeta by tauto.
              apply Hbeta.
           ++ simpl in *; rewrite !in_app_iff in *.
              rewrite dsubstf_dfv by firstorder.
              eapply star_compose; [apply Hwfl|].
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
        eapply star_compose; [apply Hewf; tauto|].
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
        eapply star_compose.
        -- simpl.
           rewrite dsubstf_dfv by admit.
           apply Hewf; tauto.
        -- rewrite !dsubstb_dsubstf in Hbeta by (eapply star_dbeta_dlc; eauto).
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
      * apply star_dbeta_dlam with (x := x); try tauto.
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
        apply star_dbeta_dlam with (x := x); try tauto.
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
      * eapply star_dbeta_dwf.
        { apply gterm_read_star_dbeta; [|eassumption].
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
      eapply star_compose.
      { apply star_dbeta_app; [apply dlc_dlam_dbody; tauto|auto|constructor|].
        apply gterm_read_star_dbeta; eassumption. }
      econstructor; constructor; [assumption | assumption |].
      apply gterm_wf_read_lc. split; [|assumption]. simpl.
      eapply star_dbeta_dlc; [eassumption|apply Hwf3].
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
     star beta (dterm_read1 (gterm_read (fst t1) (snd t1))) (dterm_read1 (gterm_read (fst t2) (snd t2)))) /\
    (forall t3, list_inc (dfv t3) L -> gterm_wf (t3, snd t1) ->
           gterm_wf (t3, snd t2) /\
           star beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
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
      eapply star_compose.
      * eapply star_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|].
           ++ unfold gterm_fv in *; simpl in *.
              eapply list_inc_trans; [|exact HL]. prove_list_inc.
           ++ unfold gterm_wf in *; simpl in *.
              split; [|tauto].
              admit.
      * apply star_star.
        eapply star_map_impl with (f := fun t => _ [x := t]).
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
    + apply star_star.
      eapply star_map_impl; [|apply H].
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
      apply star_beta_app; eauto using dlc_lc.
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
      apply star_beta_app; eauto using dlc_lc.
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
      (* apply star_beta_lam with (x := x); try tauto. *)
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
        * apply star_beta_lam with (x := x); try tauto.
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
      match goal with [ |- star beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply star_beta_lam with (x := x); try tauto.
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
      eapply star_compose.
      * eapply star_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|unfold gterm_wf in *; simpl in *; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
      * apply star_star.
        eapply star_map_impl with (f := fun t => _ [x := t]).
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
           star beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
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
      eapply star_compose.
      * eapply star_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. admit.
        -- apply IHHred; admit.
      * apply star_star.
        eapply star_map_impl with (f := fun t => _ [x := t]).
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
    star beta (dterm_read1 (gterm_read (fst t1) (snd t1))) (dterm_read1 (gterm_read (fst t2) (snd t2))) /\
    (forall t3, list_inc (dfv t3) L -> gterm_wf (t3, snd t1) ->
           star beta (dterm_read1 (gterm_read t3 (snd t1))) (dterm_read1 (gterm_read t3 (snd t2)))).
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
      apply star_beta_app; eauto using dlc_lc.
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
      apply star_beta_app; eauto using dlc_lc.
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
      match goal with [ |- star beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply star_beta_lam with (x := x); try tauto.
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
      match goal with [ |- star beta (lam ?t1) (lam ?t2) ] => pick x \notin (L ++ L1 ++ fv t1 ++ fv t2) end.
      rewrite !in_app_iff in *.
      apply star_beta_lam with (x := x); try tauto.
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
      eapply star_compose.
      * eapply star_map_impl with (f := fun t => t [x := _]); [intros t4 t5; apply beta_subst|].
        -- apply dlc_lc. apply gterm_wf_read_lc.
           unfold gterm_wf; simpl; tauto.
        -- apply IHHred; [|unfold gterm_wf; simpl; tauto|assumption|unfold gterm_wf in *; simpl in *; tauto].
           unfold gterm_fv in *; simpl in *.
           eapply list_inc_trans; [|exact HL]. prove_list_inc.
      * apply star_star.
        eapply star_map_impl with (f := fun t => _ [x := t]).
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
