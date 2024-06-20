Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Pretty.
Require Import RedE.
Require Import Inductive.

(** Strong call-by-need pretty-big-step semantics. *)

Inductive eiM :=
| eiM_lazy : term -> list freevar -> eiM
| eiM_abs1 : term -> list freevar -> eiM
| eiM_abs2 : term -> list freevar -> nfvalx_or_lam -> eiM
| eiM_constr1 : nat -> list freevar -> eiM
| eiM_constr2 : nat -> list freevar -> nfvalx_or_lam -> eiM
| eiM_val : nfvalx -> eiM.
Definition memM := list (freevar * eiM).

Definition memdom (m : memM) := map fst m.

Notation memxM := (memM * list freevar)%type.

Inductive valM : deep_flag -> Type :=
| valM_nf : forall {df}, nfvalx -> valM df
| valMs_abs : term -> list freevar -> valM shallow
| valMd_abs : term -> list freevar -> nfvalx_or_lam -> valM deep
| valMs_constr : nat -> list freevar -> valM shallow
| valMd_constr : nat -> list freevar -> nfvalx_or_lam -> valM deep.


Inductive extM : deep_flag -> Type :=
| extM_term : forall df, list freevar -> memxM -> term -> extM df
| extM_clo : forall df, memxM -> freevar -> extM df
| extM_app : forall df, list freevar -> outM (valM shallow) memxM -> term -> extM df
| extM_appnf : forall df, list freevar -> nfvalx -> outM (valM deep) memxM -> extM df
| extM_switch : forall df, list freevar -> outM (valM shallow) memxM -> list (nat * term) -> extM df
| extM_switchnf1 : forall df, list freevar -> nfvalx -> list (list freevar * nfvalx_or_lam) -> memxM -> list (nat * term) -> extM df
| extM_switchnf2 : forall df, list freevar -> nfvalx -> list (list freevar * nfvalx_or_lam) -> list freevar -> outM (valM deep) memxM -> list (nat * term) -> extM df
| extMd_abs : list freevar -> freevar -> term -> outM (valM deep) memxM -> extM deep
| extMd_constr1 : nat -> list freevar -> list nfvalx_or_lam -> memxM -> list freevar -> extM deep
| extMd_constr2 : nat -> list freevar -> list nfvalx_or_lam -> outM (valM deep) memxM -> list freevar -> extM deep.

Arguments extM_term {df} _ _ _.
Arguments extM_clo {df} _ _.
Arguments extM_app {df} _ _ _.
Arguments extM_appnf {df} _ _ _.
Arguments extM_switch {df} _ _ _.
Arguments extM_switchnf1 {df} _ _ _ _ _.
Arguments extM_switchnf2 {df} _ _ _ _ _ _.

Definition get_out_memxM {df} (o : outM (valM df) memxM) :=
  match o with
  | outM_div => None
  | outM_ret _ m => Some m
  end.

Definition get_ext_memxM {df} (e : extM df) :=
  match e with
  | extM_term _ m _ => Some m
  | extM_clo m _ => Some m
  | extM_app _ o _ => get_out_memxM o
  | extM_appnf _ _ o => get_out_memxM o
  | extM_switch _ o _ => get_out_memxM o
  | extM_switchnf1 _ _ _ m _ => Some m
  | extM_switchnf2 _ _ _ _ o _ => get_out_memxM o
  | extMd_abs _ _ _ o => get_out_memxM o
  | extMd_constr1 _ _ _ m _ => Some m
  | extMd_constr2 _ _ _ o _ => get_out_memxM o
  end.

Definition update_mem (m : memxM) x u := (update_env (fst m) x u, snd m).

Inductive update_result : forall df, freevar -> outM (valM df) memxM -> outM (valM df) memxM -> Prop :=
| upr_nf : forall df x v m,
    update_result df x (outM_ret (valM_nf v) m) (outM_ret (valM_nf v) (update_mem m x (eiM_val v)))
| upr_shallow_abs : forall x t env m,
    update_result shallow x (outM_ret (valMs_abs t env) m) (outM_ret (valMs_abs t env) (update_mem m x (eiM_abs1 t env)))
| upr_deep_abs : forall x t env v m,
    update_result deep x (outM_ret (valMd_abs t env v) m) (outM_ret (valMd_abs t env v) (update_mem m x (eiM_abs2 t env v)))
| upr_shallow_constr : forall x tag l m,
    update_result shallow x (outM_ret (valMs_constr tag l) m) (outM_ret (valMs_constr tag l) (update_mem m x (eiM_constr1 tag l)))
| upr_deep_constr : forall x tag l v m,
    update_result deep x (outM_ret (valMd_constr tag l v) m) (outM_ret (valMd_constr tag l v) (update_mem m x (eiM_constr2 tag l v)))
| upr_div : forall df x, update_result df x outM_div outM_div.

Definition getvalMd_nf (v : valM deep) : nfvalx_or_lam :=
  match v return nfvalx_or_lam with
  | valM_nf v => nxval v
  | valMd_abs t l v => v
  | valMd_constr tag l v => v
  | valMs_abs _ _ => nxval (nxvar (proj1_sig (fresh nil)))
  | valMs_constr _ _ => nxval (nxvar (proj1_sig (fresh nil)))
  end.

Definition get_outM_abort {t1 t2 m} (o : outM t1 m) : option (outM t2 m) :=
  match o with
  | outM_div => Some outM_div
  | outM_ret _ _ => None
  end.

Definition get_abortM {df t} (e : extM df) : option (outM t memxM) :=
  match e with
  | extM_term _ _ _ => None
  | extM_clo _ _ => None
  | extM_app _ o _ => get_outM_abort o
  | extM_appnf _ _ o => get_outM_abort o
  | extM_switch _ o _ => get_outM_abort o
  | extM_switchnf1 _ _ _ _ _ => None
  | extM_switchnf2 _ _ _ _ o _ => get_outM_abort o
  | extMd_abs _ _ _ o => get_outM_abort o
  | extMd_constr1 _ _ _ _ _ => None
  | extMd_constr2 _ _ _ o _ => get_outM_abort o
  end.

Definition redM_mklazy t env (m1 : memxM) x (m2 : memxM) :=
  match env_get_maybe_var env t with
  | Some y => x = y /\ m2 = m1
  | None => env_find (fst m1) x = None /\ m2 = ((x, eiM_lazy t env) :: fst m1, snd m1)
  end.

Inductive redM_mknlazy : list term -> list freevar -> memxM -> list freevar -> memxM -> Prop :=
| redM_mknlazy_nil : forall env m, redM_mknlazy nil env m nil m
| redM_mknlazy_cons : forall t l env m1 x m2 xs m3,
    redM_mklazy t env m1 x m2 -> redM_mknlazy l env m2 xs m3 -> redM_mknlazy (t :: l) env m1 (x :: xs) m3.

Definition redM_newvar (m1 m2 : memxM) a x :=
  env_find (fst m1) a = None /\ x \notin snd m1 /\ m2 = ((a, eiM_val (nxvar x)) :: fst m1, x :: snd m1).

Inductive redM_nnewvar : memxM -> memxM -> list freevar -> list freevar -> nat -> Prop :=
| redM_nnewvar_0 : forall m, redM_nnewvar m m nil nil 0
| redM_nnewvar_S : forall m1 m2 m3 a la x lx n,
    redM_newvar m1 m2 a x -> redM_nnewvar m2 m3 la lx n -> redM_nnewvar m1 m3 (a :: la) (x :: lx) (S n).

Inductive redM_ (rec : forall df, extM df -> outM (valM df) memxM -> Prop) : forall df, extM df -> outM (valM df) memxM -> Prop :=
| redM_clo_val : forall df m x v,
    env_find (fst m) x = Some (eiM_val v) ->
    redM_ rec df (extM_clo m x) (outM_ret (valM_nf v) m)

| redM_clo_abs1_shallow : forall m x t env,
    env_find (fst m) x = Some (eiM_abs1 t env) ->
    redM_ rec shallow (extM_clo m x) (outM_ret (valMs_abs t env) m)
| redM_clo_abs1_deep : forall m x t env o1 o2,
    env_find (fst m) x = Some (eiM_abs1 t env) ->
    rec deep (extM_term env m (abs t)) o1 ->
    update_result deep x o1 o2 ->
    redM_ rec deep (extM_clo m x) o2
| redM_clo_abs2_shallow : forall m x t env body,
    env_find (fst m) x = Some (eiM_abs2 t env body) ->
    redM_ rec shallow (extM_clo m x) (outM_ret (valMs_abs t env) m)
| redM_clo_abs2_deep : forall m x t env body,
    env_find (fst m) x = Some (eiM_abs2 t env body) ->
    redM_ rec deep (extM_clo m x) (outM_ret (valMd_abs t env body) m)

| redM_clo_constr1_shallow : forall m x tag l,
    env_find (fst m) x = Some (eiM_constr1 tag l) ->
    redM_ rec shallow (extM_clo m x) (outM_ret (valMs_constr tag l) m)
| redM_clo_constr1_deep : forall m x tag l o1 o2,
    env_find (fst m) x = Some (eiM_constr1 tag l) ->
    rec deep (extMd_constr1 tag l nil m l) o1 ->
    update_result deep x o1 o2 ->
    redM_ rec deep (extM_clo m x) o2
| redM_clo_constr2_shallow : forall m x tag l v,
    env_find (fst m) x = Some (eiM_constr2 tag l v) ->
    redM_ rec shallow (extM_clo m x) (outM_ret (valMs_constr tag l) m)
| redM_clo_constr2_deep : forall m x tag l v,
    env_find (fst m) x = Some (eiM_constr2 tag l v) ->
    redM_ rec deep (extM_clo m x) (outM_ret (valMd_constr tag l v) m)

| redM_clo_lazy : forall df m x t env o1 o2,
    env_find (fst m) x = Some (eiM_lazy t env) ->
    rec df (extM_term env m t) o1 ->
    update_result df x o1 o2 ->
    redM_ rec df (extM_clo m x) o2

| redM_var_clo : forall df n env m x o,
    nth_error env n = Some x ->
    rec df (extM_clo m x) o ->
    redM_ rec df (extM_term env m (var n)) o

| redM_abs_shallow : forall t env m,
    redM_ rec shallow (extM_term env m (abs t)) (outM_ret (valMs_abs t env) m)
| redM_abs_deep : forall t env m1 m2 o1 o2 x a,
    redM_newvar m1 m2 a x ->
    rec deep (extM_term (a :: env) m2 t) o1 ->
    rec deep (extMd_abs env x t o1) o2 ->
    redM_ rec deep (extM_term env m1 (abs t)) o2
| redM_abs1 : forall x t env m v,
    redM_ rec deep (extMd_abs env x t (outM_ret v m)) (outM_ret (valMd_abs t env (nxlam x (getvalMd_nf v))) m)

| redM_app : forall df env m t1 o1 t2 o2,
    rec shallow (extM_term env m t1) o1 ->
    rec df (extM_app env o1 t2) o2 ->
    redM_ rec df (extM_term env m (app t1 t2)) o2
| redM_app1_nf : forall df env m v o1 t2 o2,
    rec deep (extM_term env m t2) o1 ->
    rec df (extM_appnf env v o1) o2 ->
    redM_ rec df (extM_app env (outM_ret (valM_nf v) m) t2) o2
| redM_app1_abs : forall df env env2 x m1 m2 t1 t2 o,
    redM_mklazy t2 env m1 x m2 ->
    rec df (extM_term (x :: env2) m2 t1) o ->
    redM_ rec df (extM_app env (outM_ret (valMs_abs t1 env2) m1) t2) o
| redM_appnf : forall df env m v1 v2,
    redM_ rec df (extM_appnf env v1 (outM_ret v2 m)) (outM_ret (valM_nf (nxapp v1 (getvalMd_nf v2))) m)

| redM_constr_shallow : forall env m1 m2 tag l lc,
    redM_mknlazy l env m1 lc m2 ->
    redM_ rec shallow (extM_term env m1 (constr tag l)) (outM_ret (valMs_constr tag lc) m2)
| redM_constr_deep : forall env m1 m2 tag l lc o,
    redM_mknlazy l env m1 lc m2 ->
    rec deep (extMd_constr1 tag lc nil m2 lc) o ->
    redM_ rec deep (extM_term env m1 (constr tag l)) o
| redM_constr1_done : forall m tag l l1,
    redM_ rec deep (extMd_constr1 tag l l1 m nil) (outM_ret (valMd_constr tag l (nxconstr tag l1)) m)
| redM_constr1_step : forall m tag l l1 l2 x o1 o2,
    rec deep (extM_clo m x) o1 ->
    rec deep (extMd_constr2 tag l l1 o1 l2) o2 ->
    redM_ rec deep (extMd_constr1 tag l l1 m (x :: l2)) o2
| redM_constr2 : forall m tag l l1 l2 v o,
    rec deep (extMd_constr1 tag l (l1 ++ getvalMd_nf v :: nil) m l2) o ->
    redM_ rec deep (extMd_constr2 tag l l1 (outM_ret v m) l2) o

| redM_switch : forall df m env t o1 s o2,
    rec shallow (extM_term env m t) o1 ->
    rec df (extM_switch env o1 s) o2 ->
    redM_ rec df (extM_term env m (switch t s)) o2
| redM_switch1_constr : forall df m env tag l s t o,
    nth_error s tag = Some (length l, t) ->
    rec df (extM_term (l ++ env) m t) o ->
    redM_ rec df (extM_switch env (outM_ret (valMs_constr tag l) m) s) o
| redM_switch1_nf : forall df m env v s o,
    rec df (extM_switchnf1 env v nil m s) o ->
    redM_ rec df (extM_switch env (outM_ret (valM_nf v) m) s) o
| redM_switchnf1_done : forall df m env v s,
    redM_ rec df (extM_switchnf1 env v s m nil) (outM_ret (valM_nf (nxswitch v s)) m)
| redM_switchnf1_step : forall df m1 m2 env v s1 s2 p t la lx o1 o2,
    redM_nnewvar m1 m2 la lx p ->
    rec deep (extM_term (la ++ env) m2 t) o1 ->
    rec df (extM_switchnf2 env v s1 lx o1 s2) o2 ->
    redM_ rec df (extM_switchnf1 env v s1 m1 ((p, t) :: s2)) o2
| redM_switchnf2 : forall df m env s1 s2 v1 v2 xs o,
    rec df (extM_switchnf1 env v1 (s1 ++ (xs, getvalMd_nf v2) :: nil) m s2) o ->
    redM_ rec df (extM_switchnf2 env v1 s1 xs (outM_ret v2 m) s2) o

| redM_abort : forall df e o, get_abortM e = Some o -> redM_ rec df e o.

Inductive redM : forall df, extM df -> outM (valM df) memxM -> Prop :=
| mkredM : forall df e o, redM_ redM df e o -> redM df e o.

CoInductive coredM : forall df, extM df -> outM (valM df) memxM -> Prop :=
| mkcoredM : forall df e o, redM_ coredM df e o -> coredM df e o.

Lemma redM_is_ind3 : is_ind3 redM_ redM.
Proof. prove_ind3. Qed.

(** Lemmas for proofs and stronger induction principles. *)

Lemma update_env_fst :
  forall {A : Type} (env : list (freevar * A)) x u, map fst env \subseteq map fst (update_env env x u).
Proof.
  induction env as [|[y v] env]; intros x u z; simpl in *.
  - tauto.
  - destruct freevar_eq_dec.
    + simpl. subst. tauto.
    + simpl. specialize (IHenv x u z). tauto.
Qed.

Lemma update_result_memxM :
  forall df x m1 o1 o2, update_result df x o1 o2 -> get_out_memxM o1 = Some m1 -> exists m2, get_out_memxM o2 = Some m2 /\ memdom (fst m1) \subseteq memdom (fst m2) /\ snd m1 = snd m2.
Proof.
  intros df x [m1 xs] o1 o2 H1 H2.
  inversion H1; unexistT; subst; unexistT; subst; simpl in *; autoinjSome;
    unfold update_mem in *; simpl in *; try (refine (ex_intro _ (_, _) _); splits 3; [reflexivity| |reflexivity]; apply update_env_fst).
  congruence.
Qed.

Definition is_divM {df} (e : extM df) :=
  match e with
  | extM_term _ _ _ => False
  | extM_clo _ _ => False
  | extM_app _ o _ => o = outM_div
  | extM_appnf _ _ o => o = outM_div
  | extM_switch _ o _ => o = outM_div
  | extM_switchnf1 _ _ _ _ _ => False
  | extM_switchnf2 _ _ _ _ o _ => o = outM_div
  | extMd_abs _ _ _ o => o = outM_div
  | extMd_constr1 _ _ _ _ _ => False
  | extMd_constr2 _ _ _ o _ => o = outM_div
  end.

Lemma get_out_memxM_div :
  forall df (o : outM (valM df) memxM), o = outM_div <-> get_out_memxM o = None.
Proof.
  intros df o; destruct o; simpl; split; intros; congruence.
Qed.

Lemma is_divM_get_ext_memxM :
  forall df (e : extM df), is_divM e <-> get_ext_memxM e = None.
Proof.
  intros df e; destruct e; simpl in *; try apply get_out_memxM_div; split; intros; (discriminate || tauto).
Qed.

Lemma update_result_not_div :
  forall df x o1 o2, update_result df x o1 o2 -> o2 = outM_div -> o1 = outM_div.
Proof.
  intros df x o1 o2 H. inversion H; subst; unexistT; subst; try discriminate.
  intros; reflexivity.
Qed.

Lemma redM_not_div :
  forall df e o, redM df e o -> o = outM_div -> is_divM e.
Proof.
  refine (preserved3_rec _ _ redM_is_ind3 _ _).
  intros df e o H; inversion H; unexistT; subst; unexistT; subst; try discriminate; try eassumption;
    try (match goal with [ H : update_result _ _ _ _ |- _ ] => assert (Hdiv := update_result_not_div _ _ _ _ H) end); simpl in *; try tauto.
  destruct e; simpl in *; try congruence; destruct o0; simpl in *; congruence.
Qed.


Lemma redM_mklazy_usedvars_eq :
  forall t env m1 x m2, redM_mklazy t env m1 x m2 -> snd m1 = snd m2.
Proof.
  intros t env m1 x m2 H; unfold redM_mklazy in H.
  destruct env_get_maybe_var; destruct H as [_ ->]; reflexivity.
Qed.

Lemma redM_mknlazy_usedvars_eq :
  forall l env m1 xs m2, redM_mknlazy l env m1 xs m2 -> snd m1 = snd m2.
Proof.
  intros l env m1 xs m2 H. induction H.
  - reflexivity.
  - erewrite redM_mklazy_usedvars_eq; eassumption.
Qed.

Lemma redM_newvar_usedvars_inc :
  forall m1 m2 x a, redM_newvar m1 m2 x a -> snd m1 \subseteq snd m2.
Proof.
  intros m1 m2 x a (H1 & H2 & H3). subst. simpl. prove_list_inc.
Qed.

Lemma redM_nnewvar_usedvars_inc :
  forall m1 m2 lx la n, redM_nnewvar m1 m2 lx la n -> snd m1 \subseteq snd m2.
Proof.
  intros m1 m2 lx la n H; induction H.
  - reflexivity.
  - rewrite <- IHredM_nnewvar. eapply redM_newvar_usedvars_inc; eassumption.
Qed.

Lemma redM_usedvars_inc :
  forall df e o, redM df e o -> forall m1, get_ext_memxM e = Some m1 -> match get_out_memxM o with Some m2 => snd m1 \subseteq snd m2 | None => False end.
Proof.
  refine (preserved3_rec _ _ redM_is_ind3 _ _).
  intros df e o H m1 Hm1.
  inversion H; unexistT; subst; unexistT; subst; simpl in *; try discriminate; autoinjSome; try reflexivity.
  Local Ltac use_rec2 H :=
    let Hred := fresh "Hred" in
    let Hrec := fresh "Hrec" in
    destruct H as [Hred Hrec]; specialize (Hrec _ eq_refl).
  - use_rec2 H6. destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    eapply update_result_memxM in H7; [|eassumption].
    destruct H7 as (m2 & -> & ? & <-). assumption.
  - use_rec2 H6. destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    eapply update_result_memxM in H7; [|eassumption].
    destruct H7 as (m2 & -> & ? & <-). assumption.
  - use_rec2 H4. destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    eapply update_result_memxM in H5; [|eassumption].
    destruct H5 as (m2 & -> & ? & <-). assumption.
  - use_rec2 H4. assumption.
  - use_rec2 H6. simpl in *.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H7.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; [|eassumption]. etransitivity; [|eassumption].
    eapply redM_newvar_usedvars_inc; eassumption.
  - use_rec2 H3. simpl in *.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H4.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; eassumption.
  - use_rec2 H3. simpl in *.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H4.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; eassumption.
  - use_rec2 H4.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    erewrite redM_mklazy_usedvars_eq; eassumption.
  - erewrite redM_mknlazy_usedvars_eq; [|eassumption]. reflexivity.
  - use_rec2 H6. erewrite redM_mknlazy_usedvars_eq; eassumption.
  - use_rec2 H4.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H6.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; eassumption.
  - use_rec2 H2. eassumption.
  - use_rec2 H3.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H4.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; eassumption.
  - use_rec2 H4. eassumption.
  - use_rec2 H3. eassumption.
  - use_rec2 H4.
    destruct (get_out_memxM o1) eqn:Ho1; [|tauto].
    use_rec2 H5.
    destruct (get_out_memxM o) eqn:Ho; [|tauto].
    etransitivity; [|eassumption]. etransitivity; [|eassumption].
    eapply redM_nnewvar_usedvars_inc; eassumption.
  - use_rec2 H3. eassumption.
  - destruct e; simpl in *; try congruence; destruct o0; simpl in *; congruence.
Qed.

Lemma redM_abs_deep_result :
  forall env m t o, redM deep (extM_term env m (abs t)) o -> exists v m2, o = outM_ret (valMd_abs t env v) m2.
Proof.
  intros env m t o H.
  inversion H; unexistT; subst. inversion H3; unexistT; subst; [|simpl in *; congruence].
  inversion H7; unexistT; subst. inversion H4; unexistT; subst.
  - eexists; eexists. reflexivity.
  - exfalso. apply redM_not_div in H6; simpl in *; [assumption|].
    apply redM_not_div in H7; simpl in *; [assumption|].
    destruct o1; simpl in *; congruence.
Qed.

Lemma redM_deep_constr_aux :
  forall df e o, redM df e o -> forall (p : df = deep) tag l v m,
      (let e := match p in _ = df return extM df with eq_refl => e end in (exists l1 m l2, e = extMd_constr1 tag l l1 m l2) \/ (exists l1 o l2, e = extMd_constr2 tag l l1 o l2)) ->
      o = outM_ret v m -> exists v2, match p in _ = df return valM df with eq_refl => v end = valMd_constr tag l v2.
Proof.
  refine (preserved3_rec _ _ redM_is_ind3 _ _).
  intros df e o H p tag l v m [(l1 & m2 & l2 & He) | (l1 & o2 & l2 & He)] Hv;
  inversion H; unexistT; subst; unexistT; subst; try discriminate;
    repeat (match goal with [ H : _ /\ (forall (p : _ = deep), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - injection H3 as; injection H5 as; subst. eexists; reflexivity.
  - eapply Hrec; [|reflexivity].
    injection H1 as; subst; right; repeat eexists; reflexivity.
  - eapply Hrec; [|reflexivity].
    injection H3 as; subst; left; repeat eexists; reflexivity.
  - destruct o2; simpl in *; congruence.
Qed.

Lemma redM_constr_deep_result :
  forall m tag l1 vs l2 o, redM deep (extMd_constr1 tag l1 vs m l2) o -> exists v m2, o = outM_ret (valMd_constr tag l1 v) m2.
Proof.
  intros m tag l1 vs l2 o H.
  destruct o as [v m2|]; [|eapply redM_not_div in H; simpl in *; tauto].
  eapply redM_deep_constr_aux with (p := eq_refl) in H; simpl in *; [| |reflexivity].
  - destruct H as (v2 & ->). do 2 eexists. reflexivity.
  - left. do 3 eexists. reflexivity.
Qed.

Lemma redM_nnewvar_distinct :
  forall m1 m2 la lx p, redM_nnewvar m1 m2 la lx p -> distinct (snd m1) p lx.
Proof.
  intros m1 m2 la lx p H. induction H.
  - constructor.
  - destruct H as (H1 & H2 & H3); subst m2; simpl in *.
    constructor; assumption.
Qed.

Lemma redM_nnewvar_incl :
  forall m1 m2 la lx p, redM_nnewvar m1 m2 la lx p -> lx \subseteq (snd m2).
Proof.
  intros m1 m2 la lx p H. induction H.
  - prove_list_inc.
  - rewrite list_inc_cons_left. split; [|assumption].
    destruct H as (H1 & H2 & H3); subst m2; simpl in *.
    eapply redM_nnewvar_usedvars_inc; [eassumption|]. simpl. tauto.
Qed.

