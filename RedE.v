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
Require Import Inductive.

Inductive clo :=
| clo_var : freevar -> clo
| clo_term : list freevar -> term -> list clo -> clo.

Fixpoint clo_fv c :=
  match c with
  | clo_var x => x :: nil
  | clo_term xs t l => concat (map clo_fv l)
  end.

Inductive clo_closed : clo -> Prop :=
| cc_var : forall x, clo_closed (clo_var x)
| cc_term : forall xs t l, closed_at t (length l) -> (forall c, c \in l -> clo_closed c /\ clo_fv c \subseteq xs) -> clo_closed (clo_term xs t l).

Fixpoint clo_ind2 (P : clo -> Prop) (Hvar : forall x, P (clo_var x)) (Hterm : forall xs t l, Forall P l -> P (clo_term xs t l)) (c : clo) : P c :=
  match c with
  | clo_var x => Hvar x
  | clo_term xs t l => Hterm xs t l ((fix H (l : _) : Forall P l :=
                                 match l with
                                 | nil => @Forall_nil _ _
                                 | cons c l => @Forall_cons _ _ c l (clo_ind2 P Hvar Hterm c) (H l)
                                 end) l)
  end.

Inductive nfvalx :=
| nxvar : freevar -> nfvalx
| nxapp : nfvalx -> nfvalx_or_lam -> nfvalx
| nxswitch : nfvalx -> list (list freevar * nfvalx_or_lam) -> nfvalx

with nfvalx_or_lam :=
| nxval : nfvalx -> nfvalx_or_lam
| nxlam : freevar -> nfvalx_or_lam -> nfvalx_or_lam
| nxconstr : nat -> list nfvalx_or_lam -> nfvalx_or_lam.

Inductive valE : deep_flag -> Type :=
| valE_nf : forall {df}, nfvalx -> valE df
| valEs_abs : term -> list clo -> valE shallow
| valEs_constr : nat -> list clo -> valE shallow
| valEd_abs : term -> list clo -> nfvalx_or_lam -> valE deep
| valEd_constr : nat -> list clo -> nfvalx_or_lam -> valE deep.

Inductive extE : deep_flag -> Type :=
| extE_term : forall df, list clo -> term -> extE df
| extE_clo : forall df, clo -> extE df
| extE_app : forall df, list clo -> out (valE shallow) -> term -> extE df
| extE_appnf : forall df, list clo -> nfvalx -> out (valE deep) -> extE df
| extE_switch : forall df, list clo -> out (valE shallow) -> list (nat * term) -> extE df
| extE_switchnf1 : forall df, list clo -> nfvalx -> list (list freevar * nfvalx_or_lam) -> list (nat * term) -> extE df
| extE_switchnf2 : forall df, list clo -> nfvalx -> list (list freevar * nfvalx_or_lam) -> list freevar -> out (valE deep) -> list (nat * term) -> extE df
| extEd_abs : list clo -> freevar -> term -> out (valE deep) -> extE deep
| extEd_constr1 : nat -> list clo -> list nfvalx_or_lam -> list clo -> extE deep
| extEd_constr2 : nat -> list clo -> list nfvalx_or_lam -> out (valE deep) -> list clo -> extE deep.

Arguments extE_term {df} _ _.
Arguments extE_clo {df} _.
Arguments extE_app {df} _ _ _.
Arguments extE_appnf {df} _ _ _.
Arguments extE_switch {df} _ _ _.
Arguments extE_switchnf1 {df} _ _ _ _.
Arguments extE_switchnf2 {df} _ _ _ _ _ _.

Fixpoint nfvalx_fv v :=
  match v with
  | nxvar x => x :: nil
  | nxapp v1 v2 => nfvalx_fv v1 ++ nfvalx_or_lam_fv v2
  | nxswitch t m => nfvalx_fv t ++ concat (map (fun pt2 => list_diff (nfvalx_or_lam_fv (snd pt2)) (fst pt2)) m)
  end

with nfvalx_or_lam_fv v :=
  match v with
  | nxval v => nfvalx_fv v
  | nxlam x v => list_remove x (nfvalx_or_lam_fv v)
  | nxconstr tag l => concat (map nfvalx_or_lam_fv l)
  end.

Definition cl_closed xs l := (forall c, c \in l -> clo_closed c /\ clo_fv c \subseteq xs).

Definition valE_closed {df} xs (v : valE df) :=
  match v with
  | valEs_abs t l => closed_at t (S (length l)) /\ cl_closed xs l
  | valE_nf v => nfvalx_fv v \subseteq xs
  | valEd_abs t l v => closed_at t (S (length l)) /\ cl_closed xs l /\ nfvalx_or_lam_fv v \subseteq xs
  | valEs_constr tag l => cl_closed xs l
  | valEd_constr tag l v => cl_closed xs l /\ nfvalx_or_lam_fv v \subseteq xs
  end.

Lemma cl_closed_mono :
  forall xs1 l, cl_closed xs1 l -> forall xs2, xs1 \subseteq xs2 -> cl_closed xs2 l.
Proof.
  intros xs1 l H xs2 Hinc c Hc; split; [apply H; assumption|].
  etransitivity; [|eassumption]. apply H; assumption.
Qed.

Lemma valE_closed_mono :
  forall df (v : valE df) xs1, valE_closed xs1 v -> forall xs2, xs1 \subseteq xs2 -> valE_closed xs2 v.
Proof.
  intros df v xs1 H xs2 Hinc; destruct v; simpl in *.
  - etransitivity; eassumption.
  - destruct H; split; [|eapply cl_closed_mono]; eassumption.
  - eapply cl_closed_mono; eassumption.
  - destruct H as (? & ? & ?); splits 3; [|eapply cl_closed_mono|etransitivity]; eassumption.
  - destruct H as (H & H2). split; [|etransitivity; eassumption].
    eapply cl_closed_mono; eassumption.
Qed.

Definition outE_closed {df} xs (o : out (valE df)) :=
  match o with
  | out_div => True
  | out_ret v => valE_closed xs v
  end.

Lemma outE_closed_mono :
  forall df (o : out (valE df)) xs1, outE_closed xs1 o -> forall xs2, xs1 \subseteq xs2 -> outE_closed xs2 o.
Proof.
  intros df o xs1 H xs2 Hinc; destruct o; simpl in *; [|tauto].
  eapply valE_closed_mono; eassumption.
Qed.

Inductive extE_closed_at : forall {df}, extE df -> list freevar -> Prop :=
| extE_term_closed : forall df env t xs, cl_closed xs env -> closed_at t (length env) -> extE_closed_at (@extE_term df env t) xs
| extE_clo_closed : forall df c xs, clo_closed c -> clo_fv c \subseteq xs -> extE_closed_at (@extE_clo df c) xs
| extE_app_closed : forall df env o t xs, cl_closed xs env -> closed_at t (length env) -> outE_closed xs o -> extE_closed_at (@extE_app df env o t) xs
| extE_appnf_closed : forall df env v o xs,
    cl_closed xs env -> nfvalx_fv v \subseteq xs -> outE_closed xs o -> extE_closed_at (@extE_appnf df env v o) xs
| extE_switch_closed : forall df env o m xs,
    cl_closed xs env ->
    (forall p t2, (p, t2) \in m -> closed_at t2 (p + length env)) ->
    outE_closed xs o ->
    extE_closed_at (@extE_switch df env o m) xs
| extE_switchnf1_closed : forall df env v m1 m2 xs,
    cl_closed xs env ->
    nfvalx_fv v \subseteq xs ->
    (forall xs2 v2, (xs2, v2) \in m1 -> nfvalx_or_lam_fv v2 \subseteq xs2 ++ xs) ->
    (forall p t2, (p, t2) \in m2 -> closed_at t2 (p + length env)) ->
    extE_closed_at (@extE_switchnf1 df env v m1 m2) xs
| extE_switchnf_closed : forall df env v m1 xs2 o m2 xs,
    cl_closed xs env ->
    nfvalx_fv v \subseteq xs ->
    (forall xs2 v2, (xs2, v2) \in m1 -> nfvalx_or_lam_fv v2 \subseteq xs2 ++ xs) ->
    (forall p t2, (p, t2) \in m2 -> closed_at t2 (p + length env)) ->
    outE_closed (xs2 ++ xs) o ->
    extE_closed_at (@extE_switchnf2 df env v m1 xs2 o m2) xs
| extEd_abs_closed : forall env o t x xs,
    cl_closed xs env -> closed_at t (S (length env)) -> outE_closed (x :: xs) o -> extE_closed_at (extEd_abs env x t o) xs
| extEd_constr1_closed : forall tag l l1 l2 xs,
    cl_closed xs l ->
    (forall v, v \in l1 -> nfvalx_or_lam_fv v \subseteq xs) ->
    cl_closed xs l2 ->
    extE_closed_at (extEd_constr1 tag l l1 l2) xs
| extEd_constr2_closed : forall tag l l1 o l2 xs,
    cl_closed xs l ->
    (forall v, v \in l1 -> nfvalx_or_lam_fv v \subseteq xs) ->
    outE_closed xs o ->
    cl_closed xs l2 ->
    extE_closed_at (extEd_constr2 tag l l1 o l2) xs.

Definition dummyvar := proj1_sig (fresh nil).
Definition dummy_nfvalx := nxvar dummyvar.
Definition dummy_nfvalx_or_lam := nxval dummy_nfvalx.

Definition getvalEd_nf (v : valE deep) : nfvalx_or_lam :=
  match v return nfvalx_or_lam with
  | valE_nf v => nxval v
  | valEd_abs t l v => v
  | valEd_constr tag l v => v
  | valEs_abs _ _ => dummy_nfvalx_or_lam
  | valEs_constr _ _ => dummy_nfvalx_or_lam
  end.

Definition get_abortE {df t} (e : extE df) : option (out t) :=
  match e with
  | extE_term _ _ => None
  | extE_clo _ => None
  | extE_app _ o _ => get_out_abort o
  | extE_appnf _ _ o => get_out_abort o
  | extE_switch _ o _ => get_out_abort o
  | extE_switchnf1 _ _ _ _ => None
  | extE_switchnf2 _ _ _ _ o _ => get_out_abort o
  | extEd_abs _ _ _ o => get_out_abort o
  | extEd_constr1 _ _ _ _ => None
  | extEd_constr2 _ _ _ o _ => get_out_abort o
  end.

Inductive redE_ (rec : forall df, list freevar -> list freevar -> list freevar -> extE df -> out (valE df) -> Prop) : forall df, list freevar -> list freevar -> list freevar -> extE df -> out (valE df) -> Prop :=
| redE_clo_term : forall df xs xs2 dom fvs t env o,
    xs2 \subseteq dom -> rec df xs2 dom (list_inter xs2 fvs) (extE_term env t) o -> redE_ rec df xs dom fvs (extE_clo (clo_term xs2 t env)) o
| redE_clo_var : forall df xs dom fvs x, redE_ rec df xs dom fvs (extE_clo (clo_var x)) (out_ret (valE_nf (nxvar x)))
| redE_var : forall df xs dom fvs env n c o,
    nth_error env n = Some c ->
    rec df xs dom fvs (extE_clo c) o ->
    redE_ rec df xs dom fvs (extE_term env (var n)) o
| redE_abs_shallow : forall t xs dom fvs env,
    redE_ rec shallow xs dom fvs (extE_term env (abs t)) (out_ret (valEs_abs t env))
| redE_abs_deep : forall t x xs dom fvs env o1 o2,
    x \notin xs -> x \in dom ->
    rec deep (x :: xs) dom (x :: fvs) (extE_term (clo_var x :: env) t) o1 ->
    rec deep xs dom fvs (extEd_abs env x t o1) o2 ->
    redE_ rec deep xs dom fvs (extE_term env (abs t)) o2
| redE_abs1 : forall x t xs dom fvs env v,
    redE_ rec deep xs dom fvs (extEd_abs env x t (out_ret v)) (out_ret (valEd_abs t env (nxlam x (getvalEd_nf v))))
| redE_app : forall df xs dom fvs env t1 o1 t2 o2,
    rec shallow xs dom fvs (extE_term env t1) o1 ->
    rec df xs dom fvs (extE_app env o1 t2) o2 ->
    redE_ rec df xs dom fvs (extE_term env (app t1 t2)) o2
| redE_app1_nf : forall df xs dom fvs env v o1 t2 o2,
    rec deep xs dom fvs (extE_term env t2) o1 ->
    rec df xs dom fvs (extE_appnf env v o1) o2 ->
    redE_ rec df xs dom fvs (extE_app env (out_ret (valE_nf v)) t2) o2
| redE_app1_abs : forall df xs xs2 dom fvs env env2 t1 t2 o,
    xs \subseteq xs2 -> xs2 \subseteq dom ->
    rec df xs dom fvs (extE_term (match env_get_maybe_var env t2 with Some c => c | _ => clo_term xs2 t2 env end :: env2) t1) o ->
    redE_ rec df xs dom fvs (extE_app env (out_ret (valEs_abs t1 env2)) t2) o
| redE_appnf : forall df xs dom fvs env v1 v2,
    redE_ rec df xs dom fvs (extE_appnf env v1 (out_ret v2)) (out_ret (valE_nf (nxapp v1 (getvalEd_nf v2))))
| redE_constr_shallow : forall xs dom fvs env tag l lc,
    Forall2 (fun t c => match env_get_maybe_var env t with Some c1 => c = c1 | None => exists xs2, xs \subseteq xs2 /\ xs2 \subseteq dom /\ c = clo_term xs2 t env end) l lc ->
    redE_ rec shallow xs dom fvs (extE_term env (constr tag l)) (out_ret (valEs_constr tag lc))
| redE_constr_deep : forall xs dom fvs env tag l lc o,
    Forall2 (fun t c => match env_get_maybe_var env t with Some c1 => c = c1 | None => exists xs2, xs \subseteq xs2 /\ xs2 \subseteq dom /\ c = clo_term xs2 t env end) l lc ->
    rec deep xs dom fvs (extEd_constr1 tag lc nil lc) o ->
    redE_ rec deep xs dom fvs (extE_term env (constr tag l)) o
| redE_constr1_done : forall xs dom fvs tag l l1,
    redE_ rec deep xs dom fvs (extEd_constr1 tag l l1 nil) (out_ret (valEd_constr tag l (nxconstr tag l1)))
| redE_constr1_step : forall xs dom fvs tag l l1 l2 c o1 o2,
    rec deep xs dom fvs (extE_clo c) o1 ->
    rec deep xs dom fvs (extEd_constr2 tag l l1 o1 l2) o2 ->
    redE_ rec deep xs dom fvs (extEd_constr1 tag l l1 (c :: l2)) o2
| redE_constr2 : forall xs dom fvs tag l l1 l2 v o,
    rec deep xs dom fvs (extEd_constr1 tag l (l1 ++ getvalEd_nf v :: nil) l2) o ->
    redE_ rec deep xs dom fvs (extEd_constr2 tag l l1 (out_ret v) l2) o
| redE_switch : forall df xs dom fvs env t o1 m o2,
    rec shallow xs dom fvs (extE_term env t) o1 ->
    rec df xs dom fvs (extE_switch env o1 m) o2 ->
    redE_ rec df xs dom fvs (extE_term env (switch t m)) o2
| redE_switch1_constr : forall df xs dom fvs env tag l m t o,
    nth_error m tag = Some (length l, t) ->
    rec df xs dom fvs (extE_term (l ++ env) t) o ->
    redE_ rec df xs dom fvs (extE_switch env (out_ret (valEs_constr tag l)) m) o
| redE_switch1_nf : forall df xs dom fvs env v m o,
    rec df xs dom fvs (extE_switchnf1 env v nil m) o ->
    redE_ rec df xs dom fvs (extE_switch env (out_ret (valE_nf v)) m) o
| redE_switchnf1_done : forall df xs dom fvs env v m,
    redE_ rec df xs dom fvs (extE_switchnf1 env v m nil) (out_ret (valE_nf (nxswitch v m)))
| redE_switchnf1_step : forall df xs ys dom fvs env v m1 m2 p t o1 o2,
    distinct xs p ys -> ys \subseteq dom ->
    rec deep (ys ++ xs) dom (ys ++ fvs) (extE_term (map clo_var ys ++ env) t) o1 ->
    rec df xs dom fvs (extE_switchnf2 env v m1 ys o1 m2) o2 ->
    redE_ rec df xs dom fvs (extE_switchnf1 env v m1 ((p, t) :: m2)) o2
| redE_switchnf2 : forall df xs dom fvs env m1 m2 v1 v2 ys o,
    rec df xs dom fvs (extE_switchnf1 env v1 (m1 ++ (ys, getvalEd_nf v2) :: nil) m2) o ->
    redE_ rec df xs dom fvs (extE_switchnf2 env v1 m1 ys (out_ret v2) m2) o
| redE_abort : forall df xs dom fvs e o, get_abortE e = Some o -> redE_ rec df xs dom fvs e o.

Inductive redE : forall df, list freevar -> list freevar -> list freevar -> extE df -> out (valE df) -> Prop :=
| mkredE : forall df xs dom fvs e o, redE_ redE df xs dom fvs e o -> redE df xs dom fvs e o.

CoInductive coredE : forall df, list freevar -> list freevar -> list freevar -> extE df -> out (valE df) -> Prop :=
| mkcoredE : forall df xs dom fvs e o, redE_ coredE df xs dom fvs e o -> coredE df xs dom fvs e o.

Lemma redE_is_ind6 : is_ind6 redE_ redE.
Proof. prove_ind6. Defined.

Lemma valE_nf_closed :
  forall df v xs, nfvalx_fv v \subseteq xs -> valE_closed xs (@valE_nf df v).
Proof.
  intros [|]; simpl; tauto.
Qed.

Lemma destruct_valE :
  forall df (v : valE df),
    { v2 | existT valE df v = existT valE df (valE_nf v2) } +
    { t & { env | existT valE df v = existT valE shallow (valEs_abs t env) } } +
    { t & { env & { v2 | existT valE df v = existT valE deep (valEd_abs t env v2) } } } +
    { tag & { l | existT valE df v = existT valE shallow (valEs_constr tag l) } } +
    { tag & { l & { v2 | existT valE df v = existT valE deep (valEd_constr tag l v2) } } }.
Proof.
  intros df v. destruct v.
  - left; left; left; left. exists n. reflexivity.
  - left; left; left; right. exists t. exists l. reflexivity.
  - left; right. exists n. exists l. reflexivity.
  - left; left; right. exists t. exists l. exists n. reflexivity.
  - right. exists n. exists l. exists n0. reflexivity.
Qed.

Lemma destruct_valE_deep :
  forall (v : valE deep),
    { v2 | v = valE_nf v2 } +
    { t & { env & { v2 | v = valEd_abs t env v2 } } } +
    { tag & { l & { v2 | v = valEd_constr tag l v2 } } }.
Proof.
  intros v. assert (H := destruct_valE deep v).
  destruct H as [[[[(v2 & Heq) | (t & env & Heq)] | (t & env & v2 & Heq)] | (tag & l & Heq)] | (tag & l & v2 & Heq)].
  - unexistT. left; left. exists v2. assumption.
  - apply projT1_eq in Heq; simpl in Heq; congruence.
  - unexistT. left; right. exists t. exists env. exists v2. assumption.
  - apply projT1_eq in Heq; simpl in Heq; congruence.
  - unexistT. right. exists tag. exists l. exists v2. assumption.
Qed.

Lemma redE_coredE :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> coredE df xs dom fvs e o.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom e o H. constructor.
  eapply (is_positive6 _ _ redE_is_ind6); [|eassumption].
  simpl. intros; tauto.
Qed.

Lemma redE_xsdom_mono :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> forall xs2 dom2 fvs2, xs2 \subseteq xs -> dom \subseteq dom2 -> redE df xs2 dom2 fvs2 e o.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H; inversion H; unexistT; subst; unexistT; subst; intros xs3 dom2 fvs2 Hxs3 Hdom2; constructor.
  - eapply redE_clo_term; [etransitivity; eassumption|]. eapply H7; [reflexivity|assumption].
  - eapply redE_clo_var.
  - eapply redE_var; [eassumption|]. eapply H7; eassumption.
  - eapply redE_abs_shallow.
  - eapply redE_abs_deep; [rewrite Hxs3; eassumption|rewrite <- Hdom2; eassumption|eapply H10; [|assumption]|eapply H11; assumption].
    intros y [<- | Hy]; [left; reflexivity|right; apply Hxs3; assumption].
  - eapply redE_abs1.
  - eapply redE_app; [eapply H6|eapply H7]; assumption.
  - eapply redE_app1_nf; [eapply H6|eapply H7]; assumption.
  - eapply redE_app1_abs; [| |eapply H8; assumption]; etransitivity; eassumption.
  - eapply redE_appnf.
  - eapply redE_constr_shallow. eapply Forall2_impl; [|eassumption].
    intros t c Htc. simpl in *. destruct env_get_maybe_var; [assumption|].
    destruct Htc as (xs2 & H1 & H2 & H3); exists xs2; splits 3; try assumption; etransitivity; eassumption.
  - eapply redE_constr_deep; [|eapply H9; eassumption]. eapply Forall2_impl; [|eassumption].
    intros t c Htc. simpl in *. destruct env_get_maybe_var; [assumption|].
    destruct Htc as (xs2 & H1 & H2 & H3); exists xs2; splits 3; try assumption; etransitivity; eassumption.
  - eapply redE_constr1_done.
  - eapply redE_constr1_step; [eapply H7|eapply H9]; eassumption.
  - eapply redE_constr2. eapply H5; eassumption.
  - eapply redE_switch; [eapply H6|eapply H7]; eassumption.
  - eapply redE_switch1_constr; [eassumption|].
    eapply H7; eassumption.
  - eapply redE_switch1_nf. eapply H6; eassumption.
  - eapply redE_switchnf1_done.
  - eapply redE_switchnf1_step; [| |eapply H8|eapply H9].
    + eapply distinct_incl; eassumption.
    + etransitivity; eassumption.
    + rewrite Hxs3. reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
  - eapply redE_switchnf2. eapply H6; eassumption.
  - eapply redE_abort. eassumption.
Qed.

Lemma redE_xs_mono :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> forall xs2, xs2 \subseteq xs -> redE df xs2 dom fvs e o.
Proof.
  intros; eapply redE_xsdom_mono; try eassumption. reflexivity.
Qed.

Lemma redE_dom_mono :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> forall dom2, dom \subseteq dom2 -> redE df xs dom2 fvs e o.
Proof.
  intros; eapply redE_xsdom_mono; try eassumption. reflexivity.
Qed.

Lemma redE_fvs_any :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> forall fvs2, redE df xs dom fvs2 e o.
Proof.
  intros; eapply redE_xsdom_mono; try eassumption; reflexivity.
Qed.

Lemma out_abort_div :
  forall df t (e : extE df) (o : out t), get_abortE e = Some o -> o = out_div.
Proof.
  intros; destruct e; simpl in *; try congruence; autoinjSome; eapply get_out_abort_div; eassumption.
Qed.

Lemma valE_closed_fv :
  forall xs v, valE_closed xs v -> nfvalx_or_lam_fv (getvalEd_nf v) \subseteq xs.
Proof.
  intros xs v Hv.
  destruct (destruct_valE_deep v) as [[(v2 & ->) | (t2 & env2 & v2 & ->)] | (tag & l & v2 & ->)]; simpl in *; tauto.
Qed.

Lemma closed_preserved_down_H :
  forall Q df xs dom fvs e o,
    redE_ (fun df xs dom fvs e o => Q df xs dom fvs e o /\ (fvs \subseteq xs -> extE_closed_at e fvs -> outE_closed fvs o)) df xs dom fvs e o -> fvs \subseteq xs /\ extE_closed_at e fvs ->
    redE_ (fun df xs dom fvs e o => Q df xs dom fvs e o /\ fvs \subseteq xs /\ extE_closed_at e fvs) df xs dom fvs e o /\ outE_closed fvs o.
Proof.
  intros Q df xs dom fvs e o H [Hfvs He].
  Local Ltac use_rec H1 H2 :=
    destruct H1 as [H1 H2];
    match type of H2 with
    | ?A -> ?B -> ?C =>
      let Hfvs := fresh "Hfvs" in
      let Hclosed := fresh "Hclosed" in
      enough (Hclosed : B); [enough (Hfvs : A); [specialize (H2 Hfvs Hclosed); try solve [split; [econstructor; try splits 3; eassumption|assumption]]|
                                                 try assumption]|try assumption]
    end.
  inversion H; unexistT; subst; unexistT; subst; match goal with [ _ : context[get_abortE] |- _ ] => idtac | _ => inversion He; subst end.
  - inversion H1; subst.
    use_rec H7 Ho.
    + split; [|eapply outE_closed_mono; [apply Ho|apply list_inter_subl2]].
      constructor; [assumption|]. splits 3; assumption.
    + apply list_inter_subl1.
    + constructor; [|assumption].
      intros c Hc; split; [apply H8; assumption|].
      simpl in H3. rewrite concat_incl, Forall_map, Forall_forall in H3.
      rewrite list_inter_subr; split; [apply H8; assumption|apply H3; assumption].
  - split; [constructor|]. assumption.
  - use_rec H7 Ho.
    constructor; eapply H3, nth_error_In; eassumption.
  - split; [constructor|]. simpl.
    split; [|assumption].
    inversion H6; assumption.
  - inversion H7; subst.
    use_rec H10 Ho1.
    + use_rec H11 Ho.
      constructor; assumption.
    + rewrite Hfvs; reflexivity.
    + inversion He; subst. constructor.
      * intros c [<- | Hc]; split; [constructor|simpl; prove_list_inc|apply H5; assumption|].
        etransitivity; [apply H5; assumption|]. prove_list_inc.
      * assumption.
  - split; [constructor|]. simpl.
    splits 3; try assumption.
    simpl in *. apply valE_closed_fv in H9.
    intros y Hy. rewrite list_remove_correct in Hy.
    destruct (H9 y ltac:(tauto)); tauto.
  - inversion H5; subst.
    use_rec H6 Ho1; [|constructor; assumption].
    use_rec H7 Ho.
    constructor; assumption.
  - use_rec H6 Ho1; [|constructor; assumption].
    use_rec H7 Ho.
    constructor; assumption.
  - use_rec H8 Ho.
    constructor; simpl in *; [|tauto].
    intros c [<- | Hc].
    + destruct env_get_maybe_var as [c|] eqn:Hc; [eapply H5, env_get_maybe_var_in; eassumption|].
      split; simpl.
      * constructor; [assumption|]. eapply cl_closed_mono; [eassumption|]. etransitivity; eassumption.
      * rewrite concat_incl, Forall_map, Forall_forall.
        intros; apply H5; assumption.
    + simpl in *. apply H10. assumption.
  - split; [constructor|]. simpl. rewrite list_inc_app_left.
    split; [assumption|apply valE_closed_fv; assumption].
  - split; [constructor; assumption|]. simpl.
    intros c Hc. destruct (Forall2_In_right _ _ _ _ _ _ H5 Hc) as (t & Ht1 & Htc).
    destruct env_get_maybe_var eqn:Hc1.
    + subst. apply H4. eapply env_get_maybe_var_in; eassumption.
    + destruct Htc as (xs2 & Hxs2a & Hxs2b & ->).
      split; simpl.
      * constructor; [inversion H8; subst; apply H6; assumption|].
        eapply cl_closed_mono; [eassumption|]. etransitivity; eassumption.
      * rewrite concat_incl, Forall_map, Forall_forall.
        intros; apply H4; assumption.
  - use_rec H9 Ho.
    enough (cl_closed fvs lc) by (constructor; [|intros _ []|]; assumption).
    intros c Hc. destruct (Forall2_In_right _ _ _ _ _ _ H7 Hc) as (t & Ht1 & Htc).
    destruct env_get_maybe_var eqn:Hc1.
    + subst. apply H4. eapply env_get_maybe_var_in; eassumption.
    + destruct Htc as (xs2 & Hxs2a & Hxs2b & ->).
      split; simpl.
      * constructor; [inversion H8; subst; apply H5; assumption|].
        eapply cl_closed_mono; [eassumption|]. etransitivity; eassumption.
      * rewrite concat_incl, Forall_map, Forall_forall.
        intros; apply H4; assumption.
  - split; [constructor|]. simpl.
    split; [assumption|]. rewrite concat_incl, Forall_map, Forall_forall. assumption.
  - use_rec H7 Ho1; [|constructor; apply H11; simpl; tauto].
    use_rec H9 Ho.
    constructor; try tauto. intros c2 Hc2; apply H11; simpl in *; tauto.
  - use_rec H5 Ho.
    constructor; try assumption.
    intros v2 Hv2. rewrite in_app_iff in Hv2; simpl in Hv2.
    destruct Hv2 as [Hv2 | [<- | []]]; [apply H10; assumption|].
    apply valE_closed_fv, H11.
  - inversion H5; subst.
    use_rec H6 Ho1; [|constructor; assumption].
    use_rec H7 Ho. constructor; assumption.
  - use_rec H7 Ho.
    constructor.
    + intros c Hc; rewrite in_app_iff in Hc; destruct Hc as [Hc | Hc].
      * apply H9. assumption.
      * apply H4. assumption.
    + rewrite app_length.
      eapply H8, nth_error_In; eassumption.
  - use_rec H6 Ho.
    constructor; try assumption.
    intros xs2 v2 [].
  - split; [constructor|]. simpl.
    rewrite list_inc_app_left. split; [assumption|].
    rewrite concat_incl, Forall_map, Forall_forall. intros [xs2 v2] Hxsv2. simpl.
    apply H8 in Hxsv2. rewrite Hxsv2. intros y Hy. rewrite list_diff_In_iff, in_app_iff in Hy. tauto.
  - use_rec H8 Ho1.
    + use_rec H9 Ho.
      constructor; try tauto. intros; apply H13; simpl; tauto.
    + rewrite Hfvs. reflexivity.
    + constructor.
      * intros c Hc; rewrite in_app_iff, in_map_iff in Hc; destruct Hc as [(y & <- & Hy) | Hc].
        -- simpl. split; [constructor; assumption|]. intros z [<- | []]. rewrite in_app_iff; tauto.
        -- eapply cl_closed_mono; try eassumption. prove_list_inc.
      * erewrite app_length, map_length, distinct_length; [|eassumption].
        apply H13; simpl; tauto.
  - use_rec H6 Ho.
    constructor; try tauto.
    intros xs2 v Hxsv2; rewrite in_app_iff in Hxsv2; destruct Hxsv2 as [Hxsv2 | [[=<- <-] | []]].
    + apply H11. assumption.
    + apply valE_closed_fv, H13.
  - split.
    + constructor; assumption.
    + destruct e; simpl in *; try congruence;
        match goal with [ _ : get_out_abort ?o = _ |- _ ] => destruct o; simpl in *; autoinjSome; try congruence end;
        constructor.
Qed.

Lemma redE_closed :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> fvs \subseteq xs -> extE_closed_at e fvs -> outE_closed fvs o.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H1 H2 H3.
  eapply closed_preserved_down_H; [eassumption|]. split; assumption.
Qed.

Lemma closed_preserved_down :
  preserved_down6 redE_ redE (fun df xs dom fvs e o => fvs \subseteq xs /\ extE_closed_at e fvs).
Proof.
  intros df xs dom fvs e o Q H Hxse.
  eapply (is_positive6 _ _ redE_is_ind6); [|apply closed_preserved_down_H with (Q := fun df xs dom fvs e o => redE df xs dom fvs e o /\ Q df xs dom fvs e o)].
  - intros; simpl in *; tauto.
  - eapply (is_positive6 _ _ redE_is_ind6); [|eassumption].
    intros; simpl in *; split; [assumption|]. eapply redE_closed; apply H0.
  - assumption.
Qed.

Definition extE_shallow_to_deep (e : extE shallow) : extE deep :=
  match e return extE deep with
  | extE_term env t => extE_term env t
  | extE_clo c => extE_clo c
  | extE_app env o1 t2 => extE_app env o1 t2
  | extE_appnf env v1 o2 => extE_appnf env v1 o2
  | extE_switch env o m => extE_switch env o m
  | extE_switchnf1 env v m1 m2 => extE_switchnf1 env v m1 m2
  | extE_switchnf2 env v m1 xs o m2 => extE_switchnf2 env v m1 xs o m2
  | extEd_abs env x t o => extEd_abs env x t o
  | extEd_constr1 tag l l1 l2 => extEd_constr1 tag l l1 l2
  | extEd_constr2 tag l l1 o l2 => extEd_constr2 tag l l1 o l2
  end.

Definition extE_deep_to_shallow (e : extE deep) : option (extE shallow) :=
  match e return option (extE shallow) with
  | extE_term env t => Some (extE_term env t)
  | extE_clo c => Some (extE_clo c)
  | extE_app env o1 t2 => Some (extE_app env o1 t2)
  | extE_appnf env v1 o2 => Some (extE_appnf env v1 o2)
  | extE_switch env o m => Some (extE_switch env o m)
  | extE_switchnf1 env v m1 m2 => Some (extE_switchnf1 env v m1 m2)
  | extE_switchnf2 env v m1 xs o m2 => Some (extE_switchnf2 env v m1 xs o m2)
  | extEd_abs env x t o => None
  | extEd_constr1 tag l l1 l2 => None
  | extEd_constr2 tag l l1 o l2 => None
  end.

Lemma redE_shallow_deep_val_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = shallow) v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valE_nf v) ->
    redE deep xs dom fvs (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) (out_ret (valE_nf v)).
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p v Hv.
  inversion H; unexistT; subst; unexistT; subst; try discriminate;
    repeat (match goal with [ H : _ /\ (forall (p : _ = shallow), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end).
  - constructor. econstructor; [assumption|]. apply Hrec. reflexivity.
  - injection H6 as H6; subst. constructor; constructor.
  - constructor; econstructor; [eassumption|]. apply Hrec. reflexivity.
  - constructor; econstructor; [apply Hred0 | apply Hrec]. reflexivity.
  - constructor; econstructor; [apply H6 | apply Hrec]. reflexivity.
  - constructor; econstructor; [eassumption|eassumption|].
    apply Hrec. reflexivity.
  - injection H6 as H6; subst. constructor; econstructor.
  - constructor; econstructor; [apply Hred0 | apply Hrec]. reflexivity.
  - constructor; econstructor; [eassumption|]. apply Hrec. reflexivity.
  - constructor; econstructor. apply Hrec. reflexivity.
  - injection H6 as H6; subst. constructor; econstructor.
  - constructor; econstructor; try eassumption; [apply H8 | apply Hrec]. reflexivity.
  - constructor; econstructor. apply Hrec. reflexivity.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_shallow_deep_val :
  forall xs dom fvs e v, redE shallow xs dom fvs e (out_ret (valE_nf v)) ->
         redE deep xs dom fvs (extE_shallow_to_deep e) (out_ret (valE_nf v)).
Proof.
  intros xs dom fvs e v H.
  exact (redE_shallow_deep_val_aux shallow xs dom fvs e _ H eq_refl v eq_refl).
Qed.

Lemma redE_shallow_deep_abs_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = shallow) t env, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEs_abs t env) ->
    forall o2 dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 fvs (extE_term env (abs t)) o2 -> redE deep xs dom2 fvs (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) o2.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p t env Htenv o2 dom2 Hxs Hdom Hred2.
  inversion H; unexistT; subst; unexistT; subst; try discriminate;
    repeat (match goal with [ H : _ /\ (forall (p : _ = shallow), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - constructor; econstructor; [etransitivity; eassumption|].
    eapply Hrec; try reflexivity; try eassumption.
    eapply redE_fvs_any; eassumption.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; try reflexivity; try eassumption.
  - injection H8 as; subst. eapply redE_xs_mono; eassumption.
  - constructor; econstructor; [eapply redE_dom_mono; [apply Hred0|assumption] | eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [eapply redE_dom_mono; [apply H6|assumption]|eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [| |eapply Hrec]; try eassumption; [etransitivity; eassumption|reflexivity].
  - constructor; econstructor; [eapply redE_dom_mono; [apply Hred0|assumption] | eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [eassumption|].
    eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor. eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor; [eassumption|etransitivity; eassumption|eapply redE_dom_mono; [apply H8|assumption]|].
    eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor. eapply Hrec; try reflexivity; eassumption.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_shallow_deep_abs :
  forall xs dom fvs e t env,
    redE shallow xs dom fvs e (out_ret (valEs_abs t env)) ->
    forall o dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 fvs (extE_term env (abs t)) o -> redE deep xs dom2 fvs (extE_shallow_to_deep e) o.
Proof.
  intros xs dom fvs e t env H.
  exact (redE_shallow_deep_abs_aux shallow xs dom fvs e _ H eq_refl t env eq_refl).
Qed.


Lemma redE_deep_constr_aux :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> forall (p : df = deep) tag l v,
      (let e := match p in _ = df return extE df with eq_refl => e end in (exists l1 l2, e = extEd_constr1 tag l l1 l2) \/ (exists l1 o l2, e = extEd_constr2 tag l l1 o l2)) ->
      o = out_ret v -> exists v2, match p in _ = df return valE df with eq_refl => v end = valEd_constr tag l v2.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p tag l v [(l1 & l2 & He) | (l1 & o2 & l2 & He)] Hv;
  inversion H; unexistT; subst; unexistT; subst; try discriminate;
    repeat (match goal with [ H : _ /\ (forall (p : _ = deep), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - injection H8 as; injection H6 as; subst. eexists; reflexivity.
  - eapply Hrec; [|reflexivity].
    injection H1 as; subst; right; repeat eexists; reflexivity.
  - eapply Hrec; [|reflexivity].
    injection H6 as; subst; left; repeat eexists; reflexivity.
  - apply get_out_abort_div in H6. congruence.
Qed.

Lemma redE_deep_constr1 :
  forall xs dom fvs tag l l1 l2 v, redE deep xs dom fvs (extEd_constr1 tag l l1 l2) (out_ret v) ->
                              exists v2, v = valEd_constr tag l v2.
Proof.
  intros xs dom fvs tag l l1 l2 v H.
  eapply redE_deep_constr_aux with (p := eq_refl); [eassumption| |reflexivity].
  simpl. left. repeat eexists; reflexivity.
Qed.

Lemma redE_deep_constr2 :
  forall xs dom fvs tag l l1 o l2 v, redE deep xs dom fvs (extEd_constr2 tag l l1 o l2) (out_ret v) ->
                              exists v2, v = valEd_constr tag l v2.
Proof.
  intros xs dom fvs tag l l1 o l2 v H.
  eapply redE_deep_constr_aux with (p := eq_refl); [eassumption| |reflexivity].
  simpl. right. repeat eexists; reflexivity.
Qed.

Lemma redE_shallow_deep_constr_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = shallow) tag l, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEs_constr tag l) ->
    forall o2 dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 fvs (extEd_constr1 tag l nil l) o2 -> redE deep xs dom2 fvs (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) o2.
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p tag l Htagl o2 dom2 Hxs Hdom Hred2.
  inversion H; unexistT; subst; unexistT; subst; try discriminate;
    repeat (match goal with [ H : _ /\ (forall (p : _ = shallow), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - constructor; econstructor; [etransitivity; eassumption|].
    eapply Hrec; try reflexivity; try eassumption.
    eapply redE_fvs_any; eassumption.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; try reflexivity; try eassumption.
  - constructor; econstructor; [eapply redE_dom_mono; [apply Hred0|assumption] | eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [eapply redE_dom_mono; [apply H6|assumption]|eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [| |eapply Hrec]; try eassumption; [etransitivity; eassumption|reflexivity].
  - injection H8 as; subst. constructor; econstructor; [|eapply redE_xs_mono; eassumption].
    eapply Forall2_impl; [|eassumption]. simpl.
    intros t c Htc. destruct env_get_maybe_var; [assumption|].
    destruct Htc as (xs2 & Hxs2a & Hxs2b & Hc); exists xs2; splits 3; try assumption.
    etransitivity; eassumption.
  - constructor; econstructor; [eapply redE_dom_mono; [apply Hred0|assumption] | eapply Hrec; try reflexivity; eassumption].
  - constructor; econstructor; [eassumption|].
    eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor. eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor; [eassumption|etransitivity; eassumption|eapply redE_dom_mono; [apply H8|assumption]|].
    eapply Hrec; try reflexivity; eassumption.
  - constructor; econstructor. eapply Hrec; try reflexivity; eassumption.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_shallow_deep_constr :
  forall xs dom fvs e tag l,
    redE shallow xs dom fvs e (out_ret (valEs_constr tag l)) ->
    forall o dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 fvs (extEd_constr1 tag l nil l) o -> redE deep xs dom2 fvs (extE_shallow_to_deep e) o.
Proof.
  intros xs dom fvs e tag l H.
  exact (redE_shallow_deep_constr_aux shallow xs dom fvs e _ H eq_refl tag l eq_refl).
Qed.


Lemma redE_deep_shallow_abs_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = deep) t env v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEd_abs t env v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valEs_abs t env)).
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p t env v Htenv e2 He2.
  inversion H; unexistT; subst; unexistT; subst; try discriminate; simpl in *; autoinjSome;
    repeat (match goal with [ H : _ /\ (forall (p : _ = deep), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - enough (Heq : t = t0 /\ env = env0) by (destruct Heq; subst; constructor; econstructor).
    inversion Hred; unexistT; subst.
    inversion H11; unexistT; subst; [tauto|apply out_abort_div in H12; congruence].
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [apply Hred0 | eapply Hrec]; reflexivity.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - apply redE_deep_constr1 in Hred as [v2 Hred]. congruence.
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_deep_shallow_abs :
  forall xs dom fvs e t env v,
    redE deep xs dom fvs e (out_ret (valEd_abs t env v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valEs_abs t env)).
Proof.
  intros xs dom fvs e t env v H e2 He2.
  exact (redE_deep_shallow_abs_aux deep xs dom fvs e _ H eq_refl t env v eq_refl e2 He2).
Qed.


Lemma redE_deep_shallow_constr_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = deep) tag l v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEd_constr tag l v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valEs_constr tag l)).
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p tag l v Htagl e2 He2.
  inversion H; unexistT; subst; unexistT; subst; try discriminate; simpl in *; autoinjSome;
    repeat (match goal with [ H : _ /\ (forall (p : _ = deep), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - inversion Hred; unexistT; subst. inversion H11; unexistT; subst.
    apply out_abort_div in H12; congruence.
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [apply Hred0 | eapply Hrec]; reflexivity.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - apply redE_deep_constr1 in Hred as [v2 Hred]. injection Hred as; subst.
    constructor; econstructor; assumption.
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_deep_shallow_constr :
  forall xs dom fvs e tag l v,
    redE deep xs dom fvs e (out_ret (valEd_constr tag l v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valEs_constr tag l)).
Proof.
  intros xs dom fvs e tag l v H e2 He2.
  exact (redE_deep_shallow_constr_aux deep xs dom fvs e _ H eq_refl tag l v eq_refl e2 He2).
Qed.


Lemma redE_deep_shallow_val_aux :
  forall df xs dom fvs e o,
    redE df xs dom fvs e o -> forall (p : df = deep) v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valE_nf v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valE_nf v)).
Proof.
  refine (preserved6_rec _ _ redE_is_ind6 _ _).
  intros df xs dom fvs e o H p v Hv e2 He2.
  inversion H; unexistT; subst; unexistT; subst; try discriminate; simpl in *; autoinjSome;
    repeat (match goal with [ H : _ /\ (forall (p : _ = deep), _) |- _ ] => let Hred := fresh "Hred" in let Hrec := fresh "Hrec" in destruct H as [Hred Hrec]; specialize (Hrec eq_refl); simpl in Hrec end); simpl in *.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - injection H6 as; subst. constructor; econstructor.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - inversion Hred; unexistT; subst. inversion H11; unexistT; subst.
    apply out_abort_div in H12; congruence.
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [apply Hred0 | eapply Hrec]; reflexivity.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - injection H6 as; subst. constructor; econstructor.
  - apply redE_deep_constr1 in Hred as [v2 Hred]. congruence.
  - constructor; econstructor; [apply H6 | eapply Hrec]; reflexivity.
  - constructor; econstructor; [eassumption|].
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - injection H6 as; subst. constructor; econstructor.
  - constructor; econstructor; try eassumption.
    eapply Hrec; reflexivity.
  - constructor; econstructor. eapply Hrec; reflexivity.
  - apply out_abort_div in H6. congruence.
Qed.

Lemma redE_deep_shallow_val :
  forall xs dom fvs e v,
    redE deep xs dom fvs e (out_ret (valE_nf v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom fvs e2 (out_ret (valE_nf v)).
Proof.
  intros xs dom fvs e v H e2 He2.
  exact (redE_deep_shallow_val_aux deep xs dom fvs e _ H eq_refl v eq_refl e2 He2).
Qed.
