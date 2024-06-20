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


Inductive nfval :=
| nvar : nat -> nfval
| napp : nfval -> nfval_or_lam -> nfval
| nswitch : nfval -> list (nat * nfval_or_lam) -> nfval

with nfval_or_lam :=
| nval : nfval -> nfval_or_lam
| nlam : nfval_or_lam -> nfval_or_lam
| nconstr : nat -> list nfval_or_lam -> nfval_or_lam.

Inductive val : deep_flag -> Type :=
| vals_nf : nfval -> val shallow
| vals_abs : term -> val shallow
| vals_constr : nat -> list term -> val shallow
| vald_nf : nfval_or_lam -> val deep.

Definition val_nf {df} v : val df :=
  match df with
  | shallow => vals_nf v
  | deep => vald_nf (nval v)
  end.


Inductive ext : deep_flag -> Type :=
| ext_term : forall df, term -> ext df
| ext_app : forall df, out (val shallow) -> term -> ext df
| ext_appnf : forall df, nfval -> out (val deep) -> ext df
| ext_switch : forall df, out (val shallow) -> list (nat * term) -> ext df
| ext_switchnf : forall df, nfval -> list (nat * nfval_or_lam) -> option (nat * out (val deep)) -> list (nat * term) -> ext df
| extd_abs : out (val deep) -> ext deep
| extd_constr : nat -> list nfval_or_lam -> option (out (val deep)) -> list term -> ext deep.

Arguments ext_term {df} _.
Arguments ext_app {df} _ _.
Arguments ext_appnf {df} _ _.
Arguments ext_switch {df} _ _.
Arguments ext_switchnf {df} _ _ _ _.

Definition get_abort {df t} (e : ext df) : option (out t) :=
  match e with
  | ext_term _ => None
  | ext_app o _ => get_out_abort o
  | ext_appnf _ o => get_out_abort o
  | ext_switch o _ => get_out_abort o
  | ext_switchnf _ _ o _ => match o with Some (_, o) => get_out_abort o | None => None end
  | extd_abs o => get_out_abort o
  | extd_constr _ _ o _ => match o with Some o => get_out_abort o | None => None end
  end.

Inductive red_ (rec : forall df, ext df -> out (val df) -> Prop) : forall df, ext df -> out (val df) -> Prop :=
| red_var : forall df n,
    red_ rec df (ext_term (var n)) (out_ret (val_nf (nvar n))) (**r Free variables reduce to themselves *)
| red_abs_shallow : forall t,
    red_ rec shallow (ext_term (abs t)) (out_ret (vals_abs t)) (**r Do not look under abstractions *)
| red_abs_deep : forall t o1 o2,
    rec deep (ext_term t) o1 ->
    rec deep (extd_abs o1) o2 ->
    red_ rec deep (ext_term (abs t)) o2
| red_abs1 : forall v,
    red_ rec deep (extd_abs (out_ret (vald_nf v))) (out_ret (vald_nf (nlam v)))
| red_app : forall df t1 o1 t2 o2,
    rec shallow (ext_term t1) o1 ->
    rec df (ext_app o1 t2) o2 ->
    red_ rec df (ext_term (app t1 t2)) o2
| red_app1_nf : forall df v o1 t2 o2,
    rec deep (ext_term t2) o1 ->
    rec df (ext_appnf v o1) o2 ->
    red_ rec df (ext_app (out_ret (vals_nf v)) t2) o2
| red_app1_abs : forall df t1 t2 o,
    rec df (ext_term (subst1 t2 t1)) o ->
    red_ rec df (ext_app (out_ret (vals_abs t1)) t2) o
| red_appnf : forall df v1 v2,
    red_ rec df (ext_appnf v1 (out_ret (vald_nf v2))) (out_ret (val_nf (napp v1 v2)))
| red_constr_shallow : forall tag l,
    red_ rec shallow (ext_term (constr tag l)) (out_ret (vals_constr tag l))
| red_constr_deep : forall tag l o,
    rec deep (extd_constr tag nil None l) o ->
    red_ rec deep (ext_term (constr tag l)) o
| red_constr1_done : forall tag l,
    red_ rec deep (extd_constr tag l None nil) (out_ret (vald_nf (nconstr tag l)))
| red_constr1_step1 : forall tag l1 l2 t o1 o2,
    rec deep (ext_term t) o1 ->
    rec deep (extd_constr tag l1 (Some o1) l2) o2 ->
    red_ rec deep (extd_constr tag l1 None (t :: l2)) o2
| red_constr1_step2 : forall tag l1 l2 v o,
    rec deep (extd_constr tag (l1 ++ v :: nil) None l2) o ->
    red_ rec deep (extd_constr tag l1 (Some (out_ret (vald_nf v))) l2) o
| red_switch : forall df t o1 m o2,
    rec shallow (ext_term t) o1 ->
    rec df (ext_switch o1 m) o2 ->
    red_ rec df (ext_term (switch t m)) o2
| red_switch1_constr : forall df tag l m t o,
    nth_error m tag = Some (length l, t) ->
    rec df (ext_term (subst (read_env l) t)) o ->
    red_ rec df (ext_switch (out_ret (vals_constr tag l)) m) o
| red_switch1_nf : forall df v m o,
    rec df (ext_switchnf v nil None m) o ->
    red_ rec df (ext_switch (out_ret (vals_nf v)) m) o
| red_switchnf_done : forall df v m,
    red_ rec df (ext_switchnf v m None nil) (out_ret (val_nf (nswitch v m)))
| red_switchnf_step1 : forall df v m1 m2 p t o1 o2,
    rec deep (ext_term t) o1 ->
    rec df (ext_switchnf v m1 (Some (p, o1)) m2) o2 ->
    red_ rec df (ext_switchnf v m1 None ((p, t) :: m2)) o2
| red_switchnf_step2 : forall df m1 m2 v1 v2 p o,
    rec df (ext_switchnf v1 (m1 ++ (p, v2) :: nil) None m2) o ->
    red_ rec df (ext_switchnf v1 m1 (Some (p, out_ret (vald_nf v2))) m2) o
| red_abort : forall df e o,
    get_abort e = Some o -> red_ rec df e o.

Inductive red : forall df, ext df -> out (val df) -> Prop :=
| mkred : forall df e o, red_ red df e o -> red df e o.

CoInductive cored : forall df, ext df -> out (val df) -> Prop :=
| mkcored : forall df e o, red_ cored df e o -> cored df e o.

Lemma red_ind3 : is_ind3 red_ red.
Proof. prove_ind3. Qed.


Lemma red_not_div_preserved_down :
  preserved_down3 red_ red (fun df e o => o <> out_div).
Proof.
  intros df e o Q H1 H2.
  inversion H1; unexistT; subst; unexistT; subst;
    repeat (match goal with [ H : ?A /\ Q _ _ _ |- _ ] => destruct H end);
    try (econstructor; (eassumption || tauto)).
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H0; inversion H0; unexistT; subst; simpl in *; autoinjSome; tauto.
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H; inversion H; unexistT; subst; simpl in *; autoinjSome; tauto.
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H; inversion H; unexistT; subst; simpl in *; autoinjSome; tauto.
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H0; inversion H0; unexistT; subst; simpl in *; autoinjSome; tauto.
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H; inversion H; unexistT; subst; simpl in *; autoinjSome; tauto.
  - econstructor; splits 3; try eassumption.
    intros ->. apply (ind3_inv _ _ red_ind3) in H; inversion H; unexistT; subst; simpl in *; autoinjSome; tauto.
Qed.
