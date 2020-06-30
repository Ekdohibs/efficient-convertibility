Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.

Definition renaming := list nat.
Fixpoint renv (L : renaming) (n : nat) : nat :=
  match L with
  | nil => n
  | k :: L => if le_lt_dec k n then S (k + renv L (n - k)) else n
  end.
Lemma renv_car : forall L, { C | (forall n, renv L n < renv L (S n)) /\ (forall n, renv L (n + C) = n + renv L C) }.
Proof.
  induction L as [|k L].
  - exists 0. split.
    + intros n. simpl. constructor.
    + intros n. simpl. reflexivity.
  - destruct IHL as (C & HC1 & HC2).
    exists (k + C). split.
    + intros n. unfold renv; fold renv.
      repeat destruct le_lt_dec.
      * apply lt_n_S. apply plus_lt_compat_l.
        replace (S n - k) with (S (n - k)); [apply HC1|].
        apply minus_Sn_m. assumption.
      * lia.
      * lia.
      * lia.
    + intros. simpl.
      repeat (destruct le_lt_dec; try lia).
      replace (n + (k + C) - k) with (n + C) by lia.
      replace (k + C - k) with C by lia.
      rewrite HC2. lia.
Defined.

Lemma renv_add : forall k, { L | forall n, renv L n = k + n }.
Proof.
  induction k as [|k].
  - exists nil. simpl. reflexivity.
  - destruct IHk as (L & HL). exists (0 :: L). intros. simpl.
    f_equal. rewrite HL. lia.
Defined.

Definition plus_ren k := proj1_sig (renv_add k).
Definition plus_ren_correct k : forall n, renv (plus_ren k) n = k + n := proj2_sig (renv_add k).

Lemma f_strict_mono_le : forall f, (forall n, f n < f (S n)) -> (forall n, n <= f n).
Proof.
  intros. induction n as [|n].
  - lia.
  - specialize (H n). lia.
Qed.

Lemma f_strict_mono_f0 : forall f, (forall n, f n < f (S n)) -> (forall n, f 0 <= f n).
Proof.
  intros. induction n as [|n].
  - lia.
  - specialize (H n). lia.
Qed.

Lemma f_strict_mono : forall f, (forall n, f n < f (S n)) -> (forall n m, n < m -> f n < f m).
Proof.
  intros f H n m Hlt. induction Hlt.
  - apply H.
  - specialize (H m). lia.
Qed.

Lemma renv_repeat0 : forall k L n, renv (repeat 0 k ++ L) n = k + renv L n.
Proof.
  induction k as [|k].
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHk. f_equal. f_equal. f_equal. lia.
Qed.

Definition lift (L : renaming) : renaming :=
  match L with
  | nil => nil
  | k :: L => S k :: L
  end.

Lemma lift_renv :
  forall n L, renv (lift L) n = match n with 0 => 0 | S n => S (renv L n) end.
Proof.
  intros [|n] [|k L]; try reflexivity.
  unfold lift. unfold renv; fold renv.
  repeat destruct le_lt_dec; try lia.
  reflexivity.
Qed.

Lemma renv_uncar :
  forall f, { C | (forall n, f n < f (S n)) /\ (forall n, f (n + C) = n + f C) } -> { L | forall n, renv L n = f n }.
Proof.
  intros f (C & HC1 & HC2). revert f HC1 HC2; induction C as [|C]; intros f HC1 HC2.
  - exists (proj1_sig (renv_add (f 0))). intros n.
    destruct renv_add as (L & HL). simpl. rewrite HL.
    specialize (HC2 n). rewrite <- plus_n_O in HC2. lia.
  - specialize (IHC (fun n => f (S n) - S (f 0))). simpl in IHC.
    destruct IHC as (L & HL).
    + intros. assert (H := HC1 (S n)). assert (H2 := f_strict_mono_f0 f HC1 n). specialize (HC1 n). lia.
    + intros. rewrite plus_n_Sm, HC2. assert (H := f_strict_mono_f0 f HC1 C). specialize (HC1 C). lia.
    + exists (repeat 0 (f 0) ++ lift L). intros [|n]; rewrite renv_repeat0, lift_renv; simpl.
      * lia.
      * rewrite HL. assert (H := HC1 n). assert (H2 := f_strict_mono_f0 f HC1 n). lia.
Defined.

Lemma renv_comp_def :
  forall L1 L2, { L3 | forall n, renv L3 n = renv L1 (renv L2 n) }.
Proof.
  intros L1 L2. apply renv_uncar.
  destruct (renv_car L1) as (C1 & HC1a & HC1b).
  destruct (renv_car L2) as (C2 & HC2a & HC2b).
  exists (C1 + C2). split.
  - intros n. apply f_strict_mono; [assumption|]. apply HC2a.
  - intros n. rewrite Nat.add_assoc, !HC2b.
    rewrite Nat.add_comm with (n := C1), HC1b.
    rewrite Nat.add_comm, Nat.add_assoc, HC1b. lia.
Defined.

Definition renv_comp L1 L2 := proj1_sig (renv_comp_def L1 L2).
Definition renv_comp_correct L1 L2 : forall n, renv (renv_comp L1 L2) n = renv L1 (renv L2 n) := proj2_sig (renv_comp_def L1 L2).

Lemma renv_ext :
  forall L1 L2, (forall n, renv L1 n = renv L2 n) -> L1 = L2.
Proof.
  induction L1 as [|x1 L1]; destruct L2 as [|x2 L2].
  - intros; reflexivity.
  - intros H. specialize (H x2). simpl in H.
    destruct le_lt_dec; lia.
  - intros H. specialize (H x1). simpl in H.
    destruct le_lt_dec; lia.
  - intros H. assert (x1 = x2).
    + assert (H1 := H x1). assert (H2 := H x2).
      simpl in *.
      repeat destruct le_lt_dec; lia.
    + subst. f_equal. apply IHL1.
      intros n. specialize (H (x2 + n)).
      simpl in H. destruct le_lt_dec; [|lia].
      replace (x2 + n - x2) with n in H by lia.
      lia.
Qed.

Definition shiftn k : renaming := k :: nil.
Lemma renv_shiftn :
  forall k n, renv (shiftn k) n = if le_lt_dec k n then S n else n.
Proof.
  intros k n. simpl. destruct le_lt_dec; lia.
Qed.

Definition comp {A B C : Type} (f : B -> C) (g : A -> B) x := f (g x).
Definition scons {A : Type} (x : A) (f : nat -> A) n := match n with 0 => x | S n => f n end.

Definition id_ren : renaming := nil.


Definition pointwise_eq {A B : Type} (f g : A -> B) := forall x, f x = g x.
Infix ".=" := pointwise_eq (at level 70).

Lemma scons_0_S : scons 0 S .= id.
Proof.
  intros [|n]; reflexivity.
Qed.

Lemma comp_l : forall (A B : Type) (f : A -> B), comp id f .= f.
Proof.
  intros A B f x; unfold comp. reflexivity.
Qed.

Lemma comp_r : forall (A B : Type) (f : A -> B), comp f id .= f.
Proof.
  intros A B f x; unfold comp. reflexivity.
Qed.

Lemma comp_scons : forall (A B : Type) (x : A) f (g : A -> B), comp g (scons x f) .= scons (g x) (comp g f).
Proof.
  intros A B x f g [|n]; unfold comp; simpl; reflexivity.
Qed.

Lemma scons_comp_id : forall (A : Type) (f : nat -> A), scons (f 0) (comp f S) .= f.
Proof.
  intros A f [|n]; unfold comp; simpl; reflexivity.
Qed.

Lemma scons_comp_S : forall (A : Type) (x : A) f, comp (scons x f) S .= f.
Proof.
  intros A x f n. unfold comp; simpl. reflexivity.
Qed.




Inductive term :=
| var : nat -> term
| abs : term -> term
| app : term -> term -> term.

Fixpoint ren_term (r : renaming) t :=
  match t with
  | var n => var (renv r n)
  | abs t => abs (ren_term (lift r) t)
  | app t1 t2 => app (ren_term r t1) (ren_term r t2)
  end.

Fixpoint subst us t :=
  match t with
  | var n => us n
  | abs t => abs (subst (scons (var 0) (comp (ren_term (plus_ren 1)) us)) t)
  | app t1 t2 => app (subst us t1) (subst us t2)
  end.

Definition subst1 u t := subst (scons u (fun n => var n)) t.

Lemma subst_ext :
  forall t us1 us2, (forall n, us1 n = us2 n) -> subst us1 t = subst us2 t.
Proof.
  induction t; intros us1 us2 H; simpl.
  - apply H.
  - f_equal. apply IHt. intros [|n]; simpl; [reflexivity|unfold comp; f_equal; apply H].
  - f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Definition ren r := fun n => var (renv r n).

Lemma ren_term_is_subst :
  forall t r, ren_term r t = subst (ren r) t.
Proof.
  induction t; intros r; simpl.
  - reflexivity.
  - f_equal. rewrite IHt. apply subst_ext.
    intros [|n]; simpl.
    + unfold ren. rewrite lift_renv. reflexivity.
    + unfold ren. rewrite lift_renv. unfold comp. simpl. f_equal. f_equal. lia.
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma unfold_subst :
  forall t us, subst us t =
          match t with
          | var n => us n
          | abs t => abs (subst (scons (var 0) (comp (subst (ren (plus_ren 1))) us)) t)
          | app t1 t2 => app (subst us t1) (subst us t2)
          end.
Proof.
  destruct t; intros us; simpl.
  - reflexivity.
  - f_equal. apply subst_ext. intros [|n]; simpl; [reflexivity|].
    unfold comp; simpl. rewrite ren_term_is_subst. reflexivity.
  - reflexivity.
Qed.

Lemma ren_ren :
  forall t r1 r2, ren_term r1 (ren_term r2 t) = ren_term (renv_comp r1 r2) t.
Proof.
  induction t; intros r1 r2; simpl.
  - rewrite renv_comp_correct. reflexivity.
  - f_equal. rewrite IHt. f_equal.
    apply renv_ext.
    intros [|n]; rewrite !lift_renv, !renv_comp_correct, !lift_renv; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma ren_subst :
  forall t r us, ren_term r (subst us t) = subst (comp (ren_term r) us) t.
Proof.
  induction t; intros r us; simpl.
  - unfold comp; simpl. rewrite ren_term_is_subst. reflexivity.
  - f_equal. rewrite IHt. unfold comp. apply subst_ext.
    intros [|n]; simpl.
    + rewrite lift_renv. reflexivity.
    + rewrite !ren_ren. f_equal.
      apply renv_ext. intros [|m]; rewrite !renv_comp_correct, lift_renv; simpl; lia.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_ren :
  forall t r us, subst us (ren_term r t) = subst (comp (subst us) (ren r)) t.
Proof.
  induction t; intros r us; simpl.
  - unfold comp; simpl. reflexivity.
  - f_equal. rewrite IHt. unfold comp. apply subst_ext.
    intros [|n]; simpl.
    + rewrite lift_renv. reflexivity.
    + rewrite lift_renv. simpl. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_subst :
  forall t us1 us2, subst us2 (subst us1 t) = subst (comp (subst us2) us1) t.
Proof.
  induction t; intros us1 us2; simpl.
  - unfold comp. reflexivity.
  - f_equal. rewrite IHt. unfold comp. apply subst_ext.
    intros [|n]; simpl; [reflexivity|].
    rewrite ren_subst. rewrite subst_ren. apply subst_ext.
    intros m; unfold comp; simpl. f_equal. f_equal. lia.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_id :
  forall t, subst (fun n => var n) t = t.
Proof.
  induction t; simpl; f_equal; try assumption.
  erewrite subst_ext; [eassumption|].
  intros [|n]; unfold comp; simpl; [reflexivity|f_equal; lia].
Qed.


Inductive beta : term -> term -> Prop :=
| beta_app1 : forall t1 t2 t3, beta t1 t2 -> beta (app t1 t3) (app t2 t3)
| beta_app2 : forall t1 t2 t3, beta t1 t2 -> beta (app t3 t1) (app t3 t2)
| beta_abs : forall t1 t2, beta t1 t2 -> beta (abs t1) (abs t2)
| beta_redex : forall t1 t2, beta (app (abs t1) t2) (subst1 t2 t1).


Inductive deep_flag := shallow | deep.
Lemma deep_flag_eq_dec : forall (df1 df2 : deep_flag), { df1 = df2 } + { df1 <> df2 }.
Proof.
  intros [|] [|]; solve [left; reflexivity | right; discriminate].
Defined.

Inductive nfval :=
| nvar : nat -> nfval
| napp : nfval -> nfval_or_lam -> nfval

with nfval_or_lam :=
| nval : nfval -> nfval_or_lam
| nlam : nfval_or_lam -> nfval_or_lam.

Fixpoint read_nfval v :=
  match v with
  | nvar n => var n
  | napp v1 v2 => app (read_nfval v1) (read_nfval_or_lam v2)
  end

with read_nfval_or_lam v :=
  match v with
  | nval v => read_nfval v
  | nlam v => abs (read_nfval_or_lam v)
  end.

Inductive val : deep_flag -> Type :=
| vals_nf : nfval -> val shallow
| vals_abs : term -> val shallow
| vald_nf : nfval_or_lam -> val deep.

Definition read_val {df} (v : val df) :=
  match v with
  | vals_nf v => read_nfval v
  | vals_abs t => abs t
  | vald_nf v => read_nfval_or_lam v
  end.

Definition val_nf {df} v : val df :=
  match df with
  | shallow => vals_nf v
  | deep => vald_nf (nval v)
  end.

Lemma read_val_nf :
  forall df v, read_val (@val_nf df v) = read_nfval v.
Proof.
  intros [|] v; simpl; reflexivity.
Qed.


Inductive out t :=
| out_ret : t -> out t
| out_div : out t.

Arguments out_ret {t} _.
Arguments out_div {t}.


Inductive ext : deep_flag -> Type :=
| ext_term : forall df, term -> ext df
| ext_app : forall df, out (val shallow) -> term -> ext df
| ext_appnf : forall df, nfval -> out (val deep) -> ext df
| extd_abs : out (val deep) -> ext deep.

Arguments ext_term {df} _.
Arguments ext_app {df} _ _.
Arguments ext_appnf {df} _ _.


Inductive red : forall df, ext df -> out (val df) -> Prop :=
| red_var : forall df n, red df (ext_term (var n)) (out_ret (val_nf (nvar n))) (* Free variables reduce to themselves *)
| red_abs_shallow : forall t, red shallow (ext_term (abs t)) (out_ret (vals_abs t)) (* Do not look under abstractions *)
| red_abs_deep : forall t o1 o2,
    red deep (ext_term t) o1 ->
    red deep (extd_abs o1) o2 ->
    red deep (ext_term (abs t)) o2
| red_abs1_abort : red deep (extd_abs out_div) out_div
| red_abs1 : forall v, red deep (extd_abs (out_ret (vald_nf v))) (out_ret (vald_nf (nlam v)))
| red_app : forall df t1 o1 t2 o2,
    red shallow (ext_term t1) o1 ->
    red df (ext_app o1 t2) o2 ->
    red df (ext_term (app t1 t2)) o2
| red_app1_abort : forall df t2, red df (ext_app out_div t2) out_div
| red_app1_nf : forall df v o1 t2 o2,
    red deep (ext_term t2) o1 ->
    red df (ext_appnf v o1) o2 ->
    red df (ext_app (out_ret (vals_nf v)) t2) o2
| red_app1_abs : forall df t1 t2 o,
    red df (ext_term (subst1 t2 t1)) o ->
    red df (ext_app (out_ret (vals_abs t1)) t2) o
| red_appnf_abort : forall df v, red df (ext_appnf v out_div) out_div
| red_appnf : forall df v1 v2, red df (ext_appnf v1 (out_ret (vald_nf v2))) (out_ret (val_nf (napp v1 v2))).

CoInductive cored : forall df, ext df -> out (val df) -> Prop :=
| cored_var : forall df n, cored df (ext_term (var n)) (out_ret (val_nf (nvar n))) (* Free variables reduce to themselves *)
| cored_abs_shallow : forall t, cored shallow (ext_term (abs t)) (out_ret (vals_abs t)) (* Do not look under abstractions *)
| cored_abs_deep : forall t o1 o2,
    cored deep (ext_term t) o1 ->
    cored deep (extd_abs o1) o2 ->
    cored deep (ext_term (abs t)) o2
| cored_abs1_abort : cored deep (extd_abs out_div) out_div
| cored_abs1 : forall v, cored deep (extd_abs (out_ret (vald_nf v))) (out_ret (vald_nf (nlam v)))
| cored_app : forall df t1 o1 t2 o2,
    cored shallow (ext_term t1) o1 ->
    cored df (ext_app o1 t2) o2 ->
    cored df (ext_term (app t1 t2)) o2
| cored_app1_abort : forall df t2, cored df (ext_app out_div t2) out_div
| cored_app1_nf : forall df v o1 t2 o2,
    cored deep (ext_term t2) o1 ->
    cored df (ext_appnf v o1) o2 ->
    cored df (ext_app (out_ret (vals_nf v)) t2) o2
| cored_app1_abs : forall df t1 t2 o,
    cored df (ext_term (subst1 t2 t1)) o ->
    cored df (ext_app (out_ret (vals_abs t1)) t2) o
| cored_appnf_abort : forall df v, cored df (ext_appnf v out_div) out_div
| cored_appnf : forall df v1 v2, cored df (ext_appnf v1 (out_ret (vald_nf v2))) (out_ret (val_nf (napp v1 v2))).


CoInductive infred {A : Type} (R : A -> A -> Prop) : A -> Prop :=
| infred_step : forall x y, R x y -> infred R y -> infred R x.
CoInductive costar {A : Type} (R : A -> A -> Prop) : A -> option A -> Prop :=
| costar_refl : forall x, costar R x (Some x)
| costar_step : forall x y z, R x y -> costar R y z -> costar R x z.
Definition costarP {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 -> y1 = Some x1 \/ exists z, R x1 z /\ H z y1.

Lemma costarP_costar :
  forall A (R : A -> A -> Prop) x y, costarP R x y -> costar R x y.
Proof.
  intros A R. cofix IH. intros x y (H & H1 & H2).
  apply H2 in H1. destruct H1 as [H1 | (z & HR & H1)].
  - subst. constructor.
  - econstructor; [eassumption|]. apply IH. exists H; split; assumption.
Qed.

Definition read_out {df} (o : out (val df)) := match o with out_div => None | out_ret v => Some (read_val v) end.
Definition read_ext {df} (e : ext df) :=
  match e with
  | ext_term t => Some t
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2) | None => None end
  | extd_abs o => match read_out o with Some t => Some (abs t) | None => None end
  end.

Lemma red_star_beta :
  forall df e o, red df e o -> forall t1 t2, read_ext e = Some t1 -> read_out o = Some t2 -> star beta t1 t2.
Proof.
  intros df e o H. induction H; intros u1 u2 Hu1 Hu2; simpl in *.
  - rewrite read_val_nf in Hu2; simpl in Hu2.
    injection Hu1; injection Hu2; intros; subst. constructor.
  - injection Hu1; injection Hu2; intros; subst. constructor.
  - destruct o1.
    + simpl in *. eapply star_compose.
      * injection Hu1; intros; subst. eapply star_map_impl with (RA := beta); [intros; constructor; assumption|].
        apply IHred1; reflexivity.
      * apply IHred2; [reflexivity|assumption].
    + inversion H0; subst.
      apply inj_pair2_eq_dec in H1; [|apply deep_flag_eq_dec].
      subst; simpl in *; congruence.
  - congruence.
  - injection Hu1; injection Hu2; intros; subst. constructor.
  - destruct o1.
    + simpl in *. eapply star_compose.
      * injection Hu1; intros; subst.
        eapply star_map_impl with (f := fun t => app t t2) (RA := beta); [intros; constructor; assumption|].
        eapply IHred1; reflexivity.
      * apply IHred2; [reflexivity|assumption].
    + inversion H0; subst.
      apply inj_pair2_eq_dec in H4; [|apply deep_flag_eq_dec].
      subst; simpl in *; congruence.
  - congruence.
  - destruct o1.
    + simpl in *. eapply star_compose.
      * injection Hu1; intros; subst.
        eapply star_map_impl with (f := fun t => app _ t) (RA := beta); [intros; constructor; assumption|].
        eapply IHred1; reflexivity.
      * apply IHred2; [reflexivity|assumption].
    + inversion H0; subst.
      apply inj_pair2_eq_dec in H4; [|apply deep_flag_eq_dec].
      subst; simpl in *; congruence.
  - injection Hu1; intros; subst.
    econstructor; [apply beta_redex|].
    apply IHred; [reflexivity|assumption].
  - congruence.
  - injection Hu1; injection Hu2; intros; subst.
    rewrite read_val_nf. simpl. constructor.
Qed.

Lemma infred_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y : A, RA x y -> RB (f x) (f y)) -> forall x : A, infred RA x -> infred RB (f x).
Proof.
  intros A B RA RB f H. cofix IH. intros x Hx. inversion Hx; subst.
  econstructor; [apply H; eassumption|].
  apply IH. assumption.
Qed.

Lemma costar_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y : A, RA x y -> RB (f x) (f y)) ->
    forall x y, costar RA x y -> costar RB (f x) (match y with None => None | Some y => Some (f y) end).
Proof.
  intros A B RA RB f H. cofix IH. intros x y Hx. inversion Hx; subst.
  - constructor.
  - econstructor; [apply H; eassumption|].
    apply IH. assumption.
Qed.

Lemma costar_compose :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    costar R x y -> (forall w, y = Some w -> costar R w z) -> costar R x z.
Proof.
  intros A R. cofix IH. intros x y z H1 H2. inversion H1; subst.
  - apply H2. reflexivity.
  - econstructor; [eassumption|].
    eapply IH; eassumption.
Defined.

Ltac unexistT :=
  repeat match goal with
           [ H : @existT deep_flag _ _ _ = @existT deep_flag _ _ _ |- _ ] =>
           apply inj_pair2_eq_dec in H; [|apply deep_flag_eq_dec]
         end.

Definition option_map {A B : Type} (f : A -> B) (x : option A) := match x with Some x => Some (f x) | None => None end.
Lemma option_map_id : forall (A : Type) (x : option A), option_map id x = x.
Proof.
  intros A [x|]; reflexivity.
Qed.

Definition respectful {A : Type} (R : A -> A -> Prop) (f : A -> A) := forall x y, R x y -> R (f x) (f y).

Fixpoint size t :=
  match t with
  | var n => 0
  | abs t => S (size t)
  | app t1 t2 => S (size t1 + size t2)
  end.

Definition read_ext_with_size {df} (e : ext df) :=
  match e with
  | ext_term t => Some (t, 2 * size t)
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2, 2 * size t2 + 1) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2, 0) | None => None end
  | extd_abs o => match read_out o with Some t => Some (abs t, 0) | None => None end
  end.
Definition read_out_with_size {df} (o : out (val df)) := match o with out_div => None | out_ret v => Some (read_val v, 0) end.

Definition fst_map {A B C : Type} (f : A -> B) : (A * C) -> (B * C) := fun x => (f (fst x), snd x).
Lemma option_map_fst_id :
  forall (A B : Type) (x : option (A * B)), option_map (fst_map id) x = x.
Proof.
  destruct x as [[x y]|]; simpl; reflexivity.
Qed.

Definition weaken {A : Type} (x y : A * nat) := fst x = fst y /\ snd y <= snd x.
Definition weakenO {A : Type} (x y : option (A * nat)) := match x, y with None, None => True | Some x, Some y => weaken x y | _, _ => False end.

Lemma weaken_refl : forall (A : Type) (x : A * nat), weaken x x.
Proof.
  intros A [x y]. unfold weaken. simpl. split; reflexivity.
Qed.

Lemma weakenO_refl : forall (A : Type) (x : option (A * nat)), weakenO x x.
Proof.
  intros A [x|]; unfold weakenO; simpl.
  - apply weaken_refl.
  - tauto.
Qed.

Definition stepped {A : Type} (R : A -> A -> Prop) x y := R (fst x) (fst y) \/ (fst x = fst y /\ snd y < snd x).

Definition costarPTn {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 ->
                        weakenO (Some x1) y1 \/
                        (exists z1, stepped R x1 z1 /\ H z1 y1) \/
                        (exists z1 z2, stepped R x1 z1 /\ H z1 z2 /\ (forall v, z2 = Some v -> H v y1)).

Lemma costarPTn_destruct :
  forall (A : Type) (R : A -> A -> Prop) x y,
    costarPTn R x y -> weakenO (Some x) y \/
                      (exists z, stepped R x z /\ costarPTn R z y) \/
                      (exists z1 z2, stepped R x z1 /\ costarPTn R z1 z2 /\ (forall v, z2 = Some v -> costarPTn R v y)).
Proof.
  intros A R x y (H & H1 & H2).
  apply H2 in H1. destruct H1 as [H1 | [(z & Hz1 & Hz2) | (z1 & z2 & Hz1 & Hz2 & Hz3)]].
  - left. assumption.
  - right. left. exists z. split; [assumption|]. exists H; split; assumption.
  - right. right. exists z1. exists z2. split; [assumption|]. split.
    + exists H; split; assumption.
    + intros v ->. exists H; split; [|assumption]. apply Hz3. reflexivity.
Qed.

Lemma weaken_trans :
  forall (A : Type) (x y z : A * nat), weaken x y -> weaken y z -> weaken x z.
Proof.
  intros A [x1 x2] [y1 y2] [z1 z2]; unfold weaken; simpl.
  intros [? ?] [? ?]; split; [congruence|lia].
Qed.

Lemma stepped_weaken :
  forall (A : Type) (R : A -> A -> Prop) x y z, weaken x y -> stepped R y z -> stepped R x z.
Proof.
  intros A R [x1 x2] [y1 y2] [z1 z2] [H1 H2] [H3 | [H3 H4]]; simpl in *; subst.
  - left; simpl; assumption.
  - right; simpl; split; [reflexivity|lia].
Qed.

Lemma costarPTn_comp :
  forall (A : Type) (R : A -> A -> Prop) x y z, costarPTn R x y -> (forall v, y = Some v -> costarPTn R v z) -> costarPTn R x z.
Proof.
  intros A R x y z H1 H2. exists (fun x1 y1 => costarPTn R x1 y1 \/ exists w, costarPTn R x1 w /\ (forall v, w = Some v -> costarPTn R v y1)).
  split.
  - right. exists y. split; assumption.
  - clear x y z H1 H2. intros x z [Hxz | (y & Hxy & Hyz)].
    + apply costarPTn_destruct in Hxz. destruct Hxz as [Hxz | [(z1 & Hz1 & Hz2) | (z1 & z2 & Hz1 & Hz2 & Hz3)]].
      * left. assumption.
      * right. left. exists z1. split; tauto.
      * right. right. exists z1. exists z2. split; [assumption|]. split; [tauto|]. intros v Hv; left; apply Hz3; assumption.
    + apply costarPTn_destruct in Hxy. destruct Hxy as [Hxy | [(z1 & Hz1 & Hz2) | (z1 & z2 & Hz1 & Hz2 & Hz3)]].
      * destruct y as [y|]; simpl in *; [|tauto].
        specialize (Hyz y eq_refl).
        apply costarPTn_destruct in Hyz. destruct Hyz as [Hyz | [(z1 & Hz1 & Hz2) | (z1 & z2 & Hz1 & Hz2 & Hz3)]].
        -- destruct z as [z|]; simpl in *; [|tauto].
           left. eapply weaken_trans; eassumption.
        -- right. left. exists z1. split; [eapply stepped_weaken; eassumption|].
           left; assumption.
        -- right. right. exists z1. exists z2. split; [eapply stepped_weaken; eassumption|].
           split; [left; assumption|]. intros; left; apply Hz3; assumption.
      * right. left. exists z1. split; [assumption|].
        right. exists y. split; assumption.
      * right. right. exists z1. exists z2. split; [assumption|].
        split.
        -- left; assumption.
        -- intros v ->. right. exists y. split; [apply Hz3; reflexivity|].
           intros w ->. apply Hyz. reflexivity.
Qed.


Lemma costarPTn_costarP :
  forall (A : Type) (R : A -> A -> Prop) x y, costarPTn R x y -> costarP R (fst x) (option_map fst y).
Proof.
  intros A R x y H. exists (fun u v => exists n m, costarPTn R (u, n) (option_map (fun v => (v, m)) v)).
  split.
  - exists (snd x). exists (match y with Some y => snd y | None => 0 end).
    destruct x as [x1 x2]. destruct y as [[y1 y2]|]; simpl; assumption.
  - clear x y H. intros x y (n & m & H).
    revert x y m H; induction n as [n Hn] using lt_wf_ind; intros x y m H.
    apply costarPTn_destruct in H. destruct H as [H | [(z & Hz1 & Hz2) | (z1 & z2 & Hz1 & Hz2 & Hz3)]].
    + destruct y as [y|]; simpl in H; [|tauto].
      unfold weaken in H; simpl in H. left. destruct H; congruence.
    + destruct Hz1 as [Hz1 | Hz1]; simpl in Hz1.
      * right. exists (fst z). split; [assumption|].
        exists (snd z). exists m. destruct z; assumption.
      * destruct Hz1 as [-> Hz1]. destruct z as [z1 z2]; simpl in *.
        eapply Hn; [|eassumption]. assumption.
    + destruct Hz1 as [Hz1 | Hz1]; simpl in Hz1.
      * right. exists (fst z1). split; [assumption|].
        exists (snd z1). exists m. eapply costarPTn_comp; [destruct z1; simpl in *; eassumption|].
        eassumption.
      * destruct Hz1 as [-> Hz1]. destruct z1 as [z3 z4]; simpl in *.
        eapply Hn; [exact Hz1|].
        eapply costarPTn_comp; eassumption.
Qed.

Lemma red_div_beta_aux :
  forall t df e o, cored df e o -> read_ext_with_size e = Some t ->
              costarPTn beta t (read_out_with_size o).
Proof.
  intros t df e o H Ht.
  exists (fun x y => exists df e o f,
         cored df e o /\
         option_map f (read_ext_with_size e) = Some x /\
         y = option_map f (read_out_with_size o) /\
         respectful (stepped beta) f /\ respectful weaken f).
  split.
  {
    exists df. exists e. exists o. exists id. splits 5.
    - assumption.
    - rewrite option_map_id. assumption.
    - rewrite option_map_id. reflexivity.
    - intros x y Hxy. exact Hxy.
    - intros x y Hxy. exact Hxy.
  }
  clear t df e o H Ht. intros x y (df & e & o & f & H & Hx & -> & Hf).
  inversion H; subst; simpl in *; unexistT; subst; simpl in *; try congruence; simpl in Hx; injection Hx as Hx; subst x.
  - rewrite read_val_nf in *; simpl in *.
    left. apply Hf. unfold weaken. split; simpl; [reflexivity|lia].
  - left. apply Hf. unfold weaken. split; simpl; [reflexivity|lia].
  - right; right.
    simpl.
    exists (f (abs t, 2 * size t)).
    exists (option_map (fun t1 => f (abs (fst t1), snd t1)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|]. simpl. lia.
    + eexists. eexists. eexists. exists (fun t1 => f (abs (fst t1), snd t1)).
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal|]; tauto].
      * unfold weaken in *. simpl. split; [f_equal|]; tauto.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H6|]. simpl. split; [reflexivity|].
      split; [reflexivity|]. apply Hf.
  - left. apply Hf. apply weaken_refl.
  - right. right.
    exists (f (app t1 t2, 2 * size t1 + 2 * size t2 + 1)).
    exists (option_map (fun t3 => f (app (fst t3) t2, snd t3 + 2 * size t2 + 1)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (app (fst t3) t2, snd t3 + 2 * size t2 + 1)).
      split; [exact H3|]. simpl. split; [reflexivity|].
      split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal; tauto|lia]].
      * unfold weaken in *. simpl. split; [f_equal; tauto|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. right.
    exists (f (app (read_nfval v) t2, 2 * size t2)).
    exists (option_map (fun t3 => f (app (read_nfval v) (fst t3), snd t3)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (app (read_nfval v) (fst t3), snd t3)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal|]; tauto].
      * unfold weaken in *. simpl. split; [f_equal|]; tauto.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (subst1 t2 t1, 2 * size (subst1 t2 t1))).
    split; [apply Hf; left; apply beta_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. rewrite read_val_nf. apply weaken_refl.
Qed.

Lemma read_ext_with_size_read_ext :
  forall df (e : ext df), read_ext e = option_map fst (read_ext_with_size e).
Proof.
  intros. destruct e; simpl; try destruct read_out; simpl; reflexivity.
Qed.

Lemma read_out_with_size_read_out :
  forall df (o : out (val df)), read_out o = option_map fst (read_out_with_size o).
Proof.
  intros. destruct o; simpl; reflexivity.
Qed.

Lemma red_div_beta :
  forall t df e o, cored df e o -> read_ext e = Some t -> costar beta t (read_out o).
Proof.
  intros t df e o Hred He. apply costarP_costar.
  rewrite read_ext_with_size_read_ext in He.
  destruct read_ext_with_size as [t1|] eqn:Heqre; simpl in *; [|congruence].
  injection He as He; subst.
  rewrite read_out_with_size_read_out.
  apply costarPTn_costarP. eapply red_div_beta_aux; eassumption.
Qed.


Inductive closed_at : term -> nat -> Prop :=
| closed_at_var : forall n k, n < k -> closed_at (var n) k
| closed_at_app : forall t1 t2 k, closed_at t1 k -> closed_at t2 k -> closed_at (app t1 t2) k
| closed_at_abs : forall t k, closed_at t (S k) -> closed_at (abs t) k.

Fixpoint index l x :=
  match l with
  | nil => 0
  | y :: l => if freevar_eq_dec x y then 0 else S (index l x)
  end.

Inductive clo :=
| clo_var : freevar -> clo
| clo_term : term -> list clo -> clo.

Inductive clo_closed : clo -> Prop :=
| cc_var : forall n, clo_closed (clo_var n)
| cc_term : forall t l, closed_at t (length l) -> (forall c, c \in l -> clo_closed c) -> clo_closed (clo_term t l).

Fixpoint clo_fv c :=
  match c with
  | clo_var x => x :: nil
  | clo_term t l => concat (map clo_fv l)
  end.

(*
Fixpoint shift_clo (c : clo) : clo :=
  match c with
  | mkclo t l => mkclo (ren_term (shiftn (length l)) t) (map shift_clo l)
  end.
 *)

Definition read_env (e : list term) :=
  fun n => match nth_error e n with Some u => u | None => var (n - length e) end.

Fixpoint read_clo (xs : list freevar) (c : clo) : term :=
  match c with
  | clo_var x => var (index xs x)
  | clo_term t l =>
    let nl := map (read_clo xs) l in
    subst (read_env nl) t
  end.

Fixpoint clo_ind2 (P : clo -> Prop) (Hvar : forall x, P (clo_var x)) (Hterm : forall t l, Forall P l -> P (clo_term t l)) (c : clo) : P c :=
  match c with
  | clo_var x => Hvar x
  | clo_term t l => Hterm t l ((fix H (l : _) : Forall P l :=
                                 match l with
                                 | nil => @Forall_nil _ _
                                 | cons c l => @Forall_cons _ _ c l (clo_ind2 P Hvar Hterm c) (H l)
                                 end) l)
  end.

Lemma subst_closed_at_ext :
  forall t k us1 us2, closed_at t k -> (forall n, n < k -> us1 n = us2 n) -> subst us1 t = subst us2 t.
Proof.
  induction t; intros k us1 us2 Hclosed Hext; inversion Hclosed; subst; simpl.
  - apply Hext. assumption.
  - f_equal. eapply IHt; [eassumption|].
    intros [|n] Hn; simpl in *; [reflexivity|].
    unfold comp. f_equal. apply Hext. lia.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
Qed.

Lemma read_shift_clo :
  forall c x xs, x \notin clo_fv c -> clo_closed c -> read_clo (x :: xs) c = ren_term (plus_ren 1) (read_clo xs c).
Proof.
  induction c using clo_ind2; intros y ys Hy Hcc; inversion Hcc; subst; simpl in *.
  - f_equal. destruct freevar_eq_dec; [tauto|]. lia.
  - rewrite ren_subst. eapply subst_closed_at_ext; [eassumption|].
    intros n Hn. unfold comp, read_env.
    rewrite !nth_error_map.
    destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
    assert (u \in l) by (eapply nth_error_In; eassumption).
    rewrite Forall_forall in H. apply H; [eassumption| |apply H3; assumption].
    rewrite concat_map_In in Hy. intros Hy2; apply Hy; exists u; tauto.
Qed.

(*
Lemma read_shift_clo :
  forall c, read_clo (shift_clo c) = ren_term (plus_ren 1) (read_clo c).
Proof.
  induction c using clo_ind2.
  simpl. rewrite ren_subst, subst_ren. eapply subst_ext.
  intros n. unfold comp, read_env. simpl.
  rewrite !nth_error_map, !map_length.
  destruct (nth_error l n) as [c|] eqn:Hn.
  - destruct le_lt_dec; [rewrite <- nth_error_None in *; congruence|].
    rewrite Hn. rewrite Forall_forall in H. apply H.
    eapply nth_error_In; eassumption.
  - destruct le_lt_dec; [|rewrite nth_error_None in Hn; lia].
    replace (nth_error l _) with (@None clo) by (symmetry; apply nth_error_None; lia).
    unfold ren_term. rewrite plus_ren_correct. f_equal. lia.
Qed.
*)

Inductive nfvalx :=
| nxvar : freevar -> nfvalx
| nxapp : nfvalx -> nfvalx_or_lam -> nfvalx

with nfvalx_or_lam :=
| nxval : nfvalx -> nfvalx_or_lam
| nxlam : freevar -> nfvalx_or_lam -> nfvalx_or_lam.

Fixpoint read_nfvalx xs v :=
  match v with
  | nxvar x => nvar (index xs x)
  | nxapp v1 v2 => napp (read_nfvalx xs v1) (read_nfvalx_or_lam xs v2)
  end

with read_nfvalx_or_lam xs v :=
  match v with
  | nxval v => nval (read_nfvalx xs v)
  | nxlam x v => nlam (read_nfvalx_or_lam (x :: xs) v)
  end.


Inductive valE : deep_flag -> Type :=
| valE_nf : forall {df}, nfvalx -> valE df
| valEs_abs : term -> list clo -> valE shallow
| valEd_abs : term -> list clo -> nfvalx_or_lam -> valE deep.

Definition read_valE {df} (xs : list freevar) (v : valE df) : val df :=
  match v with
  | valE_nf v => val_nf (read_nfvalx xs v)
  | valEs_abs t l =>
    vals_abs (subst (scons (var 0) (read_env (map (fun c => ren_term (plus_ren 1) (read_clo xs c)) l))) t)
  | valEd_abs t l v => vald_nf (read_nfvalx_or_lam xs v)
  end.

Inductive extE : deep_flag -> Type :=
| extE_term : forall df, term -> extE df
| extE_app : forall df, out (valE shallow) -> term -> extE df
| extE_appnf : forall df, nfvalx -> out (valE deep) -> extE df
| extEd_abs : freevar -> term -> out (valE deep) -> extE deep.

Arguments extE_term {df} _.
Arguments extE_app {df} _ _.
Arguments extE_appnf {df} _ _.

Fixpoint nfvalx_fv v :=
  match v with
  | nxvar x => x :: nil
  | nxapp v1 v2 => nfvalx_fv v1 ++ nfvalx_or_lam_fv v2
  end

with nfvalx_or_lam_fv v :=
  match v with
  | nxval v => nfvalx_fv v
  | nxlam x v => list_remove x (nfvalx_or_lam_fv v)
  end.

Definition valE_closed {df} xs (v : valE df) :=
  match v with
  | valEs_abs t l => closed_at t (S (length l)) /\ (forall c, c \in l -> clo_closed c /\ clo_fv c \subseteq xs)
  | valE_nf v => nfvalx_fv v \subseteq xs
  | valEd_abs t l v => closed_at t (S (length l)) /\ (forall c, c \in l -> clo_closed c /\ clo_fv c \subseteq xs) /\
                      nfvalx_or_lam_fv v \subseteq xs
  end.

Definition outE_closed {df} xs (o : out (valE df)) :=
  match o with
  | out_div => True
  | out_ret v => valE_closed xs v
  end.

Inductive extE_closed_at : forall {df}, extE df -> nat -> list freevar -> Prop :=
| extE_term_closed : forall df t k xs, closed_at t k -> extE_closed_at (@extE_term df t) k xs
| extE_app_closed : forall df o t k xs, closed_at t k -> outE_closed xs o -> extE_closed_at (@extE_app df o t) k xs
| extE_appnf_closed : forall df v o k xs, nfvalx_fv v \subseteq xs -> outE_closed xs o -> extE_closed_at (@extE_appnf df v o) k xs
| extEd_abs_closed : forall o t k x xs, closed_at t (S k) -> outE_closed (x :: xs) o -> extE_closed_at (extEd_abs x t o) k xs.

Definition out_map {A B : Type} (f : A -> B) (o : out A) : out B :=
  match o with
  | out_ret x => out_ret (f x)
  | out_div => out_div
  end.

Definition read_extE {df} xs env (e : extE df) : ext df :=
  match e with
  | extE_term t => ext_term (read_clo xs (clo_term t env))
  | extE_app o1 t2 => ext_app (out_map (read_valE xs) o1) (read_clo xs (clo_term t2 env))
  | extE_appnf v1 o2 => ext_appnf (read_nfvalx xs v1) (out_map (read_valE xs) o2)
  | extEd_abs x t o => extd_abs (out_map (read_valE (x :: xs)) o)
  end.

Definition getvalEd_nf (v : valE deep) : nfvalx_or_lam :=
  match v return nfvalx_or_lam with
  | valE_nf v => nxval v
  | valEd_abs t l v => v
  | valEs_abs _ _ => nxval (nxvar (proj1_sig (fresh nil)))
  end.

Inductive redE : forall df, list freevar -> list clo -> extE df -> out (valE df) -> Prop :=
| redE_var_bound : forall df xs env n t2 env2 o,
    nth_error env n = Some (clo_term t2 env2) ->
    redE df xs env2 (extE_term t2) o ->
    redE df xs env (extE_term (var n)) o
| redE_var_free : forall df x xs env n,
    nth_error env n = Some (clo_var x) ->
    redE df xs env (extE_term (var n)) (out_ret (valE_nf (nxvar x)))
| redE_abs_shallow : forall t xs env,
    redE shallow xs env (extE_term (abs t)) (out_ret (valEs_abs t env))
| redE_abs_deep : forall t x xs env o1 o2,
    x \in xs ->
    redE deep (list_remove x xs) (clo_var x :: env) (extE_term t) o1 ->
    redE deep xs env (extEd_abs x t o1) o2 ->
    redE deep xs env (extE_term (abs t)) o2
| redE_abs1_abort : forall x t xs env, redE deep xs env (extEd_abs x t out_div) out_div
| redE_abs1 : forall x t xs env v, redE deep xs env (extEd_abs x t (out_ret v)) (out_ret (valEd_abs t env (nxlam x (getvalEd_nf v))))
| redE_app : forall df xs env t1 o1 t2 o2,
    redE shallow xs env (extE_term t1) o1 ->
    redE df xs env (extE_app o1 t2) o2 ->
    redE df xs env (extE_term (app t1 t2)) o2
| redE_app1_abort : forall df xs env t2, redE df xs env (extE_app out_div t2) out_div
| redE_app1_nf : forall df xs env v o1 t2 o2,
    redE deep xs env (extE_term t2) o1 ->
    redE df xs env (extE_appnf v o1) o2 ->
    redE df xs env (extE_app (out_ret (valE_nf v)) t2) o2
| redE_app1_abs : forall df xs env env2 t1 t2 o,
    redE df xs (match t2 with var n => match nth_error env n with Some c => c | _ => clo_term t2 env end | _ => clo_term t2 env end :: env2) (extE_term t1) o ->
    redE df xs env (extE_app (out_ret (valEs_abs t1 env2)) t2) o
| redE_appnf_abort : forall df xs env v, redE df xs env (extE_appnf v out_div) out_div
| redE_appnf : forall df xs env v1 v2, redE df xs env (extE_appnf v1 (out_ret v2)) (out_ret (valE_nf (nxapp v1 (getvalEd_nf v2)))).

(*
CoInductive coredE : forall df, list clo -> extE df -> out (valE df) -> Prop :=
| coredE_var_bound : forall df env n t2 env2 o,
    nth_error env n = Some (mkclo t2 env2) ->
    coredE df env2 (extE_term t2) o ->
    coredE df env (extE_term (var n)) o
| coredE_var_free : forall df env n,
    nth_error env n = None ->
    coredE df env (extE_term (var n)) (out_ret (valE_nf (nvar (n - length env))))
| coredE_abs_shallow : forall t env,
    coredE shallow env (extE_term (abs t)) (out_ret (valEs_abs t env))
| coredE_abs_deep : forall t env o1 o2,
    coredE deep (mkclo (var 0) nil :: map shift_clo env) (extE_term (ren_term (shiftn (S (length env))) t)) o1 ->
    coredE deep env (extEd_abs o1) o2 ->
    coredE deep env (extE_term (abs t)) o2
| coredE_abs1_abort : forall env, coredE deep env (extEd_abs out_div) out_div
| coredE_abs1 : forall env v, coredE deep env (ext				isIntNum = false;
Ed_abs (out_ret (valEd_nf v))) (out_ret (valEd_nf (nlam v)))
| coredE_app : forall df env t1 o1 t2 o2,
    coredE shallow env (extE_term t1) o1 ->
    coredE df env (extE_app o1 t2) o2 ->
    coredE df env (extE_term (app t1 t2)) o2
| coredE_app1_abort : forall df env t2, coredE df env (extE_app out_div t2) out_div
| coredE_app1_nf : forall df env v o1 t2 o2,
    coredE deep env (extE_term t2) o1 ->
    coredE df env (extE_appnf v o1) o2 ->
    coredE df env (extE_app (out_ret (valEs_nf v)) t2) o2
| coredE_app1_abs : forall df env env2 t1 t2 o,
    coredE df (mkclo t2 env :: env2) (extE_term t1) o ->
    coredE df env (extE_app (out_ret (valEs_abs t1 env2)) t2) o
| coredE_appnf_abort : forall df env v, coredE df env (extE_appnf v out_div) out_div
| coredE_appnf : forall df env v1 v2, coredE df env (extE_appnf v1 (out_ret (valEd_nf v2))) (out_ret (valE_nf (napp v1 v2))).
*)
Arguments nth_error : simpl nomatch.

Lemma valE_nf_closed :
  forall df v xs, nfvalx_fv v \subseteq xs -> valE_closed xs (@valE_nf df v).
Proof.
  intros [|]; simpl; tauto.
Qed.

Lemma destruct_valE :
  forall df (v : valE df),
    { v2 | existT valE df v = existT valE df (valE_nf v2) } +
    { t & { env | existT valE df v = existT valE shallow (valEs_abs t env) } } +
    { t & { env & { v2 | existT valE df v = existT valE deep (valEd_abs t env v2) } } }.
Proof.
  intros df v. destruct v.
  - left; left. exists n. reflexivity.
  - left; right. exists t. exists l. reflexivity.
  - right. exists t. exists l. exists n. reflexivity.
Qed.

Lemma destruct_valE_deep :
  forall (v : valE deep),
    { v2 | v = valE_nf v2 } +
    { t & { env & { v2 | v = valEd_abs t env v2 } } }.
Proof.
  intros v. assert (H := destruct_valE deep v).
  destruct H as [[(v2 & Heq) | (t & env & Heq)] | (t & env & v2 & Heq)].
  - unexistT. left. exists v2. assumption.
  - apply projT1_eq in Heq; simpl in Heq; congruence.
  - unexistT. right. exists t. exists env. exists v2. assumption.
Qed.


(*
Lemma clo_closed_mono :
  forall c k1, clo_closed_at c k1 -> forall k2, k1 < k2 -> clo_closed_at c k2.
Proof.
  induction c using clo_ind2; intros k1 Hck1 k2 Hk12; inversion Hck1; subst; constructor.
  - lia.
  - assumption.
  - rewrite Forall_forall in H. intros c Hc. eapply H; [assumption| |eassumption].
    apply H4; assumption.
Qed.
 *)

Lemma redE_closed :
  forall df xs xs2 env e o, (forall c, c \in env -> clo_closed c /\ clo_fv c \subseteq xs) -> extE_closed_at e (length env) xs -> redE df xs2 env e o -> outE_closed xs o.
Proof.
  intros df xs xs2 env e o Henv He H. revert xs Henv He; induction H; intros nxs Henv He; simpl in *; inversion He; subst.
  - apply nth_error_In, Henv in H. destruct H as [H1 H2]. inversion H1; subst.
    apply IHredE; [|constructor; assumption].
    intros c Hc; split; [apply H6; assumption|].
    simpl in H2. rewrite concat_incl, Forall_map, Forall_forall in H2.
    apply H2; assumption.
  - apply (Henv (clo_var x)). eapply nth_error_In. eassumption.
  - split; [|assumption].
    inversion H1; subst. assumption.
  - apply IHredE2; [assumption|]. constructor; [inversion H4; subst; assumption|].
    apply IHredE1.
    + intros c [<- | Hc]; split; [constructor|simpl; prove_list_inc|apply Henv; assumption|].
      etransitivity; [apply Henv; assumption|]. prove_list_inc.
    + constructor. inversion H4; subst. assumption.
  - tauto.
  - split; [assumption|]. split; [assumption|]. intros y Hy. rewrite list_remove_correct in Hy.
    destruct (destruct_valE_deep v) as [(v2 & ->) | (t2 & env2 & v2 & ->)]; simpl in *.
    + specialize (H5 y ltac:(tauto)). destruct H5; simpl in *; tauto.
    + destruct H5 as (H5 & H6 & H7); specialize (H7 y ltac:(tauto)). destruct H7; simpl in *; tauto.
  - apply IHredE2; [assumption|]. constructor; [inversion H3; subst; assumption|].
    apply IHredE1; [assumption|]. constructor; inversion H3; subst; assumption.
  - tauto.
  - apply IHredE2; [assumption|]. constructor; [assumption|].
    apply IHredE1; [assumption|]. constructor. assumption.
  - apply IHredE; [intros c [<- | Hc]|].
    + destruct t2; try (split; simpl; [constructor; [assumption|intros; apply Henv; assumption] | rewrite concat_incl, Forall_map, Forall_forall; intros; apply Henv; assumption]).
      destruct nth_error eqn:Hu; [|split; simpl; [constructor; [assumption|intros; apply Henv; assumption] | rewrite concat_incl, Forall_map, Forall_forall; intros; apply Henv; assumption]].
      eapply Henv, nth_error_In; eassumption.
    + simpl in *. apply H6. assumption.
    + simpl in *. constructor. apply H6.
  - tauto.
  - rewrite list_inc_app_left.
    split; [assumption|]. simpl in H5.
    destruct (destruct_valE_deep v2) as [(v & ->) | (t & env2 & v & ->)]; simpl in *; tauto.
Qed.

Lemma redE_red :
  forall df xs xs2 env e o, (forall c, c \in env -> clo_closed c /\ clo_fv c \subseteq xs) -> extE_closed_at e (length env) xs -> (forall x, x \in xs -> x \notin xs2) -> redE df xs2 env e o -> red df (read_extE xs env e) (out_map (read_valE xs) o).
Proof.
  intros df xs xs2 env e o Henv He Hdisj H. revert xs Henv He Hdisj; induction H; intros nxs Henv He Hdisj; simpl in *; inversion He; subst.
  - unfold read_env. rewrite nth_error_map, H.
    apply nth_error_In, Henv in H. destruct H as [H1 H2]. inversion H1; subst.
    apply IHredE.
    + intros c Hc. split; [apply H6; assumption|].
      simpl in H2. rewrite concat_incl, Forall_map, Forall_forall in H2. apply H2; eassumption.
    + constructor. assumption.
    + assumption.
  - unfold read_env. rewrite nth_error_map, H. constructor.
  - inversion H1; subst.
    erewrite subst_closed_at_ext; [constructor|eassumption|].
    intros [|n] Hn; [reflexivity|]. unfold comp, read_env; simpl.
    rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu.
    + (* rewrite read_shift_clo; [reflexivity|]. apply Henv. eapply nth_error_In; eassumption. *) reflexivity.
    + apply nth_error_None in Hu. lia.
  - econstructor; [|apply IHredE2; [assumption|constructor|assumption]].
    erewrite subst_closed_at_ext.
    + apply IHredE1; [|constructor; inversion H4; assumption|].
      * intros c [<- | Hc]; [split; [constructor|simpl; prove_list_inc]|].
        split; [apply Henv; assumption|].
        etransitivity; [apply Henv; assumption|]. prove_list_inc.
      * intros y [<- | Hy]; rewrite list_remove_correct; [tauto|]. specialize (Hdisj y); tauto.
    + inversion H4; eassumption.
    + intros [|n] Hn; unfold comp, read_env; simpl; [destruct freevar_eq_dec; congruence|].
      rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
      apply nth_error_In, Henv in Hu. destruct Hu as [Hu1 Hu2].
      rewrite read_shift_clo; [reflexivity| |apply Hu1].
      rewrite Hu2. intros Hx. apply Hdisj in Hx. tauto.
    + inversion H4; subst; assumption.
    + eapply redE_closed; [| |eassumption].
      * intros c [<- | Hc]; [split; [constructor|simpl; prove_list_inc]|].
        apply Henv in Hc; destruct Hc as [Hc1 Hc2].
        split; [apply Hc1 | rewrite Hc2; prove_list_inc].
      * constructor. inversion H4; simpl; subst. assumption.
  - constructor.
  - destruct (destruct_valE_deep v) as [(v2 & ->) | (t2 & env2 & v2 & ->)]; simpl in *; constructor.
  - econstructor; [apply IHredE1|apply IHredE2]; try assumption; constructor; try (inversion H3; assumption).
    eapply redE_closed; [| |eassumption]; [assumption|]. constructor. inversion H3; assumption.
  - constructor.
  - econstructor; [apply IHredE1|apply IHredE2]; try assumption; constructor; try assumption.
    eapply redE_closed; [| |eassumption]; [assumption|]. constructor. assumption.
  - econstructor.
    unfold subst1. rewrite subst_subst.
    erewrite subst_closed_at_ext; [apply IHredE| |].
    + intros c [<- | Hc]; [|simpl in H6; apply H6; assumption].
      destruct t2; try (split; simpl; [constructor; [assumption|intros; apply Henv; assumption] | rewrite concat_incl, Forall_map, Forall_forall; intros; apply Henv; assumption]).
      destruct nth_error eqn:Hu; [|split; simpl; [constructor; [assumption|intros; apply Henv; assumption] | rewrite concat_incl, Forall_map, Forall_forall; intros; apply Henv; assumption]].
      eapply Henv, nth_error_In; eassumption.
    + simpl in H6. constructor. apply H6.
    + assumption.
    + simpl in H6. apply H6.
    + unfold comp, read_env.
      intros [|n] Hn; simpl.
      * destruct t2; try reflexivity. simpl.
        rewrite nth_error_map. destruct nth_error eqn:Hu; [|apply nth_error_None in Hu; inversion H3; subst; lia].
        reflexivity.
      * rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
        rewrite subst_ren; unfold comp; simpl.
        erewrite subst_ext; [apply subst_id|]; intros; f_equal; lia.
  - constructor.
  - destruct (destruct_valE_deep v2) as [(v & ->) | (t & env2 & v & ->)]; simpl in *; constructor.
Qed.



Definition extE_shallow_to_deep (e : extE shallow) : extE deep :=
  match e return extE deep with
  | extE_term t => extE_term t
  | extE_app o1 t2 => extE_app o1 t2
  | extE_appnf v1 o2 => extE_appnf v1 o2
  | extEd_abs x t o => extEd_abs x t o
  end.

Definition extE_deep_to_shallow (e : extE deep) : option (extE shallow) :=
  match e return option (extE shallow) with
  | extE_term t => Some (extE_term t)
  | extE_app o1 t2 => Some (extE_app o1 t2)
  | extE_appnf v1 o2 => Some (extE_appnf v1 o2)
  | extEd_abs x t o => None
  end.

Lemma redE_shallow_deep_val_aux :
  forall df xs env e o,
    redE df xs env e o -> forall (p : df = shallow) v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valE_nf v) ->
    redE deep xs env (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) (out_ret (valE_nf v)).
Proof.
  intros df xs env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nv Ho; try discriminate Ho; simpl.
  - subst. econstructor; [eassumption|]. eapply (IHredE eq_refl). reflexivity.
  - injection Ho as Ho; subst. apply (redE_var_free deep). assumption.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl). assumption.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl). assumption.
  - econstructor.
    eapply (IHredE eq_refl). eassumption.
  - injection Ho as Ho; subst. constructor.
Qed.

Lemma redE_shallow_deep_val :
  forall xs env e v, redE shallow xs env e (out_ret (valE_nf v)) ->
         redE deep xs env (extE_shallow_to_deep e) (out_ret (valE_nf v)).
Proof.
  intros xs env e v H.
  exact (redE_shallow_deep_val_aux shallow xs env e _ H eq_refl v eq_refl).
Qed.

Lemma redE_shallow_deep_abs_aux :
  forall df xs env e o,
    redE df xs env e o -> forall (p : df = shallow) t env2, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEs_abs t env2) ->
    forall o2, redE deep xs env2 (extE_term (abs t)) o2 -> redE deep xs env (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) o2.
Proof.
  intros df k env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nt nenv Ho; try discriminate Ho; simpl.
  - subst. intros o2 Ho2. econstructor; [eassumption|]. eapply (IHredE eq_refl); [reflexivity|eassumption].
  - injection Ho as Ho; subst. intros; assumption.
  - intros o3. specialize (IHredE2 eq_refl nt nenv Ho o3). simpl in IHredE2.
    intros HredE. econstructor; [eassumption|]. apply IHredE2; assumption.
  - intros o3. specialize (IHredE2 eq_refl nt nenv Ho o3). simpl in IHredE2.
    intros HredE. econstructor; [eassumption|]. apply IHredE2; assumption.
  - intros o3. specialize (IHredE eq_refl nt nenv Ho o3). simpl in IHredE.
    intros HredE. constructor. apply IHredE; assumption.
Qed.

Lemma redE_shallow_deep_abs :
  forall xs env env2 e t,
    redE shallow xs env e (out_ret (valEs_abs t env2)) ->
    forall o, redE deep xs env2 (extE_term (abs t)) o -> redE deep xs env (extE_shallow_to_deep e) o.
Proof.
  intros xs env env2 e t H.
  exact (redE_shallow_deep_abs_aux shallow xs env e _ H eq_refl t env2 eq_refl).
Qed.


Lemma redE_deep_shallow_abs_aux :
  forall df xs env e o,
    redE df xs env e o -> forall (p : df = deep) t env2 v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEd_abs t env2 v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs env e2 (out_ret (valEs_abs t env2)).
Proof.
  intros df k env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nt nenv nv Ho e2 He2; try discriminate Ho; subst; simpl in *; try discriminate He2; injection He2 as <-.
  - econstructor; [eassumption|]. eapply (IHredE eq_refl); reflexivity.
  - inversion H1; subst. constructor.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor.
    eapply (IHredE eq_refl); reflexivity.
Qed.

Lemma redE_deep_shallow_abs :
  forall xs env env2 e t v,
    redE deep xs env e (out_ret (valEd_abs t env2 v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs env e2 (out_ret (valEs_abs t env2)).
Proof.
  intros xs env env2 e t v H e2 He2.
  exact (redE_deep_shallow_abs_aux deep xs env e _ H eq_refl t env2 v eq_refl e2 He2).
Qed.

Lemma redE_deep_shallow_val_aux :
  forall df xs env e o,
    redE df xs env e o -> forall (p : df = deep) v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valE_nf v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs env e2 (out_ret (valE_nf v)).
Proof.
  intros df k env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nv Ho e2 He2; try discriminate Ho; subst; simpl in *; try discriminate He2; injection He2 as <-.
  - econstructor; [eassumption|]. eapply (IHredE eq_refl); reflexivity.
  - inversion Ho; intros; subst. constructor. assumption.
  - inversion H1.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor.
    eapply (IHredE eq_refl); reflexivity.
  - injection Ho; intros; subst. constructor.
Qed.

Lemma redE_deep_shallow_val :
  forall xs env e v,
    redE deep xs env e (out_ret (valE_nf v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs env e2 (out_ret (valE_nf v)).
Proof.
  intros xs env e v H e2 He2.
  exact (redE_deep_shallow_val_aux deep xs env e _ H eq_refl v eq_refl e2 He2).
Qed.







Inductive eiM :=
| eiM_lazy : term -> list freevar -> eiM
| eiM_abs1 : term -> list freevar -> eiM
| eiM_abs2 : term -> list freevar -> nfvalx_or_lam -> eiM
| eiM_val : nfvalx -> eiM.
Definition memM := list (freevar * eiM).

Definition memdom (m : memM) := map fst m.

Inductive read_eiM (res : freevar -> option clo) xs : eiM -> clo -> Prop :=
| read_eiM_lazy : forall t ys vs,
    map Some vs = map res ys ->
    read_eiM res xs (eiM_lazy t ys) (clo_term t vs)
| read_eiM_abs1 : forall t ys u ws vs,
    map Some vs = map res ys ->
    redE shallow xs ws (extE_term u) (out_ret (valEs_abs t vs)) ->
    read_eiM res xs (eiM_abs1 t ys) (clo_term u ws)
| read_eiM_abs2 : forall t ys u ws v vs,
    map Some vs = map res ys ->
    redE deep xs ws (extE_term u) (out_ret (valEd_abs t vs v)) ->
    read_eiM res xs (eiM_abs2 t ys v) (clo_term u ws)
| read_eiM_val : forall u ws v,
    redE shallow xs ws (extE_term u) (out_ret (valE_nf v)) ->
    read_eiM res xs (eiM_val v) (clo_term u ws)
| read_eiM_var : forall y,
    read_eiM res xs (eiM_val (nxvar y)) (clo_var y).

Definition read_memM (m : memM) (res : freevar -> option clo) :=
  (forall x u, env_find m x = Some u -> exists v, res x = Some v /\ read_eiM res (memdom m) u v) /\
  (forall x, env_find m x = None -> res x = None).

Lemma read_memM_Some :
  forall m res x u v, read_memM m res -> env_find m x = Some u -> res x = Some v -> read_eiM res (memdom m) u v.
Proof.
  intros m res x u v Hread Hm Hres. apply Hread in Hm.
  destruct Hm as (v2 & Hx2 & Hv2). congruence.
Qed.

Inductive valM : deep_flag -> Type :=
| valM_nf : forall {df}, nfvalx -> valM df
| valMs_abs : term -> list freevar -> valM shallow
| valMd_abs : term -> list freevar -> nfvalx_or_lam -> valM deep.

Inductive read_valM : forall {df}, (freevar -> option clo) -> valM df -> valE df -> Prop :=
| read_valM_nf : forall df res v, @read_valM df res (valM_nf v) (valE_nf v)
| read_valMs_abs : forall res t ys vs,
    map Some vs = map res ys ->
    @read_valM shallow res (valMs_abs t ys) (valEs_abs t vs)
| read_valMd_nf : forall res t ys v vs,
    map Some vs = map res ys ->
    @read_valM deep res (valMd_abs t ys v) (valEd_abs t vs v).


Inductive outM t m :=
| outM_ret : t -> m -> outM t m
| outM_div : outM t m.

Arguments outM_ret {t} {m} _ _.
Arguments outM_div {t} {m}.

Inductive extM : deep_flag -> Type :=
| extM_term : forall df, term -> extM df
| extM_app : forall df, outM (valM shallow) memM -> term -> extM df
| extM_appnf : forall df, nfvalx -> outM (valM deep) memM -> extM df
| extMd_abs : freevar -> term -> outM (valM deep) memM -> extM deep.

Arguments extM_term {df} _.
Arguments extM_app {df} _ _.
Arguments extM_appnf {df} _ _.

(*
Definition compat_memM (m1 m2 : memM) (res : freevar -> clo) :=
  forall x c xs, read_eiM m1 x c xs -> read_eiM m2 x c xs.
 *)

Definition get_out_memM {df} (m : memM) (o : outM (valM df) memM) :=
  match o with
  | outM_div => m
  | outM_ret _ m => m
  end.

Definition get_ext_memM {df} (m : memM) (e : extM df) :=
  match e with
  | extM_term _ => m
  | extM_app o _ => get_out_memM m o
  | extM_appnf _ o => get_out_memM m o
  | extMd_abs _ _ o => get_out_memM m o
  end.

Inductive read_outM : forall df, (freevar -> option clo) -> outM (valM df) memM -> out (valE df) -> Prop :=
| read_outM_div : forall df res, read_outM df res outM_div out_div
| read_outM_ret : forall df res m v1 v2,
    read_memM m res -> read_valM res v1 v2 -> read_outM df res (outM_ret v1 m) (out_ret v2).

Inductive read_extM : forall df, (freevar -> option clo) -> extM df -> extE df -> Prop :=
| read_extM_term : forall df res t, read_extM df res (extM_term t) (extE_term t)
| read_extM_app : forall df res o1 o2 t,
    read_outM shallow res o1 o2 -> read_extM df res (extM_app o1 t) (extE_app o2 t)
| read_extM_appnf : forall df res v o1 o2,
    read_outM deep res o1 o2 -> read_extM df res (extM_appnf v o1) (extE_appnf v o2)
| read_extMd_abs : forall res x t o1 o2,
    read_outM deep res o1 o2 -> read_extM deep res (extMd_abs x t o1) (extEd_abs x t o2).


Inductive update_result : forall df, freevar -> outM (valM df) memM -> outM (valM df) memM -> Prop :=
| upr_nf : forall df x v m,
    update_result df x (outM_ret (valM_nf v) m) (outM_ret (valM_nf v) (update_env m x (eiM_val v)))
| upr_shallow_abs : forall x t env m,
    update_result shallow x (outM_ret (valMs_abs t env) m) (outM_ret (valMs_abs t env) (update_env m x (eiM_abs1 t env)))
| upr_deep_abs : forall x t env v m,
    update_result deep x (outM_ret (valMd_abs t env v) m) (outM_ret (valMd_abs t env v) (update_env m x (eiM_abs2 t env v)))
| upr_div : forall df x, update_result df x outM_div outM_div.

Definition getvalMd_nf (v : valM deep) : nfvalx_or_lam :=
  match v return nfvalx_or_lam with
  | valM_nf v => nxval v
  | valMd_abs t l v => v
  | valMs_abs _ _ => nxval (nxvar (proj1_sig (fresh nil)))
  end.


Inductive redM : forall df, list freevar -> list freevar -> extM df -> memM -> outM (valM df) memM -> Prop :=
| redM_var_val : forall df xs n env m x v,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_val v) ->
    redM df xs env (extM_term (var n)) m (outM_ret (valM_nf v) m)
| redM_var_abs1_shallow : forall xs n env m x t env2,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_abs1 t env2) ->
    redM shallow xs env (extM_term (var n)) m (outM_ret (valMs_abs t env2) m)
| redM_var_abs1_deep : forall xs n env m x t env2 o1 o2,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_abs1 t env2) ->
    redM deep xs env2 (extM_term (abs t)) m o1 ->
    update_result deep x o1 o2 ->
    redM deep xs env (extM_term (var n)) m o2
| redM_var_abs2_shallow : forall xs n env m x t env2 body,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_abs2 t env2 body) ->
    redM shallow xs env (extM_term (var n)) m (outM_ret (valMs_abs t env2) m)
| redM_var_abs2_deep : forall xs n env m x t env2 body,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_abs2 t env2 body) ->
    redM deep xs env (extM_term (var n)) m (outM_ret (valMd_abs t env2 body) m)
| redM_var_lazy : forall df xs n env m x t env2 o1 o2,
    nth_error env n = Some x ->
    env_find m x = Some (eiM_lazy t env2) ->
    redM df xs env2 (extM_term t) m o1 ->
    update_result df x o1 o2 ->
    redM df xs env (extM_term (var n)) m o2
(* | redM_var_bound : forall df env n t2 env2 o,
    nth_error env n = Some (mkclo t2 env2) ->
    redM df env2 (extM_term t2) o ->
    redM df env (extM_term (var n)) o
| redM_var_free : forall df env n,
    nth_error env n = None ->
    redM df env (extM_term (var n)) (out_ret (valM_nf (nvar (n - length env)))) *)
| redM_abs_shallow : forall xs t env m,
    redM shallow xs env (extM_term (abs t)) m (outM_ret (valMs_abs t env) m)
| redM_abs_deep : forall xs t env m1 m2 o1 o2 x a,
    env_find m1 a = None -> m2 = (a, eiM_val (nxvar x)) :: m1 -> x \notin xs ->
    redM deep (x :: xs) (a :: env) (extM_term t) m2 o1 ->
    redM deep xs env (extMd_abs x t o1) m2 o2 ->
    redM deep xs env (extM_term (abs t)) m1 o2
| redM_abs1_abort : forall x t xs env m, redM deep xs env (extMd_abs x t outM_div) m outM_div
| redM_abs1 : forall x t xs env m1 m2 v, redM deep xs env (extMd_abs x t (outM_ret v m2)) m1 (outM_ret (valMd_abs t env (nxlam x (getvalMd_nf v))) m2)
| redM_app : forall df xs env m t1 o1 t2 o2,
    redM shallow xs env (extM_term t1) m o1 ->
    redM df xs env (extM_app o1 t2) m o2 ->
    redM df xs env (extM_term (app t1 t2)) m o2
| redM_app1_abort : forall df xs env m t2, redM df xs env (extM_app outM_div t2) m outM_div
| redM_app1_nf : forall df xs env m1 m2 v o1 t2 o2,
    redM deep xs env (extM_term t2) m2 o1 ->
    redM df xs env (extM_appnf v o1) m2 o2 ->
    redM df xs env (extM_app (outM_ret (valM_nf v) m2) t2) m1 o2
| redM_app1_abs : forall df xs env env2 env3 m1 m2 m3 a t1 t2 o,
    a = match t2 with var n => nth_error env n | _ => None end ->
    match a with Some x => env3 = x :: env2 /\ m3 = m2 | None => exists x, env_find m2 x = None /\ env3 = x :: env2 /\ m3 = (x, eiM_lazy t2 env) :: m2 end ->
    redM df xs env3 (extM_term t1) m3 o ->
    redM df xs env (extM_app (outM_ret (valMs_abs t1 env2) m2) t2) m1 o
| redM_appnf_abort : forall df xs env m v, redM df xs env (extM_appnf v outM_div) m outM_div
| redM_appnf : forall df xs env m1 m2 v1 v2,
    redM df xs env (extM_appnf v1 (outM_ret v2 m2)) m1 (outM_ret (valM_nf (nxapp v1 (getvalMd_nf v2))) m2).

(*
Lemma compat_memM_refl :
  forall m, compat_memM m m.
Proof.
  intros m x c xs H. exact H.
Qed.

Lemma compat_memM_trans :
  forall m1 m2 m3, compat_memM m1 m2 -> compat_memM m2 m3 -> compat_memM m1 m3.
Proof.
  intros m1 m2 m3 H1 H2 x c xs H. apply H2. apply H1. assumption.
Qed.

Lemma compat_memM_read_outM :
  forall df k m1 m2 o1 o2, compat_memM m1 m2 -> read_outM df k m2 o1 o2 -> read_outM df k m1 o1 o2.
Proof.
  intros df k m1 m2 o1 o2 H1 H2. inversion H2; unexistT; subst; simpl in *.
  - constructor.
  - constructor; [|assumption].
    eapply compat_memM_trans; eassumption.
Qed.
*)

Definition compat_res (res1 res2 : freevar -> option clo) := (forall x u, res1 x = Some u -> res2 x = Some u).

Lemma compat_res_refl :
  forall res, compat_res res res.
Proof.
  intros res x u H. exact H.
Qed.

Lemma compat_res_trans :
  forall res1 res2 res3, compat_res res1 res2 -> compat_res res2 res3 -> compat_res res1 res3.
Proof.
  intros res1 res2 res3 H1 H2 x u H. apply H2. apply H1. assumption.
Qed.

(*
Definition compat_xres (res1 : freevar -> option clo) (xss1 : freevar -> list freevar) res2 xss2 :=
  (forall x u, res1 x = Some u -> res2 x = Some u /\ xss1 x = xss2 x).

Lemma compat_xres_refl :
  forall res xss, compat_xres res xss res xss.
Proof.
  intros res xss x u H. split; [assumption|reflexivity].
Qed.

Lemma compat_xres_trans :
  forall res1 xss1 res2 xss2 res3 xss3, compat_xres res1 xss1 res2 xss2 -> compat_xres res2 xss2 res3 xss3 -> compat_xres res1 xss1 res3 xss3.
Proof.
  intros res1 xss1 res2 xss2 res3 xss3 H1 H2 x u H.
  apply H1 in H. destruct H as (H & ->). apply H2 in H. assumption.
Qed.
 *)




Lemma nenv_eqs : forall {A B : Type} {res : A -> option B} {env1 : list A} {env2 : list B} {n : nat} {x : A},
    nth_error env1 n = Some x -> map Some env2 = map res env1 -> exists u, nth_error env2 n = Some u /\ res x = Some u.
Proof.
  intros A B res env1 env2 n x H1 H2.
  assert (Heq : nth_error (map Some env2) n = nth_error (map res env1) n) by congruence.
  rewrite nth_error_map, nth_error_map, H1 in Heq.
  destruct (nth_error env2 n) as [u|]; [|congruence]. exists u; split; congruence.
Qed.

(*
Lemma nenv_compat_list : forall {res1 res2 : freevar -> option clo} {env1 : list freevar} {env2 : list clo} {xss1 xss2 : freevar -> list freevar},
    compat_xres res1 xss1 res2 xss2 -> map Some env2 = map res1 env1 -> map Some env2 = map res2 env1.
Proof.
  intros res1 res2 env1 env2 xss1 xss2 Hcompat. revert env2; induction env1 as [|x env1 Henv1]; intros env2 Heq.
  - simpl in *. assumption.
  - simpl in *. destruct env2 as [|u env2]; simpl in *; [congruence|].
    injection Heq; intros. f_equal; [|apply Henv1; assumption].
    symmetry. apply Hcompat. symmetry. assumption.
Qed.

Lemma compat_xres_read_eiM :
  forall res1 xss1 res2 xss2 u c xs,
    compat_xres res1 xss1 res2 xss2 -> read_eiM res1 u c xs -> read_eiM res2 u c xs.
Proof.
  intros res1 xss1 res2 xss2 u c xs H1 H2. inversion H2; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.
*)

Lemma nenv_compat_list : forall {res1 res2 : freevar -> option clo} {env1 : list freevar} {env2 : list clo},
    compat_res res1 res2 -> map Some env2 = map res1 env1 -> map Some env2 = map res2 env1.
Proof.
  intros res1 res2 env1 env2 Hcompat. revert env2; induction env1 as [|x env1 Henv1]; intros env2 Heq.
  - simpl in *. assumption.
  - simpl in *. destruct env2 as [|u env2]; simpl in *; [congruence|].
    injection Heq; intros. f_equal; [|apply Henv1; assumption].
    symmetry. apply Hcompat. symmetry. assumption.
Qed.

Lemma compat_res_read_eiM :
  forall res1 res2 xs u c,
    compat_res res1 res2 -> read_eiM res1 xs u c -> read_eiM res2 xs u c.
Proof.
  intros res1 res2 xs u c H1 H2. inversion H2; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.


(*
Lemma compat_xres_read_memM :
  forall res1 xss1 res2 xss2 m,
    compat_xres res1 xss1 res2 xss2 -> read_memM m res1 xss1 -> read_memM m res2 xss2.
Proof.
  intros res1 xss1 res2 xss2 m H1 H2. split.
  - intros x u Hxu; apply H2 in Hxu.
    destruct Hxu as (v & Hv1 & Hv2). exists v.
    assert (Hx := H1 _ _ Hv1). destruct Hx as (Hx & <-).
    split; [assumption|]. eapply compat_xres_read_eiM; eassumption.
  - intros x Hx. 
Qed.
 *)

(*
Lemma compat_xres_read_valM :
  forall res1 xss1 res2 xss2 df v1 v2,
    compat_xres res1 xss1 res2 xss2 -> @read_valM df xss1 res1 v1 v2 -> @read_valM df xss2 res2 v1 v2.
Proof.
  intros res1 xss1 res2 xss2 df v1 v2 H1 H2.
  inversion H2; subst; unexistT; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.
 *)

Lemma compat_res_read_valM :
  forall res1 res2 df v1 v2,
    compat_res res1 res2 -> @read_valM df res1 v1 v2 -> @read_valM df res2 v1 v2.
Proof.
  intros res1 res2 df v1 v2 H1 H2.
  inversion H2; subst; unexistT; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.


(*
Lemma compat_xres_read_outM :
  forall res1 xss1 res2 xss2 df o1 o2,
    compat_xres res1 xss1 res2 xss2 -> read_outM df xss1 res1 o1 o2 -> read_outM df xss2 res2 o1 o2.
Proof.
  intros res1 xss1 res2 xss2 df o1 o2 H1 H2.
  inversion H2; subst; unexistT; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.
*)

Lemma update_env_in_fst :
  forall {A : Type} (env : list (freevar * A)) x u v, env_find env x = Some u -> map fst (update_env env x v) = map fst env.
Proof.
  induction env as [|[y w] env]; intros x u v H.
  - simpl in H. congruence.
  - simpl in *. destruct freevar_eq_dec.
    + simpl. congruence.
    + simpl. f_equal. eapply IHenv; eassumption.
Qed.

Lemma read_memM_update :
  forall m res x c u, read_memM m res -> res x = Some c -> read_eiM res (memdom m) u c -> read_memM (update_env m x u) res.
Proof.
  intros m res x c u Hmem Hres Hread.
  assert (Hdom : memdom (update_env m x u) = memdom m).
  {
    unfold memdom in *.
    destruct (env_find m x) as [v|] eqn:Hv; [|apply Hmem in Hv; congruence].
    erewrite update_env_in_fst; [reflexivity|eassumption].
  }
  split.
  - intros y v Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + injection Hy; intros; subst. exists c. rewrite Hdom; split; assumption.
    + rewrite Hdom; apply Hmem. assumption.
  - intros y Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + congruence.
    + apply Hmem. assumption.
Qed.

Lemma redE_xs_mono :
  forall df xs env e o, redE df xs env e o -> forall xs2, xs \subseteq xs2 -> redE df xs2 env e o.
Proof.
  intros df xs env e o H; induction H; intros xs2 Hxs2.
  - eapply redE_var_bound; [eassumption|]. eapply IHredE; eassumption.
  - eapply redE_var_free; eassumption.
  - eapply redE_abs_shallow.
  - eapply redE_abs_deep; [apply Hxs2; eassumption|eapply IHredE1|eapply IHredE2; assumption].
    intros y Hy; rewrite !list_remove_correct in *; specialize (Hxs2 y); tauto.
  - eapply redE_abs1_abort.
  - eapply redE_abs1.
  - eapply redE_app; [eapply IHredE1|eapply IHredE2]; assumption.
  - eapply redE_app1_abort.
  - eapply redE_app1_nf; [eapply IHredE1|eapply IHredE2]; assumption.
  - eapply redE_app1_abs. eapply IHredE; assumption.
  - eapply redE_appnf_abort.
  - eapply redE_appnf.
Qed.

Lemma redM_redE :
  forall df xs env e m o,
    redM df xs env e m o ->
    forall res e2 env2, read_memM m res -> read_extM df res e e2 -> map Some env2 = map res env ->
             exists o2 res2, redEs df env2 e2 o2 /\ read_outM df res2 o o2 /\ compat_res res res2.
Proof.
  intros df xs env e m o H. induction H; intros res e2 nenv Hres Hread Hnenv; inversion Hread; unexistT; subst; simpl in *.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    + exists (out_ret (valE_nf v)). exists res.
      splits 3.
      * destruct H2 as (L & H2). exists L.
        econstructor; [eassumption|].
        destruct df; simpl; [assumption|].
        eapply redE_shallow_deep_val in H2. assumption.
      * constructor; [assumption|]. constructor.
      * apply compat_res_refl.
    + exists (out_ret (valE_nf (nxvar y))). exists res.
      splits 3.
      * exists nil. eapply redE_var_free. assumption.
      * constructor; [assumption|]. constructor.
      * apply compat_res_refl.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 3.
    + destruct H5 as (L & H5). exists L. econstructor; eassumption.
    + constructor; [assumption|]. constructor. assumption.
    + apply compat_res_refl.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    specialize (IHredM res (extE_term (abs t)) vs).
    destruct IHredM as (o3 & res3 & HredE & Ho3 & Hcompat); [assumption|constructor|assumption|].
    exists o3. exists res3. splits 3.
    + destruct H7 as (L & H7). destruct HredE as (L2 & HredE).
      exists (L ++ L2).
      econstructor; [eassumption|].
      eapply redE_shallow_deep_abs with (e := extE_term u); eapply redE_xs_mono; try eassumption; prove_list_inc.
    + inversion Ho3; unexistT; subst; inversion H2; unexistT; subst; constructor; try assumption.
      * inversion H1; unexistT; subst. inversion H15.
      * eapply read_memM_update; [assumption|apply Hcompat; eassumption|].
        inversion H10; unexistT; subst.
        econstructor; [eassumption|].
        destruct H7 as (L & H7). destruct HredE as (L2 & HredE).
        exists (L ++ L2).
        eapply redE_shallow_deep_abs with (e := extE_term u); eapply redE_xs_mono; try eassumption; prove_list_inc.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 3.
    + destruct H6 as (L & H6); exists L. econstructor; [eassumption|].
      eapply redE_deep_shallow_abs with (e := extE_term u); [eassumption|reflexivity].
    + constructor; [assumption|]. constructor. assumption.
    + apply compat_res_refl.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 3.
    + destruct H6 as (L & H6); exists L; econstructor; eassumption.
    + constructor; [assumption|]. constructor. assumption.
    + apply compat_res_refl.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ Hres H0 Hc2). inversion Hx2; subst.
    specialize (IHredM res (extE_term t) vs).
    destruct IHredM as (o3 & res3 & HredE & Ho3 & Hcompat); [assumption|constructor|assumption|].
    exists o3. exists res3. splits 3.
    + destruct HredE as (L & HredE); exists L; econstructor; eassumption.
    + inversion Ho3; unexistT; subst; inversion H2; subst; unexistT; subst; constructor; try assumption.
      all: eapply read_memM_update; [assumption|apply Hcompat; eassumption|].
      all: inversion H9; unexistT; subst.
      * constructor. destruct df; [assumption|].
        destruct HredE as (L & HredE); exists L.
        eapply redE_deep_shallow_val in HredE; [|reflexivity]. assumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
    + assumption.
  - eexists; exists res; splits 3; [exists nil; econstructor| |apply compat_res_refl].
    constructor; [assumption|]. constructor. assumption.
  - specialize (IHredM1 (fun y => if freevar_eq_dec y a then Some (clo_var x) else res y) (extE_term t) (clo_var x :: nenv)).
    destruct IHredM1 as (o3 & res3 & HredE1 & Ho3 & Hcompat); [|constructor| |].
    + admit.
    + admit.
    + specialize (IHredM2 res3 (extEd_abs x t o3) nenv).
      destruct IHredM2 as (o4 & res4 & HredE2 & Ho4 & Hcompat4).
      * admit.
      * constructor. assumption.
      * admit.
      * exists o4. exists res4. splits 3.
        -- econstructor; eassumption.
        -- assumption.
        -- admit.
  - inversion H3; unexistT; subst; simpl in *.
    eexists; exists res; splits 3; [econstructor|constructor|intros; assumption].
  - inversion H3; unexistT; subst; simpl in *.
    inversion H7; unexistT; subst; simpl in *.
    + eexists; exists res; splits 3; [econstructor| |intros; assumption].
      constructor; [admit|]. constructor. assumption.
    + eexists; exists res; splits 3; [econstructor| |intros; assumption].
      constructor; [admit|]. constructor. assumption.
  - specialize (IHredM1 res (extE_term t1) nenv).
    destruct IHredM1 as (o3 & res3 & HredE1 & Ho3 & Hcompat); [assumption|constructor|assumption|].
    specialize (IHredM2 res3 (extE_app o3 t2) nenv).
    destruct IHredM2 as (o4 & res4 & HredE2 & Ho4 & Hcompat4).
      [admit|constructor; assumption|eapply nenv_compat_list; eassumption|].
    exists o4. exists res4. splits 3; [econstructor; eassumption|eassumption|].
    admit.
  - inversion H3; unexistT; subst; simpl in *.
    eexists; exists res; splits 3; [econstructor| |intros; assumption]. constructor.
  - inversion H5; unexistT; subst; simpl in *.
    inversion H9; unexistT; subst; simpl in *.
    specialize (IHredM1 cenv (extE_term t2)).
    destruct IHredM1 as (o3 & HredE1 & Ho3); [reflexivity|intros; apply H8; apply Henv2; assumption|constructor|].
    specialize (IHredM2 cenv (extE_appnf v o3)).
    destruct IHredM2 as (o4 & HredE2 & Ho4); [reflexivity|intros; apply H8; apply Henv2; assumption|constructor; assumption|].
    exists o4. split; [econstructor; eassumption|].
    eapply compat_memM_read_outM; eassumption.
  - inversion H6; unexistT; subst; simpl in *.
    inversion H9; unexistT; subst; simpl in *.
    match goal with [ _ : match ?a with Some _ => _ | None => _ end |- _ ] => destruct a as [x|] eqn:Ha end.
    + destruct H0 as [Henv3 Hm3]; subst.
      destruct t2; try congruence.
      rewrite nth_error_map in Ha. destruct nth_error as [xv|] eqn:Hxv; [|congruence]; subst.
      injection Ha as <-.
      specialize (IHredM (xv :: xvs) (extE_term t1)).
      destruct IHredM as (o2 & HredE & Ho2).
      * reflexivity.
      * intros x c [-> | Hxc]; [|apply H7; assumption].
        eapply H8, Henv2, nth_error_In; eassumption.
      * constructor.
      * exists o2. split; [|eapply compat_memM_read_outM; eassumption].
        constructor. rewrite nth_error_map, Hxv; assumption.
    + destruct H0 as (x & Hx & Henv3 & Hm3); subst.
      assert (Hcompat : compat_memM m2 ((x, eiM_lazy t2 (map fst cenv)) :: m2)) by admit.
      specialize (IHredM ((x, clo_term t2 (map snd cenv)) :: xvs) (extE_term t1)).
      destruct IHredM as (o2 & HredE & Ho2).
      * reflexivity.
      * intros y c [[=<- <-] | Hyc]; [|eapply Hcompat, H7; assumption].
        eapply read_eiM_lazy; simpl; [rewrite freevar_eq_dec_eq_ifte; reflexivity|].
        intros y c Hyc; apply Hcompat, H8, Henv2; assumption.
      * constructor.
      * exists o2. split; [|eapply compat_memM_read_outM, compat_memM_read_outM; eassumption].
        constructor. simpl in *. destruct t2; try assumption.
        rewrite nth_error_map in *; destruct nth_error; [congruence|assumption].
  - inversion H3; unexistT; subst; simpl in *.
    eexists; split; [econstructor|]. constructor.
  - inversion H3; unexistT; subst; simpl in *.
    inversion H7; unexistT; subst; simpl in *.
    + eexists; split; [econstructor|].
      constructor; [assumption|]. apply read_valM_nf.
    + eexists; split; [econstructor|].
      constructor; [assumption|]. apply read_valM_nf.
Qed.
































