Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.


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



Inductive clo :=
| mkclo : term -> list clo -> clo.

Fixpoint shift_clo (c : clo) : clo :=
  match c with
  | mkclo t l => mkclo (ren_term (shiftn (length l)) t) (map shift_clo l)
  end.

Definition read_env (e : list term) :=
  fun n => match nth_error e n with Some u => u | None => var (n - length e) end.

Fixpoint read_clo (c : clo) : term :=
  match c with
  | mkclo t l =>
    let nl := map read_clo l in
    subst (read_env nl) t
  end.

Fixpoint clo_ind2 (P : clo -> Prop) (H : forall t l, Forall P l -> P (mkclo t l)) (c : clo) : P c :=
  match c with
  | mkclo t l => H t l ((fix H2 (l : _) : Forall P l :=
              match l with
              | nil => @Forall_nil _ _
              | cons c l => @Forall_cons _ _ c l (clo_ind2 P H c) (H2 l)
              end) l)
  end.

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

Inductive valE : deep_flag -> Type :=
| valEs_nf : nfval -> valE shallow
| valEs_abs : term -> list clo -> valE shallow
| valEd_nf : nfval_or_lam -> valE deep.

Definition read_valE {df} (v : valE df) : val df :=
  match v with
  | valEs_nf v => vals_nf v
  | valEs_abs t v => vals_abs (subst (scons (var 0) (comp (ren_term (plus_ren 1)) (read_env (map read_clo v)))) t)
  | valEd_nf v => vald_nf v
  end.

Definition valE_nf {df} v : valE df :=
  match df with
  | shallow => valEs_nf v
  | deep => valEd_nf (nval v)
  end.

Lemma read_valE_nf :
  forall df v, read_valE (@valE_nf df v) = val_nf v.
Proof.
  intros [|] v; simpl; reflexivity.
Qed.

Inductive extE : deep_flag -> Type :=
| extE_term : forall df, term -> extE df
| extE_app : forall df, out (valE shallow) -> term -> extE df
| extE_appnf : forall df, nfval -> out (valE deep) -> extE df
| extEd_abs : out (valE deep) -> extE deep.

Arguments extE_term {df} _.
Arguments extE_app {df} _ _.
Arguments extE_appnf {df} _ _.

Definition out_map {A B : Type} (f : A -> B) (o : out A) : out B :=
  match o with
  | out_ret x => out_ret (f x)
  | out_div => out_div
  end.

Definition read_extE {df} env (e : extE df) : ext df :=
  match e with
  | extE_term t => ext_term (read_clo (mkclo t env))
  | extE_app o1 t2 => ext_app (out_map read_valE o1) (read_clo (mkclo t2 env))
  | extE_appnf v1 o2 => ext_appnf v1 (out_map read_valE o2)
  | extEd_abs o => extd_abs (out_map read_valE o)
  end.

Inductive redE : forall df, list clo -> extE df -> out (valE df) -> Prop :=
| redE_var_bound : forall df env n t2 env2 o,
    nth_error env n = Some (mkclo t2 env2) ->
    redE df env2 (extE_term t2) o ->
    redE df env (extE_term (var n)) o
| redE_var_free : forall df env n,
    nth_error env n = None ->
    redE df env (extE_term (var n)) (out_ret (valE_nf (nvar (n - length env))))
| redE_abs_shallow : forall t env,
    redE shallow env (extE_term (abs t)) (out_ret (valEs_abs t env))
| redE_abs_deep : forall t env o1 o2,
    redE deep (mkclo (var 0) nil :: map shift_clo env) (extE_term (ren_term (shiftn (S (length env))) t)) o1 ->
    redE deep env (extEd_abs o1) o2 ->
    redE deep env (extE_term (abs t)) o2
| redE_abs1_abort : forall env, redE deep env (extEd_abs out_div) out_div
| redE_abs1 : forall env v, redE deep env (extEd_abs (out_ret (valEd_nf v))) (out_ret (valEd_nf (nlam v)))
| redE_app : forall df env t1 o1 t2 o2,
    redE shallow env (extE_term t1) o1 ->
    redE df env (extE_app o1 t2) o2 ->
    redE df env (extE_term (app t1 t2)) o2
| redE_app1_abort : forall df env t2, redE df env (extE_app out_div t2) out_div
| redE_app1_nf : forall df env v o1 t2 o2,
    redE deep env (extE_term t2) o1 ->
    redE df env (extE_appnf v o1) o2 ->
    redE df env (extE_app (out_ret (valEs_nf v)) t2) o2
| redE_app1_abs : forall df env env2 t1 t2 o,
    redE df (mkclo t2 env :: env2) (extE_term t1) o ->
    redE df env (extE_app (out_ret (valEs_abs t1 env2)) t2) o
| redE_appnf_abort : forall df env v, redE df env (extE_appnf v out_div) out_div
| redE_appnf : forall df env v1 v2, redE df env (extE_appnf v1 (out_ret (valEd_nf v2))) (out_ret (valE_nf (napp v1 v2))).

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
| coredE_abs1 : forall env v, coredE deep env (extEd_abs (out_ret (valEd_nf v))) (out_ret (valEd_nf (nlam v)))
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

Arguments nth_error : simpl nomatch.
Lemma redE_red :
  forall df env e o, redE df env e o -> red df (read_extE env e) (out_map read_valE o).
Proof.
  intros df env e o H. induction H; simpl in *.
  - unfold read_env. rewrite nth_error_map, H. assumption.
  - unfold read_env. rewrite nth_error_map, H, map_length, read_valE_nf. constructor.
  - constructor.
  - rewrite subst_ren in IHredE1.
    econstructor; [|eassumption].
    erewrite subst_ext; [eassumption|].
    intros [|n]; unfold comp, read_env; [reflexivity|].
    unfold ren. rewrite renv_shiftn.
    destruct le_lt_dec; simpl; rewrite !nth_error_map, !map_length; destruct nth_error as [u|] eqn:Hu.
    + assert (Hu2 : nth_error env n <> None) by congruence; rewrite nth_error_Some in Hu2; lia.
    + assert (HSn : nth_error env (S n) = None) by (apply nth_error_None; lia); rewrite HSn.
      unfold ren_term. simpl. destruct (length env); f_equal; simpl; lia.
    + rewrite read_shift_clo. reflexivity.
    + rewrite nth_error_None in Hu. lia.
  - constructor.
  - constructor.
  - econstructor; eassumption.
  - constructor.
  - econstructor; eassumption.
  - econstructor.
    unfold subst1. rewrite subst_subst.
    erewrite subst_ext; [eassumption|].
    unfold comp, read_env.
    intros [|n]; simpl.
    + reflexivity.
    + rewrite subst_ren; unfold comp; simpl.
      erewrite subst_ext; [apply subst_id|]; intros; f_equal; lia.
  - constructor.
  - rewrite read_valE_nf. constructor.
Qed.

(*
Inductive redE : forall df, list clo -> extE df -> out (valE df) -> Prop :=
| redE_var_bound : forall df env n t2 env2 o,
    nth_error env n = Some (mkclo t2 env2) ->
    redE df env2 (extE_term t2) o ->
    redE df env (extE_term (var n)) o
| redE_var_free : forall df env n,
    nth_error env n = None ->
    redE df env (extE_term (var n)) (out_ret (valE_nf (nvar (n - length env))))
| redE_abs_shallow : forall t env,
    redE shallow env (extE_term (abs t)) (out_ret (valEs_abs t env))
| redE_abs_deep : forall t env o1 o2,
    redE deep (mkclo (var 0) nil :: map shift_clo env) (extE_term (ren_term (shiftn (S (length env))) t)) o1 ->
    redE deep env (extEd_abs o1) o2 ->
    redE deep env (extE_term (abs t)) o2
| redE_abs1_abort : forall env, redE deep env (extEd_abs out_div) out_div
| redE_abs1 : forall env v, redE deep env (extEd_abs (out_ret (valEd_nf v))) (out_ret (valEd_nf (nlam v)))
| redE_app : forall df env t1 o1 t2 o2,
    redE shallow env (extE_term t1) o1 ->
    redE df env (extE_app o1 t2) o2 ->
    redE df env (extE_term (app t1 t2)) o2
| redE_app1_abort : forall df env t2, redE df env (extE_app out_div t2) out_div
| redE_app1_nf : forall df env v o1 t2 o2,
    redE deep env (extE_term t2) o1 ->
    redE df env (extE_appnf v o1) o2 ->
    redE df env (extE_app (out_ret (valEs_nf v)) t2) o2
| redE_app1_abs : forall df env env2 t1 t2 o,
    redE df (mkclo t2 env :: env2) (extE_term t1) o ->
    redE df env (extE_app (out_ret (valEs_abs t1 env2)) t2) o
| redE_appnf_abort : forall df env v, redE df env (extE_appnf v out_div) out_div
| redE_appnf : forall df env v1 v2, redE df env (extE_appnf v1 (out_ret (valEd_nf v2))) (out_ret (valE_nf (napp v1 v2))).
*)


































Definition ext_shallow_to_deep (e : ext shallow) : ext deep :=
  match e return ext deep with
  | ext_term t => ext_term t
  | ext_app o1 t2 => ext_app o1 t2
  | ext_appnf v1 o2 => ext_appnf v1 o2
  | extd_abs t => extd_abs t
  end.

Lemma red_shallow_deep_val_aux :
  forall df e o,
    red df e o -> forall (p : df = shallow) v, (match p in _ = df return out (val df) with eq_refl => o end) = out_ret (vals_nf v) ->
    red deep (ext_shallow_to_deep (match p in _ = df return ext df with eq_refl => e end)) (out_ret (vald_nf (nval v))).
Proof.
  intros df e o H.
  induction H; try destruct df; intros p; try discriminate p; rewrite (UIP_dec deep_flag_eq_dec p eq_refl);
    intros nv Ho; try discriminate Ho; simpl.
  - injection Ho as Ho; subst. constructor.
  - econstructor; [eassumption|].
    eapply (IHred2 eq_refl). assumption.
  - econstructor; [eassumption|].
    eapply (IHred2 eq_refl). assumption.
  - econstructor.
    eapply (IHred eq_refl). eassumption.
  - injection Ho as Ho; subst. constructor.
Qed.

Lemma red_shallow_deep_val :
  forall e v, red shallow e (out_ret (vals_nf v)) ->
         red deep (ext_shallow_to_deep e) (out_ret (vald_nf (nval v))).
Proof.
  intros e v H.
  exact (red_shallow_deep_val_aux shallow e _ H eq_refl v eq_refl).
Qed.

Lemma red_shallow_deep_abs_aux :
  forall df e o,
    red df e o -> forall (p : df = shallow) t, (match p in _ = df return out (val df) with eq_refl => o end) = out_ret (vals_abs t) ->
    forall o2, red deep (ext_term (abs t)) o2 -> red deep (ext_shallow_to_deep (match p in _ = df return ext df with eq_refl => e end)) o2.
Proof.
  intros df e o H.
  induction H; try destruct df; intros p; try discriminate p; rewrite (UIP_dec deep_flag_eq_dec p eq_refl);
    intros nt Ho; try discriminate Ho; simpl.
  - injection Ho as Ho; subst. intros; assumption.
  - intros o3. specialize (IHred2 eq_refl nt Ho o3). simpl in IHred2.
    intros Hred. econstructor; [eassumption|]. apply IHred2; assumption.
  - intros o3. specialize (IHred2 eq_refl nt Ho o3). simpl in IHred2.
    intros Hred. econstructor; [eassumption|]. apply IHred2; assumption.
  - intros o3. specialize (IHred eq_refl nt Ho o3). simpl in IHred.
    intros Hred. constructor. apply IHred; assumption.
Qed.

Lemma red_shallow_deep_abs :
  forall e t,
    red shallow e (out_ret (vals_abs t)) ->
    forall o, red deep (ext_term (abs t)) o -> red deep (ext_shallow_to_deep e) o.
Proof.
  intros e t H.
  exact (red_shallow_deep_abs_aux shallow e _ H eq_refl t eq_refl).
Qed.
