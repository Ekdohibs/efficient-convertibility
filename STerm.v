Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.

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







Inductive term :=
| var : nat -> term
| abs : term -> term
| app : term -> term -> term.

Fixpoint ren (r : renaming) t :=
  match t with
  | var n => var (renv r n)
  | abs t => abs (ren (lift r) t)
  | app t1 t2 => app (ren r t1) (ren r t2)
  end.

Fixpoint subst t k u :=
  match t with
  | var n => if Nat.eq_dec k n then u else var n
  | abs t => abs (subst t (S k) (ren (plus_ren 1) u))
  | app t1 t2 => app (subst t1 k u) (subst t2 k u)
  end.

Inductive beta : term -> term -> Prop :=
| beta_app1 : forall t1 t2 t3, beta t1 t2 -> beta (app t1 t3) (app t2 t3)
| beta_app2 : forall t1 t2 t3, beta t1 t2 -> beta (app t3 t1) (app t3 t2)
| beta_abs : forall t1 t2, beta t1 t2 -> beta (abs t1) (abs t2)
| beta_redex : forall t1 t2, beta (app (abs t1) t2) (subst t1 0 t2).

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
    red df (ext_term (subst t1 0 t2)) o ->
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
    cored df (ext_term (subst t1 0 t2)) o ->
    cored df (ext_app (out_ret (vals_abs t1)) t2) o
| cored_appnf_abort : forall df v, cored df (ext_appnf v out_div) out_div
| cored_appnf : forall df v1 v2, cored df (ext_appnf v1 (out_ret (vald_nf v2))) (out_ret (val_nf (napp v1 v2))).

CoInductive infred {A : Type} (R : A -> A -> Prop) : A -> Prop :=
| infred_step : forall x y, R x y -> infred R y -> infred R x.
CoInductive costar {A : Type} (R : A -> A -> Prop) : A -> option A -> Prop :=
| costar_refl : forall x, costar R x (Some x)
| costar_step : forall x y z, R x y -> costar R y z -> costar R x z.
CoInductive costarT {A : Type} (R : A -> A -> Prop) : A -> option A -> Prop :=
| costarT_refl : forall x, costarT R x (Some x)
| costarT_step : forall x y z, R x y -> costarT R y z -> costarT R x z
| costarT_comp : forall w x y z, R w x -> costarT R x y -> (forall v, y = Some v -> costarT R v z) -> costarT R w z.
Definition costarP {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 -> y1 = Some x1 \/ exists z, R x1 z /\ H z y1.
Definition costarPT {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 -> y1 = Some x1 \/ (exists z, R x1 z /\ H z y1) \/ exists z1 z2, R x1 z1 /\ H z1 z2 /\ (forall v, z2 = Some v -> H v y1).

Inductive costarZ_gen {A : Type} (R : A -> A -> Prop) (H : A -> option A -> Prop) : A -> option A -> Prop :=
| costarZ_gen_refl : forall x, costarZ_gen R H x (Some x)
| costarZ_gen_step : forall x y z, R x y -> H y z -> costarZ_gen R H x z
| costarZ_gen_comp : forall x y z, costarZ_gen R H x y -> (forall w, y = Some w -> costarZ_gen R H w z) -> costarZ_gen R H x z.
Definition costarZ {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 -> costarZ_gen R H x1 y1.
Inductive costarW_gen {A : Type} (R : A -> A -> Prop) (H : A -> option A -> Prop) : A -> option A -> Prop :=
| costarW_gen_refl : forall x, costarW_gen R H x (Some x)
| costarW_gen_step : forall x y z, R x y -> H y z -> costarW_gen R H x z
| costarW_gen_comp : forall x y z, costarW_gen R H x y -> (forall w, y = Some w -> H w z) -> costarW_gen R H x z.
Definition costarW {A : Type} (R : A -> A -> Prop) x y :=
  exists H, H x y /\ forall x1 y1, H x1 y1 -> costarW_gen R H x1 y1.

Lemma costarP_costar :
  forall A (R : A -> A -> Prop) x y, costarP R x y -> costar R x y.
Proof.
  intros A R. cofix IH. intros x y (H & H1 & H2).
  apply H2 in H1. destruct H1 as [H1 | (z & HR & H1)].
  - subst. constructor.
  - econstructor; [eassumption|]. apply IH. exists H; split; assumption.
Qed.

Lemma costarPT_costarT :
  forall A (R : A -> A -> Prop) x y, costarPT R x y -> costarT R x y.
Proof.
  intros A R. cofix IH. intros x y (H & H1 & H2).
  apply H2 in H1. destruct H1 as [H1 | [(z & HR & H1) | (z1 & z2 & HR & H1a & H1b)]].
  - subst. constructor.
  - econstructor; [eassumption|]. apply IH. exists H; split; assumption.
  - eapply costarT_comp; [eassumption| |].
    + apply IH. exists H; split; eassumption.
    + intros v ->. apply IH. exists H; split; [|eassumption]. apply H1b. reflexivity.
Qed.

Lemma costarT_comp1 :
  forall A (R : A -> A -> Prop) x y z, costarT R x y -> (forall v, y = Some v -> costarT R v z) -> costarT R x z.
Proof.
  intros A R. cofix IH. intros x y z H1 H2. inversion H1; subst.
  - apply H2. reflexivity.
  - eapply costarT_step; [eassumption|]. eapply IH; eassumption.
  - eapply costarT_comp; [eassumption|eassumption|].
    intros v Hv; eapply IH.
    + apply H3. assumption.
    + assumption.
Qed.

Lemma costarT_costarP :
  forall A (R : A -> A -> Prop) x y, costarT R x y -> costarP R x y.
Proof.
  intros A R x y H. exists (costarT R).
  split; [assumption|]. intros x1 y1 H1. inversion H1; subst.
  - left; reflexivity.
  - right; eexists; split; eassumption.
  - right; eexists; split; [eassumption|].
    eapply costarT_comp1; eassumption.
Qed.

Lemma costarZ_gen_mono : forall A (R : A -> A -> Prop) (H1 H2 : A -> option A -> Prop) x y,
    (forall x y, H1 x y -> H2 x y) -> costarZ_gen R H1 x y -> costarZ_gen R H2 x y.
Proof.
  intros A R H1 H2 x y H12 Hgen. induction Hgen.
  - apply costarZ_gen_refl.
  - eapply costarZ_gen_step; [eassumption|]. apply H12. assumption.
  - eapply costarZ_gen_comp; [eassumption|]. eassumption.
Qed.

Lemma costarW_gen_mono : forall A (R : A -> A -> Prop) (H1 H2 : A -> option A -> Prop) x y,
    (forall x y, H1 x y -> H2 x y) -> costarW_gen R H1 x y -> costarW_gen R H2 x y.
Proof.
  intros A R H1 H2 x y H12 Hgen. induction Hgen.
  - apply costarW_gen_refl.
  - eapply costarW_gen_step; [eassumption|]. apply H12. assumption.
  - eapply costarW_gen_comp; [eassumption|]. intros w Hw. apply H12. apply H; assumption.
Qed.

Lemma costarZ_comp :
  forall A (R : A -> A -> Prop) x y z, costarZ R x y -> (forall v, y = Some v -> costarZ R v z) -> costarZ R x z.
Proof.
  intros A R x y z H1 H2. destruct y as [y|].
  - specialize (H2 y eq_refl). destruct H1 as (H1 & H1a & H1b). destruct H2 as (H2 & H2a & H2b).
    exists (fun u v => H1 u v \/ H2 u v \/ exists w, H1 u (Some w) /\ H2 w v).
    split.
    + right. right. exists y. split; assumption.
    + clear x y z H1a H2a. intros x z [Hxz | [Hxz | (y & Hxy & Hyz)]].
      * eapply costarZ_gen_mono; [|apply H1b; assumption].
        intros; tauto.
      * eapply costarZ_gen_mono; [|apply H2b; assumption].
        intros; tauto.
      * eapply costarZ_gen_comp.
        -- eapply costarZ_gen_mono; [|apply H1b; apply Hxy].
           intros; tauto.
        -- intros w [= <-]. eapply costarZ_gen_mono; [|apply H2b; apply Hyz].
           intros; tauto.
  - destruct H1 as (H1 & H1a & H1b). exists (fun u v => H1 u v \/ H1 u None).
    split; [right; assumption|]. clear x z H1a H2.
    intros x y [Hxy | Hxy].
    + eapply costarZ_gen_mono; [|apply H1b; assumption].
      intros; tauto.
    + apply H1b in Hxy. remember None as z; revert Heqz; induction Hxy.
      * discriminate.
      * intros ->. eapply costarZ_gen_step; [eassumption|]. right. assumption.
      * intros ->. eapply costarZ_gen_comp; [eapply costarZ_gen_mono; [|eassumption]; intros; tauto|].
        intros; apply H0; [assumption | reflexivity].
Qed.

Lemma costarW_comp :
  forall A (R : A -> A -> Prop) x y z, costarW R x y -> (forall v, y = Some v -> costarW R v z) -> costarW R x z.
Proof.
  intros A R x y z H1 H2. destruct y as [y|].
  - specialize (H2 y eq_refl). destruct H1 as (H1 & H1a & H1b). destruct H2 as (H2 & H2a & H2b).
    exists (fun u v => H1 u v \/ H2 u v \/ exists w, H1 u (Some w) /\ H2 w v).
    split.
    + right. right. exists y. split; assumption.
    + clear x y z H1a H2a. intros x z [Hxz | [Hxz | (y & Hxy & Hyz)]].
      * eapply costarW_gen_mono; [|apply H1b; assumption].
        intros; tauto.
      * eapply costarW_gen_mono; [|apply H2b; assumption].
        intros; tauto.
      * eapply costarW_gen_comp.
        -- eapply costarW_gen_mono; [|apply H1b; apply Hxy].
           intros; tauto.
        -- intros w [= <-]. tauto.
  - destruct H1 as (H1 & H1a & H1b). exists (fun u v => H1 u v \/ H1 u None).
    split; [right; assumption|]. clear x z H1a H2.
    intros x y [Hxy | Hxy].
    + eapply costarW_gen_mono; [|apply H1b; assumption].
      intros; tauto.
    + apply H1b in Hxy. remember None as z; revert Heqz; induction Hxy.
      * discriminate.
      * intros ->. eapply costarW_gen_step; [eassumption|]. right. assumption.
      * intros ->. eapply costarW_gen_comp; [eapply costarW_gen_mono; [|eassumption]; intros; tauto|].
        intros. right. apply H. assumption.
Qed.


Lemma costarZ_costarP :
  forall A (R : A -> A -> Prop) x y, costarZ R x y -> costarP R x y.
Proof.
  intros A R x y H. exists (costarZ R).
  split; [assumption|]. clear x y H. intros x y H. destruct H as (H & H1 & H2).
  apply H2 in H1. induction H1.
  - left. reflexivity.
  - right. exists y. split; [assumption|]. eexists; split; eassumption.
  - destruct IHcostarZ_gen as [-> | (w & Hw1 & Hw2)].
    + apply H3. reflexivity.
    + right. exists w; split; [assumption|].
      eapply costarZ_comp; [eassumption|].
      intros v ->. specialize (H0 v eq_refl).
      exists (fun u v => H u v \/ costarZ_gen R H u v).
      split; [right; assumption|].
      intros s t [Hst | Hst].
      * eapply costarZ_gen_mono; [|apply H2; assumption]; intros; tauto.
      * eapply costarZ_gen_mono; [|apply Hst; assumption]; intros; tauto.
Qed.

Lemma costarW_costarP :
  forall A (R : A -> A -> Prop) x y, costarW R x y -> costarP R x y.
Proof.
  intros A R x y H. exists (costarW R).
  split; [assumption|]. clear x y H. intros x y H. destruct H as (H & H1 & H2).
  apply H2 in H1. induction H1.
  - left. reflexivity.
  - right. exists y. split; [assumption|]. eexists; split; eassumption.
  - destruct IHcostarW_gen as [-> | (w & Hw1 & Hw2)].
Abort. (*
    + apply H3. reflexivity.
    + right. exists w; split; [assumption|].
      eapply costarW_comp; [eassumption|].
      intros v ->. specialize (H0 v eq_refl).
      exists (fun u v => H u v \/ costarZ_gen R H u v).
      split; [right; assumption|].
      intros s t [Hst | Hst].
      * eapply costarZ_gen_mono; [|apply H2; assumption]; intros; tauto.
      * eapply costarZ_gen_mono; [|apply Hst; assumption]; intros; tauto.
Qed.
*)


Lemma costarPT_costarP :
  forall A (R : A -> A -> Prop) x y, costarPT R x y -> costarP R x y.
Proof.
  intros A R x y H. exists (costarPT R). split; [assumption|]. clear x y H.
  intros x y (H & H1 & H2). apply H2 in H1. destruct H1 as [H1 | [H1 | H1]].
  - left; assumption.
  - right. destruct H1 as (z & Hz1 & Hz2). exists z. split; [assumption|]. exists H. split; assumption.
  - admit.
Abort.

Definition read_out {df} (o : out (val df)) := match o with out_div => None | out_ret v => Some (read_val v) end.
Definition read_ext {df} (e : ext df) :=
  match e with
  | ext_term t => Some t
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2) | None => None end
  | extd_abs o => match read_out o with Some t => Some (abs t) | None => None end
  end.

Require Import Star.
Require Import Coq.Logic.Eqdep_dec.

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

Lemma costarT_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y : A, RA x y -> RB (f x) (f y)) ->
    forall x y, costarT RA x y -> costarT RB (f x) (match y with None => None | Some y => Some (f y) end).
Proof.
  intros A B RA RB f H. cofix IH. intros x y Hx. inversion Hx; subst.
  - constructor.
  - econstructor; [apply H; eassumption|].
    apply IH. assumption.
  - econstructor; [apply H; eassumption| |].
    + apply IH. eassumption.
    + destruct y0 as [y1|]; intros v; [|discriminate]; intros [= <-].
      apply IH. apply H2. reflexivity.
Defined.
Print costarT_map_impl.
Eval cbv in costarT_map_impl.

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

(*
Lemma red_div_beta :
  forall t df e o, cored df e o -> read_ext e = Some t -> costarPT (fun x y => beta x y \/ x = y) t (read_out o).
Proof.
  intros t df e o H Ht.
  exists (fun x y => exists df e o f, cored df e o /\ option_map f (read_ext e) = Some x /\ y = option_map f (read_out o) /\ respectful beta f).
  split; [exists df; exists e; exists o; exists id; split; [assumption|split; rewrite option_map_id; [assumption|split; [reflexivity|intros x y Hxy; assumption]]]|].
  clear t df e o H Ht. intros t y (df & e & o & f & H & Ht & -> & Hf);
  inversion H; subst; simpl in *; unexistT; subst; simpl in *; try congruence; injection Ht; intros; subst.
  - left. rewrite read_val_nf. reflexivity.
  - left. reflexivity.
  - right. right.
    eexists. eexists. split; [right; reflexivity|]. split.
    + eexists. eexists. eexists. exists (fun t1 => f (abs t1)).
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. intros x y Hxy. apply Hf. apply beta_abs. assumption.
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H6|]. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. reflexivity.
  - right. right.
    eexists. eexists. split; [right; reflexivity|]. split.
    + eexists. eexists. eexists. exists (fun t3 => f (app t3 t2)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. intros x y Hxy. apply Hf. apply beta_app1. assumption.
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. right.
    eexists. eexists. split; [right; reflexivity|]. split.
    + eexists. eexists. eexists. exists (fun t3 => f (app (read_nfval v) t3)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. intros x y Hxy. apply Hf. apply beta_app2. assumption.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (subst t1 0 t2)). split; [left; apply Hf; apply beta_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. rewrite read_val_nf. reflexivity.
Qed.
 *)

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
    exists (f (subst t1 0 t2, 2 * size (subst t1 0 t2))).
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

(*
Require Import Coq.Arith.Wf_nat.
Lemma red_div_beta2 :
  forall t df e o, cored df e o -> read_ext e = Some t ->
              costarZ beta t (read_out o).
Proof.
  intros t df e o H Ht.
  exists (fun x y => exists df e o f, cored df e o /\ option_map f (read_ext e) = Some x /\
                         y = option_map f (read_out o) /\ respectful beta f).
  split.
  {
    exists df; exists e; exists o; exists id. splits 4.
    - assumption.
    - rewrite option_map_id. assumption.
    - rewrite option_map_id. reflexivity.
    - intros x y Hxy. exact Hxy.
  }
  clear t df e o H Ht. intros x y (df & e & o & f & H & Hx & -> & Hf).
  rewrite read_ext_with_size_read_ext in Hx.
  destruct (read_ext_with_size e) as [[re n]|] eqn:Heqre; simpl in *; [|congruence]. simpl in Hx; injection Hx as Hx; subst x.
  revert df re e o f H Hf Heqre. induction n as [n IHn] using lt_wf_ind. intros df re e o f H Hf Heqre.
  inversion H; subst; simpl in *; unexistT; subst; simpl in *; try congruence; injection Heqre; intros; subst.
  - rewrite read_val_nf. apply costarZ_gen_refl.
  - apply costarZ_gen_refl.
  - eapply costarZ_gen_comp.
    + eapply IHn with (f := fun t1 => f (abs t1)); [|exact H4| |reflexivity]; [lia|].
      intros x y Hxy. apply Hf. apply beta_abs. assumption.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eapply IHn with (f := f); [|exact H6|assumption|reflexivity]. simpl. lia.
      split; [exact H6|]. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. reflexivity.
  - right. right.
    eexists. eexists. split; [right; reflexivity|]. split.
    + eexists. eexists. eexists. exists (fun t3 => f (app t3 t2)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. intros x y Hxy. apply Hf. apply beta_app1. assumption.
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. right.
    eexists. eexists. split; [right; reflexivity|]. split.
    + eexists. eexists. eexists. exists (fun t3 => f (app (read_nfval v) t3)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. intros x y Hxy. apply Hf. apply beta_app2. assumption.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (subst t1 0 t2)). split; [left; apply Hf; apply beta_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. rewrite read_val_nf. reflexivity.
Qed.
*)

(*
  cofix IH. intros t df e o H Ht;
              inversion H; subst; simpl in *; unexistT; subst; simpl in *; try congruence; injection Ht; intros; subst.
  - rewrite read_val_nf; simpl. constructor.
  - constructor.
  - eapply costarT_comp with (y := match read_out o1 with | Some y => Some (abs y) | None => None end); [right; reflexivity| |].
    + eapply costarT_map_impl; [|eapply IH; [exact H4|reflexivity]].
      intros u1 u2 [Hu|Hu]; [left; constructor; assumption|right; congruence].
    + intros w. destruct o1; simpl; [|discriminate]; intros [= <-].
      eapply IH; [exact H6|reflexivity].
  - constructor.
  - admit.
  - admit.
  - eapply costarT_step; [left; apply beta_redex|].
    eapply IH; [apply H3|]. reflexivity.
  - rewrite read_val_nf; simpl. constructor.
Qed.

  - inversion H5; subst. injection Ht; intros; subst.
    eapply infred_map_impl with (RA := beta) (f := abs); [intros; constructor; assumption|].
    admit.
  - 
  - admit.

  - apply inj_pair2_eq_dec in H1; [|apply deep_flag_eq_dec].
    apply inj_pair2_eq_dec in H3; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H3; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H0; [|apply deep_flag_eq_dec].
    apply inj_pair2_eq_dec in H1; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H2; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H0; [|apply deep_flag_eq_dec].
    apply inj_pair2_eq_dec in H1; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H0; [|apply deep_flag_eq_dec].
    apply inj_pair2_eq_dec in H2; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - apply inj_pair2_eq_dec in H2; [|apply deep_flag_eq_dec].
    subst. simpl in *. congruence.
  - 


  cofix IH. intros df e H. inversion H; subst; intros u Hu; simpl in *.
  - apply inj_pair2_eq_dec in H1; [|apply deep_flag_eq_dec].
    apply inj_pair2_eq_dec in H3; [|apply deep_flag_eq_dec].
    subst. injection Hu; intros; subst.
    eapply infred_map_impl with (RA := beta) (f := abs); [intros; constructor; assumption|].
    destruct o1.
    + admit.
    + eapply IH; [exact H4|]. reflexivity.
  - congruence.
  - admit.
  - congruence.
  - admit.
  - admit.
  - congruence.
Qed.

    rewrite read_val_nf in Hu2; simpl in Hu2.
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
*)

















(* STerms *)

Inductive sterm :=
| sbvar : nat -> sterm
| sevar : nat -> sterm
| sfvar : freevar -> sterm
| slam : sterm -> sterm
| sapp : sterm -> sterm -> sterm.

Inductive sitem :=
| sitem1 : sterm -> sitem
| sitem2 : sterm -> sterm -> sitem.

Definition readitem si :=
  match si with
  | sitem1 t => t
  | sitem2 t1 t2 => t1
  end.

Fixpoint ssubstb k u t :=
  match t with
  | sbvar n => if Nat.eq_dec n k then u else sbvar n
  | sevar n => sevar n
  | sfvar x => sfvar x
  | slam t => slam (ssubstb (S k) u t)
  | sapp t1 t2 => sapp (ssubstb k u t1) (ssubstb k u t2)
  end.

Fixpoint sshifte k off t :=
  match t with
  | sbvar n => sbvar n
  | sevar n => if le_lt_dec k n then sevar (off + n) else sevar n
  | sfvar x => sfvar x
  | slam t => slam (sshifte k off t)
  | sapp t1 t2 => sapp (sshifte k off t1) (sshifte k off t2)
  end.

Definition sishifte k off si :=
  match si with
  | sitem1 t => sitem1 (sshifte k off t)
  | sitem2 t1 t2 => sitem2 (sshifte k off t1) (sshifte k off t2)
  end.

Fixpoint seshifte k off e :=
  match e with
  | nil => nil
  | si :: e => sishifte k off si :: seshifte k off e
  end.

Inductive sterm_red : list sterm -> sterm -> sterm -> list sterm -> Prop :=
| sterm_red_var : forall env n t, nth_error env n = Some t -> sterm_red env (sevar n) t nil
| sterm_red_app1 : forall env t1 t2 t3 e, sterm_red env t1 t2 e -> sterm_red env (sapp t1 t3) (sapp t2 t3) e
| sterm_red_app2 : forall env t1 t2 t3 e, sterm_red env t1 t2 e -> sterm_red env (sapp t3 t1) (sapp t3 t2) e
| sterm_red_lam : forall env t1 t2 e, sterm_red env t1 t2 e -> sterm_red env (slam t1) (slam t2) e
| sterm_red_redex : forall env t1 t2, sterm_red env (sapp (slam t1) t2) (ssubstb 0 (sevar (length env)) t1) (t2 :: nil).

Inductive sterme_red : list sterm -> list sitem -> list sitem -> Prop :=
| sterme_red_promote : forall env t rest, sterme_red env (sitem1 t :: rest) (sitem2 t t :: rest)
| sterme_red_env : forall env si e1 e2, sterme_red (env ++ readitem si :: nil) e1 e2 -> sterme_red env (si :: e1) (si :: e2)
| sterme_red_red1 :
    forall env t1 t2 e rest,
      sterm_red env t1 t2 e ->
      sterme_red env (sitem1 t1 :: rest) (map sitem1 e ++ sitem1 t2 :: seshifte (length env) (length e) rest)
| sterme_red_red2 :
    forall env t1 t2 t3 e rest,
      sterm_red env t1 t2 e ->
      sterme_red env (sitem2 t3 t1 :: rest) (map sitem1 e ++ sitem2 t3 t2 :: seshifte (length env) (length e) rest).
