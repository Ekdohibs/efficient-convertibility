Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import Inductive.

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

Definition liftn p (L : renaming) : renaming :=
  match L with
  | nil => nil
  | k :: L => p + k :: L
  end.

Lemma liftn_renv_small :
  forall n p L, n < p -> renv (liftn p L) n = n.
Proof.
  intros n p [|k L] Hp; simpl; try reflexivity.
  destruct le_lt_dec; lia.
Qed.

Lemma liftn_renv_large :
  forall n p L, p <= n -> renv (liftn p L) n = p + renv L (n - p).
Proof.
  intros n p [|k L] Hp; simpl; try lia.
  repeat destruct le_lt_dec; try lia.
  replace (n - p - k) with (n - (p + k)) by lia. lia.
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
| app : term -> term -> term
| constr : nat -> list term -> term
| switch : term -> list (nat * term) -> term.

Fixpoint term_ind2 (P : term -> Prop)
         (Hvar : forall n, P (var n))
         (Habs : forall t, P t -> P (abs t))
         (Happ : forall t1 t2, P t1 -> P t2 -> P (app t1 t2))
         (Hconstr : forall tag l, Forall P l -> P (constr tag l))
         (Hswitch : forall t m, P t -> Forall (fun '(p, t2) => P t2) m -> P (switch t m))
         (t : term) : P t :=
  match t with
  | var n => Hvar n
  | abs t => Habs t (term_ind2 P Hvar Habs Happ Hconstr Hswitch t)
  | app t1 t2 =>
    Happ t1 t2
      (term_ind2 P Hvar Habs Happ Hconstr Hswitch t1)
      (term_ind2 P Hvar Habs Happ Hconstr Hswitch t2)
  | constr tag l =>
    Hconstr tag l
            ((fix H (l : _) : Forall P l :=
              match l with
              | nil => @Forall_nil _ _
              | cons t l => @Forall_cons _ _ t l (term_ind2 P Hvar Habs Happ Hconstr Hswitch t) (H l)
              end) l)
  | switch t m =>
    Hswitch t m
            (term_ind2 P Hvar Habs Happ Hconstr Hswitch t)
            ((fix H (m : _) : Forall (fun '(p, t2) => P t2) m :=
              match m with
              | nil => @Forall_nil _ _
              | cons (p, t2) m => @Forall_cons _ _ (p, t2) m (term_ind2 P Hvar Habs Happ Hconstr Hswitch t2) (H m)
              end) m)
  end.


Fixpoint ren_term (r : renaming) t :=
  match t with
  | var n => var (renv r n)
  | abs t => abs (ren_term (lift r) t)
  | app t1 t2 => app (ren_term r t1) (ren_term r t2)
  | constr tag l => constr tag (map (ren_term r) l)
  | switch t l => switch (ren_term r t) (map (fun pt2 => (fst pt2, ren_term (liftn (fst pt2) r) (snd pt2))) l)
  end.

Definition lift_subst us := scons (var 0) (comp (ren_term (plus_ren 1)) us).
Definition liftn_subst p us n := if le_lt_dec p n then ren_term (plus_ren p) (us (n - p)) else var n.

Fixpoint subst us t :=
  match t with
  | var n => us n
  | abs t => abs (subst (lift_subst us) t)
  | app t1 t2 => app (subst us t1) (subst us t2)
  | constr tag l => constr tag (map (subst us) l)
  | switch t l => switch (subst us t) (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) us) (snd pt2))) l)
  end.

Definition subst1 u t := subst (scons u (fun n => var n)) t.

Lemma subst_ext :
  forall t us1 us2, (forall n, us1 n = us2 n) -> subst us1 t = subst us2 t.
Proof.
  induction t using term_ind2; intros us1 us2 Heq; simpl.
  - apply Heq.
  - f_equal. apply IHt. intros [|n]; simpl; [reflexivity|unfold comp; f_equal; apply Heq].
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply map_ext_in. intros t Ht. rewrite Forall_forall in H. apply H; assumption.
  - f_equal; [apply IHt; assumption|].
    apply map_ext_in. intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. apply (H _ Hpt2).
    intros n. unfold liftn_subst. destruct le_lt_dec; [|reflexivity]. f_equal. apply Heq.
Qed.

Definition ren r := fun n => var (renv r n).

Lemma ren_term_is_subst :
  forall t r, ren_term r t = subst (ren r) t.
Proof.
  induction t using term_ind2; intros r; simpl.
  - reflexivity.
  - f_equal. rewrite IHt. apply subst_ext.
    intros [|n]; simpl.
    + unfold ren. rewrite lift_renv. reflexivity.
    + unfold ren. rewrite lift_renv. unfold comp. simpl. f_equal. f_equal. lia.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply map_ext_in. intros t Ht. rewrite Forall_forall in H. apply H; assumption.
  - f_equal; [apply IHt|].
    apply map_ext_in. intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H.
    erewrite subst_ext; [apply (H _ Hpt2)|]. intros n.
    unfold liftn_subst, ren. destruct le_lt_dec.
    + simpl. rewrite liftn_renv_large, plus_ren_correct; [reflexivity|assumption].
    + f_equal. rewrite liftn_renv_small; [reflexivity|assumption].
Qed.

Lemma unfold_lift_subst :
  forall us n, lift_subst us n = match n with 0 => var 0 | S n => subst (ren (plus_ren 1)) (us n) end.
Proof.
  intros us [|n]; simpl; [reflexivity|].
  unfold comp. apply ren_term_is_subst.
Qed.

Lemma unfold_liftn_subst :
  forall p us n, liftn_subst p us n = if le_lt_dec p n then subst (ren (plus_ren p)) (us (n - p)) else var n.
Proof.
  intros p us n. unfold liftn_subst. destruct le_lt_dec; [|reflexivity].
  apply ren_term_is_subst.
Qed.


Lemma unfold_subst :
  forall t us, subst us t =
          match t with
          | var n => us n
          | abs t => abs (subst (lift_subst us) t)
          | app t1 t2 => app (subst us t1) (subst us t2)
          | constr tag l => constr tag (map (subst us) l)
          | switch t l => switch (subst us t) (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) us) (snd pt2))) l)
          end.
Proof.
  destruct t; intros us; reflexivity.
Qed.

Lemma ren_ren :
  forall t r1 r2, ren_term r1 (ren_term r2 t) = ren_term (renv_comp r1 r2) t.
Proof.
  induction t using term_ind2; intros r1 r2; simpl.
  - rewrite renv_comp_correct. reflexivity.
  - f_equal. rewrite IHt. f_equal.
    apply renv_ext.
    intros [|n]; rewrite !lift_renv, !renv_comp_correct, !lift_renv; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. rewrite map_map; apply map_ext_in. intros t Ht.
    rewrite Forall_forall in H. apply H. assumption.
  - f_equal; [apply IHt|]. rewrite map_map; apply map_ext_in.
    intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H.
    rewrite (H _ Hpt2). f_equal. apply renv_ext. intros n.
    destruct (le_lt_dec p n).
    + rewrite renv_comp_correct, !liftn_renv_large, renv_comp_correct; try assumption.
      * f_equal. f_equal. lia.
      * rewrite liftn_renv_large; lia.
    + rewrite renv_comp_correct, !liftn_renv_small; try assumption.
      * reflexivity.
      * rewrite liftn_renv_small; assumption.
Qed.

Lemma ren_subst :
  forall t r us, ren_term r (subst us t) = subst (comp (ren_term r) us) t.
Proof.
  induction t using term_ind2; intros r us; simpl.
  - unfold comp; simpl. rewrite ren_term_is_subst. reflexivity.
  - f_equal. rewrite IHt. unfold comp. apply subst_ext.
    intros [|n]; simpl.
    + rewrite lift_renv. reflexivity.
    + unfold comp. rewrite !ren_ren. f_equal.
      apply renv_ext. intros [|m]; rewrite !renv_comp_correct, lift_renv; simpl; lia.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. rewrite map_map; apply map_ext_in. intros t Ht.
    rewrite Forall_forall in H. apply H. assumption.
  - f_equal; [apply IHt|]. rewrite map_map; apply map_ext_in.
    intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. rewrite (H _ Hpt2). apply subst_ext.
    intros n. unfold comp, liftn_subst. destruct le_lt_dec.
    + rewrite !ren_ren. f_equal. apply renv_ext. intros n2.
      rewrite !renv_comp_correct, !plus_ren_correct, liftn_renv_large by lia.
      f_equal. f_equal. lia.
    + simpl. rewrite liftn_renv_small; [reflexivity|assumption].
Qed.

Lemma subst_ren :
  forall t r us, subst us (ren_term r t) = subst (comp (subst us) (ren r)) t.
Proof.
  induction t using term_ind2; intros r us; simpl.
  - unfold comp; simpl. reflexivity.
  - f_equal. rewrite IHt. unfold comp. apply subst_ext.
    intros [|n]; simpl.
    + rewrite lift_renv. reflexivity.
    + rewrite lift_renv. simpl. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. rewrite map_map; apply map_ext_in. intros t Ht.
    rewrite Forall_forall in H. apply H. assumption.
  - f_equal; [apply IHt|]. rewrite map_map; apply map_ext_in.
    intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. rewrite (H _ Hpt2). apply subst_ext.
    intros n. unfold comp, liftn_subst, ren; simpl. destruct (le_lt_dec p n).
    + unfold ren. simpl. rewrite liftn_renv_large by assumption.
      destruct le_lt_dec; [|lia]. f_equal. f_equal. lia.
    + unfold ren. rewrite liftn_renv_small by assumption. destruct le_lt_dec; [lia|reflexivity].
Qed.

Lemma subst_subst :
  forall t us1 us2, subst us2 (subst us1 t) = subst (comp (subst us2) us1) t.
Proof.
  induction t using term_ind2; intros us1 us2; simpl.
  - unfold comp. reflexivity.
  - f_equal. rewrite IHt. unfold lift_subst, comp. apply subst_ext.
    intros [|n]; simpl; [reflexivity|].
    rewrite ren_subst. rewrite subst_ren. apply subst_ext.
    intros m; unfold comp; simpl. f_equal. f_equal. lia.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. rewrite map_map; apply map_ext_in.
    intros t Ht. rewrite Forall_forall in H. apply H. assumption.
  - f_equal; [apply IHt|]. rewrite map_map; apply map_ext_in.
    intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H. rewrite (H _ Hpt2). apply subst_ext.
    intros n. unfold comp, liftn_subst; simpl. destruct le_lt_dec; simpl.
    + rewrite subst_ren. rewrite ren_subst. apply subst_ext.
      intros n2; unfold comp; simpl. rewrite plus_ren_correct. destruct le_lt_dec; [|lia].
      f_equal. f_equal. lia.
    + destruct le_lt_dec; [lia|]. reflexivity.
Qed.

Lemma subst_id :
  forall t, subst (fun n => var n) t = t.
Proof.
  induction t using term_ind2; simpl; f_equal; try assumption.
  - erewrite subst_ext; [eassumption|].
    intros [|n]; unfold lift_subst, comp; simpl; [reflexivity|f_equal; lia].
  - erewrite map_ext_in; [apply map_id|]. intros t Ht.
    rewrite Forall_forall in H. apply H. assumption.
  - erewrite map_ext_in; [apply map_id|]. intros [p t2] Hpt2. simpl.
    f_equal. rewrite Forall_forall in H.
    erewrite subst_ext; [apply (H _ Hpt2)|]. intros n; unfold liftn_subst.
    destruct le_lt_dec; [|reflexivity]. simpl.
    rewrite plus_ren_correct; f_equal; lia.
Qed.

Definition read_env (e : list term) :=
  fun n => match nth_error e n with Some u => u | None => var (n - length e) end.

Inductive beta : term -> term -> Prop :=
| beta_app1 : forall t1 t2 t3, beta t1 t2 -> beta (app t1 t3) (app t2 t3)
| beta_app2 : forall t1 t2 t3, beta t1 t2 -> beta (app t3 t1) (app t3 t2)
| beta_abs : forall t1 t2, beta t1 t2 -> beta (abs t1) (abs t2)
| beta_redex : forall t1 t2, beta (app (abs t1) t2) (subst1 t2 t1)
| beta_constr : forall tag t1 t2 l1 l2, beta t1 t2 -> beta (constr tag (l1 ++ t1 :: l2)) (constr tag (l1 ++ t2 :: l2))
| beta_switch1 : forall t1 t2 l, beta t1 t2 -> beta (switch t1 l) (switch t2 l)
| beta_switch2 : forall t p t1 t2 l1 l2, beta t1 t2 -> beta (switch t (l1 ++ (p, t1) :: l2)) (switch t (l1 ++ (p, t2) :: l2))
| beta_switch_redex : forall l t l1 l2, beta (switch (constr (length l1) l) (l1 ++ (length l, t) :: l2)) (subst (read_env l) t).


Inductive deep_flag := shallow | deep.
Lemma deep_flag_eq_dec : forall (df1 df2 : deep_flag), { df1 = df2 } + { df1 <> df2 }.
Proof.
  intros [|] [|]; solve [left; reflexivity | right; discriminate].
Defined.

Inductive nfval :=
| nvar : nat -> nfval
| napp : nfval -> nfval_or_lam -> nfval
| nswitch : nfval -> list (nat * nfval_or_lam) -> nfval

with nfval_or_lam :=
| nval : nfval -> nfval_or_lam
| nlam : nfval_or_lam -> nfval_or_lam
| nconstr : nat -> list nfval_or_lam -> nfval_or_lam.


Fixpoint read_nfval v :=
  match v with
  | nvar n => var n
  | napp v1 v2 => app (read_nfval v1) (read_nfval_or_lam v2)
  | nswitch v l => switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) l)
  end

with read_nfval_or_lam v :=
  match v with
  | nval v => read_nfval v
  | nlam v => abs (read_nfval_or_lam v)
  | nconstr tag l => constr tag (map read_nfval_or_lam l)
  end.

Inductive val : deep_flag -> Type :=
| vals_nf : nfval -> val shallow
| vals_abs : term -> val shallow
| vals_constr : nat -> list term -> val shallow
| vald_nf : nfval_or_lam -> val deep.

Definition read_val {df} (v : val df) :=
  match v with
  | vals_nf v => read_nfval v
  | vals_abs t => abs t
  | vals_constr tag l => constr tag l
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

Definition todo := nat.
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

Definition get_out_abort {t1 t2} (o : out t1) : option (out t2) :=
  match o with
  | out_div => Some out_div
  | _ => None
  end.

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
    red_ rec df (ext_term (var n)) (out_ret (val_nf (nvar n))) (* Free variables reduce to themselves *)
| red_abs_shallow : forall t,
    red_ rec shallow (ext_term (abs t)) (out_ret (vals_abs t)) (* Do not look under abstractions *)
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

Lemma red_ind3 : is_ind3 red_ red.
Proof. prove_ind3. Qed.

CoInductive cored : forall df, ext df -> out (val df) -> Prop :=
| mkcored : forall df e o, red_ cored df e o -> cored df e o.

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
  | ext_switch o m => match read_out o with Some t2 => Some (switch t2 m) | None => None end
  | ext_switchnf v m1 o m2 =>
    match o with
    | None => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ m2))
    | Some (p, o) =>
      match read_out o with
      | Some t2 => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t2) :: m2))
      | None => None
      end
    end
  | extd_abs o => match read_out o with Some t => Some (abs t) | None => None end
  | extd_constr tag l1 o l2 =>
    match o with
    | None => Some (constr tag (map read_nfval_or_lam l1 ++ l2))
    | Some o =>
      match read_out o with
      | Some t2 => Some (constr tag (map read_nfval_or_lam l1 ++ t2 :: l2))
      | None => None
      end
    end
  end.

Ltac unexistT :=
  repeat match goal with
           [ H : @existT deep_flag _ _ _ = @existT deep_flag _ _ _ |- _ ] =>
           apply inj_pair2_eq_dec in H; [|apply deep_flag_eq_dec]
         end.
Lemma Some_inj : forall A (x y : A), Some x = Some y -> x = y.
Proof.
  intros; congruence.
Qed.
Ltac autoinjSome :=
  repeat match goal with
           [ H : Some ?x = Some ?y |- _ ] => apply Some_inj in H; subst
         end.

Lemma nth_error_decompose :
  forall (A : Type) (L : list A) x n, nth_error L n = Some x -> exists L1 L2, L = L1 ++ x :: L2 /\ length L1 = n.
Proof.
  intros A L. induction L as [|y L]; intros x [|n] H; simpl in *; try congruence; autoinjSome.
  - exists nil. exists L. split; reflexivity.
  - apply IHL in H. destruct H as (L1 & L2 & H1 & H2). exists (y :: L1). exists L2.
    split; [rewrite H1; reflexivity|simpl; rewrite H2; reflexivity].
Qed.

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

Lemma red_star_beta :
  forall df e o, red df e o -> forall t1 t2, read_ext e = Some t1 -> read_out o = Some t2 -> star beta t1 t2.
Proof.
  enough (forall df e o, red df e o -> o <> out_div -> forall t1 t2, read_ext e = Some t1 -> read_out o = Some t2 -> star beta t1 t2).
  { intros; eapply H; try eassumption. destruct o; simpl in *; congruence. }
  refine (preserved_with_inv3_rec _ _ red_ind3 _ _ red_not_div_preserved_down _).
  intros df e o H _ u1 u2 Hu1 Hu2.
  inversion H; unexistT; subst; unexistT; subst; simpl in *; autoinjSome.
  - rewrite read_val_nf. simpl. constructor.
  - constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (RA := beta); [intros; constructor; assumption|].
      apply H4; reflexivity.
    + apply H6; [reflexivity|assumption].
  - constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => app t t2) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => app _ t) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - econstructor; [apply beta_redex|].
    apply H3; [reflexivity|assumption].
  - rewrite read_val_nf. simpl. constructor.
  - constructor.
  - apply H2; [reflexivity|assumption].
  - rewrite app_nil_r. constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => constr _ (_ ++ t :: _)) (RA := beta); [intros; constructor; assumption|].
      eapply H4; reflexivity.
    + apply H6; [reflexivity|assumption].
  - apply H2; [|assumption]. rewrite map_app, <- app_assoc; reflexivity.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => switch t _) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - apply nth_error_decompose in H3. destruct H3 as (m1 & m2 & -> & <-).
    econstructor; [|apply H4; [reflexivity|assumption]]. constructor.
  - apply H3; [reflexivity|assumption].
  - rewrite read_val_nf, app_nil_r. constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => switch _ (_ ++ (_, t) :: _)) (RA := beta);
        [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - apply H3; [|assumption]. rewrite map_app, <- app_assoc; reflexivity.
  - destruct e; simpl in *; try congruence;
      try solve [destruct o0; simpl in *; autoinjSome; simpl in *; congruence];
      destruct o0 as [o0|]; simpl in *; try congruence.
    + destruct o0 as [p o0]; destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
    + destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
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

Definition option_map {A B : Type} (f : A -> B) (x : option A) := match x with Some x => Some (f x) | None => None end.
Lemma option_map_id : forall (A : Type) (x : option A), option_map id x = x.
Proof.
  intros A [x|]; reflexivity.
Qed.

Definition respectful {A : Type} (R : A -> A -> Prop) (f : A -> A) := forall x y, R x y -> R (f x) (f y).

Fixpoint list_sum l := match l with nil => 0 | x :: l => x + list_sum l end.
Fixpoint size t :=
  match t with
  | var n => 0
  | abs t => S (size t)
  | app t1 t2 => S (size t1 + size t2)
  | constr tag l => S (list_sum (map (fun t => S (size t)) l))
  | switch t m => S (size t + list_sum (map (fun pt2 => S (size (snd pt2))) m))
  end.

Definition read_ext_with_size {df} (e : ext df) :=
  match e with
  | ext_term t => Some (t, 2 * size t)
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2, 2 * size t2 + 1) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2, 0) | None => None end
  | ext_switch o m =>
    match read_out o with
    | Some t2 => Some (switch t2 m, 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m) + 1)
    | None => None
    end
  | ext_switchnf v m1 o m2 =>
    match o with
    | Some (p, o) =>
      match read_out o with
      | Some t2 => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t2) :: m2), 1 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))
      | None => None
      end
    | None => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ m2), 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))
    end
  | extd_abs o => match read_out o with Some t => Some (abs t, 0) | None => None end
  | extd_constr tag l1 o l2 =>
    match o with
    | Some o =>
      match read_out o with
      | Some t2 => Some (constr tag (map read_nfval_or_lam l1 ++ t2 :: l2), 1 + 2 * list_sum (map (fun t => S (size t)) l2))
      | None => None
      end
    | None => Some (constr tag (map read_nfval_or_lam l1 ++ l2), 2 * list_sum (map (fun t => S (size t)) l2))
    end
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
  inversion H as [? ? ? NH]; unexistT; subst.
  inversion NH; subst; simpl in *; unexistT; subst; simpl in *; autoinjSome; simpl in *.
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
  - left. apply Hf. unfold weaken; split; simpl; [reflexivity|lia].
  - right. left.
    exists (f (constr tag l, 2 * list_sum (map (fun t => S (size t)) l))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H2|]. split; [reflexivity|]. tauto.
  - left. apply Hf. rewrite app_nil_r. unfold weaken; simpl; split; [reflexivity|lia].
  - right. right.
    exists (f (constr tag (map read_nfval_or_lam l1 ++ t :: l2), 1 + 2 * size t + 2 * list_sum (map (fun t => S (size t)) l2))).
    exists (option_map (fun t3 => f (constr tag (map read_nfval_or_lam l1 ++ fst t3 :: l2), 1 + snd t3 + 2 * list_sum (map (fun t => S (size t)) l2))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (constr tag (map read_nfval_or_lam l1 ++ fst t3 :: l2), 1 + snd t3 + 2 * list_sum (map (fun t => S (size t)) l2))).
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy];
          [left; simpl; constructor; assumption|right; simpl; split; [destruct Hxy; congruence|lia]].
      * unfold weaken in *. simpl. split; [destruct Hxy; congruence|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H6|]. split; [reflexivity|]. tauto.
  - right. left.
    exists (f (constr tag (map read_nfval_or_lam l1 ++ read_nfval_or_lam v :: l2), 2 * list_sum (map (fun t => S (size t)) l2))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H2|]. split; [simpl; rewrite map_app, <- app_assoc; reflexivity|]. tauto.
  - right. right.
    exists (f (switch t m, 1 + 2 * size t + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
    exists (option_map (fun t3 => f (switch (fst t3) m, 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (switch (fst t3) m, 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
      split; [exact H3|]. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal; tauto|lia]].
      * unfold weaken in *. simpl. split; [f_equal; tauto|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [f_equal; f_equal; f_equal; lia|]. tauto.
  - right. left.
    exists (f (subst (read_env l) t, 2 * size (subst (read_env l) t))).
    apply nth_error_decompose in H3. destruct H3 as (m1 & m2 & -> & <-).
    split; [apply Hf; left; apply beta_switch_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (switch (read_nfval v) m, 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. split; [reflexivity|]. tauto.
  - left. apply Hf. unfold weaken; split; simpl; [rewrite read_val_nf, app_nil_r; reflexivity|lia].
  - right. right.
    exists (f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t) :: m2), 1 + 2 * size t + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
    exists (option_map (fun t3 => f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, fst t3) :: m2), 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, fst t3) :: m2), 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy];
          [left; simpl; constructor; assumption|right; simpl; split; [destruct Hxy; congruence|lia]].
      * unfold weaken in *. simpl. split; [destruct Hxy; congruence|lia].
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [f_equal; f_equal; f_equal; lia|]. tauto.
  - right. left.
    exists (f (switch (read_nfval v1) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, read_nfval_or_lam v2) :: m2), 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. split; [simpl; rewrite map_app, <- app_assoc; reflexivity|]. tauto.
  - exfalso. destruct e; simpl in *; try congruence;
      try solve [destruct o0; simpl in *; autoinjSome; simpl in *; congruence];
      destruct o0 as [o0|]; simpl in *; try congruence.
    + destruct o0 as [p o0]; destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
    + destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
Qed.

Lemma read_ext_with_size_read_ext :
  forall df (e : ext df), read_ext e = option_map fst (read_ext_with_size e).
Proof.
  intros. destruct e; simpl; try destruct read_out; simpl; try reflexivity.
  - destruct o as [[p o0]|]; simpl in *; [|reflexivity].
    destruct read_out; simpl; reflexivity.
  - destruct o as [o|]; simpl in *; [|reflexivity].
    destruct read_out; simpl; reflexivity.
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
| closed_at_abs : forall t k, closed_at t (S k) -> closed_at (abs t) k
| closed_at_constr : forall tag l k, (forall t, t \in l -> closed_at t k) -> closed_at (constr tag l) k
| closed_at_switch :
    forall t m k, closed_at t k -> (forall p t2, (p, t2) \in m -> closed_at t2 (p + k)) -> closed_at (switch t m) k.

Fixpoint index l x :=
  match l with
  | nil => 0
  | y :: l => if freevar_eq_dec x y then 0 else S (index l x)
  end.

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

(*
Fixpoint shift_clo (c : clo) : clo :=
  match c with
  | mkclo t l => mkclo (ren_term (shiftn (length l)) t) (map shift_clo l)
  end.
 *)

Fixpoint read_clo (xs : list freevar) (c : clo) : term :=
  match c with
  | clo_var x => var (index xs x)
  | clo_term _ t l =>
    let nl := map (read_clo xs) l in
    subst (read_env nl) t
  end.

Fixpoint clo_ind2 (P : clo -> Prop) (Hvar : forall x, P (clo_var x)) (Hterm : forall xs t l, Forall P l -> P (clo_term xs t l)) (c : clo) : P c :=
  match c with
  | clo_var x => Hvar x
  | clo_term xs t l => Hterm xs t l ((fix H (l : _) : Forall P l :=
                                 match l with
                                 | nil => @Forall_nil _ _
                                 | cons c l => @Forall_cons _ _ c l (clo_ind2 P Hvar Hterm c) (H l)
                                 end) l)
  end.

Lemma subst_closed_at_ext :
  forall t k us1 us2, closed_at t k -> (forall n, n < k -> us1 n = us2 n) -> subst us1 t = subst us2 t.
Proof.
  induction t using term_ind2; intros k us1 us2 Hclosed Hext; inversion Hclosed; subst; simpl.
  - apply Hext. assumption.
  - f_equal. eapply IHt; [eassumption|].
    intros [|n] Hn; simpl in *; [reflexivity|].
    unfold comp. f_equal. apply Hext. lia.
  - f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal. apply map_ext_in; intros t Ht.
    rewrite Forall_forall in H; eapply H; try eassumption.
    apply H3; assumption.
  - f_equal; [eapply IHt; eassumption|].
    apply map_ext_in; intros [p t2] Hpt2. simpl. f_equal.
    rewrite Forall_forall in H; eapply (H _ Hpt2); [apply H4; eassumption|].
    intros n Hn. unfold liftn_subst.
    destruct le_lt_dec.
    + f_equal. apply Hext. lia.
    + reflexivity.
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
    rewrite Forall_forall in H. apply H; [eassumption| |apply H4; assumption].
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
| nxswitch : nfvalx -> list (list freevar * nfvalx_or_lam) -> nfvalx

with nfvalx_or_lam :=
| nxval : nfvalx -> nfvalx_or_lam
| nxlam : freevar -> nfvalx_or_lam -> nfvalx_or_lam
| nxconstr : nat -> list nfvalx_or_lam -> nfvalx_or_lam.

Fixpoint read_nfvalx xs v :=
  match v with
  | nxvar x => nvar (index xs x)
  | nxapp v1 v2 => napp (read_nfvalx xs v1) (read_nfvalx_or_lam xs v2)
  | nxswitch t m => nswitch (read_nfvalx xs t) (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m)
  end

with read_nfvalx_or_lam xs v :=
  match v with
  | nxval v => nval (read_nfvalx xs v)
  | nxlam x v => nlam (read_nfvalx_or_lam (x :: xs) v)
  | nxconstr tag l => nconstr tag (map (read_nfvalx_or_lam xs) l)
  end.

Inductive valE : deep_flag -> Type :=
| valE_nf : forall {df}, nfvalx -> valE df
| valEs_abs : term -> list clo -> valE shallow
| valEs_constr : nat -> list clo -> valE shallow
| valEd_abs : term -> list clo -> nfvalx_or_lam -> valE deep
| valEd_constr : nat -> list clo -> nfvalx_or_lam -> valE deep.

Definition read_valE {df} (xs : list freevar) (v : valE df) : val df :=
  match v with
  | valE_nf v => val_nf (read_nfvalx xs v)
  | valEs_abs t l =>
    vals_abs (subst (scons (var 0) (read_env (map (fun c => ren_term (plus_ren 1) (read_clo xs c)) l))) t)
  | valEd_abs t l v => vald_nf (read_nfvalx_or_lam xs v)
  | valEs_constr tag l =>
    vals_constr tag (map (read_clo xs) l)
  | valEd_constr tag l v => vald_nf (read_nfvalx_or_lam xs v)
  end.

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

Definition out_map {A B : Type} (f : A -> B) (o : out A) : out B :=
  match o with
  | out_ret x => out_ret (f x)
  | out_div => out_div
  end.

Definition read_extE {df} xs (e : extE df) : ext df :=
  match e with
  | extE_term env t => ext_term (read_clo xs (clo_term xs t env))
  | extE_clo c => ext_term (read_clo xs c)
  | extE_app env o1 t2 => ext_app (out_map (read_valE xs) o1) (read_clo xs (clo_term xs t2 env))
  | extE_appnf env v1 o2 => ext_appnf (read_nfvalx xs v1) (out_map (read_valE xs) o2)
  | extE_switch env o m =>
    ext_switch
      (out_map (read_valE xs) o)
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m)
  | extE_switchnf1 env v m1 m2 =>
    ext_switchnf
      (read_nfvalx xs v)
      (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m1)
      None
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m2)
  | extE_switchnf2 env v m1 xs2 o m2 =>
    ext_switchnf
      (read_nfvalx xs v)
      (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m1)
      (Some (length xs2, out_map (read_valE (xs2 ++ xs)) o))
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m2)
  | extEd_abs env x t o => extd_abs (out_map (read_valE (x :: xs)) o)
  | extEd_constr1 tag l l1 l2 =>
    extd_constr tag
                (map (read_nfvalx_or_lam xs) l1)
                None
                (map (read_clo xs) l2)
  | extEd_constr2 tag l l1 o l2 =>
    extd_constr tag
                (map (read_nfvalx_or_lam xs) l1)
                (Some (out_map (read_valE xs) o))
                (map (read_clo xs) l2)
  end.

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

Definition env_get_maybe_var {A: Type} (env : list A) t :=
  match t with
  | var n => nth_error env n
  | _ => None
  end.

Definition list_inter L1 L2 := filter (fun y => if in_dec freevar_eq_dec y L1 then true else false) L2.
Lemma list_inter_correct :
  forall L1 L2 x, x \in list_inter L1 L2 <-> x \in L1 /\ x \in L2.
Proof.
  intros L1 L2 x. unfold list_inter. rewrite filter_In.
  destruct in_dec; try tauto. assert (~ (false = true)) by discriminate; tauto.
Qed.

Lemma list_inter_subl1 :
  forall L1 L2, list_inter L1 L2 \subseteq L1.
Proof.
  intros L1 L2 x; rewrite list_inter_correct; tauto.
Qed.

Lemma list_inter_subl2 :
  forall L1 L2, list_inter L1 L2 \subseteq L2.
Proof.
  intros L1 L2 x; rewrite list_inter_correct; tauto.
Qed.

Lemma list_inter_subr :
  forall L1 L2 L3, L1 \subseteq list_inter L2 L3 <-> L1 \subseteq L2 /\ L1 \subseteq L3.
Proof.
  intros L1 L2 L3; split.
  - intros H; split; intros x; specialize (H x); rewrite list_inter_correct in H; tauto.
  - intros [H1 H2] x; specialize (H1 x); specialize (H2 x); rewrite list_inter_correct; tauto.
Qed.


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

(*;
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


(*
Inductive clo_sub : clo -> clo -> Prop :=
| clo_sub_var : forall x, clo_sub (clo_var x) (clo_var x)
| clo_sub_term : forall xs1 xs2 t env1 env2, xs1 \subseteq xs2 -> Forall2 clo_sub env1 env2 -> clo_sub (clo_term xs1 t env1) (clo_term xs2 t env2).

Inductive valE_sub : forall df, valE df -> valE df -> Prop :=
| valE_sub_nf : forall df v, valE_sub df (valE_nf v) (valE_nf v)
| valEs_sub_abs : forall t env1 env2, Forall2 clo_sub env1 env2 -> valE_sub shallow (valEs_abs t env1) (valEs_abs t env2)
| valEd_sub_abs : forall t v env1 env2, Forall2 clo_sub env1 env2 -> valE_sub deep (valEd_abs t env1 v) (valEd_abs t env2 v).

Inductive outE_sub : forall df, out (valE df) -> out (valE df) -> Prop :=
| outE_sub_div : forall df, outE_sub df out_div out_div
| outE_sub_ret : forall df v1 v2, valE_sub df v1 v2 -> outE_sub df (out_ret v1) (out_ret v2).

Inductive extE_sub : forall df, extE df -> extE df -> Prop :=
| extE_sub_term : forall df t, extE_sub df (extE_term t) (extE_term t)
| extE_sub_app : forall df o1 o2 t, outE_sub _ o1 o2 -> extE_sub df (extE_app o1 t) (extE_app o2 t)
| extE_sub_appnf : forall df v o1 o2, outE_sub _ o1 o2 -> extE_sub df (extE_appnf v o1) (extE_appnf v o2)
| extEd_sub_abs : forall x t o1 o2, outE_sub _ o1 o2 -> extE_sub deep (extEd_abs x t o1) (extEd_abs x t o2).
 *)

Lemma nth_error_Forall2 :
  forall {A B : Type} {P : A -> B -> Prop} {L1 L2 n x}, Forall2 P L1 L2 -> nth_error L1 n = Some x -> exists y, nth_error L2 n = Some y /\ P x y.
Proof.
  intros A B P. intros L1 L2 n x H; revert n x; induction H; intros n x1 Hx1; destruct n as [|n]; simpl in *; try congruence.
  - injection Hx1; intros; subst. exists y. split; [reflexivity|assumption].
  - apply IHForall2. assumption.
Qed.

Lemma nth_error_Forall2_rev :
  forall {A B : Type} {P : A -> B -> Prop} {L1 L2 n x}, Forall2 P L1 L2 -> nth_error L2 n = Some x -> exists y, nth_error L1 n = Some y /\ P y x.
Proof.
  intros A B P. intros L1 L2 n x H; revert n x; induction H; intros n x1 Hx1; destruct n as [|n]; simpl in *; try congruence.
  - injection Hx1; intros; subst. exists x. split; [reflexivity|assumption].
  - apply IHForall2. assumption.
Qed.

Lemma nth_error_Forall2_None :
  forall {A B : Type} {P : A -> B -> Prop} {L1 L2 n}, Forall2 P L1 L2 -> nth_error L1 n = None <-> nth_error L2 n = None.
Proof.
  intros A B P. intros L1 L2 n H; revert n; induction H; intros n; destruct n as [|n]; simpl in *; try tauto.
  - split; intros; congruence.
  - apply IHForall2.
Qed.

(*
Lemma redE_xs_mono_rec :
  forall df xs dom env e o, redE df xs dom env e o -> forall xs2 env2 e2, xs2 \subseteq xs -> Forall2 clo_sub env2 env -> extE_sub df e2 e -> exists o2, outE_sub df o2 o /\ redE df xs2 dom env2 e2 o2.
Proof.
  intros df xs dom env e o H; induction H; intros xs3 env3 e3 Hxs3 Henv3 He3; inversion He3; unexistT; subst.
  - destruct (nth_error_Forall2_rev Henv3 H) as (u & Hu1 & Hu2).
    inversion Hu2; subst.
    destruct (IHredE xs1 env1 (extE_term t2)) as (o2 & Hsub & HredE); [assumption|assumption|constructor|].
    exists o2. split; [assumption|]. econstructor; try eassumption. etransitivity; eassumption.
  - destruct (nth_error_Forall2_rev Henv3 H) as (u & Hu1 & Hu2).
    inversion Hu2; subst.
    eexists. split; [|eapply redE_var_free; eassumption]. constructor. constructor.
  - eexists; split; [|eapply redE_abs_shallow]. econstructor. econstructor. assumption.
  - destruct (IHredE1 (x :: xs3) (clo_var x :: env3) (extE_term t)) as (o3 & Hsub3 & HredE1);
      [intros y [<- | Hy]; [left; reflexivity|right; apply Hxs3; assumption]|constructor; [constructor|assumption]|constructor|].
    destruct (IHredE2 xs3 env3 (extEd_abs x t o3)) as (o4 & Hsub4 & HredE2); [assumption|assumption|constructor;assumption|].
    exists o4. split; [assumption|]. eapply redE_abs_deep; try eassumption. rewrite Hxs3; assumption.
  - inversion H2; unexistT; subst.
    eexists; split; [|eapply redE_abs1]. constructor.
    inversion H3; unexistT; subst; constructor; assumption.
  - destruct (IHredE1 xs3 env3 (extE_term t1)) as (o3 & Hsub3 & HredE1); [assumption|assumption|constructor|].
    destruct (IHredE2 xs3 env3 (extE_app o3 t2)) as (o4 & Hsub4 & HredE2); [assumption|assumption|constructor; assumption|].
    eexists; split; [|eapply redE_app; eassumption]. assumption.
  - destruct (IHredE1 xs3 env3 (extE_term t2)) as (o3 & Hsub3 & HredE1); [assumption|assumption|constructor|].
    destruct (IHredE2 xs3 env3 (extE_appnf v o3)) as (o4 & Hsub4 & HredE2); [assumption|assumption|constructor; assumption|].
    eexists; split; [eassumption|].
    inversion H4; unexistT; subst. inversion H5; unexistT; subst. eapply redE_app1_nf; eassumption.
  - inversion H5; unexistT; subst. inversion H6; unexistT; subst.
    match goal with [_ : context[?a :: env2] |- _ ] => remember a as c end.
    destruct (IHredE xs3 (match env_get_maybe_var env3 t2 with | Some c => c | None => clo_term xs t2 env3 end :: env1) (extE_term t1)) as (o3 & Hsub3 & HredE1).
    + assumption.
    + constructor; [|assumption]. rewrite Heqc. destruct t2; try (constructor; assumption).
      simpl.
      destruct (nth_error env n) as [c1|] eqn:Hc1.
      * destruct (nth_error_Forall2_rev Henv3 Hc1) as (c2 & Hc2a & Hc2b); rewrite Hc2a. assumption.
      * eapply nth_error_Forall2_None in Hc1; [|eassumption]. rewrite Hc1. constructor; assumption.
    + constructor.
    + exists o3. split; [assumption|]. econstructor; try eassumption. etransitivity; eassumption.
  - inversion H2; unexistT; subst. eexists; split; [|eapply redE_appnf]. constructor.
    inversion H3; unexistT; subst; simpl in *; constructor.
  - eexists; split; [constructor|].
Qed.
 *)

(*
Lemma clo_sub_refl :
  forall c, clo_sub c c.
Proof.
  induction c using clo_ind2.
  - constructor.
  - constructor; [reflexivity|]. apply Forall2_map_same. assumption.
Qed.

Lemma valE_sub_refl :
  forall df (v : valE df), valE_sub df v v.
Proof.
  intros df v; destruct v; constructor; apply Forall2_map_same, Forall_True, clo_sub_refl.
Qed.

Lemma outE_sub_refl :
  forall df (o : out (valE df)), outE_sub df o o.
Proof.
  intros df o; destruct o; constructor; apply valE_sub_refl.
Qed.

Lemma extE_sub_refl :
  forall df (e : extE df), extE_sub df e e.
Proof.
  intros df e; destruct e; constructor; apply outE_sub_refl.
Qed.
*)

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


Lemma env_get_maybe_var_in :
  forall (A : Type) t (env : list A) x, env_get_maybe_var env t = Some x -> x \in env.
Proof.
  intros A t env x H. destruct t; simpl in *; try congruence.
  eapply nth_error_In. eassumption.
Qed.

Lemma get_out_abort_div :
  forall t1 t2 (o1 : out t1) (o2 : out t2), get_out_abort o1 = Some o2 -> o2 = out_div.
Proof.
  intros; destruct o1; simpl in *; congruence.
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
  Ltac use_rec H1 H2 :=
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

Lemma read_valE_deep :
  forall (v : valE deep) xs, read_valE xs v = vald_nf (read_nfvalx_or_lam xs (getvalEd_nf v)).
Proof.
  intros v xs.
  destruct (destruct_valE_deep v) as [[(v2 & ->) | (t & env & v2 & ->)] | (tag & l & v2 & ->)]; reflexivity.
Qed.

Lemma index_app :
  forall L1 L2 x, x \in L1 -> index (L1 ++ L2) x = index L1 x.
Proof.
  intros L1 L2 x H. induction L1; simpl in *.
  - tauto.
  - destruct freevar_eq_dec; [reflexivity|]. f_equal. apply IHL1. destruct H; [congruence|tauto].
Qed.

Lemma index_app2 :
  forall L1 L2 x, x \notin L1 -> index (L1 ++ L2) x = length L1 + index L2 x.
Proof.
  intros L1 L2 x H. induction L1; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; subst; [simpl in *; tauto|]. f_equal.
    apply IHL1. tauto.
Qed.


Lemma nth_error_index :
  forall L p xs n x, distinct L p xs -> nth_error xs n = Some x -> index xs x = n.
Proof.
  intros L p xs n x H; revert n x; induction H; intros [|k] y Hy; simpl in *.
  - congruence.
  - congruence.
  - destruct freevar_eq_dec; [reflexivity|]. congruence.
  - destruct freevar_eq_dec; [|f_equal; apply IHdistinct; assumption].
    subst. exfalso. eapply distinct_distinct; [eassumption|left; reflexivity|eapply nth_error_In; eassumption].
Qed.

Lemma read_shiftn_clo :
  forall c ys p xs, distinct (clo_fv c) p ys -> clo_closed c -> read_clo (ys ++ xs) c = ren_term (plus_ren p) (read_clo xs c).
Proof.
  induction c using clo_ind2; intros ys p zs Hdistinct Hcc; inversion Hcc; subst; simpl in *.
  - f_equal. erewrite index_app2, plus_ren_correct, distinct_length; [reflexivity|eassumption|].
    intros H. eapply distinct_distinct; try eassumption. simpl. tauto.
  - rewrite ren_subst. eapply subst_closed_at_ext; [eassumption|].
    intros n Hn. unfold comp, read_env.
    rewrite !nth_error_map.
    destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
    assert (u \in l) by (eapply nth_error_In; eassumption).
    rewrite Forall_forall in H. apply H; [eassumption| |apply H4; assumption].
    eapply distinct_incl; [|eassumption].
    intros y Hy. rewrite concat_map_In. exists u. tauto.
Qed.

Lemma redE_red :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> fvs \subseteq xs /\ extE_closed_at e fvs -> forall fvs2, fvs \subseteq fvs2 -> red df (read_extE fvs2 e) (out_map (read_valE fvs2) o).
Proof.
  refine (preserved_with_inv6_rec _ _ redE_is_ind6 _ _ closed_preserved_down _).
  intros df xs dom fvs e o H [Hfvs He] fvs2 Hfvs2. inversion H; unexistT; subst; unexistT; subst; simpl in *.
  - apply H7.
    rewrite <- Hfvs2. apply list_inter_subl2.
  - constructor. constructor.
  - unfold read_env. rewrite nth_error_map, H6.
    apply H7. assumption.
  - inversion He; subst. inversion H6; subst.
    erewrite subst_closed_at_ext; [constructor; constructor|eassumption|].
    intros [|n] Hn; [reflexivity|]. simpl; unfold read_env, comp; simpl.
    rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu.
    + reflexivity.
    + apply nth_error_None in Hu. lia.
  - inversion He; subst. inversion H7; subst.
    constructor; econstructor; [|apply H11; assumption].
    erewrite subst_closed_at_ext.
    + eapply H10. rewrite Hfvs2; reflexivity.
    + eassumption.
    + intros [|n] Hn; simpl; unfold comp, read_env; simpl; [destruct freevar_eq_dec; congruence|].
      rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
      apply nth_error_In, H5 in Hu. destruct Hu as [Hu1 Hu2].
      rewrite read_shift_clo; [reflexivity| |apply Hu1].
      rewrite Hu2, Hfvs. assumption.
  - rewrite read_valE_deep. constructor; constructor.
  - constructor; econstructor; [eapply H6|eapply H7]; assumption.
  - constructor; econstructor; [eapply H6|eapply H7]; assumption.
  - inversion He; subst. inversion H10; subst.
    constructor; econstructor.
    unfold subst1. rewrite subst_subst.
    erewrite subst_closed_at_ext; [eapply H8| |].
    + assumption.
    + eassumption.
    + unfold comp, read_env.
      intros [|n] Hn; simpl.
      * destruct t2; try reflexivity. simpl.
        rewrite nth_error_map. destruct nth_error eqn:Hu; [|apply nth_error_None in Hu; inversion H9; subst; lia].
        reflexivity.
      * rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
        rewrite subst_ren; unfold comp; simpl.
        erewrite subst_ext; [apply subst_id|]; intros; f_equal; lia.
  - rewrite read_valE_deep. constructor; constructor.
  - replace (map (read_clo fvs2) lc) with (map (subst (read_env (map (read_clo fvs2) env))) l); [constructor; constructor|].
    eapply Forall2_map_eq, Forall2_impl; [|eassumption]. intros t c Htc; simpl in *.
    destruct env_get_maybe_var as [c1|] eqn:Hc1.
    + subst. destruct t; simpl in *; try congruence.
      unfold read_env. rewrite nth_error_map, Hc1. reflexivity.
    + destruct Htc as (xs2 & Hxs2a & Hxs2b & ->). reflexivity.
  - constructor. constructor.
    replace (map (subst (read_env (map (read_clo fvs2) env))) l) with (map (read_clo fvs2) lc).
    + eapply H9. assumption.
    + symmetry. eapply Forall2_map_eq, Forall2_impl; [|eassumption]. intros t c Htc; simpl in *.
      destruct env_get_maybe_var as [c1|] eqn:Hc1.
      * subst. destruct t; simpl in *; try congruence.
        unfold read_env. rewrite nth_error_map, Hc1. reflexivity.
      * destruct Htc as (xs2 & Hxs2a & Hxs2b & ->). reflexivity.
  - constructor. constructor.
  - constructor; econstructor; [apply H7; assumption|apply H9; assumption].
  - rewrite read_valE_deep. constructor. econstructor.
    rewrite <- map_app with (f := read_nfvalx_or_lam fvs2) (l' := getvalEd_nf v :: nil).
    apply H5. assumption.
  - constructor. econstructor.
    + apply H6. assumption.
    + apply H7. assumption.
  - inversion He; subst.
    constructor; econstructor; [rewrite nth_error_map, H6, map_length; simpl; reflexivity|].
    rewrite subst_subst.
    erewrite subst_closed_at_ext; [apply H7; assumption|eapply H8, nth_error_In; eassumption|].
    intros n Hn. unfold comp, liftn_subst, read_env.
    destruct le_lt_dec.
    + rewrite !nth_error_map, nth_error_app2 by assumption.
      destruct (nth_error env _) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      rewrite subst_ren. erewrite subst_ext; [apply subst_id|]. intros n2. simpl.
      unfold comp; simpl. rewrite nth_error_map, plus_ren_correct, map_length.
      replace (nth_error l (length l + n2)) with (@None clo) by (symmetry; apply nth_error_None; lia).
      f_equal. lia.
    + simpl. rewrite !nth_error_map, nth_error_app1 by assumption.
      destruct (nth_error l _) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia]. reflexivity.
  - constructor. constructor. apply H6. assumption.
  - constructor. constructor.
  - inversion He; subst.
    constructor. econstructor.
    + erewrite subst_closed_at_ext; [apply H8; rewrite Hfvs2; reflexivity|apply H13; left; reflexivity|].
      intros n Hn. unfold liftn_subst, read_env.
      destruct le_lt_dec.
      * rewrite !nth_error_map, nth_error_app2 by (erewrite map_length, distinct_length; eassumption).
        erewrite !map_length, app_length, map_length, distinct_length by eassumption.
        destruct nth_error eqn:Hu.
        -- erewrite read_shiftn_clo; [reflexivity| |eapply H7, nth_error_In; eassumption].
           eapply distinct_incl; [|eassumption].
           rewrite <- Hfvs. eapply H7, nth_error_In; eassumption.
        -- apply nth_error_None in Hu. lia.
      * rewrite nth_error_map, nth_error_app1, nth_error_map by (erewrite map_length, distinct_length; eassumption).
        destruct nth_error as [y|] eqn:Hy.
        -- simpl. f_equal. rewrite index_app; [|eapply nth_error_In; eassumption].
           symmetry; eapply nth_error_index; eassumption.
        -- apply nth_error_None in Hy. erewrite distinct_length in Hy by eassumption. lia.
    + replace p with (length ys) by (eapply distinct_length; eassumption).
      apply H9. assumption.
  - rewrite read_valE_deep. constructor. econstructor.
    rewrite <- map_app with (f := fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ fvs2) (snd pt2))) (l' := (ys, getvalEd_nf v2) :: nil).
    apply H6. assumption.
  - constructor. constructor.
    destruct e; simpl in *; try congruence; try (destruct o0; simpl in *; autoinjSome; simpl; congruence).
Qed.

Print extE.

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
  - injection Hv as Hv; subst. constructor; constructor.
  - constructor; econstructor; [eassumption|]. apply Hrec. reflexivity.
  - constructor; econstructor; [apply Hred0 | apply Hrec]. reflexivity.
  - constructor; econstructor; [apply H6 | apply Hrec]. reflexivity.
  - constructor; econstructor; [eassumption|eassumption|].
    apply Hrec. reflexivity.
  - injection Hv as Hv; subst. constructor; econstructor.
  - constructor; econstructor; [apply Hred0 | apply Hrec]. reflexivity.
  - constructor; econstructor; [eassumption|]. apply Hrec. reflexivity.
  - constructor; econstructor. apply Hrec. reflexivity.
  - injection Hv as Hv; subst. constructor; econstructor.
  - constructor; econstructor; try eassumption; [apply H8 | apply Hrec]. reflexivity.
  - constructor; econstructor. apply Hrec. reflexivity.
  - constructor; constructor.
    apply out_abort_div in H6. congruence.
Qed.

Lemma redE_shallow_deep_val :
  forall xs dom fvs e v, redE shallow xs dom fvs e (out_ret (valE_nf v)) ->
         redE deep xs dom fvs (extE_shallow_to_deep e) (out_ret (valE_nf v)).
Proof.
  intros xs dom fvs e v H.
  exact (redE_shallow_deep_val_aux shallow xs dom fvs e _ H eq_refl v eq_refl).
Qed.

(*
Inductive clo_xs_in (xs : list freevar) : clo -> Prop :=
| clo_xs_in_var : forall x, clo_xs_in xs (clo_var x)
| clo_xs_in_term : forall xs2 t env, xs2 \subseteq xs -> (forall c, c \in env -> clo_xs_in xs c) -> clo_xs_in xs (clo_term xs2 t env).
 *)

Lemma redE_shallow_deep_abs_aux :
  forall df xs dom env e o,
    redE df xs dom env e o -> forall (p : df = shallow) t env2, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEs_abs t env2) ->
    forall o2 dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 env2 (extE_term (abs t)) o2 -> redE deep xs dom2 env (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) o2.
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nt nenv Ho; try discriminate Ho; simpl.
  - subst. intros o2 dom2 Hxs Hdom2 Ho2.
    econstructor; [eassumption|etransitivity; eassumption|].
    eapply IHredE with (p := eq_refl); [reflexivity|assumption|assumption|assumption].
  - injection Ho as Ho; subst.
    intros o2 dom2 Hxs Hdom2 Ho2. eapply redE_xs_mono; eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3. specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    econstructor; [| |eapply IHredE with (p := eq_refl)]; try eassumption. etransitivity; eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    econstructor; [eassumption|].
    eapply (IHredE eq_refl); eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    econstructor. eapply (IHredE eq_refl); eassumption.
  - intros o3 dom2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [eassumption|etransitivity; eassumption|eapply redE_dom_mono; eassumption|eassumption].
  - intros o3 dom2 Hxs Hdom2 Ho3.
    econstructor. eapply (IHredE eq_refl); eassumption.
  - subst. apply out_abort_div in H. congruence.
Qed.

Lemma redE_shallow_deep_abs :
  forall xs dom env env2 e t,
    redE shallow xs dom env e (out_ret (valEs_abs t env2)) ->
    forall o dom2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 env2 (extE_term (abs t)) o -> redE deep xs dom2 env (extE_shallow_to_deep e) o.
Proof.
  intros xs dom env env2 e t H.
  exact (redE_shallow_deep_abs_aux shallow xs dom env e _ H eq_refl t env2 eq_refl).
Qed.

Lemma redE_deep_constr_aux :
  forall df xs dom env e o, redE df xs dom env e o -> forall (p : df = deep) tag l l1 o2 l2 v,
      match p in _ = df return extE df with eq_refl => e end = extEd_constr tag l l1 o2 l2 ->
      o = out_ret v -> exists v2, match p in _ = df return valE df with eq_refl => v end = valEd_constr tag l v2.
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros tag2 l3 l4 o3 l5 v3 He Ho; try discriminate He; try discriminate Ho.
  - injection He; intros; subst. injection Ho; intros; subst.
    eexists. reflexivity.
  - injection He; intros; subst.
    eapply (IHredE eq_refl); reflexivity.
  - injection He; intros; subst.
    eapply (IHredE2 eq_refl); reflexivity.
  - injection He; intros; subst.
    eapply (IHredE eq_refl); reflexivity.
  - subst. apply out_abort_div in H. congruence.
Qed.

Lemma redE_deep_constr :
  forall xs dom env tag l l1 o2 l2 v, redE deep xs dom env (extEd_constr tag l l1 o2 l2) (out_ret v) ->
                                 exists v2, v = valEd_constr tag l v2.
Proof.
  intros xs dom env tag l l1 o2 l2 v H.
  exact (redE_deep_constr_aux deep xs dom env _ _ H eq_refl _ _ _ _ _ _ eq_refl eq_refl).
Qed.

Lemma redE_deep_constr_noenv_aux :
    forall df xs dom env e o, redE df xs dom env e o -> forall (p : df = deep) tag l l1 o2 l2,
        match p in _ = df return extE df with eq_refl => e end = extEd_constr tag l l1 o2 l2 ->
        forall env2, redE df xs dom env2 e o.
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros tag2 l3 l4 o3 l5 He env3; try discriminate He; try discriminate Ho.
  - injection He; intros; subst.
    constructor.
  - injection He; intros; subst.
    constructor. eapply (IHredE eq_refl); reflexivity.
  - injection He; intros; subst.
    econstructor; try eassumption. eapply (IHredE2 eq_refl); reflexivity.
  - injection He; intros; subst.
    constructor. eapply (IHredE eq_refl); reflexivity.
  - subst. constructor. assumption.
Qed.

Lemma redE_deep_constr_noenv :
  forall xs dom env env2 tag l l1 o2 l2 o,
    redE deep xs dom env (extEd_constr tag l l1 o2 l2) o -> redE deep xs dom env2 (extEd_constr tag l l1 o2 l2) o.
Proof.
  intros xs dom env env2 tag l l1 o2 l2 o H.
  exact (redE_deep_constr_noenv_aux deep xs dom env _ o H eq_refl _ _ _ _ _ eq_refl env2).
Qed.

Lemma redE_shallow_deep_constr_aux :
  forall df xs dom env e o,
    redE df xs dom env e o -> forall (p : df = shallow) tag l, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEs_constr tag l) ->
    forall o2 dom2 env2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 env2 (extEd_constr tag l nil None l) o2 -> redE deep xs dom2 env (extE_shallow_to_deep (match p in _ = df return extE df with eq_refl => e end)) o2.
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nt nenv Ho; try discriminate Ho; simpl.
  - subst. intros o2 dom2 env3 Hxs Hdom2 Ho2.
    econstructor; [eassumption|etransitivity; eassumption|].
    eapply IHredE with (p := eq_refl); [reflexivity|assumption|assumption|eassumption].
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 env2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 env2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 env3 Hxs Hdom2 Ho3.
    econstructor; [| |eapply IHredE with (p := eq_refl)]; try eassumption. etransitivity; eassumption.
  - injection Ho as Ho; subst.
    intros o2 dom2 env2 Hxs Hdom2 Ho2.
    econstructor; [eapply Forall2_impl; [|eassumption]; simpl|].
    + intros t c Htc. destruct env_get_maybe_var; [assumption|].
      destruct Htc as (xs2 & Hxs2a & Hxs2b & Hc); exists xs2; splits 3; try assumption.
      etransitivity; eassumption.
    + eapply redE_xs_mono; [|eassumption].
      eapply redE_deep_constr_noenv; eassumption.
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 env2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [|eassumption]. eapply redE_dom_mono; eassumption.
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    econstructor; [eassumption|].
    eapply (IHredE eq_refl); eassumption.
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    econstructor. eapply (IHredE eq_refl); eassumption.
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    specialize (IHredE2 eq_refl nt nenv Ho o3 dom2 env2 Hxs Hdom2 Ho3). simpl in IHredE2.
    econstructor; [eassumption|etransitivity; eassumption|eapply redE_dom_mono; eassumption|eassumption].
  - intros o3 dom2 env2 Hxs Hdom2 Ho3.
    econstructor. eapply (IHredE eq_refl); eassumption.
  - subst. apply out_abort_div in H. congruence.
Qed.

Lemma redE_shallow_deep_constr :
  forall xs dom env e tag l,
    redE shallow xs dom env e (out_ret (valEs_constr tag l)) ->
    forall o dom2 env2, xs \subseteq dom -> dom \subseteq dom2 -> redE deep dom dom2 env2 (extEd_constr tag l nil None l) o -> redE deep xs dom2 env (extE_shallow_to_deep e) o.
Proof.
  intros xs dom env e tag l H.
  exact (redE_shallow_deep_constr_aux shallow xs dom env e _ H eq_refl tag l eq_refl).
Qed.


Lemma redE_deep_shallow_abs_aux :
  forall df xs dom env e o,
    redE df xs dom env e o -> forall (p : df = deep) t env2 v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEd_abs t env2 v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom env e2 (out_ret (valEs_abs t env2)).
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros ntag nl nv Ho e2 He2; try discriminate Ho; subst; simpl in *; try discriminate; autoinjSome.
  - econstructor; [eassumption|eassumption|]. eapply (IHredE eq_refl); reflexivity.
  - inversion H2; subst.
    + constructor.
    + unexistT; subst. apply out_abort_div in H9. congruence.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - apply redE_deep_constr in H0. destruct H0 as (v2 & H0); congruence.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - econstructor. eapply (IHredE eq_refl); reflexivity.
  - econstructor; try eassumption.
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor. eapply (IHredE eq_refl); reflexivity.
  - apply out_abort_div in H. congruence.
Qed.

Lemma redE_deep_shallow_abs :
  forall xs dom env env2 e t v,
    redE deep xs dom env e (out_ret (valEd_abs t env2 v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom env e2 (out_ret (valEs_abs t env2)).
Proof.
  intros xs dom env env2 e t v H e2 He2.
  exact (redE_deep_shallow_abs_aux deep xs dom env e _ H eq_refl t env2 v eq_refl e2 He2).
Qed.


Lemma redE_deep_shallow_constr_aux :
  forall df xs dom env e o,
    redE df xs dom env e o -> forall (p : df = deep) tag l v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valEd_constr tag l v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom env e2 (out_ret (valEs_constr tag l)).
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros ntag nl nv Ho e2 He2; try discriminate Ho; subst; simpl in *; try discriminate; autoinjSome.
  - econstructor; [eassumption|eassumption|]. eapply (IHredE eq_refl); reflexivity.
  - inversion H2; subst.
    unexistT; subst. apply out_abort_div in H9. congruence.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - apply redE_deep_constr in H0.
    destruct H0 as (v2 & H0); injection H0 as H0; subst.
    econstructor; eassumption.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - econstructor. eapply (IHredE eq_refl); reflexivity.
  - econstructor; try eassumption.
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor. eapply (IHredE eq_refl); reflexivity.
  - apply out_abort_div in H. congruence.
Qed.

Lemma redE_deep_shallow_constr :
  forall xs dom env e tag l v,
    redE deep xs dom env e (out_ret (valEd_constr tag l v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom env e2 (out_ret (valEs_constr tag l)).
Proof.
  intros xs dom env e tag l v H e2 He2.
  exact (redE_deep_shallow_constr_aux deep xs dom env e _ H eq_refl tag l v eq_refl e2 He2).
Qed.


Lemma redE_deep_shallow_val_aux :
  forall df xs dom env e o,
    redE df xs dom env e o -> forall (p : df = deep) v, (match p in _ = df return out (valE df) with eq_refl => o end) = out_ret (valE_nf v) ->
    forall e2, extE_deep_to_shallow (match p in _ = df return extE df with eq_refl => e end) = Some e2 -> redE shallow xs dom env e2 (out_ret (valE_nf v)).
Proof.
  intros df xs dom env e o H.
  induction H; try destruct df; intros Hdf; try discriminate Hdf; rewrite (UIP_dec deep_flag_eq_dec Hdf eq_refl);
    intros nv Ho e2 He2; try discriminate Ho; subst; simpl in *; try discriminate; autoinjSome.
  - econstructor; [eassumption|eassumption|]. eapply (IHredE eq_refl); reflexivity.
  - inversion Ho; intros; subst. constructor. assumption.
  - inversion H2; unexistT; subst.
    apply out_abort_div in H9. congruence.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - injection Ho; intros; subst. constructor.
  - apply redE_deep_constr in H0. destruct H0 as (v2 & H0); congruence.
  - econstructor; [eassumption|].
    eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; [eassumption|].
    eapply (IHredE eq_refl); reflexivity.
  - econstructor. eapply (IHredE eq_refl); reflexivity.
  - injection Ho; intros; subst. constructor.
  - econstructor; try eassumption. eapply (IHredE2 eq_refl); reflexivity.
  - econstructor; try eassumption. eapply (IHredE eq_refl); reflexivity.
  - apply out_abort_div in H. congruence.
Qed.

Lemma redE_deep_shallow_val :
  forall xs dom env e v,
    redE deep xs dom env e (out_ret (valE_nf v)) ->
    forall e2, extE_deep_to_shallow e = Some e2 -> redE shallow xs dom env e2 (out_ret (valE_nf v)).
Proof.
  intros xs dom env e v H e2 He2.
  exact (redE_deep_shallow_val_aux deep xs dom env e _ H eq_refl v eq_refl e2 He2).
Qed.







Inductive eiM :=
| eiM_lazy : term -> list freevar -> eiM
| eiM_abs1 : term -> list freevar -> eiM
| eiM_abs2 : term -> list freevar -> nfvalx_or_lam -> eiM
| eiM_constr1 : nat -> list freevar -> eiM
| eiM_constr2 : nat -> list freevar -> nfvalx_or_lam -> eiM
| eiM_val : nfvalx -> eiM.
Definition memM := list (freevar * eiM).

Definition memdom (m : memM) := map fst m.

Inductive read_eiM (res : freevar -> option clo) dom : eiM -> clo -> Prop :=
| read_eiM_lazy : forall t ys vs xs,
    map Some vs = map res ys ->
    read_eiM res dom (eiM_lazy t ys) (clo_term xs t vs)
| read_eiM_abs1 : forall t ys u ws vs xs,
    map Some vs = map res ys ->
    redE shallow xs dom ws (extE_term u) (out_ret (valEs_abs t vs)) ->
    read_eiM res dom (eiM_abs1 t ys) (clo_term xs u ws)
| read_eiM_abs2 : forall t ys u ws v vs xs,
    map Some vs = map res ys ->
    redE deep xs dom ws (extE_term u) (out_ret (valEd_abs t vs v)) ->
    read_eiM res dom (eiM_abs2 t ys v) (clo_term xs u ws)
| read_eiM_constr1 : forall tag ys u ws vs xs,
    map Some vs = map res ys ->
    redE shallow xs dom ws (extE_term u) (out_ret (valEs_constr tag vs)) ->
    read_eiM res dom (eiM_constr1 tag ys) (clo_term xs u ws)
| read_eiM_constr2 : forall tag ys u ws v vs xs,
    map Some vs = map res ys ->
    redE deep xs dom ws (extE_term u) (out_ret (valEd_constr tag vs v)) ->
    read_eiM res dom (eiM_constr2 tag ys v) (clo_term xs u ws)
| read_eiM_val : forall u ws v xs,
    redE shallow xs dom ws (extE_term u) (out_ret (valE_nf v)) ->
    read_eiM res dom (eiM_val v) (clo_term xs u ws)
| read_eiM_var : forall y,
    read_eiM res dom (eiM_val (nxvar y)) (clo_var y).

Lemma read_eiM_dom_mono :
  forall res dom u c, read_eiM res dom u c -> forall dom2, dom \subseteq dom2 -> read_eiM res dom2 u c.
Proof.
  intros res dom u c H; inversion H; subst; intros dom2 Hdom2; econstructor; try eassumption;
    eapply redE_dom_mono; eassumption.
Qed.

Notation memxM := (memM * list freevar)%type.

Definition read_memM (m : memxM) (res : freevar -> option clo) :=
  (forall x u, env_find (fst m) x = Some u -> exists v, res x = Some v /\ read_eiM res (snd m) u v) /\
  (forall x, env_find (fst m) x = None -> res x = None).

Lemma read_memM_Some :
  forall m res x u v, read_memM m res -> env_find (fst m) x = Some u -> res x = Some v -> read_eiM res (snd m) u v.
Proof.
  intros m res x u v Hread Hm Hres. apply Hread in Hm.
  destruct Hm as (v2 & Hx2 & Hv2). congruence.
Qed.

Inductive valM : deep_flag -> Type :=
| valM_nf : forall {df}, nfvalx -> valM df
| valMs_abs : term -> list freevar -> valM shallow
| valMd_abs : term -> list freevar -> nfvalx_or_lam -> valM deep
| valMs_constr : nat -> list freevar -> valM shallow
| valMd_constr : nat -> list freevar -> nfvalx_or_lam -> valM deep.

Inductive read_valM : forall {df}, (freevar -> option clo) -> valM df -> valE df -> Prop :=
| read_valM_nf : forall df res v, @read_valM df res (valM_nf v) (valE_nf v)
| read_valMs_abs : forall res t ys vs,
    map Some vs = map res ys ->
    @read_valM shallow res (valMs_abs t ys) (valEs_abs t vs)
| read_valMd_abs : forall res t ys v vs,
    map Some vs = map res ys ->
    @read_valM deep res (valMd_abs t ys v) (valEd_abs t vs v)
| read_valMs_constr : forall res tag ys vs,
    map Some vs = map res ys ->
    @read_valM shallow res (valMs_constr tag ys) (valEs_constr tag vs)
| read_valMd_constr : forall res tag ys v vs,
    map Some vs = map res ys ->
    @read_valM deep res (valMd_constr tag ys v) (valEd_constr tag vs v).


Inductive outM t m :=
| outM_ret : t -> m -> outM t m
| outM_div : outM t m.

Arguments outM_ret {t} {m} _ _.
Arguments outM_div {t} {m}.

Print extE.
Inductive extM : deep_flag -> Type :=
| extM_term : forall df, term -> extM df
| extM_app : forall df, outM (valM shallow) memxM -> term -> extM df
| extM_appnf : forall df, nfvalx -> outM (valM deep) memxM -> extM df
| extM_switch : forall df, outM (valM shallow) memxM -> list (nat * term) -> extM df
| extM_switchnf1 : forall df, nfvalx -> list (list freevar * nfvalx_or_lam) -> list (nat * term) -> extM df
| extM_switchnf2 : forall df, nfvalx -> list (list freevar * nfvalx_or_lam) -> list freevar -> outM (valM deep) memxM -> list (nat * term) -> extM df
| extMd_abs : freevar -> term -> outM (valM deep) memxM -> extM deep
| extMd_constr1 : nat -> list freevar -> list nfvalx_or_lam -> list freevar -> extM deep
| extMd_constr2 : nat -> list freevar -> list nfvalx_or_lam -> outM (valM deep) memxM -> list freevar -> extM deep.


Arguments extM_term {df} _.
Arguments extM_app {df} _ _.
Arguments extM_appnf {df} _ _.
Arguments extM_switch {df} _ _.
Arguments extM_switchnf1 {df} _ _ _.
Arguments extM_switchnf2 {df} _ _ _ _ _.

(*
Definition compat_memM (m1 m2 : memM) (res : freevar -> clo) :=
  forall x c xs, read_eiM m1 x c xs -> read_eiM m2 x c xs.
 *)

Definition get_out_memxM {df} (m : memxM) (o : outM (valM df) memxM) :=
  match o with
  | outM_div => m
  | outM_ret _ m => m
  end.

Definition get_ext_memxM {df} (m : memxM) (e : extM df) :=
  match e with
  | extM_term _ => m
  | extM_app o _ => get_out_memxM m o
  | extM_appnf _ o => get_out_memxM m o
  | extM_switch o _ => get_out_memxM m o
  | extM_switchnf1 _ _ _ => m
  | extM_switchnf2 _ _ _ o _ => get_out_memxM m o
  | extMd_abs _ _ o => get_out_memxM m o
  | extMd_constr1 _ _ _ _ => m
  | extMd_constr2 _ _ _ o _ => get_out_memxM m o
  end.

Inductive read_outM : forall df, (freevar -> option clo) -> outM (valM df) memxM -> out (valE df) -> Prop :=
| read_outM_div : forall df res, read_outM df res outM_div out_div
| read_outM_ret : forall df res m v1 v2,
    read_memM m res -> read_valM res v1 v2 -> read_outM df res (outM_ret v1 m) (out_ret v2).

Inductive read_extM : forall df, (freevar -> option clo) -> extM df -> extE df -> Prop :=
| read_extM_term : forall df res t, read_extM df res (extM_term t) (extE_term t)
| read_extM_app : forall df res o1 o2 t,
    read_outM shallow res o1 o2 -> read_extM df res (extM_app o1 t) (extE_app o2 t)
| read_extM_appnf : forall df res v o1 o2,
    read_outM deep res o1 o2 -> read_extM df res (extM_appnf v o1) (extE_appnf v o2)
| read_extM_switch : forall df res o1 o2 m,
    read_outM shallow res o1 o2 -> read_extM df res (extM_switch o1 m) (extE_switch o2 m)
| read_extM_switchnf1 : forall df res v m1 m2,
    read_extM df res (extM_switchnf1 v m1 m2) (extE_switchnf v m1 None m2)
| read_extM_switchnf2 : forall df res v m1 xs o1 o2 m2,
    read_outM deep res o1 o2 -> read_extM df res (extM_switchnf2 v m1 xs o1 m2) (extE_switchnf v m1 (Some (xs, o2)) m2)
| read_extMd_abs : forall res x t o1 o2,
    read_outM deep res o1 o2 -> read_extM deep res (extMd_abs x t o1) (extEd_abs x t o2)
| read_extMd_constr1 : forall res tag xs vs l ys ws,
    map Some vs = map res xs -> map Some ws = map res ys ->
    read_extM deep res (extMd_constr1 tag xs l ys) (extEd_constr tag vs l None ws)
| read_extMd_constr2 : forall res tag xs vs l o1 o2 ys ws,
    read_outM deep res o1 o2 -> map Some vs = map res xs -> map Some ws = map res ys ->
    read_extM deep res (extMd_constr2 tag xs l o1 ys) (extEd_constr tag vs l (Some o2) ws).

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
  | extM_term _ => None
  | extM_app o _ => get_outM_abort o
  | extM_appnf _ o => get_outM_abort o
  | extM_switch o _ => get_outM_abort o
  | extM_switchnf1 _ _ _ => None
  | extM_switchnf2 _ _ _ o _ => get_outM_abort o
  | extMd_abs _ _ o => get_outM_abort o
  | extMd_constr1 _ _ _ _ => None
  | extMd_constr2 _ _ _ o _ => get_outM_abort o
  end.


Inductive redM : forall df, list freevar -> extM df -> memxM -> outM (valM df) memxM -> Prop :=
| redM_var_val : forall df n env m x v,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_val v) ->
    redM df env (extM_term (var n)) m (outM_ret (valM_nf v) m)
| redM_var_abs1_shallow : forall n env m x t env2,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_abs1 t env2) ->
    redM shallow env (extM_term (var n)) m (outM_ret (valMs_abs t env2) m)
| redM_var_abs1_deep : forall n env m x t env2 o1 o2,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_abs1 t env2) ->
    redM deep env2 (extM_term (abs t)) m o1 ->
    update_result deep x o1 o2 ->
    redM deep env (extM_term (var n)) m o2
| redM_var_abs2_shallow : forall n env m x t env2 body,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_abs2 t env2 body) ->
    redM shallow env (extM_term (var n)) m (outM_ret (valMs_abs t env2) m)
| redM_var_abs2_deep : forall n env m x t env2 body,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_abs2 t env2 body) ->
    redM deep env (extM_term (var n)) m (outM_ret (valMd_abs t env2 body) m)
| redM_var_constr1_shallow : forall n env m x tag l,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_constr1 tag l) ->
    redM shallow env (extM_term (var n)) m (outM_ret (valMs_constr tag l) m)
| redM_var_constr1_deep : forall n env m x tag l o1 o2,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_constr1 tag l) ->
    redM deep nil (extMd_constr1 tag l nil l) m o1 ->
    update_result deep x o1 o2 ->
    redM deep env (extM_term (var n)) m o2
| redM_var_constr2_shallow : forall n env m x tag l v,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_constr2 tag l v) ->
    redM shallow env (extM_term (var n)) m (outM_ret (valMs_constr tag l) m)
| redM_var_constr2_deep : forall n env m x tag l v,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_constr2 tag l v) ->
    redM deep env (extM_term (var n)) m (outM_ret (valMd_constr tag l v) m)
| redM_var_lazy : forall df n env m x t env2 o1 o2,
    nth_error env n = Some x ->
    env_find (fst m) x = Some (eiM_lazy t env2) ->
    redM df env2 (extM_term t) m o1 ->
    update_result df x o1 o2 ->
    redM df env (extM_term (var n)) m o2
| redM_abs_shallow : forall t env m,
    redM shallow env (extM_term (abs t)) m (outM_ret (valMs_abs t env) m)
| redM_abs_deep : forall t env m1 m2 o1 o2 x a,
    env_find (fst m1) a = None -> m2 = ((a, eiM_val (nxvar x)) :: fst m1, x :: snd m1) -> x \notin (snd m1) ->
    redM deep (a :: env) (extM_term t) m2 o1 ->
    redM deep env (extMd_abs x t o1) m2 o2 ->
    redM deep env (extM_term (abs t)) m1 o2
| redM_abs1 : forall x t env m1 m2 v, redM deep env (extMd_abs x t (outM_ret v m2)) m1 (outM_ret (valMd_abs t env (nxlam x (getvalMd_nf v))) m2)
| redM_app : forall df env m t1 o1 t2 o2,
    redM shallow env (extM_term t1) m o1 ->
    redM df env (extM_app o1 t2) m o2 ->
    redM df env (extM_term (app t1 t2)) m o2
| redM_app1_nf : forall df env m1 m2 v o1 t2 o2,
    redM deep env (extM_term t2) m2 o1 ->
    redM df env (extM_appnf v o1) m2 o2 ->
    redM df env (extM_app (outM_ret (valM_nf v) m2) t2) m1 o2
| redM_app1_abs : forall df env env2 env3 m1 m2 m3 t1 t2 o,
    match env_get_maybe_var env t2 with Some x => env3 = x :: env2 /\ m3 = m2 | None => exists x, env_find (fst m2) x = None /\ env3 = x :: env2 /\ m3 = ((x, eiM_lazy t2 env) :: fst m2, snd m2) end ->
    redM df env3 (extM_term t1) m3 o ->
    redM df env (extM_app (outM_ret (valMs_abs t1 env2) m2) t2) m1 o
| redM_appnf : forall df env m1 m2 v1 v2,
    redM df env (extM_appnf v1 (outM_ret v2 m2)) m1 (outM_ret (valM_nf (nxapp v1 (getvalMd_nf v2))) m2)
(* | redM_constr_shallow : *)
(* | redM_constr_deep : *)
| redM_constr1_done : forall env m tag l l1,
    redM deep env (extMd_constr1 tag l l1 nil) m (outM_ret (valMd_constr tag l (nxconstr tag l1)) m)
| redM_constr1_step_var : forall env m tag l l1,
    redM deep env (extMd_constr1 tag l l1 nil) m (outM_ret (valMd_constr tag l (nxconstr tag l1)) m)

| redM_abort : forall df env e m o, get_abortM e = Some o -> redM df env e m o.

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
  forall dom res1 res2 u c,
    compat_res res1 res2 -> read_eiM res1 dom u c -> read_eiM res2 dom u c.
Proof.
  intros dom res1 res2 u c H1 H2. inversion H2; subst; econstructor; try eassumption.
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
  forall m res x c u, read_memM m res -> res x = Some c -> read_eiM res (snd m) u c -> read_memM (update_mem m x u) res.
Proof.
  intros [m dom] res x c u Hmem Hres Hread. unfold update_mem; simpl in *.
  split; simpl.
  - intros y v Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + injection Hy; intros; subst. exists c. split; assumption.
    + apply Hmem. assumption.
  - intros y Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + congruence.
    + apply Hmem. assumption.
Qed.

Definition read_memxM m res := read_memM m res /\ (forall x xs t env, res x = Some (clo_term xs t env) -> xs \subseteq (snd m)).
Lemma read_memxM_update :
  forall m res x c u, read_memxM m res -> res x = Some c -> read_eiM res (snd m) u c -> read_memxM (update_mem m x u) res.
Proof.
  intros m res x c u H1 H2 H3. split; [|apply H1].
  eapply read_memM_update; [apply H1|eassumption|eassumption].
Qed.

Lemma update_env_fst :
  forall {A : Type} (env : list (freevar * A)) x u, map fst env \subseteq map fst (update_env env x u).
Proof.
  induction env as [|[y v] env]; intros x u z; simpl in *.
  - tauto.
  - destruct freevar_eq_dec.
    + simpl. subst. tauto.
    + simpl. specialize (IHenv x u z). tauto.
Qed.

Lemma update_result_memdom :
  forall df x m o1 o2, update_result df x o1 o2 -> memdom (fst (get_out_memxM m o1)) \subseteq memdom (fst (get_out_memxM m o2)).
Proof.
  intros df x m o1 o2 H. inversion H; unexistT; subst; unexistT; subst; simpl in *.
  - apply update_env_fst.
  - apply update_env_fst.
  - apply update_env_fst.
  - apply update_env_fst.
  - apply update_env_fst.
  - reflexivity.
Qed.

Lemma redM_memdom_inc :
  forall df env e m o, redM df env e m o -> memdom (fst (get_ext_memxM m e)) \subseteq memdom (fst (get_out_memxM (get_ext_memxM m e) o)).
Proof.
  intros df env e m o H.
  induction H; simpl in *;
    try reflexivity;
    try (match goal with [ H : update_result _ _ _ _ |- _ ] => eapply update_result_memdom in H end);
    try (etransitivity; eassumption).
  - destruct o2; [|reflexivity]. simpl in *.
    transitivity (memdom (fst m2)); [|etransitivity; eassumption].
    subst. unfold memdom. simpl. prove_list_inc.
  - destruct o2; [|reflexivity]. simpl in *.
    etransitivity; eassumption.
  - destruct o2; [|reflexivity]. simpl in *.
    etransitivity; eassumption.
  - destruct env_get_maybe_var as [x|].
    + destruct H as (? & ?); subst.
      assumption.
    + destruct H as (x & ? & ? & ?); subst.
      destruct o; [|reflexivity]. simpl in *.
      etransitivity; [|eassumption]. prove_list_inc.
  - destruct e; simpl in *; try congruence; destruct o0; simpl in *; try congruence; autoinjSome; simpl in *; reflexivity.
Qed.

Lemma update_result_usedvars :
  forall df x m o1 o2, update_result df x o1 o2 -> snd (get_out_memxM m o1) = snd (get_out_memxM m o2).
Proof.
  intros df x m o1 o2 H. inversion H; unexistT; subst; unexistT; subst; simpl in *; reflexivity.
Qed.

Lemma redM_usedvars_inc :
  forall df env e m o, redM df env e m o -> snd (get_ext_memxM m e) \subseteq snd (get_out_memxM (get_ext_memxM m e) o).
Proof.
  intros df env e m o H.
  induction H; simpl in *;
    try reflexivity;
    try (match goal with [ H : update_result _ _ _ _ |- _ ] => eapply update_result_usedvars in H; rewrite <- H end);
    try eassumption;
    try (etransitivity; eassumption).
  - destruct o2; [|reflexivity]. simpl in *.
    transitivity (snd m2); [|etransitivity; eassumption].
    subst. simpl. prove_list_inc.
  - destruct o2; [|reflexivity]. simpl in *.
    etransitivity; eassumption.
  - destruct o2; [|reflexivity]. simpl in *.
    etransitivity; eassumption.
  - destruct env_get_maybe_var as [x|].
    + destruct H as (? & ?); subst.
      assumption.
    + destruct H as (x & ? & ? & ?); subst.
      destruct o; [|reflexivity]. simpl in *.
      etransitivity; [|eassumption]. prove_list_inc.
  - destruct e; simpl in *; try congruence; destruct o0; simpl in *; try congruence; autoinjSome; simpl in *; reflexivity.
Qed.

Definition is_divM {df} (e : extM df) :=
  match e with
  | extM_term _ => False
  | extM_app o _ => o = outM_div
  | extM_appnf _ o => o = outM_div
  | extM_switch o _ => o = outM_div
  | extM_switchnf1 _ _ _ => False
  | extM_switchnf2 _ _ _ o _ => o = outM_div
  | extMd_abs _ _ o => o = outM_div
  | extMd_constr1 _ _ _ _ => False
  | extMd_constr2 _ _ _ o _ => o = outM_div
  end.

Lemma update_result_not_div :
  forall df x o1 o2, update_result df x o1 o2 -> o2 = outM_div -> o1 = outM_div.
Proof.
  intros df x o1 o2 H. inversion H; subst; unexistT; subst; try discriminate.
  intros; reflexivity.
Qed.

Lemma redM_not_div :
  forall df env e m o, redM df env e m o -> o = outM_div -> is_divM e.
Proof.
  intros df env e m o H; induction H; try discriminate; try eassumption;
    try (match goal with [ H : update_result _ _ _ _ |- _ ] => assert (Hdiv := update_result_not_div _ _ _ _ H) end); simpl in *; try tauto.
  destruct e; simpl in *; try congruence; destruct o0; simpl in *; congruence.
Qed.

Lemma redM_redE :
  forall df env e m o,
    redM df env e m o ->
    forall res e2 env2, read_memxM (get_ext_memxM m e) res -> read_extM df res e e2 -> map Some env2 = map res env ->
             exists o2 res2, redE df (snd (get_ext_memxM m e)) (snd (get_out_memxM (get_ext_memxM m e) o)) env2 e2 o2 /\ read_outM df res2 o o2 /\ compat_res res res2 /\ read_memxM (get_out_memxM (get_ext_memxM m e) o) res2.
Proof.
  intros df env e m o H. induction H; intros res e2 nenv Hres Hread Hnenv; lazymatch goal with [ _ : get_abortM _ = _ |- _ ] => idtac | _ => inversion Hread end; unexistT; subst; simpl in *.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    + exists (out_ret (valE_nf v)). exists res.
      splits 4.
      * econstructor; [eassumption| |].
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- destruct df; simpl; [assumption|].
           eapply redE_shallow_deep_val in H2. assumption.
      * constructor; [apply Hres|]. constructor.
      * apply compat_res_refl.
      * assumption.
    + exists (out_ret (valE_nf (nxvar y))). exists res.
      splits 4.
      * eapply redE_var_free. assumption.
      * constructor; [apply Hres|]. constructor.
      * apply compat_res_refl.
      * assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |eassumption].
      destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    specialize (IHredM res (extE_term (abs t)) vs).
    destruct IHredM as (o3 & res3 & HredE & Ho3 & Hcompat & Hread3); [assumption|constructor|assumption|].
    exists o3. exists res3. splits 4.
    + econstructor; [eassumption| |].
      * destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2.
        etransitivity; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. eapply update_result_usedvars in H2; simpl in H2.
        rewrite <- H2; assumption.
      * eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_abs with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- rewrite <- H2; assumption.
        -- rewrite <- H2; eassumption.
    + inversion Ho3; unexistT; subst; inversion H2; unexistT; subst; constructor; try assumption.
      * inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence.
      * eapply read_memxM_update; [assumption|apply Hcompat; eassumption|].
        inversion H10; unexistT; subst.
        econstructor; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_abs with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- assumption.
        -- assumption.
      * inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence.
    + assumption.
    + inversion Ho3; unexistT; subst; inversion H2; unexistT; subst; try assumption.
      * inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence.
      * eapply read_memxM_update; [assumption|apply Hcompat; eassumption|].
        inversion H10; unexistT; subst.
        econstructor; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_abs with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- assumption.
        -- assumption.
      * inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |].
      * destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
      * eapply redE_deep_shallow_abs with (e := extE_term u); [eassumption|reflexivity].
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |eassumption].
      destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |eassumption].
      destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    specialize (IHredM res (extEd_constr tag vs nil None vs) nil).
    destruct IHredM as (o3 & res3 & HredE & Ho3 & Hcompat & Hread3); [assumption|constructor; assumption|reflexivity|].
    exists o3. exists res3. splits 4.
    + econstructor; [eassumption| |].
      * destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2.
        etransitivity; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. eapply update_result_usedvars in H2; simpl in H2.
        rewrite <- H2; assumption.
      * eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_constr with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- rewrite <- H2; assumption.
        -- rewrite <- H2; eassumption.
    + inversion Ho3; unexistT; subst; inversion H2; unexistT; subst; constructor; try assumption.
      * (* inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence. *) admit.
      * admit.
      * eapply read_memxM_update; [assumption|apply Hcompat; eassumption|].
        inversion H10; unexistT; subst.
        econstructor; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_constr with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- assumption.
        -- eassumption.
    + assumption.
    + inversion Ho3; unexistT; subst; inversion H2; unexistT; subst; try assumption.
      * (* inversion H1; unexistT; subst; [|simpl in *; congruence]. inversion H14; unexistT; subst; destruct o1; simpl in *; congruence. *) admit.
      * admit.
      * eapply read_memxM_update; [assumption|apply Hcompat; eassumption|].
        inversion H10; unexistT; subst.
        econstructor; [eassumption|].
        eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
        eapply redE_shallow_deep_constr with (e := extE_term u).
        -- eassumption.
        -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
        -- assumption.
        -- eassumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |].
      * destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
      * eapply redE_deep_shallow_constr with (e := extE_term u); [eassumption|reflexivity].
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    eexists; exists res; splits 4.
    + econstructor; [eassumption| |eassumption].
      destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2. assumption.
    + constructor; [apply Hres|]. constructor. assumption.
    + apply compat_res_refl.
    + assumption.
  - destruct (nenv_eqs H Hnenv) as (c & Hc1 & Hc2).
    assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 Hres) H0 Hc2). inversion Hx2; subst.
    specialize (IHredM res (extE_term t) vs).
    destruct IHredM as (o3 & res3 & HredE & Ho3 & Hcompat & Hread3); [assumption|constructor|assumption|].
    exists o3. exists res3.
    eapply redE_xs_mono in HredE; [|apply Hres in Hc2; eassumption].
    splits 4.
    + eapply redM_usedvars_inc in H1; simpl in H1. apply update_result_usedvars with (m := m) in H2; simpl in H2.
      econstructor; [eassumption| |].
      -- destruct Hres as [Hres1 Hres2]. apply Hres2 in Hc2.
         etransitivity; [eassumption|]. rewrite <- H2. assumption.
      -- rewrite <- H2. assumption.
    + inversion Ho3; unexistT; subst; inversion H2; subst; unexistT; subst; constructor; try assumption.
      all: eapply read_memM_update; [assumption|apply Hcompat; eassumption|].
      all: inversion H9; unexistT; subst.
      * constructor. destruct df; [assumption|].
        eapply redE_deep_shallow_val in HredE; [|reflexivity]. assumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
    + assumption.
    + inversion Ho3; unexistT; subst; inversion H2; subst; unexistT; subst; try assumption.
      all: eapply read_memxM_update; [assumption|apply Hcompat; eassumption|].
      all: inversion H9; unexistT; subst.
      * constructor. destruct df; [assumption|].
        eapply redE_deep_shallow_val in HredE; [|reflexivity]. assumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
      * econstructor; eassumption.
  - eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
    constructor; [apply Hres|]. constructor. assumption.
  - pose (res2 := (fun y => if freevar_eq_dec y a then Some (clo_var x) else res y)).
    assert (Hcompat : compat_res res res2).
    {
      intros y u Hyu. unfold res2. destruct freevar_eq_dec; [|assumption]. subst.
      apply Hres in H. congruence.
    }
    specialize (IHredM1 res2 (extE_term t) (clo_var x :: nenv)).
    destruct IHredM1 as (o3 & res3 & HredE1 & Ho3 & Hcompat3 & Hread3); [|constructor| |].
    + split; [split|]; simpl.
      * intros y u Hyu. destruct freevar_eq_dec.
        -- injection Hyu; intros; subst. unfold res2. exists (clo_var x).
           split; [rewrite freevar_eq_dec_eq_ifte; reflexivity|]. constructor.
        -- apply Hres in Hyu. destruct Hyu as (v & Hv1 & Hv2). exists v.
           split; [|eapply compat_res_read_eiM; try eassumption; eapply read_eiM_dom_mono; [eassumption|prove_list_inc]].
           unfold res2. rewrite freevar_eq_dec_neq_ifte; assumption.
      * intros y Hy. unfold res2. destruct freevar_eq_dec.
        -- congruence.
        -- apply Hres in Hy. assumption.
      * intros y xs t2 env2 Hy. unfold res2 in Hy. destruct freevar_eq_dec.
        -- congruence.
        -- apply Hres in Hy. rewrite Hy. prove_list_inc.
    + simpl. f_equal; [|eapply nenv_compat_list; eassumption]. unfold res2. rewrite freevar_eq_dec_eq_ifte; reflexivity.
    + specialize (IHredM2 res3 (extEd_abs x t o3) nenv).
      destruct IHredM2 as (o4 & res4 & HredE2 & Ho4 & Hcompat4 & Hread4).
      * assumption.
      * constructor. assumption.
      * eapply nenv_compat_list; [|eassumption]. eapply compat_res_trans; eassumption.
      * exists o4. exists res4. splits 4.
        -- destruct o1; [|apply redM_not_div in H2; simpl in H2; tauto].
           destruct o2; [|apply redM_not_div in H3; simpl in H3; [congruence|tauto]].
           eapply redM_usedvars_inc in H2; eapply redM_usedvars_inc in H3; simpl in *.
           econstructor; [eassumption|rewrite <- H3, <- H2; simpl; tauto|eapply redE_dom_mono; eassumption|].
           eapply redE_xs_mono; [eassumption|]. rewrite <- H2. prove_list_inc.
        -- assumption.
        -- eapply compat_res_trans; [eassumption|]. eapply compat_res_trans; eassumption.
        -- destruct o2; [assumption|].
           apply redM_not_div in H3; [|reflexivity]; simpl in *; subst.
           apply redM_not_div in H2; [|reflexivity]; simpl in *. tauto.
  - inversion H2; unexistT; subst; simpl in *.
    inversion H6; unexistT; subst; simpl in *.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. constructor. assumption.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. constructor. assumption.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. constructor. assumption.
  - specialize (IHredM1 res (extE_term t1) nenv).
    destruct IHredM1 as (o3 & res3 & HredE1 & Ho3 & Hcompat & Hread3); [assumption|constructor|assumption|].
    specialize (IHredM2 res3 (extE_app o3 t2) nenv).
    destruct IHredM2 as (o4 & res4 & HredE2 & Ho4 & Hcompat4 & Hread4); [assumption|constructor; assumption|eapply nenv_compat_list; eassumption|].
    exists o4. exists res4. splits 4.
    + destruct o1; [|apply redM_not_div in H; simpl in H; tauto].
      destruct o2; [|apply redM_not_div in H0; simpl in H0; [congruence|tauto]].
      eapply redM_usedvars_inc in H; eapply redM_usedvars_inc in H0; simpl in *.
      econstructor; [eapply redE_dom_mono|eapply redE_xs_mono]; eassumption.
    + assumption.
    + eapply compat_res_trans; eassumption.
    + destruct o2; simpl in *; [assumption|].
      apply redM_not_div in H0; [|reflexivity]. simpl in H0; subst.
      apply redM_not_div in H; [|reflexivity]. simpl in H. tauto.
  - inversion H4; unexistT; subst; simpl in *.
    inversion H8; unexistT; subst; simpl in *.
    specialize (IHredM1 res (extE_term t2) nenv).
    destruct IHredM1 as (o3 & res3 & HredE1 & Ho3 & Hcompat3 & Hread3); [assumption|constructor|assumption|].
    specialize (IHredM2 res3 (extE_appnf v o3) nenv).
    destruct IHredM2 as (o4 & res4 & HredE2 & Ho4 & Hcompat4 & Hread4); [assumption|constructor; assumption|eapply nenv_compat_list; eassumption|].
    exists o4. exists res4. splits 4.
    + destruct o1; [|apply redM_not_div in H; simpl in H; tauto].
      destruct o2; [|apply redM_not_div in H0; simpl in H0; [congruence|tauto]].
      eapply redM_usedvars_inc in H; eapply redM_usedvars_inc in H0; simpl in *.
      econstructor; [eapply redE_dom_mono|eapply redE_xs_mono]; eassumption.
    + assumption.
    + eapply compat_res_trans; eassumption.
    + destruct o2; simpl in *; [assumption|].
      apply redM_not_div in H0; [|reflexivity]. simpl in *; subst.
      apply redM_not_div in H; [|reflexivity]. simpl in *; subst. tauto.
  - inversion H4; unexistT; subst; simpl in *.
    inversion H8; unexistT; subst; simpl in *.
    destruct env_get_maybe_var as [x|] eqn:Ha.
    + destruct H as [Henv3 Hm3]; subst.
      destruct t2; simpl in Ha; try congruence.
      destruct (nenv_eqs Ha Hnenv) as (c & Hc1 & Hc2).
      specialize (IHredM res (extE_term t1) (c :: vs)).
      destruct IHredM as (o2 & res2 & HredE & Ho2 & Hcompat2 & Hread2); [assumption|constructor|simpl; f_equal; congruence|].
      exists o2. exists res2. splits 4.
      * econstructor; [reflexivity| |].
        -- eapply redM_usedvars_inc in H0. apply H0.
        -- simpl. rewrite Hc1. assumption.
      * assumption.
      * assumption.
      * assumption.
    + destruct H as (x & Hx & Henv3 & Hm3); subst; simpl in *.
      pose (res2 := (fun a => if freevar_eq_dec a x then Some (clo_term (snd m2) t2 nenv) else res a)).
      assert (Hcompat : compat_res res res2).
      {
        intros a u Hau. unfold res2. destruct freevar_eq_dec; [|assumption]. subst.
        apply Hres in Hx. congruence.
      }
      specialize (IHredM res2 (extE_term t1) (clo_term (snd m2) t2 nenv :: vs)).
      destruct IHredM as (o2 & res3 & HredE & Ho2 & Hcompat3 & Hread3).
      * split; [|intros y xs t3 env3 Hy; unfold res2 in Hy; destruct freevar_eq_dec; simpl; [injection Hy; intros; subst; reflexivity|eapply Hres; eassumption]].
        split; [|intros y Hy; simpl in Hy; unfold res2 in *; destruct freevar_eq_dec; [congruence|apply Hres; assumption]].
        intros y u Hu. simpl in Hu. destruct freevar_eq_dec.
        -- subst. eexists. split; [unfold res2; rewrite freevar_eq_dec_eq_ifte; reflexivity|].
           injection Hu; intros; subst. econstructor. eapply nenv_compat_list; eassumption.
        -- apply H7 in Hu. destruct Hu as (v & Hv1 & Hv2). exists v. split; [unfold res2; rewrite freevar_eq_dec_neq_ifte; assumption|].
           eapply compat_res_read_eiM; eassumption.
      * constructor.
      * simpl. f_equal.
        -- unfold res2. rewrite freevar_eq_dec_eq_ifte; reflexivity.
        -- eapply nenv_compat_list; eassumption.
      * exists o2. exists res3. splits 4.
        -- econstructor; [reflexivity|eapply redM_usedvars_inc in H0; destruct o; apply H0|].
           destruct t2; try (destruct o; assumption). simpl.
           destruct (nth_error nenv n) eqn:Hc; [|destruct o; assumption]. exfalso.
           assert (length (map Some nenv) = length (map res env)) by congruence; rewrite !map_length in *.
           simpl in *.
           erewrite nth_error_None, <- H, <- nth_error_None in Ha. congruence.
        -- assumption.
        -- eapply compat_res_trans; eassumption.
        -- destruct o; [assumption|]. apply redM_not_div in H0; [|reflexivity]; simpl in *; subst. tauto.
  - inversion H2; unexistT; subst; simpl in *.
    inversion H6; unexistT; subst; simpl in *.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. apply read_valM_nf.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. apply read_valM_nf.
    + eexists; exists res; splits 4; [econstructor| |apply compat_res_refl|assumption].
      constructor; [assumption|]. apply read_valM_nf.
  - exists out_div. exists res. splits 4.
    + constructor.
      inversion Hread; unexistT; subst; unexistT; subst; simpl in *; try congruence;
        lazymatch goal with [ H : read_outM _ _ _ _ |- _ ] => inversion H end; unexistT; subst; simpl in *; congruence.
    + destruct o; [|constructor]. exfalso.
      destruct e; simpl in *; try congruence; destruct o; simpl in *; congruence.
    + apply compat_res_refl.
    + destruct o; [|assumption]. exfalso.
      destruct e; simpl in *; try congruence; destruct o; simpl in *; congruence.
Qed.
































