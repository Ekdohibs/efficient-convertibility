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

Fixpoint size t :=
  match t with
  | var n => 0
  | abs t => S (size t)
  | app t1 t2 => S (size t1 + size t2)
  | constr tag l => S (list_sum (map (fun t => S (size t)) l))
  | switch t m => S (size t + list_sum (map (fun pt2 => S (size (snd pt2))) m))
  end.

Inductive closed_at : term -> nat -> Prop :=
| closed_at_var : forall n k, n < k -> closed_at (var n) k
| closed_at_app : forall t1 t2 k, closed_at t1 k -> closed_at t2 k -> closed_at (app t1 t2) k
| closed_at_abs : forall t k, closed_at t (S k) -> closed_at (abs t) k
| closed_at_constr : forall tag l k, (forall t, t \in l -> closed_at t k) -> closed_at (constr tag l) k
| closed_at_switch :
    forall t m k, closed_at t k -> (forall p t2, (p, t2) \in m -> closed_at t2 (p + k)) -> closed_at (switch t m) k.

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


(* TODO move? *)
Definition env_get_maybe_var {A: Type} (env : list A) t :=
  match t with
  | var n => nth_error env n
  | _ => None
  end.

Lemma env_get_maybe_var_in :
  forall (A : Type) t (env : list A) x, env_get_maybe_var env t = Some x -> x \in env.
Proof.
  intros A t env x H. destruct t; simpl in *; try congruence.
  eapply nth_error_In. eassumption.
Qed.

