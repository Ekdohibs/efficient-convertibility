Require Import List.
Require Import Setoid.
Require Import Morphisms.
Require Import Arith.
Require Import Psatz.
Require Import Coq.Logic.Eqdep_dec.

Lemma Some_inj : forall A (x y : A), Some x = Some y -> x = y.
Proof.
  intros; congruence.
Qed.
Ltac autoinjSome :=
  repeat match goal with
           [ H : Some ?x = Some ?y |- _ ] => apply Some_inj in H; subst
         end.

(** List Notations *)

Notation "x '\in' L" := (In x L) (at level 80, only parsing).
Notation "x '\notin' L" := (~ In x L) (at level 80, only parsing).
Notation "x ∈ L" := (x \in L) (at level 80).
Notation "x ∉ L" := (x \notin L) (at level 80).

Fixpoint index {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) L x :=
  match L with
  | nil => None
  | y :: L => if dec x y then Some 0 else option_map S (index dec L x)
  end.

Lemma index_notin_None :
  forall A eq_dec (l : list A) (x : A), x \notin l -> index eq_dec l x = None.
Proof.
  intros A eq_dec l x H; induction l.
  - reflexivity.
  - simpl in *. destruct eq_dec; [intuition congruence|].
    rewrite IHl; tauto.
Qed.

Lemma index_app :
  forall A eq_dec (l1 l2 : list A) x,
    index eq_dec (l1 ++ l2) x =
    match index eq_dec l1 x with
    | Some n => Some n
    | None => option_map (fun n => length l1 + n) (index eq_dec l2 x)
    end.
Proof.
  intros A eq_dec l1 l2 x; induction l1; simpl in *.
  - destruct index; reflexivity.
  - destruct eq_dec; [reflexivity|].
    rewrite IHl1. destruct (index eq_dec l1 x); [reflexivity|].
    destruct (index eq_dec l2 x); reflexivity.
Qed.

Lemma index_in_Some :
  forall A eq_dec (l : list A) (x : A), x \in l -> exists k, index eq_dec l x = Some k.
Proof.
  intros A eq_dec l x H; induction l.
  - simpl in *; tauto.
  - simpl. destruct eq_dec; [exists 0; reflexivity|].
    destruct IHl as (k & Hk).
    + destruct H; [symmetry in H|]; tauto.
    + exists (S k). rewrite Hk; reflexivity.
Qed.

Lemma index_in_not_None :
  forall A eq_dec (l : list A) (x : A), x \in l -> index eq_dec l x <> None.
Proof.
  intros A eq_dec l x H. destruct (index_in_Some A eq_dec l x H) as (k & Hk). congruence.
Qed.

Lemma nth_error_index :
  forall A eq_dec (x : A) l n, index eq_dec l x = Some n -> nth_error l n = Some x.
Proof.
  intros A eq_dec x. induction l; intros [|n]; simpl in *; try congruence; destruct eq_dec; simpl in *; try congruence.
  - destruct index; simpl; congruence.
  - destruct index; simpl; [|congruence]. intros; apply IHl; congruence.
Qed.

Lemma index_nth_error :
  forall (A : Type) eq_dec (vars : list A) k x, NoDup vars -> nth_error vars k = Some x -> index eq_dec vars x = Some k.
Proof.
  intros A eq_dec vars k x H1 H2. revert k H2; induction vars as [|y vars]; intros k H2; simpl in *.
  - destruct k; simpl in *; congruence.
  - destruct k; simpl in *.
    + injection H2 as H2; subst. destruct eq_dec; [|tauto]. reflexivity.
    + destruct eq_dec; [subst|].
      * inversion H1; subst. exfalso. apply H3. eapply nth_error_In; eassumption.
      * erewrite IHvars; [reflexivity| |eassumption].
        inversion H1; subst; assumption.
Qed.

Lemma index_seq :
  forall eq_dec a len x,
    a <= x < a + len ->
    index eq_dec (seq a len) x = Some (x - a).
Proof.
  intros eq_dec a len x Hx. revert a Hx; induction len; intros a Hx.
  - lia.
  - simpl index. destruct eq_dec.
    + subst. f_equal. lia.
    + rewrite IHlen; [|lia]. simpl. f_equal. lia.
Qed.

Lemma index_length :
  forall A eq_dec (x : A) l n, index eq_dec l x = Some n -> n < length l.
Proof.
  induction l; intros n Hn; simpl in *.
  - congruence.
  - destruct eq_dec; [injection Hn as Hn; lia|].
    destruct index eqn:Hidx; simpl in *; [|congruence].
    specialize (IHl n1 eq_refl). injection Hn as Hn; lia.
Qed.

Lemma nth_error_map :
  forall (A B : Type) (f : A -> B) L n, nth_error (map f L) n = match nth_error L n with Some x => Some (f x) | None => None end.
Proof.
  intros A B f L. induction L as [|a L]; intros [|n]; simpl; try reflexivity.
  apply IHL.
Qed.

Lemma nth_error_decompose :
  forall (A : Type) (L : list A) x n, nth_error L n = Some x -> exists L1 L2, L = L1 ++ x :: L2 /\ length L1 = n.
Proof.
  intros A L. induction L as [|y L]; intros x [|n] H; simpl in *; try congruence; autoinjSome.
  - exists nil. exists L. split; reflexivity.
  - apply IHL in H. destruct H as (L1 & L2 & H1 & H2). exists (y :: L1). exists L2.
    split; [rewrite H1; reflexivity|simpl; rewrite H2; reflexivity].
Qed.

Lemma nth_error_Some2 :
  forall (A : Type) (l : list A) n, n < length l -> exists x, nth_error l n = Some x.
Proof.
  intros A l n. revert l; induction n; intros l H; destruct l as [|x l]; simpl in *; try lia.
  - exists x. reflexivity.
  - apply IHn. lia.
Qed.

Lemma nth_error_Some3 :
  forall (A : Type) (l : list A) n x, nth_error l n = Some x -> n < length l.
Proof.
  intros. apply nth_error_Some. destruct nth_error; congruence.
Qed.

Lemma nth_error_app_Some :
  forall (A : Type) (l1 l2 : list A) k x, nth_error l1 k = Some x -> nth_error (l1 ++ l2) k = Some x.
Proof.
  induction l1; intros l2 [|k] x; simpl in *; intros; try congruence.
  apply IHl1; assumption.
Qed.

Lemma nth_error_extend :
  forall {A : Type} (l : list A) x, nth_error (l ++ x :: nil) (length l) = Some x.
Proof.
  intros A l x. rewrite nth_error_app2 by lia.
  destruct (length l - length l) eqn:Hll; [reflexivity|lia].
Qed.

Lemma nth_error_extend_case :
  forall {A : Type} l (x : A) n,
    nth_error (l ++ x :: nil) n = nth_error l n \/ (n = length l /\ nth_error (l ++ x :: nil) n = Some x).
Proof.
  intros A l x n.
  destruct (le_lt_dec (length l) n).
  - rewrite nth_error_app2 by assumption.
    destruct (n - length l) eqn:Hn; simpl; [right; split; [lia|reflexivity]|].
    left. destruct n0; symmetry; apply nth_error_None; assumption.
  - left. rewrite nth_error_app1; tauto.
Qed.

Definition nth_error_None_rw :
  forall {A : Type} (l : list A) (n : nat), length l <= n -> nth_error l n = None.
Proof.
  intros. apply nth_error_None. assumption.
Qed.

Lemma nth_error_select :
  forall (A : Type) (l1 l2 : list A) (x : A), nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  intros; induction l1; simpl in *; [reflexivity|assumption].
Qed.


Lemma list_exists :
  forall (A : Type) (P : nat -> A -> Prop) n, (forall k, k < n -> exists x, P k x) -> exists L, length L = n /\ (forall k x, nth_error L k = Some x -> P k x).
Proof.
  intros A P n. induction n; intros H.
  - exists nil. split; [reflexivity|].
    intros [|k]; simpl; intros; discriminate.
  - destruct IHn as [L HL]; [intros k Hk; apply H; lia|].
    destruct (H n) as [x Hx]; [lia|].
    exists (L ++ x :: nil). split.
    + rewrite app_length; simpl. lia.
    + intros k y.
      destruct (le_lt_dec n k).
      * rewrite nth_error_app2 by lia.
        destruct (k - length L) as [|u] eqn:Hu; simpl.
        -- assert (k = n) by lia. congruence.
        -- destruct u; simpl; discriminate.
      * rewrite nth_error_app1 by lia. apply HL.
Qed.

Lemma list_app_eq_length :
  forall A (l1 l2 l3 l4 : list A), l1 ++ l3 = l2 ++ l4 -> length l1 = length l2 -> l1 = l2 /\ l3 = l4.
Proof.
  intros A l1 l2 l3 l4; revert l2; induction l1; intros l2 H1 H2; destruct l2; simpl in *; try intuition congruence.
  specialize (IHl1 l2 ltac:(congruence) ltac:(congruence)).
  intuition congruence.
Qed.

Lemma list_select_eq :
  forall (A : Type) (l1a l1b l2a l2b : list A) (x1 x2 : A),
    l1a ++ x1 :: l1b = l2a ++ x2 :: l2b ->
    (l1a = l2a /\ x1 = x2 /\ l1b = l2b) \/
    (exists l3, l1a ++ x1 :: l3 = l2a /\ l1b = l3 ++ x2 :: l2b) \/
    (exists l3, l1a = l2a ++ x2 :: l3 /\ l3 ++ x1 :: l1b = l2b).
Proof.
  intros A l1a. induction l1a as [|x1a l1a IH]; intros l1b l2a l2b x1 x2 Heq; destruct l2a as [|x2a l2a]; simpl in *.
  - left. split; [reflexivity|].
    split; congruence.
  - right. left. exists l2a. split; congruence.
  - right. right. exists l1a. split; congruence.
  - specialize (IH l1b l2a l2b x1 x2 ltac:(congruence)).
    destruct IH as [IH | [IH | IH]]; [left|right; left|right; right].
    + intuition congruence.
    + destruct IH as (l3 & H1 & H2). exists l3. intuition congruence.
    + destruct IH as (l3 & H1 & H2). exists l3. intuition congruence.
Qed.

Lemma select2_app_assoc :
  forall (A : Type) (l1 l2 l3 : list A) (x1 x2 : A),
    (l1 ++ x1 :: l2) ++ x2 :: l3 = l1 ++ x1 :: l2 ++ x2 :: l3.
Proof.
  intros.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma length_select :
  forall (A : Type) (l1 l2 : list A) (x1 x2 : A),
    length (l1 ++ x1 :: l2) = length (l1 ++ x2 :: l2).
Proof.
  intros; rewrite !app_length; reflexivity.
Qed.


(** Map for association lists *)

Definition map_assq {A B C : Type} (f : A -> B -> C) (L : list (A * B)) := map (fun '(x, u) => (x, f x u)) L.

Lemma map_assq_id_forall :
  forall (A B : Type) (f : A -> B -> B) (L : list (A * B)), Forall (fun '(x, u) => f x u = u) L -> map_assq f L = L.
Proof.
  intros A B f L H. induction L as [|[x u] L].
  - reflexivity.
  - inversion H; subst.
    simpl. f_equal.
    + congruence.
    + auto.
Qed.

Lemma map_assq_compose :
  forall {A B C D : Type} (f : A -> B -> C) (g : A -> C -> D) L, map_assq g (map_assq f L) = map_assq (fun x u => g x (f x u)) L.
Proof.
  intros. unfold map_assq. rewrite map_map. apply map_ext.
  intros [? ?]; simpl; reflexivity.
Qed.

Lemma map_assq_length :
  forall {A B C : Type} (f : A -> B -> C) L, length (map_assq f L) = length L.
Proof.
  intros; unfold map_assq; rewrite map_length; reflexivity.
Qed.

Lemma map_assq_ext :
  forall {A B C : Type} (f g : A -> B -> C) L, (forall x u, f x u = g x u) -> map_assq f L = map_assq g L.
Proof.
  intros; unfold map_assq; apply map_ext; intros [? ?]; f_equal; auto.
Qed.

(** Theorems on Forall *)

Lemma Forall_cons_iff :
  forall A (P : A -> Prop) a L, Forall P (a :: L) <-> P a /\ Forall P L.
Proof.
  intros. split.
  - intros H; inversion H; tauto.
  - intros; constructor; tauto.
Qed.

Lemma Forall_app_iff :
  forall A (P : A -> Prop) L1 L2, Forall P (L1 ++ L2) <-> Forall P L1 /\ Forall P L2.
Proof.
  intros. induction L1.
  - simpl. firstorder.
  - intros; simpl.
    rewrite !Forall_cons_iff, IHL1. tauto.
Qed.

Lemma Forall_map :
  forall A B (f : A -> B) (P : B -> Prop) L, Forall P (map f L) <-> Forall (fun x => P (f x)) L.
Proof.
  intros. induction L.
  - simpl. firstorder.
  - simpl. rewrite !Forall_cons_iff. firstorder.
Qed.

Lemma Forall_ext_In :
  forall (A : Type) (P1 P2 : A -> Prop) (L : list A), Forall (fun x => P1 x <-> P2 x) L -> Forall P1 L <-> Forall P2 L.
Proof.
  intros. induction L.
  - split; constructor.
  - inversion H; subst.
    rewrite !Forall_cons_iff. tauto.
Qed.

Lemma Forall_True :
  forall (A : Type) (P : A -> Prop) (L : list A), (forall x, P x) -> Forall P L.
Proof.
  intros. induction L.
  - constructor.
  - constructor; auto.
Qed.

Lemma Forall_True_transparent :
  forall (A : Type) (P : A -> Prop) (L : list A), (forall x, P x) -> Forall P L.
Proof.
  intros. induction L.
  - constructor.
  - constructor; auto.
Defined.

Lemma Forall_ext :
  forall (A : Type) (P1 P2 : A -> Prop) (L : list A), (forall x, P1 x <-> P2 x) -> Forall P1 L <-> Forall P2 L.
Proof.
  intros. apply Forall_ext_In.
  apply Forall_True. assumption.
Qed.

Lemma Forall_map_assq :
  forall (A B C : Type) (f : A -> B -> C) (P : A * C -> Prop) (L : list (A * B)), Forall P (map_assq f L) <-> Forall (fun '(x, u) => P (x, f x u)) L.
Proof.
  intros.
  unfold map_assq.
  rewrite Forall_map.
  apply Forall_ext. intros [x u].
  reflexivity.
Qed.

Lemma Forall_filter :
  forall (A : Type) (P : A -> Prop) (f : A -> bool) (L : list A), Forall P (filter f L) <-> Forall (fun x => f x = true -> P x) L.
Proof.
  intros. induction L.
  - simpl. split; constructor.
  - simpl. destruct (f a) eqn:Hfa.
    + rewrite !Forall_cons_iff. tauto.
    + rewrite Forall_cons_iff. intuition congruence.
Qed.

Lemma Forall_filter_eq :
  forall A (P : A -> bool) L, Forall (fun x => P x = true) L -> filter P L = L.
Proof.
  intros A P L. induction L.
  - intros; reflexivity.
  - intros H. simpl. inversion H; subst.
    rewrite H2; simpl; f_equal; apply IHL. assumption.
Qed.

Lemma Forall_In :
  forall (A : Type) (P : A -> Prop) (L : list A), Forall P L <-> (forall x, In x L -> P x).
Proof.
  intros A P L. induction L.
  - simpl. split; intros; [tauto|constructor].
  - rewrite Forall_cons_iff, IHL. simpl.
    firstorder congruence.
Qed.

Lemma Forall_and :
  forall (A : Type) (P Q : A -> Prop) L, Forall P L /\ Forall Q L <-> Forall (fun x => P x /\ Q x) L.
Proof.
  intros A P Q L. induction L as [|x L].
  - simpl. repeat split; constructor.
  - simpl. rewrite !Forall_cons_iff, <- IHL. tauto.
Qed.

Lemma nth_error_Forall_iff :
  forall A (P : A -> Prop) L,
    Forall P L <-> (forall n x, nth_error L n = Some x -> P x).
Proof.
  intros A P L. split.
  - intros H. induction H.
    + intros; destruct n; simpl in *; discriminate.
    + intros [|n]; simpl; [|apply IHForall].
      intros; congruence.
  - induction L as [|x L IH]; intros Hforall; simpl in *.
    + constructor.
    + constructor.
      * apply (Hforall 0); reflexivity.
      * apply IH. intros n; apply (Hforall (S n)).
Qed.

Lemma Forall_impl_transparent :
  forall (A : Type) (P Q : A -> Prop) L, (forall x, P x -> Q x) -> Forall P L -> Forall Q L.
Proof.
  intros A P Q L Himpl H. induction H.
  - constructor.
  - constructor.
    + apply Himpl. assumption.
    + assumption.
Defined.

Lemma Forall_Exists :
  forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (R : Prop) (L : list A),
    (forall x, P x -> Q x -> R) -> Forall P L -> Exists Q L -> R.
Proof.
  intros A P Q R L H1 H2; induction H2; intros H3; inversion H3; subst.
  - eapply H1; eassumption.
  - apply IHForall; assumption.
Qed.

Lemma Forall2_cons_iff :
  forall (A B : Type) (P : A -> B -> Prop) x y L1 L2, Forall2 P (x :: L1) (y :: L2) <-> P x y /\ Forall2 P L1 L2.
Proof.
  intros. split.
  - intros H. inversion H. tauto.
  - intros [H1 H2]. constructor; assumption.
Qed.

Lemma Forall2_map_eq :
  forall (A B C : Type) (f : A -> C) (g : B -> C) L1 L2, map f L1 = map g L2 <-> Forall2 (fun u v => f u = g v) L1 L2.
Proof.
  intros A B C f g L1 L2. split.
  - intros Heq. revert L2 Heq; induction L1 as [|x L1]; intros [|y L2] Heq; simpl in *; try congruence.
    + constructor.
    + injection Heq as Heq1 Heq2. constructor; [assumption|].
      apply IHL1. assumption.
  - intros H. induction H.
    + reflexivity.
    + simpl. f_equal; assumption.
Qed.

Lemma Forall2_map_left :
  forall (A B C : Type) (P : A -> B -> Prop) (f : C -> A) L1 L2, Forall2 P (map f L1) L2 <-> Forall2 (fun u v => P (f u) v) L1 L2.
Proof.
  intros A B C P f L1 L2. revert L2; induction L1 as [|x L1]; intros [|y L2].
  - simpl. split; intros; constructor.
  - simpl. split; intros H; inversion H.
  - simpl. split; intros H; inversion H.
  - simpl. rewrite !Forall2_cons_iff, IHL1. reflexivity.
Qed.

Lemma Forall2_comm :
  forall (A B : Type) (P : A -> B -> Prop) L1 L2, Forall2 P L1 L2 <-> Forall2 (fun u v => P v u) L2 L1.
Proof.
  intros A B P L1 L2. revert L2; induction L1 as [|x L1]; intros [|y L2].
  - simpl. split; intros; constructor.
  - simpl. split; intros H; inversion H.
  - simpl. split; intros H; inversion H.
  - simpl. rewrite !Forall2_cons_iff, IHL1. reflexivity.
Qed.

Lemma Forall2_map_right :
  forall (A B C : Type) (P : A -> B -> Prop) (f : C -> B) L1 L2, Forall2 P L1 (map f L2) <-> Forall2 (fun u v => P u (f v)) L1 L2.
Proof.
  intros A B C P f L1 L2. revert L2; induction L1 as [|x L1]; intros [|y L2].
  - simpl. split; intros; constructor.
  - simpl. split; intros H; inversion H.
  - simpl. split; intros H; inversion H.
  - simpl. rewrite !Forall2_cons_iff, IHL1. reflexivity.
Qed.

Lemma Forall2_map_same :
  forall (A : Type) (P : A -> A -> Prop) L, Forall2 P L L <-> Forall (fun x => P x x) L.
Proof.
  intros A P L. induction L as [|x L].
  - split; constructor.
  - rewrite Forall2_cons_iff, Forall_cons_iff, IHL. reflexivity.
Qed.

Lemma Forall2_impl :
  forall (A B : Type) (P Q : A -> B -> Prop) L1 L2, (forall x y, P x y -> Q x y) -> Forall2 P L1 L2 -> Forall2 Q L1 L2.
Proof.
  intros A B P Q L1 L2 HPQ H. induction H.
  - constructor.
  - constructor; [apply HPQ; assumption|]. assumption.
Qed.

Lemma Forall2_impl_transparent : forall (A B : Type) (P Q : A -> B -> Prop) (L1 : list A) (L2 : list B), (forall (x : A) (y : B), P x y -> Q x y) -> Forall2 P L1 L2 -> Forall2 Q L1 L2.
Proof.
  intros A B P Q L1 L2 Himpl H. induction H.
  - constructor.
  - constructor.
    + apply Himpl. assumption.
    + assumption.
Defined.

Lemma Forall2_In_left :
  forall (A B : Type) (P : A -> B -> Prop) L1 L2 x, Forall2 P L1 L2 -> x \in L1 -> exists y, y \in L2 /\ P x y.
Proof.
  intros A B P L1 L2 x H Hx; induction H; simpl in *.
  - tauto.
  - destruct Hx as [-> | Hx]; [exists y; tauto|].
    destruct (IHForall2 Hx) as (y0 & Hy1 & Hy2); exists y0; tauto.
Qed.

Lemma Forall2_In_right :
  forall (A B : Type) (P : A -> B -> Prop) L1 L2 y, Forall2 P L1 L2 -> y \in L2 -> exists x, x \in L1 /\ P x y.
Proof.
  intros A B P L1 L2 y H Hy; induction H; simpl in *.
  - tauto.
  - destruct Hy as [-> | Hy]; [exists x; tauto|].
    destruct (IHForall2 Hy) as (x0 & Hx1 & Hx2); exists x0; tauto.
Qed.


Lemma Forall2_impl_In_left_transparent :
  forall (A B : Type) (P Q : A -> B -> Prop) L1 L2,
    (forall x y, In x L1 -> P x y -> Q x y) -> Forall2 P L1 L2 -> Forall2 Q L1 L2.
Proof.
  intros A B P Q L1 L2 H Hforall. induction Hforall.
  - constructor.
  - econstructor.
    + apply H; [left; reflexivity|assumption].
    + apply IHHforall.
      intros; eapply H; [right|]; eassumption.
Defined.

Lemma Forall2_In_left_transparent :
  forall (A B : Type) (P : A -> B -> Prop) (Q : Prop) (L1 : list A) (L2 : list B) (x : A) (H : forall y, P x y -> Q), Forall2 P L1 L2 -> x ∈ L1 -> Q.
Proof.
  intros A B P Q L1 L2 x HQ H Hx; induction H.
  - simpl in Hx; tauto.
  - destruct Hx as [-> | Hx]; [eapply HQ; eassumption|apply (IHForall2 Hx)].
Defined.

Lemma Forall2_Exists_left_transparent :
  forall (A B : Type) (P : A -> B -> Prop) (Q : A -> Prop) (R : Prop) (L1 : list A) (L2 : list B) (H : forall x y, P x y -> Q x -> R), Forall2 P L1 L2 -> Exists Q L1 -> R.
Proof.
  intros A B P Q R L1 L2 H HP HQ; induction HP.
  - inversion HQ.
  - inversion HQ; subst; [eapply H; eassumption|].
    apply IHHP, H2.
Defined.


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

Lemma nth_error_Forall2_iff:
  forall A B (P : A -> B -> Prop) L1 L2,
    Forall2 P L1 L2 <-> (length L1 = length L2 /\ forall n x y, nth_error L1 n = Some x -> nth_error L2 n = Some y -> P x y).
Proof.
  intros A B P L1 L2. split.
  - intros H. induction H.
    + split; [reflexivity|]. intros; destruct n; simpl in *; discriminate.
    + destruct IHForall2 as [Hlen Hforall].
      split; [simpl; congruence|].
      intros [|n]; simpl; [|apply Hforall].
      intros; congruence.
  - revert L2; induction L1 as [|x L1 IH]; intros [|y L2] [Hlen Hforall]; simpl in *.
    + constructor.
    + discriminate.
    + discriminate.
    + constructor; [apply (Hforall 0); reflexivity|].
      apply IH. split; [congruence|].
      intros n; apply (Hforall (S n)).
Qed.

Lemma Forall2_length :
  forall (A B : Type) (P : A -> B -> Prop) L1 L2, Forall2 P L1 L2 -> length L1 = length L2.
Proof.
  intros A B P L1 L2 H. induction H; simpl; congruence.
Qed.

Lemma Forall2_and :
  forall (A B : Type) (P Q : A -> B -> Prop) L1 L2, Forall2 P L1 L2 -> Forall2 Q L1 L2 -> Forall2 (fun x y => P x y /\ Q x y) L1 L2.
Proof.
  intros A B P Q L1 L2 HP. induction HP; intros HQ; inversion HQ; subst.
  - constructor.
  - constructor; [split; assumption|apply IHHP; assumption].
Qed.

Lemma Forall2_select1 :
  forall (A B : Type) (P : A -> Prop) (l1 : list A) (l2 : list B), Forall2 (fun a b => P a) l1 l2 -> Forall P l1.
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma Forall2_select2 :
  forall (A B : Type) (P : B -> Prop) (l1 : list A) (l2 : list B), Forall2 (fun a b => P b) l1 l2 -> Forall P l2.
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma Forall2_and_Forall_left :
  forall (A B : Type) (P : A -> B -> Prop) (Q : A -> Prop) (L1 : list A) (L2 : list B), Forall2 P L1 L2 -> Forall Q L1 -> Forall2 (fun x y => P x y /\ Q x) L1 L2.
Proof.
  intros A B P Q L1 L2 H1; induction H1; intros H2; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall2_and_Forall_right :
  forall (A B : Type) (P : A -> B -> Prop) (Q : B -> Prop) (L1 : list A) (L2 : list B), Forall2 P L1 L2 -> Forall Q L2 -> Forall2 (fun x y => P x y /\ Q y) L1 L2.
Proof.
  intros A B P Q L1 L2 H1; induction H1; intros H2; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall2_eq :
  forall (A : Type) (l1 l2 : list A), Forall2 eq l1 l2 -> l1 = l2.
Proof.
  intros A l1 l2 H; induction H.
  - reflexivity.
  - congruence.
Qed.

Lemma Forall2_from_combine :
  forall (A B : Type) (P : A * B -> Prop) l1 l2, length l1 = length l2 -> Forall P (combine l1 l2) -> Forall2 (fun x y => P (x, y)) l1 l2.
Proof.
  intros A B P; induction l1; intros l2; destruct l2; intros H1 Hforall; simpl in *; try congruence.
  - constructor.
  - inversion Hforall; subst. constructor; [assumption|].
    apply IHl1; [congruence|assumption].
Qed.

Lemma Forall_combine_from_Forall2 :
  forall (A B : Type) (P : A * B -> Prop) l1 l2, Forall2 (fun a b => P (a, b)) l1 l2 -> Forall P (combine l1 l2).
Proof.
  intros A B P l1 l2 H; induction H; constructor; assumption.
Qed.

Lemma Forall_square :
  forall (A B C D : Type) (P : A -> B -> Prop) (Q : C -> D -> Prop) (R : A -> C -> Prop) l1 l2 l3 l4,
    Forall2 P l1 l2 -> Forall2 Q l3 l4 -> Forall2 R l1 l3 -> Forall2 (fun b d => exists a c, P a b /\ Q c d /\ R a c) l2 l4.
Proof.
  intros A B C D P Q R; induction l1; intros l2 l3 l4 H1 H2 H3; inversion H1; subst; inversion H3; subst; inversion H2; subst;
    constructor.
  - eexists. eexists. split; [eassumption|]. split; eassumption.
  - eapply IHl1; eassumption.
Qed.

Lemma Exists_neg_Forall2 :
  forall (A B : Type) (P : A -> B -> Prop) l1 l2, Exists (fun xy => ~ P (fst xy) (snd xy)) (combine l1 l2) -> ~ (Forall2 P l1 l2).
Proof.
  intros A B P; induction l1; intros l2 H1 H2; destruct l2; simpl in *; inversion H1; subst; inversion H2; subst; simpl in *.
  - tauto.
  - eapply IHl1; eassumption.
Qed.

Lemma Exists_square :
  forall (A B C D : Type) (P : A -> B -> Prop) (Q : C -> D -> Prop) (R : A * C -> Prop) l1 l2 l3 l4,
    Forall2 P l1 l2 -> Forall2 Q l3 l4 -> Exists R (combine l1 l3) -> Exists (fun bd => exists a c, P a (fst bd) /\ Q c (snd bd) /\ R (a, c)) (combine l2 l4).
Proof.
  intros A B C D P Q R; induction l1; intros l2 l3 l4 H1 H2 H3; inversion H1; subst; simpl in *; inversion H2; subst; simpl in *; inversion H3; subst.
  - apply Exists_cons_hd. eexists. eexists. split; [eassumption|]. split; eassumption.
  - apply Exists_cons_tl. eapply IHl1; eassumption.
Qed.



Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 R nil nil nil
| Forall3_cons : forall x y z l1 l2 l3, R x y z -> Forall3 R l1 l2 l3 -> Forall3 R (x :: l1) (y :: l2) (z :: l3).

Lemma Forall3_impl :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) l1 l2 l3,
    (forall x y z, P x y z -> Q x y z) -> Forall3 P l1 l2 l3 -> Forall3 Q l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 HPQ H; induction H; constructor; [apply HPQ|]; assumption.
Qed.

Lemma Forall3_app :
  forall (A B C : Type) (P : A -> B -> C -> Prop) l1a l1b l1c l2a l2b l2c, Forall3 P l1a l1b l1c -> Forall3 P l2a l2b l2c -> Forall3 P (l1a ++ l2a) (l1b ++ l2b) (l1c ++ l2c).
Proof.
  intros A B C P l1a l1b l1c l2a l2b l2c H1 H2; induction H1; simpl in *.
  - assumption.
  - constructor; assumption.
Qed.

Lemma Forall3_and :
  forall A B C (P Q : A -> B -> C -> Prop) l1 l2 l3, Forall3 P l1 l2 l3 -> Forall3 Q l1 l2 l3 -> Forall3 (fun a b c => P a b c /\ Q a b c) l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H1 H2; induction H1; simpl in *; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall3_select12 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R x y) l1 l2 l3 -> Forall2 R l1 l2.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall3_select13 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R x z) l1 l2 l3 -> Forall2 R l1 l3.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall3_select23 :
  forall A B C R (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => R y z) l1 l2 l3 -> Forall2 R l2 l3.
Proof.
  intros A B C R l1 l2 l3 H; induction H; constructor; auto.
Qed.

Lemma Forall3_select3 :
  forall A B C (P : C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall3 (fun _ _ c => P c) l1 l2 l3 -> Forall P l3.
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; tauto.
Qed.

Lemma Forall3_unselect1 :
  forall A B C (P : A -> Prop) (R : A -> B -> C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall P l1 -> Forall3 R l1 l2 l3 -> Forall3 (fun a _ _ => P a) l1 l2 l3.
Proof.
  intros A B C P R l1 l2 l3 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.

Lemma Forall3_unselect2 :
  forall A B C (P : B -> Prop) (R : A -> B -> C -> Prop) (l1 : list A) (l2 : list B) (l3 : list C), Forall P l2 -> Forall3 R l1 l2 l3 -> Forall3 (fun _ b _ => P b) l1 l2 l3.
Proof.
  intros A B C P R l1 l2 l3 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.

Lemma Forall3_from_Forall2 :
  forall (A B C : Type) (P : A -> B -> Prop) (Q : A -> C -> Prop) l1 l2 l3,
    Forall2 P l1 l2 -> Forall2 Q l1 l3 -> Forall3 (fun x y z => P x y /\ Q x z) l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H1. revert l3; induction H1; intros l3 H2; inversion H2; subst.
  - constructor.
  - constructor.
    + split; assumption.
    + apply IHForall2. assumption.
Qed.

Lemma Forall3_Exists_2_transparent :
  forall (A B C : Type) (P : A -> B -> C -> Prop) (Q : B -> Prop) (R : Prop) L1 L2 L3 (H : forall x y z, P x y z -> Q y -> R), Forall3 P L1 L2 L3 -> Exists Q L2 -> R.
Proof.
  intros A B C P Q R L1 L2 L3 H HP HQ; induction HP.
  - inversion HQ.
  - inversion HQ; subst; [eapply H; eassumption|].
    apply IHHP, H2.
Defined.

Lemma Forall3_impl_In :
  forall (A B C : Type) (P Q : A -> B -> C -> Prop) L1 L2 L3,
    (forall x y z, In x L1 -> In y L2 -> In z L3 -> P x y z -> Q x y z) -> Forall3 P L1 L2 L3 -> Forall3 Q L1 L2 L3.
Proof.
  intros A B C P Q L1 L2 L3 H Hforall. induction Hforall.
  - constructor.
  - econstructor.
    + apply H; try (left; reflexivity). assumption.
    + apply IHHforall.
      intros; eapply H; try right; assumption.
Qed.

Lemma Forall3_map3 :
  forall (A B C D : Type) (P : A -> B -> D -> Prop) (f : C -> D) (L1 : list A) (L2 : list B) (L3 : list C), Forall3 P L1 L2 (map f L3) <-> Forall3 (fun x y z => P x y (f z)) L1 L2 L3.
Proof.
  intros A B C D P f L1 L2 L3; split; intros H.
  - remember (map f L3) as L4. revert L3 HeqL4.
    induction H; intros; destruct L3; subst; simpl in *; try congruence; constructor.
    + injection HeqL4 as HeqL4; subst. assumption.
    + injection HeqL4 as HeqL4; subst. apply IHForall3. reflexivity.
  - induction H; constructor; assumption.
Qed.

Lemma Forall2_select121 :
  forall (A B : Type) (P : A -> B -> A -> Prop) (L1 : list A) (L2 : list B), Forall2 (fun x y => P x y x) L1 L2 -> Forall3 P L1 L2 L1.
Proof.
  intros A B P L1 L2 H; induction H; constructor; assumption.
Qed.

Lemma Forall2_select12combine :
  forall (A B : Type) (P : A -> B -> A * B -> Prop) (L1 : list A) (L2 : list B), Forall2 (fun x y => P x y (x, y)) L1 L2 -> Forall3 P L1 L2 (combine L1 L2).
Proof.
  intros A B P L1 L2 H; induction H; constructor; assumption.
Qed.

Lemma Forall3_combine23_3 :
  forall (A B C : Type) (P : A -> B -> B * C -> Prop) l1 l2 l3, Forall3 (fun x y z => P x y (y, z)) l1 l2 l3 -> Forall3 P l1 l2 (combine l2 l3).
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; assumption.
Qed.

Lemma Forall3_select1 :
  forall (A B C : Type) (P : A -> Prop) l1 (l2 : list B) (l3 : list C), Forall3 (fun x y z => P x) l1 l2 l3 -> Forall P l1.
Proof.
  intros A B C P l1 l2 l3 H; induction H; simpl in *; constructor; assumption.
Qed.


Inductive Forall4 {A B C D : Type} (R : A -> B -> C -> D -> Prop) : list A -> list B -> list C -> list D -> Prop :=
| Forall4_nil : Forall4 R nil nil nil nil
| Forall4_cons : forall x y z w l1 l2 l3 l4, R x y z w -> Forall4 R l1 l2 l3 l4 -> Forall4 R (x :: l1) (y :: l2) (z :: l3) (w :: l4).

Lemma Forall4_impl :
  forall (A B C D : Type) (P Q : A -> B -> C -> D -> Prop) l1 l2 l3 l4,
    (forall x y z w, P x y z w -> Q x y z w) -> Forall4 P l1 l2 l3 l4 -> Forall4 Q l1 l2 l3 l4.
Proof.
  intros A B C D P Q l1 l2 l3 l4 HPQ H; induction H; constructor; [apply HPQ|]; assumption.
Qed.

Lemma Forall4_select123 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y z) l1 l2 l3 l4 -> Forall3 R l1 l2 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select124 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y w) l1 l2 l3 l4 -> Forall3 R l1 l2 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select134 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x z w) l1 l2 l3 l4 -> Forall3 R l1 l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select234 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y z w) l1 l2 l3 l4 -> Forall3 R l2 l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select12 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x y) l1 l2 l3 l4 -> Forall2 R l1 l2.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select13 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x z) l1 l2 l3 l4 -> Forall2 R l1 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select14 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R x w) l1 l2 l3 l4 -> Forall2 R l1 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select23 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y z) l1 l2 l3 l4 -> Forall2 R l2 l3.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select24 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R y w) l1 l2 l3 l4 -> Forall2 R l2 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.

Lemma Forall4_select34 :
  forall A B C D R (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D),
    Forall4 (fun x y z w => R z w) l1 l2 l3 l4 -> Forall2 R l3 l4.
Proof.
  intros A B C D R l1 l2 l3 l4 H; induction H; constructor; auto.
Qed.


Lemma Forall_exists_Forall2 :
  forall (A B : Type) (P : A -> B -> Prop) (l1 : list A),
    Forall (fun x => exists y, P x y) l1 -> exists l2, Forall2 P l1 l2.
Proof.
  intros A B P l1 H; induction H.
  - exists nil. constructor.
  - destruct IHForall as [l2 IH].
    destruct H as [y Hy].
    exists (y :: l2). constructor; assumption.
Qed.

Lemma Forall2_exists_Forall3 :
  forall (A B C : Type) (P : A -> B -> C -> Prop) (l1 : list A) (l2 : list B),
    Forall2 (fun x y => exists z, P x y z) l1 l2 -> exists l3, Forall3 P l1 l2 l3.
Proof.
  intros A B C P l1 l2 H; induction H.
  - exists nil. constructor.
  - destruct IHForall2 as [l3 IH].
    destruct H as [z Hz].
    exists (z :: l3). constructor; assumption.
Qed.

Lemma Forall3_exists_Forall4 :
  forall (A B C D: Type) (P : A -> B -> C -> D -> Prop) (l1 : list A) (l2 : list B) (l3 : list C),
    Forall3 (fun x y z => exists w, P x y z w) l1 l2 l3 -> exists l4, Forall4 P l1 l2 l3 l4.
Proof.
  intros A B C D P l1 l2 l3 H; induction H.
  - exists nil. constructor.
  - destruct IHForall3 as [l4 IH].
    destruct H as [w Hw].
    exists (w :: l4). constructor; assumption.
Qed.

Lemma Forall4_and :
  forall A B C D (P Q : A -> B -> C -> D -> Prop) l1 l2 l3 l4, Forall4 P l1 l2 l3 l4 -> Forall4 Q l1 l2 l3 l4 -> Forall4 (fun a b c d => P a b c d /\ Q a b c d) l1 l2 l3 l4.
Proof.
  intros A B C D P Q l1 l2 l3 l4 H1 H2; induction H1; simpl in *; inversion H2; subst; constructor; tauto.
Qed.

Lemma Forall4_unselect123 :
  forall A B C D (P : A -> B -> C -> Prop) (R : A -> B -> C -> D -> Prop) (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D), Forall3 P l1 l2 l3 -> Forall4 R l1 l2 l3 l4 -> Forall4 (fun a b c _ => P a b c) l1 l2 l3 l4.
Proof.
  intros A B C D P R l1 l2 l3 l4 H1 H2; induction H2; simpl in *; inversion H1; subst; constructor; tauto.
Qed.




(** Forall using quantifiers *)
Lemma forall_cons_iff :
  forall (A : Type) (P : A -> Prop) a L, (forall x, x \in (a :: L) -> P x) <-> P a /\ (forall x, x \in L -> P x).
Proof.
  intros. simpl. firstorder congruence.
Qed.

Lemma forall_map :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) L, (forall x, x \in map f L -> P x) <-> (forall x, x \in L -> P (f x)).
Proof.
  intros. rewrite <- !Forall_forall. rewrite Forall_map. reflexivity.
Qed.

Lemma forall_pair :
  forall (A B : Type) (P : A -> B -> Prop) L, (forall x y, (x, y) \in L -> P x y) <-> (forall xy, xy \in L -> P (fst xy) (snd xy)).
Proof.
  intros. split; [|firstorder].
  intros H [x y] ?; firstorder.
Qed.

Lemma forall_pair2 :
  forall (A B : Type) (P : A * B -> Prop) L, (forall xy, xy \in L -> P xy) <-> (forall x y, (x, y) \in L -> P (x, y)).
Proof.
  intros. split; [firstorder|]. intros H [x y] ?; firstorder.
Qed.

(** List inclusion and equivalence *)

Definition list_inc {A : Type} (L1 L2 : list A) := forall x, In x L1 -> In x L2.
Definition list_same {A : Type} (L1 L2 : list A) := forall x, In x L1 <-> In x L2.

Notation "L1 '\subseteq' L2" := (list_inc L1 L2) (at level 70, only parsing).
Notation "L1 '⊆' L2" := (list_inc L1 L2) (at level 70).
Notation "L1 '==' L2" := (list_same L1 L2) (at level 70).

Ltac prove_list_inc := (let x := fresh "x" in intros x; simpl; try repeat (rewrite in_app_iff; simpl); tauto).
Ltac prove_list_same := (let x := fresh "x" in intros x; simpl; try repeat (rewrite in_app_iff; simpl); tauto).


Lemma list_inc_trans :
  forall A (L1 L2 L3 : list A), L1 \subseteq L2 -> L2 \subseteq L3 -> L1 \subseteq L3.
Proof.
  intros; unfold list_inc in *; firstorder.
Qed.

Lemma list_inc_app_left :
  forall A (L1 L2 L3 : list A), list_inc (L1 ++ L2) L3 <-> list_inc L1 L3 /\ list_inc L2 L3.
Proof.
  intros; unfold list_inc in *.
  split; [intros H; split; intros x Hx; apply H; rewrite in_app_iff; tauto|].
  intros [H1 H2] x Hx; rewrite in_app_iff in Hx; firstorder.
Qed.

Lemma list_same_inc_iff :
  forall A (L1 L2 : list A), list_same L1 L2 <-> list_inc L1 L2 /\ list_inc L2 L1.
Proof.
  intros; unfold list_same, list_inc. firstorder.
Qed.

Lemma list_same_inc :
  forall A (L1 L2 : list A), list_same L1 L2 -> list_inc L1 L2.
Proof.
  intros. rewrite list_same_inc_iff in H. tauto.
Qed.


Global Instance list_inc_Reflexive {A : Type} : Reflexive (@list_inc A).
Proof.
  firstorder.
Qed.

Global Instance list_inc_Transitive {A : Type} : Transitive (@list_inc A).
Proof.
  firstorder.
Qed.

Global Instance list_inc_PreOrdered {A : Type} : PreOrder (@list_inc A).
Proof.
  split; auto with typeclass_instances.
Qed.

Global Instance list_same_Reflexive {A : Type} : Reflexive (@list_same A).
Proof.
  firstorder.
Qed.

Global Instance list_same_Transitive {A : Type} : Transitive (@list_same A).
Proof.
  firstorder.
Qed.

Global Instance list_same_Symmetric {A : Type} : Symmetric (@list_same A).
Proof.
  firstorder.
Qed.

Global Instance list_same_Equivalence {A : Type} : Equivalence (@list_same A).
Proof.
  split; auto with typeclass_instances.
Qed.

Global Instance app_list_inc_Proper {A : Type} : Proper (list_inc ++> list_inc ++> list_inc) (@app A).
Proof.
  intros L1 L2 H12 L3 L4 H34.
  rewrite list_inc_app_left, H12, H34.
  split; prove_list_inc.
Qed.

Global Instance In_list_inc_Proper {A : Type} : Proper (eq ==> list_inc ++> Basics.impl) (@In A).
Proof.
  intros x1 x2 -> L1 L2 HL.
  firstorder.
Qed.

Global Instance app_list_same_Proper {A : Type} : Proper (list_same ==> list_same ==> list_same) (@app A).
Proof.
  intros L1 L2 H12 L3 L4 H34.
  rewrite list_same_inc_iff in *.
  split; apply app_list_inc_Proper; tauto.
Qed.

Global Instance In_list_same_Proper {A : Type} : Proper (eq ==> list_same ==> iff) (@In A).
Proof.
  intros x1 x2 -> L1 L2 HL.
  apply HL.
Qed.

Global Instance list_inc_list_same_Proper {A : Type} : Proper (list_same ==> list_same ==> iff) (@list_inc A).
Proof.
  intros L1 L2 H12 L3 L4 H34; split; intros H x; specialize (H12 x); specialize (H34 x); specialize (H x); tauto.
Qed.

Lemma one_elem_list_inc :
  forall A (x : A) L, x :: nil \subseteq L <-> x \in L.
Proof.
  intros x L. split.
  - intros H. apply H. simpl. tauto.
  - intros H y Hy. simpl in Hy; destruct Hy as [Hy | []]. subst. assumption.
Qed.

Lemma list_inc_cons_left :
  forall A L1 L2 (x : A), x :: L1 \subseteq L2 <-> x \in L2 /\ L1 \subseteq L2.
Proof.
  intros. rewrite list_inc_app_left with (L1 := x :: nil) (L2 := L1).
  rewrite one_elem_list_inc. reflexivity.
Qed.

Global Instance list_inc_cons_Proper {A : Type} : Proper (eq ==> list_inc ==> list_inc) (@cons A).
Proof.
  intros z1 z2 -> e1 e2 H12 x H. simpl in *. specialize (H12 x). tauto.
Qed.

(** List concatenation *)
Lemma concat_In :
  forall (A : Type) (L : list (list A)) x, In x (concat L) <-> exists l, In x l /\ In l L.
Proof.
  intros A L x. induction L.
  - simpl. firstorder.
  - simpl. rewrite in_app_iff.
    split.
    + intros [H | H]; [|firstorder]. exists a. tauto.
    + intros (l & H1 & [H2 | H2]); [subst; tauto|].
      right. apply IHL. exists l. tauto.
Qed.

Lemma concat_map_In :
  forall (A B : Type) (f : A -> list B) L x, In x (concat (map f L)) <-> exists u, In x (f u) /\ In u L.
Proof.
  intros. rewrite concat_In. split.
  - intros (l & Hx & Hl). rewrite in_map_iff in Hl. destruct Hl as (u & <- & Hu); exists u; split; assumption.
  - intros (u & Hx & Hu). exists (f u). split; [assumption|apply in_map; assumption].
Qed.

Lemma concat_incl :
  forall A (L : list (list A)) L2, concat L \subseteq L2 <-> Forall (fun L3 => L3 \subseteq L2) L.
Proof.
  induction L.
  - intros L2. simpl. split.
    + intros. constructor.
    + intros _ y Hy. simpl in Hy. tauto.
  - intros L2. simpl. rewrite list_inc_app_left. rewrite Forall_cons_iff. f_equiv. apply IHL.
Qed.



(** Induction on length of a list *)
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

(** Smallest integer above all others in a list *)

Fixpoint smallest_above l :=
  match l with
  | nil => 0
  | a :: l => Nat.max (smallest_above l) (S a)
  end.

Lemma smallest_above_gt :
  forall l x, x < smallest_above l <-> exists y, x <= y /\ In y l.
Proof.
  induction l.
  - intros; simpl in *. split; [lia|]. intros (y & Hy1 & Hy2); tauto.
  - intros x. simpl. rewrite Nat.max_lt_iff.
    split.
    + intros [Hx | Hx]; [|exists a; simpl; split; [lia|tauto]].
      apply IHl in Hx. destruct Hx as [y Hy]; exists y; simpl; tauto.
    + intros (y & Hy1 & [Hy2 | Hy2]); [subst; lia|].
      left. apply IHl. exists y. tauto.
Qed.

Lemma smallest_above_map_gt :
  forall {A : Type} (f : A -> nat) l x, x < smallest_above (map f l) <-> exists y, x <= f y /\ In y l.
Proof.
  intros. rewrite smallest_above_gt. split.
  - intros (y & Hy1 & Hy2). rewrite in_map_iff in Hy2. destruct Hy2 as (z & <- & Hz). exists z. tauto.
  - intros (y & Hy1 & Hy2). exists (f y). rewrite in_map_iff. split; [assumption|].
    exists y. tauto.
Qed.

Lemma smallest_above_le :
  forall l x, smallest_above l <= x <-> (forall y, In y l -> y < x).
Proof.
  intros l x. rewrite Nat.le_ngt, smallest_above_gt.
  split; intros H.
  - intros y Hy. rewrite Nat.lt_nge. intros Hy2. apply H. exists y. tauto.
  - intros (y & Hy1 & Hy2). specialize (H y Hy2). lia.
Qed.

Lemma smallest_above_map_le :
  forall {A : Type} (f : A -> nat) l x, smallest_above (map f l) <= x <-> (forall y, In y l -> f y < x).
Proof.
  intros. rewrite smallest_above_le. split.
  - intros H y Hy. apply H. rewrite in_map_iff. exists y; tauto.
  - intros H y Hy. rewrite in_map_iff in Hy. destruct Hy as (z & <- & Hz). apply H. assumption.
Qed.

Lemma smallest_above_app :
  forall L1 L2, smallest_above (L1 ++ L2) = Nat.max (smallest_above L1) (smallest_above L2).
Proof.
  induction L1.
  - intros L2. simpl. reflexivity.
  - intros L2. simpl.
    rewrite IHL1. lia.
Qed.


(** Ordered sublists of a list *)

Inductive sublist_ordered {A : Type} : list A -> list A -> Prop :=
| sublist_ordered_nil : sublist_ordered nil nil
| sublist_ordered_cons_both : forall x L1 L2, sublist_ordered L1 L2 -> sublist_ordered (x :: L1) (x :: L2)
| sublist_ordered_cons_one : forall x L1 L2, sublist_ordered L1 L2 -> sublist_ordered L1 (x :: L2).

Lemma sublist_ordered_map :
  forall (A B : Type) (f : A -> B) L1 L2, sublist_ordered L1 L2 -> sublist_ordered (map f L1) (map f L2).
Proof.
  intros A B f L1 L2 H. induction H.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma sublist_ordered_map_assq :
  forall (A B C : Type) (f : A -> B -> C) L1 L2, sublist_ordered L1 L2 -> sublist_ordered (map_assq f L1) (map_assq f L2).
Proof.
  intros. apply sublist_ordered_map. assumption.
Qed.

Lemma sublist_ordered_filter :
  forall (A : Type) (P : A -> bool) L, sublist_ordered (filter P L) L.
Proof.
  intros A P L. induction L.
  - constructor.
  - simpl. destruct (P a); constructor; assumption.
Qed.

(** List update *)

Fixpoint update {A : Type} (l : list A) (k : nat) (x : A) : list A :=
  match l with
  | nil => nil
  | y :: l =>
    match k with
    | O => x :: l
    | S k => y :: update l k x
    end
  end.
Arguments update {A} _ _ _ : simpl nomatch.

Lemma nth_error_update :
  forall (A : Type) (l : list A) k x y, nth_error l k = Some x -> nth_error (update l k y) k = Some y.
Proof.
  induction l; intros [|k] x y; simpl in *; intros; try congruence.
  eapply IHl; eassumption.
Qed.

Lemma nth_error_update2 :
  forall (A : Type) (l : list A) k x, nth_error (update l k x) k = match nth_error l k with Some _ => Some x | None => None end.
Proof.
  induction l; intros [|k] x; simpl in *; intros; try congruence.
  apply IHl.
Qed.

Lemma nth_error_update3 :
  forall (A : Type) (l : list A) k1 k2 x, k1 <> k2 -> nth_error (update l k1 x) k2 = nth_error l k2.
Proof.
  induction l; intros [|k1] [|k2] x H; simpl in *; try congruence.
  apply IHl; congruence.
Qed.

Lemma update_length :
  forall {A : Type} (l : list A) k x, length (update l k x) = length l.
Proof.
  induction l; intros [|k] x; simpl in *; congruence.
Qed.

Lemma update_case :
  forall {A : Type} (l : list A) k1 k2 x, (k1 = k2 /\ nth_error (update l k1 x) k2 = Some x) \/ (nth_error (update l k1 x) k2 = nth_error l k2).
Proof.
  intros A l k1 k2 x.
  destruct (Nat.eq_dec k1 k2).
  + subst. rewrite nth_error_update2.
    destruct nth_error; tauto.
  + rewrite nth_error_update3 by assumption. tauto.
Qed.

Lemma nth_error_update_None :
  forall (A : Type) l k1 k2 (x : A), nth_error l k1 = None -> nth_error (update l k2 x) k1 = None.
Proof.
  intros A l; induction l; intros k1 k2 x H; destruct k1; destruct k2; simpl in *; try congruence.
  apply IHl. assumption.
Qed.


Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n => split; [|splits n]
  end.


Inductive deep_flag := shallow | deep.
Lemma deep_flag_eq_dec : forall (df1 df2 : deep_flag), { df1 = df2 } + { df1 <> df2 }.
Proof.
  intros [|] [|]; solve [left; reflexivity | right; discriminate].
Defined.

Ltac unexistT :=
  repeat match goal with
           [ H : @existT deep_flag _ _ _ = @existT deep_flag _ _ _ |- _ ] =>
           apply inj_pair2_eq_dec in H; [|apply deep_flag_eq_dec]
         end.

Definition option_default {A : Type} (o : option A) (d : A) :=
  match o with Some x => x | None => d end.

Lemma option_map_id : forall (A : Type) (x : option A), option_map id x = x.
Proof.
  intros A [x|]; reflexivity.
Qed.

Definition respectful {A : Type} (R : A -> A -> Prop) (f : A -> A) := forall x y, R x y -> R (f x) (f y).

Fixpoint list_sum l := match l with nil => 0 | x :: l => x + list_sum l end.

Ltac ereplace t :=
  let tmp := fresh "_tmp" in
  let typ := type of t in
  evar (tmp : typ);
  replace t with tmp; unfold tmp.



Lemma and_left :
  forall (A B : Prop), A -> (A -> B) -> A /\ B.
Proof.
  intros A B HA HB; split; [apply HA|apply HB, HA].
Qed.

Lemma and_right :
  forall (A B : Prop), (B -> A) -> B -> A /\ B.
Proof.
  intros A B HA HB; split; [apply HA, HB|apply HB].
Qed.

Ltac and_left := apply and_left.
Ltac and_right := apply and_right.
Tactic Notation "and_left" "as" simple_intropattern(p) := and_left; [|intros p].
Tactic Notation "and_right" "as" simple_intropattern(p) := and_right; [intros p|].

Ltac dedup x :=
  refine ((fun (x : _) => _) _).

Lemma seq_shiftn :
  forall n len a, map (fun k => k + n) (seq a len) = seq (a + n) len.
Proof.
  intros n; induction len; intros a; simpl in *; f_equal.
  apply IHlen.
Qed.

Lemma seq_is_shiftn :
  forall a len, seq a len = map (fun k => k + a) (seq 0 len).
Proof.
  intros a len; rewrite seq_shiftn; reflexivity.
Qed.

Lemma seq_nth_error :
  forall len a n, n < len -> nth_error (seq a len) n = Some (a + n).
Proof.
  induction len; intros a [|n] Hn; simpl in *; try lia.
  - f_equal; lia.
  - rewrite IHlen; [f_equal|]; lia.
Qed.


Lemma NoDup_app :
  forall (A : Type) (l1 l2 : list  A), NoDup l1 -> NoDup l2 -> Forall (fun x => x \notin l2) l1 -> NoDup (l1 ++ l2).
Proof.
  induction l1; intros l2 Hnd1 Hnd2 Hdisj; inversion Hnd1; subst; inversion Hdisj; subst; simpl in *.
  - assumption.
  - constructor.
    + rewrite in_app_iff; tauto.
    + apply IHl1; assumption.
Qed.


Inductive reflect (P : Prop) : bool -> Prop :=
| reflect_true : P -> reflect P true
| reflect_false : ~ P -> reflect P false.

Lemma reflect_iff :
  forall P Q b, P <-> Q -> reflect P b <-> reflect Q b.
Proof.
  intros P Q H; split; intros H1; inversion H1; subst; constructor; tauto.
Qed.
