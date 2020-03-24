Require Import List.
Require Import Setoid.
Require Import Morphisms.
Require Import Arith.
Require Import Psatz.

(* List Notations *)

Notation "x '\in' L" := (In x L) (at level 80, only parsing).
Notation "x '\notin' L" := (~ In x L) (at level 80, only parsing).
Notation "x ∈ L" := (x \in L) (at level 80).
Notation "x ∉ L" := (x \notin L) (at level 80).

(* Map for association lists *)

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

(* Theorems on Forall *)

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

(* List inclusion and equivalence *)

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
  firstorder using in_app_iff.
  rewrite in_app_iff in *; firstorder.
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

(* Smallest integer above all others in a list *)

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


(* Ordered sublists of a list *)

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




Ltac splits n :=
  match n with
  | O => fail
  | S O => idtac
  | S ?n => split; [|splits n]
  end.

