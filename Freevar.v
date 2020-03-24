Require Import List.
Require Import Arith.
Require Import Psatz.
Require Import Misc.
Require Import Setoid.
Require Import Morphisms.

(* Free variables and fresh name generator *)

Definition freevar := nat.
Lemma freevar_eq_dec : forall (v1 v2 : freevar), { v1 = v2 } + { v1 <> v2 }.
Proof.
  apply Nat.eq_dec.
Qed.
Lemma fresh : forall (L : list freevar), { x | x \notin L }.
Proof.
  intros L.
  assert (H : { x | forall y, y \in L -> y < x }).
  - induction L.
    + exists 0. intros y [].
    + destruct IHL as [x IH].
      exists (Nat.max (S a) x); unfold freevar in *.
      intros y [Hy | Hy]; [|specialize (IH y Hy)]; lia.
  - destruct H as [x Hx]; exists x.
    intros H; apply Hx in H; lia.
Qed.
Global Opaque freevar.

Notation "'forall' x '∉' L , P" := (forall (x : freevar), ~ In x L -> P) (at level 200, x ident, only printing).

Tactic Notation "pick" ident(x) "\notin" constr(L) "as" ident(H) := destruct (fresh L) as [x H].
Tactic Notation "pick" ident(x) "\notin" constr(L) := (let H := fresh "H" in pick x \notin L as H).
Tactic Notation "pick" ident(x) "∉" constr(L) "as" ident(H) := destruct (fresh L) as [x H].
Tactic Notation "pick" ident(x) "∉" constr(L) := (let H := fresh "H" in pick x \notin L as H).


Definition list_remove x L := filter (fun y => if freevar_eq_dec x y then false else true) L.
Lemma list_remove_correct :
  forall x y L, y \in list_remove x L <-> y \in L /\ x <> y.
Proof.
  intros x y L.
  unfold list_remove. rewrite filter_In.
  destruct freevar_eq_dec; intuition congruence.
Qed.

Lemma list_remove_app :
  forall x L1 L2, list_remove x (L1 ++ L2) = list_remove x L1 ++ list_remove x L2.
Proof.
  intros. unfold list_remove. induction L1.
  - reflexivity.
  - simpl. destruct freevar_eq_dec; simpl; rewrite IHL1; reflexivity.
Qed.

Definition list_diff (L1 L2 : list freevar) := filter (fun x => if in_dec freevar_eq_dec x L2 then false else true) L1.

Lemma list_diff_In_iff :
  forall L1 L2 x, x \in list_diff L1 L2 <-> x \in L1 /\ x \notin L2.
Proof.
  intros L1 L2 x. unfold list_diff.
  rewrite filter_In.
  destruct in_dec; intuition congruence.
Qed.

Global Instance list_diff_inc_Proper : Proper (list_inc ++> list_inc --> list_inc) list_diff.
Proof.
  intros L1 L2 H12 L3 L4 H34 x.
  rewrite !list_diff_In_iff.
  rewrite H12. rewrite H34.
  tauto.
Qed.

Global Instance list_diff_same_Proper : Proper (list_same ==> list_same ==> list_same) list_diff.
Proof.
  intros L1 L2 H12 L3 L4 H34.
  rewrite list_same_inc_iff in *.
  split; apply list_diff_inc_Proper; tauto.
Qed.
