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

Lemma freevar_eq_dec_eq :
  forall v1 v2 (P : v1 = v2), freevar_eq_dec v1 v2 = left P.
Proof.
  intros v1 v2 H. subst. destruct freevar_eq_dec; [|exfalso; tauto].
  f_equal. erewrite UIP_nat. reflexivity.
Qed.

Lemma freevar_eq_dec_eq_ifte :
  forall (A : Type) (ifso ifelse : A) v1 v2, v1 = v2 -> (if freevar_eq_dec v1 v2 then ifso else ifelse) = ifso.
Proof.
  intros. destruct freevar_eq_dec; tauto.
Qed.

Lemma freevar_eq_dec_neq_ifte :
  forall (A : Type) (ifso ifelse : A) v1 v2, v1 <> v2 -> (if freevar_eq_dec v1 v2 then ifso else ifelse) = ifelse.
Proof.
  intros. destruct freevar_eq_dec; tauto.
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

Tactic Notation "pick" ident(x) "\notin" uconstr(L) "as" ident(H) := refine (match (fresh L) with exist _ x H => _ end).
Tactic Notation "pick" ident(x) "\notin" uconstr(L) := (let H := fresh "H" in pick x \notin L as H).
Tactic Notation "pick" ident(x) "∉" uconstr(L) "as" ident(H) := (pick x \notin L as H).
Tactic Notation "pick" ident(x) "∉" uconstr(L) := (let H := fresh "H" in pick x \notin L as H).



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



Inductive distinct : list freevar -> nat -> list freevar -> Prop :=
| distinct_nil : forall L, distinct L 0 nil
| distinct_cons : forall L1 L2 x n, x \notin L1 -> distinct (x :: L1) n L2 -> distinct L1 (S n) (x :: L2).

Fixpoint fresh_list L n :=
  match n with
  | O => nil
  | S n => let x := proj1_sig (fresh L) in x :: fresh_list (x :: L) n
  end.

Lemma fresh_list_distinct :
  forall n L, distinct L n (fresh_list L n).
Proof.
  induction n as [|n]; intros L; simpl.
  - constructor.
  - constructor.
    + destruct fresh. simpl. assumption.
    + apply IHn.
Qed.

Lemma distinct_distinct :
  forall n x L1 L2, distinct L1 n L2 -> x \in L1 -> x \in L2 -> False.
Proof.
  intros n x L1 L2 H. induction H.
  - simpl. tauto.
  - simpl in *. intros H1 [-> | H2]; tauto.
Qed.

Lemma distinct_incl :
  forall n L1 L2 L, L2 \subseteq L1 -> distinct L1 n L -> distinct L2 n L.
Proof.
  intros n L1 L2 L Hinc H. revert L2 Hinc. induction H; intros L3 Hinc.
  - constructor.
  - constructor.
    + rewrite Hinc. assumption.
    + apply IHdistinct. rewrite Hinc. prove_list_inc.
Qed.

Lemma distinct_length :
  forall n L1 L2, distinct L1 n L2 -> length L2 = n.
Proof.
  intros n L1 L2 H. induction H.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma notin_app_iff :
  forall (x : freevar) L1 L2, x \notin L1 ++ L2 <-> x \notin L1 /\ x \notin L2.
Proof.
  intros. rewrite in_app_iff. tauto.
Qed.

Lemma notin_app_l :
  forall (x : freevar) L1 L2, x \notin L1 ++ L2 -> x \notin L1.
Proof.
  intros. rewrite notin_app_iff in *. tauto.
Qed.

Lemma notin_app_r :
  forall (x : freevar) L1 L2, x \notin L1 ++ L2 -> x \notin L2.
Proof.
  intros. rewrite notin_app_iff in *. tauto.
Qed.

Lemma notin_cons1 :
  forall (x y : freevar) L, x \notin y :: L -> x <> y.
Proof.
  intros ? ? ? ? ->. simpl in *. tauto.
Qed.

Lemma notin_cons2 :
  forall (x y : freevar) L, x \notin y :: L -> y <> x.
Proof.
  intros ? ? ? ? ->. simpl in *. tauto.
Qed.

Lemma notin_one :
  forall (x y : freevar), y <> x -> x \notin (y :: nil).
Proof.
  intros. simpl. tauto.
Qed.

Lemma qed_opaque_helper {A : Type} (x : A) : { y | y = x }.
Proof.
  exists x. reflexivity.
Qed.
Definition qed_opaque {A : Type} (x : A) : A := proj1_sig (qed_opaque_helper x).
Definition qed_opaque_eq (A : Type) (x : A) : qed_opaque x = x := proj2_sig (qed_opaque_helper x).
Global Opaque qed_opaque qed_opaque_eq.

Definition Bound (L : list freevar) : list freevar := qed_opaque L.
Definition Bound_eq (L : list freevar) : Bound L = L := qed_opaque_eq _ L.
Global Opaque Bound.

Ltac bound := (let L := fresh "L" in evar (L : list freevar); let r := constr:(Bound L) in subst L; exact r).

Ltac use_fresh_aux x L HxL :=
  let L := (eval hnf in L) in
  lazymatch L with
  | ?L1 ++ ?L2 => use_fresh_aux x L2 (notin_app_r x L1 L2 HxL)
  | ?y :: ?L2 => use_fresh_aux x L2 (notin_app_r x (y :: nil) L2 HxL)
  | _ =>
    match goal with
    | [ |- x \notin ?L2 ] => refine (notin_app_l _ L2 _ HxL)
    | [ |- x \in ?L2 -> False ] => refine (notin_app_l _ L2 _ HxL)
    | [ |- x <> ?y ] => refine (notin_cons1 _ y _ HxL)
    | [ |- ?y <> x ] => refine (notin_cons2 _ y _ HxL)
    | [ |- ?y \notin (x :: nil) ] => refine (notin_one _ _ (notin_cons1 _ y _ HxL))
    | [ H : x \in ?L2 |- _ ] => exfalso; refine (notin_app_l _ L2 _ HxL H)
    | [ H : x = ?y |- _ ] => exfalso; refine (notin_cons1 _ y _ HxL H)
    | [ H : ?y = x |- _ ] => exfalso; refine (notin_cons2 _ y _ HxL H)
    | [ H : ?y \in (x :: nil) |- _ ] => exfalso; refine (notin_one _ _ (notin_cons1 _ y _ HxL) H)
    end
  end.

Ltac use_fresh x :=
  lazymatch goal with
  | [ H : x \notin Bound ?L |- _ ] =>
    use_fresh_aux x L (@eq_ind _ _ (fun L2 => x \notin L2) H _ (Bound_eq L));
    (* Move the list freevar goal to the shelf *)
    lazymatch goal with
    | [ |- list freevar ] => shelve
    end
  | [ H : x \in Bound ?L -> False |- _ ] =>
    use_fresh_aux x L (@eq_ind _ _ (fun L2 => x \notin L2) H _ (Bound_eq L));
    (* Move the list freevar goal to the shelf *)
    lazymatch goal with
    | [ |- list freevar ] => shelve
    end
  end.

Ltac specialize_fresh H x :=
  match type of H with
  | forall y, y \notin ?L -> _ =>
    let H2 := fresh in
    assert (H2 : x \notin L) by use_fresh x;
    specialize (H x H2); clear H2
  end.

Tactic Notation "pick" "fresh" ident(x) "as" ident(H) := pick x \notin (Bound _) as H.
Tactic Notation "pick" "fresh" ident(x) := pick x \notin (Bound _).

Tactic Notation "pickn" constr(n) "distinct" ident(xs) "\notin" uconstr(L) "as" ident(H) :=
  refine ((fun xs (H : distinct L n xs) => _) (fresh_list L n) (fresh_list_distinct n L)).
Tactic Notation "pickn" constr(n) "distinct" ident(xs) "\notin" uconstr(L) :=
  (let H := fresh "H" in pickn n distinct xs \notin L as H).
Tactic Notation "pickn" constr(n) "distinct" ident(xs) "∉" uconstr(L) "as" ident(H) :=
  (pickn n distinct xs \notin L as H).
Tactic Notation "pickn" constr(n) "distinct" ident(xs) "∉" uconstr(L) :=
  (pickn n distinct xs \notin L).

Tactic Notation "pickn" constr(n) "distinct" "fresh" ident(xs) "as" ident(H) :=
  pickn n distinct xs \notin (Bound _) as H.
Tactic Notation "pickn" constr(n) "distinct" "fresh" ident(x) :=
  pickn n distinct xs \notin (Bound _).
