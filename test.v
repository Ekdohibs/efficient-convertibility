Inductive test (rec : nat -> nat -> Prop) : nat -> nat -> Prop :=
| test_O : test rec O O
| test_SS : forall n m, rec n m -> test rec (S (S n)) (S (S m)).

Inductive t : nat -> nat -> Prop :=
| t_intro : forall n m, test t n m -> t n m.

Definition preserved (P : nat -> nat -> Prop) :=
  forall n m, test (fun k1 k2 => t k1 k2 /\ P k1 k2) n m -> P n m.
Definition preserved_with_inv (P P2 : nat -> nat -> Prop) :=
  forall n m, test (fun k1 k2 => t k1 k2 /\ P k1 k2 /\ P2 k1 k2) n m -> P n m.
Definition preserved_down (P : nat -> nat -> Prop) :=
  forall n m H, test (fun k1 k2 => t k1 k2 /\ H k1 k2) n m -> P n m -> test (fun k1 k2 => t k1 k2 /\ H k1 k2 /\ P k1 k2) n m.

Lemma test_map : forall (P1 P2 : nat -> nat -> Prop), (forall x y, P1 x y -> P2 x y) -> forall x y, test P1 x y -> test P2 x y.
Proof.
  intros P1 P2 H x y Hxy; destruct Hxy; constructor; try assumption; apply H; assumption.
Defined.

Lemma preserved_rec :
  forall P, preserved P -> forall k1 k2, t k1 k2 -> P k1 k2.
Proof.
  intros P HP. fix H 3. intros k1 k2 Hk.
  destruct Hk as [n m Hnm].
  apply test_map with (P2 := fun k1 k2 => t k1 k2 /\ P k1 k2) in Hnm.
  - apply HP in Hnm. assumption.
  - intros x y Hxy. split; [assumption|apply H; assumption].
Qed.

Lemma preserved_with_inv_rec :
  forall P P2, preserved_down P2 -> preserved_with_inv P P2 -> forall k1 k2, t k1 k2 -> P2 k1 k2 -> P k1 k2.
Proof.
  intros P P2 H1 H2. refine (preserved_rec (fun k1 k2 => P2 k1 k2 -> P k1 k2) _).
  intros n m H3 H4. apply H2.
  apply test_map with (P1 := fun k1 k2 => t k1 k2 /\ (P2 k1 k2 -> P k1 k2) /\ P2 k1 k2); [intros; tauto|].
  apply H1; assumption.
Qed.

Lemma test_preserved_down :
  preserved_down (fun k1 k2 => k1 = k2).
Proof.
  intros n m X H1 H2. inversion H1; subst; constructor.
  split; [|split]; try tauto. congruence.
Qed.

Lemma h : forall n1 n2, t n1 -> t n2 -> t (n1 + n2).
Proof.
  intros n1 n2 H1 H2. revert n1 H1; apply preserved_rec.
  intros n1 Hn1. destruct Hn1.
  - assumption.
  - simpl. constructor. constructor. tauto.
Qed.
