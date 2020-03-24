(* Transitive reflexive closure *)

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star R x x
| star_step : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_compose :
  forall (A : Type) (R : A -> A -> Prop) x y z, star R x y -> star R y z -> star R x z.
Proof.
  intros A R x y z H. induction H.
  - intros; assumption.
  - intros; econstructor; [eassumption | firstorder].
Qed.

Lemma star_map_impl :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B),
    (forall x y, RA x y -> RB (f x) (f y)) -> forall x y, star RA x y -> star RB (f x) (f y).
Proof.
  intros A B RA RB f HR x y H. induction H.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma star_star :
  forall (A : Type) (R : A -> A -> Prop), forall x y, star (star R) x y -> star R x y.
Proof.
  intros A R x y H. induction H.
  - constructor.
  - eapply star_compose; eauto.
Qed.

Lemma star_induction_rev :
  forall {A : Type} (R : A -> A -> Prop) (P : A -> Prop) (x : A),
    P x -> (forall y z, P y -> R y z -> P z) -> (forall y, star R x y -> P y).
Proof.
  intros A R P x HPx HPind y Hy. revert HPx.
  induction Hy; firstorder.
Qed.

Lemma star_same :
  forall (A : Type) (R : A -> A -> Prop) t1 t2, t1 = t2 -> star R t1 t2.
Proof.
  intros A R t1 t2 ->. constructor.
Qed.
