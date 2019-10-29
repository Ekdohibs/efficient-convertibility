Definition church := forall (A : Type), (A -> A) -> A -> A.
Definition church_succ (n : church) := fun A f x => n A f (f x).
Fixpoint church_from_nat n : church :=
  match n with
  | O => fun A f x => x
  | S n => church_succ (church_from_nat n)
  end.
Definition church_mul (c1 c2 : church) : church :=
  fun A f x => c1 A (c2 A f) x.
Definition church_pow (c1 c2 : church) : church :=
  fun A => c2 (A -> A) (c1 A).
Definition church_mul_nat (c1 c2 : (nat -> nat) -> nat -> nat) : (nat -> nat) -> nat -> nat :=
  fun f x => c1 (c2 f) x.
Definition church_pow_nat (c1 : (nat -> nat) -> nat -> nat) (c2 : ((nat -> nat) -> (nat -> nat)) -> (nat -> nat) -> (nat -> nat)) :=
  c2 c1.

Definition bool_nat := nat -> nat -> nat.
Definition bool_not_nat (b : bool_nat) : bool_nat := fun x y => b y x.

Definition church_mul_bool (c1 c2 : (bool_nat -> bool_nat) -> bool_nat -> bool_nat) : (bool_nat -> bool_nat) -> bool_nat -> bool_nat :=
  fun f x => c1 (c2 f) x.
Definition church_pow_bool (c1 : (bool_nat -> bool_nat) -> bool_nat -> bool_nat) (c2 : ((bool_nat -> bool_nat) -> (bool_nat -> bool_nat)) -> (bool_nat -> bool_nat) -> (bool_nat -> bool_nat)) :=
  c2 c1.

Definition church_is_even (c : (bool_nat -> bool_nat) -> bool_nat -> bool_nat) : bool_nat :=
  c bool_not_nat (fun x y => x).

Definition church_1000_nat := Eval compute in church_from_nat 1000 nat.
Definition church_10_nat := Eval compute in church_from_nat 10 nat.
Definition church_6_natnat := Eval compute in church_from_nat 6 (nat -> nat).

Definition church_1000_bool := Eval compute in church_from_nat 1000 bool_nat.
Definition church_10_bool := Eval compute in church_from_nat 10 bool_nat.
Definition church_6_boolbool := Eval compute in church_from_nat 6 (bool_nat -> bool_nat).

Fixpoint ff (n : nat) (m : nat) :=
  match n with
  | O => O
  | S n => S (ff n m)
  end.
Eval lazy in (fun (n : nat) => match n with 0 => ff 0 | S n => ff (S n) end).

Time Definition t1 := Eval cbv in church_pow_nat church_10_nat church_6_natnat.
Time Definition t2 := Eval lazy in church_pow_nat church_10_nat church_6_natnat.
Time Definition t3 := Eval vm_compute in church_pow_nat church_10_nat church_6_natnat.
Time Definition t4 := Eval native_compute in church_pow_nat church_10_nat church_6_natnat.

Time Definition t5 := Eval cbv in church_mul_nat church_1000_nat church_1000_nat.
Time Definition t6 := Eval lazy in church_mul_nat church_1000_nat church_1000_nat.
Time Definition t7 := Eval vm_compute in church_mul_nat church_1000_nat church_1000_nat.
Time Definition t8 := Eval native_compute in church_mul_nat church_1000_nat church_1000_nat.

Time Definition t9 := Eval cbv in church_is_even (church_pow_bool church_10_bool church_6_boolbool).
Time Definition t10 := Eval lazy in church_is_even (church_pow_bool church_10_bool church_6_boolbool).
Time Definition t11 := Eval vm_compute in church_is_even (church_pow_bool church_10_bool church_6_boolbool).
Time Definition t12 := Eval native_compute in church_is_even (church_pow_bool church_10_bool church_6_boolbool).

Time Definition t13 := Eval cbv in church_is_even (church_mul_bool church_1000_bool church_1000_bool).
Time Definition t14 := Eval lazy in church_is_even (church_mul_bool church_1000_bool church_1000_bool).
Time Definition t15 := Eval vm_compute in church_is_even (church_mul_bool church_1000_bool church_1000_bool).
Time Definition t16 := Eval native_compute in church_is_even (church_mul_bool church_1000_bool church_1000_bool).
