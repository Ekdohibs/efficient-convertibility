
Fixpoint church_from_nat A n f (x : A) :=
  match n with
  | O => x
  | S n => f (church_from_nat A n f x)
  end.

Definition church_10a := Eval compute in church_from_nat nat 10.
Definition church_10b := Eval compute in church_from_nat (nat -> nat) 10.
Definition church_10c := Eval compute in church_from_nat (nat -> nat -> nat) 10.
Definition church_10d := Eval compute in church_from_nat ((nat -> nat -> nat) -> (nat -> nat -> nat)) 10.

Definition church_7a := Eval compute in church_from_nat nat 7.
Definition church_7b := Eval compute in church_from_nat (nat -> nat) 7.
Definition church_7c := Eval compute in church_from_nat (nat -> nat -> nat) 7.
Definition church_7d := Eval compute in church_from_nat ((nat -> nat -> nat) -> (nat -> nat -> nat)) 7.

Time Eval native_compute in (fun (n : nat) => n).
Time Eval native_compute in (fun m n => m n) church_7d church_10c (fun b x y => b y x) (fun x y => x).
Time Eval native_compute in (fun m n => m n) (fun f x => f (f (f (f (f (f (f x))))))) (fun f x => f (f (f (f (f (f (f (f (f (f x)))))))))) (fun b x y => b y x) (fun (x y : nat) => x).
Time Eval native_compute in (fun m n => m n) church_7d (fun f x => f (f (f (f (f (f (f (f (f (f x)))))))))) (fun b x y => b y x) (fun x y => x).
Time Eval native_compute in (fun m n => m n) (fun f x => f (f (f (f (f (f (f x))))))) church_10c (fun b x y => b y x) (fun x y => x).
