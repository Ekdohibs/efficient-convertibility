
Inductive out t :=
| out_ret : t -> out t
| out_div : out t.

Arguments out_ret {t} _.
Arguments out_div {t}.

Definition out_map {A B : Type} (f : A -> B) (o : out A) : out B :=
  match o with
  | out_ret x => out_ret (f x)
  | out_div => out_div
  end.

Definition get_out_abort {t1 t2} (o : out t1) : option (out t2) :=
  match o with
  | out_div => Some out_div
  | _ => None
  end.

Lemma get_out_abort_div :
  forall t1 t2 (o1 : out t1) (o2 : out t2), get_out_abort o1 = Some o2 -> o2 = out_div.
Proof.
  intros; destruct o1; simpl in *; congruence.
Qed.

Inductive outM t m :=
| outM_ret : t -> m -> outM t m
| outM_div : outM t m.

Arguments outM_ret {t} {m} _ _.
Arguments outM_div {t} {m}.
