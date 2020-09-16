open Format

let print_indn ff n =
  assert (n >= 1);
  let print f = fprintf ff f in
  let print_xlist ff i =
    assert (i >= 1);
    fprintf ff "x1";
    for j = 2 to i do
      fprintf ff " x%d" j
    done;
  in
  let px = print_xlist in
  let print_arrows ff i =
    assert (i >= 0);
    if (i = 1) then
      fprintf ff "A1 -> "
    else if (i >= 2) then
      fprintf ff "forall %a, A%d %a -> " px (i - 1) i px (i - 1)
  in
  let pa = print_arrows in
  let xs ff = px ff n in
  let ys ff =
    fprintf ff "y1";
    for j = 2 to n do
      fprintf ff " y%d" j
    done;
  in


  print "@[<v>";
  print "Section Ind%d.@,@," n;
  for i = 1 to n do
    print "Context {A%d : %aType}.@," i pa (i - 1);
  done;
  print "Context (G : (%aProp) -> (%aProp)).@," pa n pa n;
  print "Context (P : %aProp).@,@," pa n;

  print "Implicit Types Q R : %aProp.@,@," pa n;

  print "Definition is_ind%d :=@," n;
  print "  (forall Q R, (forall %t, Q %t -> R %t) -> forall %t, G Q %t -> G R %t) /\\@," xs xs xs xs xs xs;
  print "  (forall Q, (forall %t, G Q %t -> Q %t) -> forall %t, P %t -> Q %t) /\\@," xs xs xs xs xs xs;
  print "  (forall %t, G P %t -> P %t).@,@," xs xs xs;

  print "Hypothesis Hind : is_ind%d.@,@," n;

  print "Let is_positive := proj1 Hind.@,";
  print "Definition is_positive%d := is_positive.@," n;
  print "Let has_ind := proj1 (proj2 Hind).@,";
  print "Let is_ind := proj2 (proj2 Hind).@,@,";

  print "Definition preserved%d Q :=@," n;
  print "  forall %t, G (fun %t => P %t /\\ Q %t) %t -> Q %t.@," xs xs xs xs xs xs;
  print "Definition preserved_with_inv%d Q R :=@," n;
  print "  forall %t, G (fun %t => P %t /\\ Q %t /\\ R %t) %t -> R %t -> Q %t.@," xs xs xs xs xs xs xs xs;
  print "Definition preserved_down%d Q :=@," n;
  print "  forall %t R, G (fun %t => P %t /\\ R %t) %t -> Q %t -> G (fun %t => P %t /\\ Q %t /\\ R %t) %t.@,@,"
    xs xs xs xs xs xs xs xs xs xs xs;

  print "Lemma preserved%d_rec :@," n;
  print "  forall Q, preserved%d Q -> forall %t, P %t -> Q %t.@," n xs xs xs;
  print "Proof.@,";
  print "  intros Q HQ.@,";
  print "  enough (H : forall %t, P %t -> P %t /\\ Q %t) by (intros; apply H; assumption).@," xs xs xs xs;
  print "  apply has_ind. intros; split.@,";
  print "  - eapply is_ind, is_positive; [|eassumption].@,";
  print "    simpl. intros; tauto.@,";
  print "  - apply HQ. assumption.@,";
  print "Qed.@,@,";

  print "Lemma preserved_with_inv%d_rec :@," n;
  print "  forall Q R, preserved_down%d R -> preserved_with_inv%d Q R -> forall %t, P %t -> R %t -> Q %t.@," n n xs xs xs xs;
  print "Proof.@,";
  print "  intros Q R H1 H2. refine (preserved%d_rec (fun %t => R %t -> Q %t) _).@," n xs xs xs;
  print "  intros %t H3 H4. apply H2; [|assumption].@," xs;
  print "  apply is_positive with (Q := fun %t => P %t /\\ R %t /\\ (R %t -> Q %t)); [intros; tauto|].@," xs xs xs xs xs;
  print "  apply H1; assumption.@,";
  print "Qed.@,@,";

  print "Lemma ind%d_inv :@," n;
  print "  forall %t, P %t -> G P %t.@," xs xs xs;
  print "Proof.@,";
  print "  apply preserved%d_rec. intros %t H.@," n xs;
  print "  eapply is_positive; [|eassumption].@,";
  print "  simpl. intros; tauto.@,";
  print "Qed.@,@,";

  print "End Ind%d.@,@," n;

  print "Ltac prove_ind%d :=@," n;
  print "  unfold is_ind%d;@," n;
  print "  match goal with [ |- ?G1_ /\\ ?G2_ /\\ ?G3_ ] =>@,";
  print "    pose (G1 := G1_);@,";
  print "    assert (Hmap : G1) by (intros Q R H1 %t H2; destruct H2 eqn:Heq; match type of Heq with (_ = ?Z) => match Z with context E [?C Q] => eapply C end end; try eassumption; eapply H1; eassumption);@," xs;
  print "    split; [exact Hmap|];@,";
  print "    split; [|intros %t H; constructor; assumption];@," xs;
  print "    intros Q HQ; fix H %d; intros %t H1;@," (n + 1) xs;
  print "    destruct H1 as [%t H1];@," ys;
  print "    apply (Hmap _ Q) in H1; [apply HQ; assumption|assumption]@,";
  print "  end.@,";

  print "@]@."

let () =
  for i = 1 to 16 do
    print_indn std_formatter i
  done;
  printf "@."
