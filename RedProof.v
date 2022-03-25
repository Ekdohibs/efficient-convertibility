Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Beta.
Require Import Red.
Require Import Costar.
Require Import Pretty.
Require Import Inductive.
Require Import Rewrite.

Fixpoint read_nfval v :=
  match v with
  | nvar n => var n
  | napp v1 v2 => app (read_nfval v1) (read_nfval_or_lam v2)
  | nswitch v l => switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) l)
  end

with read_nfval_or_lam v :=
  match v with
  | nval v => read_nfval v
  | nlam v => abs (read_nfval_or_lam v)
  | nconstr tag l => constr tag (map read_nfval_or_lam l)
  end.

Definition read_val {df} (v : val df) :=
  match v with
  | vals_nf v => read_nfval v
  | vals_abs t => abs t
  | vals_constr tag l => constr tag l
  | vald_nf v => read_nfval_or_lam v
  end.

Lemma read_val_nf :
  forall df v, read_val (@val_nf df v) = read_nfval v.
Proof.
  intros [|] v; simpl; reflexivity.
Qed.

Definition read_out {df} (o : out (val df)) := match o with out_div => None | out_ret v => Some (read_val v) end.
Definition read_ext {df} (e : ext df) :=
  match e with
  | ext_term t => Some t
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2) | None => None end
  | ext_switch o m => match read_out o with Some t2 => Some (switch t2 m) | None => None end
  | ext_switchnf v m1 o m2 =>
    match o with
    | None => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ m2))
    | Some (p, o) =>
      match read_out o with
      | Some t2 => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t2) :: m2))
      | None => None
      end
    end
  | extd_abs o => match read_out o with Some t => Some (abs t) | None => None end
  | extd_constr tag l1 o l2 =>
    match o with
    | None => Some (constr tag (map read_nfval_or_lam l1 ++ l2))
    | Some o =>
      match read_out o with
      | Some t2 => Some (constr tag (map read_nfval_or_lam l1 ++ t2 :: l2))
      | None => None
      end
    end
  end.


Lemma red_star_beta :
  forall df e o, red df e o -> forall t1 t2, read_ext e = Some t1 -> read_out o = Some t2 -> star beta t1 t2.
Proof.
  enough (forall df e o, red df e o -> o <> out_div -> forall t1 t2, read_ext e = Some t1 -> read_out o = Some t2 -> star beta t1 t2).
  { intros; eapply H; try eassumption. destruct o; simpl in *; congruence. }
  refine (preserved_with_inv3_rec _ _ red_ind3 _ _ red_not_div_preserved_down _).
  intros df e o H _ u1 u2 Hu1 Hu2.
  inversion H; unexistT; subst; unexistT; subst; simpl in *; autoinjSome.
  - rewrite read_val_nf. simpl. constructor.
  - constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (RA := beta); [intros; constructor; assumption|].
      apply H4; reflexivity.
    + apply H6; [reflexivity|assumption].
  - constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => app t t2) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => app _ t) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - econstructor; [apply beta_redex|].
    apply H3; [reflexivity|assumption].
  - rewrite read_val_nf. simpl. constructor.
  - constructor.
  - apply H2; [reflexivity|assumption].
  - rewrite app_nil_r. constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => constr _ (_ ++ t :: _)) (RA := beta); [intros; constructor; assumption|].
      eapply H4; reflexivity.
    + apply H6; [reflexivity|assumption].
  - apply H2; [|assumption]. rewrite map_app, <- app_assoc; reflexivity.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => switch t _) (RA := beta); [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - apply nth_error_decompose in H3. destruct H3 as (m1 & m2 & -> & <-).
    econstructor; [|apply H4; [reflexivity|assumption]]. constructor.
  - apply H3; [reflexivity|assumption].
  - rewrite read_val_nf, app_nil_r. constructor.
  - destruct o1; [|tauto].
    simpl in *. eapply star_compose.
    + eapply star_map_impl with (f := fun t => switch _ (_ ++ (_, t) :: _)) (RA := beta);
        [intros; constructor; assumption|].
      eapply H3; reflexivity.
    + apply H4; [reflexivity|assumption].
  - apply H3; [|assumption]. rewrite map_app, <- app_assoc; reflexivity.
  - destruct e; simpl in *; try congruence;
      try solve [destruct o0; simpl in *; autoinjSome; simpl in *; congruence];
      destruct o0 as [o0|]; simpl in *; try congruence.
    + destruct o0 as [p o0]; destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
    + destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
Qed.

Definition read_ext_with_size {df} (e : ext df) :=
  match e with
  | ext_term t => Some (t, 2 * size t)
  | ext_app o t2 => match read_out o with Some t1 => Some (app t1 t2, 2 * size t2 + 1) | None => None end
  | ext_appnf v1 o => match read_out o with Some t2 => Some (app (read_nfval v1) t2, 0) | None => None end
  | ext_switch o m =>
    match read_out o with
    | Some t2 => Some (switch t2 m, 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m) + 1)
    | None => None
    end
  | ext_switchnf v m1 o m2 =>
    match o with
    | Some (p, o) =>
      match read_out o with
      | Some t2 => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t2) :: m2), 1 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))
      | None => None
      end
    | None => Some (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ m2), 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))
    end
  | extd_abs o => match read_out o with Some t => Some (abs t, 0) | None => None end
  | extd_constr tag l1 o l2 =>
    match o with
    | Some o =>
      match read_out o with
      | Some t2 => Some (constr tag (map read_nfval_or_lam l1 ++ t2 :: l2), 1 + 2 * list_sum (map (fun t => S (size t)) l2))
      | None => None
      end
    | None => Some (constr tag (map read_nfval_or_lam l1 ++ l2), 2 * list_sum (map (fun t => S (size t)) l2))
    end
  end.

Definition read_out_with_size {df} (o : out (val df)) := match o with out_div => None | out_ret v => Some (read_val v, 0) end.

Definition fst_map {A B C : Type} (f : A -> B) : (A * C) -> (B * C) := fun x => (f (fst x), snd x).
Lemma option_map_fst_id :
  forall (A B : Type) (x : option (A * B)), option_map (fst_map id) x = x.
Proof.
  destruct x as [[x y]|]; simpl; reflexivity.
Qed.


Lemma red_div_beta_aux :
  forall t df e o, cored df e o -> read_ext_with_size e = Some t ->
              costarPTn beta t (read_out_with_size o).
Proof.
  intros t df e o H Ht.
  exists (fun x y => exists df e o f,
         cored df e o /\
         option_map f (read_ext_with_size e) = Some x /\
         y = option_map f (read_out_with_size o) /\
         respectful (stepped beta) f /\ respectful weaken f).
  split.
  {
    exists df. exists e. exists o. exists id. splits 5.
    - assumption.
    - rewrite option_map_id. assumption.
    - rewrite option_map_id. reflexivity.
    - intros x y Hxy. exact Hxy.
    - intros x y Hxy. exact Hxy.
  }
  clear t df e o H Ht. intros x y (df & e & o & f & H & Hx & -> & Hf).
  inversion H as [? ? ? NH]; unexistT; subst.
  inversion NH; subst; simpl in *; unexistT; subst; simpl in *; autoinjSome; simpl in *.
  - rewrite read_val_nf in *; simpl in *.
    left. apply Hf. unfold weaken. split; simpl; [reflexivity|lia].
  - left. apply Hf. unfold weaken. split; simpl; [reflexivity|lia].
  - right; right.
    simpl.
    exists (f (abs t, 2 * size t)).
    exists (option_map (fun t1 => f (abs (fst t1), snd t1)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|]. simpl. lia.
    + eexists. eexists. eexists. exists (fun t1 => f (abs (fst t1), snd t1)).
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal|]; tauto].
      * unfold weaken in *. simpl. split; [f_equal|]; tauto.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H6|]. simpl. split; [reflexivity|].
      split; [reflexivity|]. apply Hf.
  - left. apply Hf. apply weaken_refl.
  - right. right.
    exists (f (app t1 t2, 2 * size t1 + 2 * size t2 + 1)).
    exists (option_map (fun t3 => f (app (fst t3) t2, snd t3 + 2 * size t2 + 1)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (app (fst t3) t2, snd t3 + 2 * size t2 + 1)).
      split; [exact H3|]. simpl. split; [reflexivity|].
      split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal; tauto|lia]].
      * unfold weaken in *. simpl. split; [f_equal; tauto|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. right.
    exists (f (app (read_nfval v) t2, 2 * size t2)).
    exists (option_map (fun t3 => f (app (read_nfval v) (fst t3), snd t3)) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (app (read_nfval v) (fst t3), snd t3)).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal|]; tauto].
      * unfold weaken in *. simpl. split; [f_equal|]; tauto.
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (subst1 t2 t1, 2 * size (subst1 t2 t1))).
    split; [apply Hf; left; apply beta_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - left. rewrite read_val_nf. apply weaken_refl.
  - left. apply Hf. unfold weaken; split; simpl; [reflexivity|lia].
  - right. left.
    exists (f (constr tag l, 2 * list_sum (map (fun t => S (size t)) l))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H2|]. split; [reflexivity|]. tauto.
  - left. apply Hf. rewrite app_nil_r. unfold weaken; simpl; split; [reflexivity|lia].
  - right. right.
    exists (f (constr tag (map read_nfval_or_lam l1 ++ t :: l2), 1 + 2 * size t + 2 * list_sum (map (fun t => S (size t)) l2))).
    exists (option_map (fun t3 => f (constr tag (map read_nfval_or_lam l1 ++ fst t3 :: l2), 1 + snd t3 + 2 * list_sum (map (fun t => S (size t)) l2))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (constr tag (map read_nfval_or_lam l1 ++ fst t3 :: l2), 1 + snd t3 + 2 * list_sum (map (fun t => S (size t)) l2))).
      split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy];
          [left; simpl; constructor; assumption|right; simpl; split; [destruct Hxy; congruence|lia]].
      * unfold weaken in *. simpl. split; [destruct Hxy; congruence|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H6|]. split; [reflexivity|]. tauto.
  - right. left.
    exists (f (constr tag (map read_nfval_or_lam l1 ++ read_nfval_or_lam v :: l2), 2 * list_sum (map (fun t => S (size t)) l2))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H2|]. split; [simpl; rewrite map_app, <- app_assoc; reflexivity|]. tauto.
  - right. right.
    exists (f (switch t m, 1 + 2 * size t + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
    exists (option_map (fun t3 => f (switch (fst t3) m, 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (switch (fst t3) m, 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
      split; [exact H3|]. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy]; [left; simpl; constructor; assumption|right; simpl; split; [f_equal; tauto|lia]].
      * unfold weaken in *. simpl. split; [f_equal; tauto|lia].
    + intros v Hv. destruct o1; simpl in Hv; [|discriminate]. injection Hv; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [f_equal; f_equal; f_equal; lia|]. tauto.
  - right. left.
    exists (f (subst (read_env l) t, 2 * size (subst (read_env l) t))).
    apply nth_error_decompose in H3. destruct H3 as (m1 & m2 & -> & <-).
    split; [apply Hf; left; apply beta_switch_redex|].
    eexists. eexists. eexists. exists f.
    split; [exact H4|]. simpl. split; [reflexivity|]. split; [reflexivity|]. assumption.
  - right. left.
    exists (f (switch (read_nfval v) m, 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. split; [reflexivity|]. tauto.
  - left. apply Hf. unfold weaken; split; simpl; [rewrite read_val_nf, app_nil_r; reflexivity|lia].
  - right. right.
    exists (f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, t) :: m2), 1 + 2 * size t + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
    exists (option_map (fun t3 => f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, fst t3) :: m2), 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))) (read_out_with_size o1)).
    splits 3.
    + apply Hf. right. simpl. split; [reflexivity|lia].
    + eexists. eexists. eexists. exists (fun t3 => f (switch (read_nfval v) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, fst t3) :: m2), 1 + snd t3 + 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
      split; [exact H3|]. simpl. split; [reflexivity|]. split; [reflexivity|].
      split; intros x y Hxy; apply Hf.
      * destruct Hxy as [Hxy | Hxy];
          [left; simpl; constructor; assumption|right; simpl; split; [destruct Hxy; congruence|lia]].
      * unfold weaken in *. simpl. split; [destruct Hxy; congruence|lia].
    + intros w Hw. destruct o1; simpl in Hw; [|discriminate]. injection Hw; intros; subst.
      eexists. eexists. eexists. exists f.
      split; [exact H4|]. simpl. split; [f_equal; f_equal; f_equal; lia|]. tauto.
  - right. left.
    exists (f (switch (read_nfval v1) (map (fun pt2 => (fst pt2, read_nfval_or_lam (snd pt2))) m1 ++ (p, read_nfval_or_lam v2) :: m2), 2 * list_sum (map (fun pt2 => S (size (snd pt2))) m2))).
    split; [apply Hf; right; simpl; split; [reflexivity|lia]|].
    eexists. eexists. eexists. exists f.
    split; [exact H3|]. split; [simpl; rewrite map_app, <- app_assoc; reflexivity|]. tauto.
  - exfalso. destruct e; simpl in *; try congruence;
      try solve [destruct o0; simpl in *; autoinjSome; simpl in *; congruence];
      destruct o0 as [o0|]; simpl in *; try congruence.
    + destruct o0 as [p o0]; destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
    + destruct o0; simpl in *; autoinjSome; simpl in *; congruence.
Qed.

Lemma read_ext_with_size_read_ext :
  forall df (e : ext df), read_ext e = option_map fst (read_ext_with_size e).
Proof.
  intros. destruct e; simpl; try destruct read_out; simpl; try reflexivity.
  - destruct o as [[p o0]|]; simpl in *; [|reflexivity].
    destruct read_out; simpl; reflexivity.
  - destruct o as [o|]; simpl in *; [|reflexivity].
    destruct read_out; simpl; reflexivity.
Qed.

Lemma read_out_with_size_read_out :
  forall df (o : out (val df)), read_out o = option_map fst (read_out_with_size o).
Proof.
  intros. destruct o; simpl; reflexivity.
Qed.

Lemma red_div_beta :
  forall t df e o, cored df e o -> read_ext e = Some t -> costar beta t (read_out o).
Proof.
  intros t df e o Hred He. apply costarP_costar.
  rewrite read_ext_with_size_read_ext in He.
  destruct read_ext_with_size as [t1|] eqn:Heqre; simpl in *; [|congruence].
  injection He as He; subst.
  rewrite read_out_with_size_read_out.
  apply costarPTn_costarP. eapply red_div_beta_aux; eassumption.
Qed.
