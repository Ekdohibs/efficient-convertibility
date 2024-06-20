Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Red.
Require Import RedE.
Require Import Pretty.
Require Import Inductive.

Fixpoint index l x :=
  match l with
  | nil => 0
  | y :: l => if freevar_eq_dec x y then 0 else S (index l x)
  end.

Fixpoint read_clo (xs : list freevar) (c : clo) : term :=
  match c with
  | clo_var x => var (index xs x)
  | clo_term _ t l =>
    let nl := map (read_clo xs) l in
    subst (read_env nl) t
  end.

Lemma read_shift_clo :
  forall c x xs, x \notin clo_fv c -> clo_closed c -> read_clo (x :: xs) c = ren_term (plus_ren 1) (read_clo xs c).
Proof.
  induction c using clo_ind2; intros y ys Hy Hcc; inversion Hcc; subst; simpl in *.
  - f_equal. destruct freevar_eq_dec; [tauto|]. lia.
  - rewrite ren_subst. eapply subst_closed_at_ext; [eassumption|].
    intros n Hn. unfold comp, read_env.
    rewrite !nth_error_map.
    destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
    assert (u \in l) by (eapply nth_error_In; eassumption).
    rewrite Forall_forall in H. apply H; [eassumption| |apply H4; assumption].
    rewrite concat_map_In in Hy. intros Hy2; apply Hy; exists u; tauto.
Qed.

Fixpoint read_nfvalx xs v :=
  match v with
  | nxvar x => nvar (index xs x)
  | nxapp v1 v2 => napp (read_nfvalx xs v1) (read_nfvalx_or_lam xs v2)
  | nxswitch t m => nswitch (read_nfvalx xs t) (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m)
  end

with read_nfvalx_or_lam xs v :=
  match v with
  | nxval v => nval (read_nfvalx xs v)
  | nxlam x v => nlam (read_nfvalx_or_lam (x :: xs) v)
  | nxconstr tag l => nconstr tag (map (read_nfvalx_or_lam xs) l)
  end.

Definition read_valE {df} (xs : list freevar) (v : valE df) : val df :=
  match v with
  | valE_nf v => val_nf (read_nfvalx xs v)
  | valEs_abs t l =>
    vals_abs (subst (scons (var 0) (read_env (map (fun c => ren_term (plus_ren 1) (read_clo xs c)) l))) t)
  | valEd_abs t l v => vald_nf (read_nfvalx_or_lam xs v)
  | valEs_constr tag l =>
    vals_constr tag (map (read_clo xs) l)
  | valEd_constr tag l v => vald_nf (read_nfvalx_or_lam xs v)
  end.

Definition read_extE {df} xs (e : extE df) : ext df :=
  match e with
  | extE_term env t => ext_term (read_clo xs (clo_term xs t env))
  | extE_clo c => ext_term (read_clo xs c)
  | extE_app env o1 t2 => ext_app (out_map (read_valE xs) o1) (read_clo xs (clo_term xs t2 env))
  | extE_appnf env v1 o2 => ext_appnf (read_nfvalx xs v1) (out_map (read_valE xs) o2)
  | extE_switch env o m =>
    ext_switch
      (out_map (read_valE xs) o)
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m)
  | extE_switchnf1 env v m1 m2 =>
    ext_switchnf
      (read_nfvalx xs v)
      (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m1)
      None
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m2)
  | extE_switchnf2 env v m1 xs2 o m2 =>
    ext_switchnf
      (read_nfvalx xs v)
      (map (fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ xs) (snd pt2))) m1)
      (Some (length xs2, out_map (read_valE (xs2 ++ xs)) o))
      (map (fun pt2 => (fst pt2, subst (liftn_subst (fst pt2) (read_env (map (read_clo xs) env))) (snd pt2))) m2)
  | extEd_abs env x t o => extd_abs (out_map (read_valE (x :: xs)) o)
  | extEd_constr1 tag l l1 l2 =>
    extd_constr tag
                (map (read_nfvalx_or_lam xs) l1)
                None
                (map (read_clo xs) l2)
  | extEd_constr2 tag l l1 o l2 =>
    extd_constr tag
                (map (read_nfvalx_or_lam xs) l1)
                (Some (out_map (read_valE xs) o))
                (map (read_clo xs) l2)
  end.

Lemma read_valE_deep :
  forall (v : valE deep) xs, read_valE xs v = vald_nf (read_nfvalx_or_lam xs (getvalEd_nf v)).
Proof.
  intros v xs.
  destruct (destruct_valE_deep v) as [[(v2 & ->) | (t & env & v2 & ->)] | (tag & l & v2 & ->)]; reflexivity.
Qed.

Lemma index_app :
  forall L1 L2 x, x \in L1 -> index (L1 ++ L2) x = index L1 x.
Proof.
  intros L1 L2 x H. induction L1; simpl in *.
  - tauto.
  - destruct freevar_eq_dec; [reflexivity|]. f_equal. apply IHL1. destruct H; [congruence|tauto].
Qed.

Lemma index_app2 :
  forall L1 L2 x, x \notin L1 -> index (L1 ++ L2) x = length L1 + index L2 x.
Proof.
  intros L1 L2 x H. induction L1; simpl in *.
  - reflexivity.
  - destruct freevar_eq_dec; subst; [simpl in *; tauto|]. f_equal.
    apply IHL1. tauto.
Qed.


Lemma nth_error_index :
  forall L p xs n x, distinct L p xs -> nth_error xs n = Some x -> index xs x = n.
Proof.
  intros L p xs n x H; revert n x; induction H; intros [|k] y Hy; simpl in *.
  - congruence.
  - congruence.
  - destruct freevar_eq_dec; [reflexivity|]. congruence.
  - destruct freevar_eq_dec; [|f_equal; apply IHdistinct; assumption].
    subst. exfalso. eapply distinct_distinct; [eassumption|left; reflexivity|eapply nth_error_In; eassumption].
Qed.

Lemma read_shiftn_clo :
  forall c ys p xs, distinct (clo_fv c) p ys -> clo_closed c -> read_clo (ys ++ xs) c = ren_term (plus_ren p) (read_clo xs c).
Proof.
  induction c using clo_ind2; intros ys p zs Hdistinct Hcc; inversion Hcc; subst; simpl in *.
  - f_equal. erewrite index_app2, plus_ren_correct, distinct_length; [reflexivity|eassumption|].
    intros H. eapply distinct_distinct; try eassumption. simpl. tauto.
  - rewrite ren_subst. eapply subst_closed_at_ext; [eassumption|].
    intros n Hn. unfold comp, read_env.
    rewrite !nth_error_map.
    destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
    assert (u \in l) by (eapply nth_error_In; eassumption).
    rewrite Forall_forall in H. apply H; [eassumption| |apply H4; assumption].
    eapply distinct_incl; [|eassumption].
    intros y Hy. rewrite concat_map_In. exists u. tauto.
Qed.

Lemma redE_red :
  forall df xs dom fvs e o, redE df xs dom fvs e o -> fvs \subseteq xs /\ extE_closed_at e fvs -> forall fvs2, fvs \subseteq fvs2 -> red df (read_extE fvs2 e) (out_map (read_valE fvs2) o).
Proof.
  refine (preserved_with_inv6_rec _ _ redE_is_ind6 _ _ closed_preserved_down _).
  intros df xs dom fvs e o H [Hfvs He] fvs2 Hfvs2. inversion H; unexistT; subst; unexistT; subst; simpl in *.
  - apply H7.
    rewrite <- Hfvs2. apply list_inter_subl2.
  - constructor. constructor.
  - unfold read_env. rewrite nth_error_map, H6.
    apply H7. assumption.
  - inversion He; subst. inversion H6; subst.
    erewrite subst_closed_at_ext; [constructor; constructor|eassumption|].
    intros [|n] Hn; [reflexivity|]. simpl; unfold read_env, comp; simpl.
    rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu.
    + reflexivity.
    + apply nth_error_None in Hu. lia.
  - inversion He; subst. inversion H7; subst.
    constructor; econstructor; [|apply H11; assumption].
    erewrite subst_closed_at_ext.
    + eapply H10. rewrite Hfvs2; reflexivity.
    + eassumption.
    + intros [|n] Hn; simpl; unfold comp, read_env; simpl; [destruct freevar_eq_dec; congruence|].
      rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
      apply nth_error_In, H5 in Hu. destruct Hu as [Hu1 Hu2].
      rewrite read_shift_clo; [reflexivity| |apply Hu1].
      rewrite Hu2, Hfvs. assumption.
  - rewrite read_valE_deep. constructor; constructor.
  - constructor; econstructor; [eapply H6|eapply H7]; assumption.
  - constructor; econstructor; [eapply H6|eapply H7]; assumption.
  - inversion He; subst. inversion H10; subst.
    constructor; econstructor.
    unfold subst1. rewrite subst_subst.
    erewrite subst_closed_at_ext; [eapply H8| |].
    + assumption.
    + eassumption.
    + unfold comp, read_env.
      intros [|n] Hn; simpl.
      * destruct t2; try reflexivity. simpl.
        rewrite nth_error_map. destruct nth_error eqn:Hu; [|apply nth_error_None in Hu; inversion H9; subst; lia].
        reflexivity.
      * rewrite !nth_error_map; destruct nth_error as [u|] eqn:Hu; [|apply nth_error_None in Hu; lia].
        rewrite subst_ren; unfold comp; simpl.
        erewrite subst_ext; [apply subst_id|]; intros; f_equal; lia.
  - rewrite read_valE_deep. constructor; constructor.
  - replace (map (read_clo fvs2) lc) with (map (subst (read_env (map (read_clo fvs2) env))) l); [constructor; constructor|].
    eapply Forall2_map_eq, Forall2_impl; [|eassumption]. intros t c Htc; simpl in *.
    destruct env_get_maybe_var as [c1|] eqn:Hc1.
    + subst. destruct t; simpl in *; try congruence.
      unfold read_env. rewrite nth_error_map, Hc1. reflexivity.
    + destruct Htc as (xs2 & Hxs2a & Hxs2b & ->). reflexivity.
  - constructor. constructor.
    replace (map (subst (read_env (map (read_clo fvs2) env))) l) with (map (read_clo fvs2) lc).
    + eapply H9. assumption.
    + symmetry. eapply Forall2_map_eq, Forall2_impl; [|eassumption]. intros t c Htc; simpl in *.
      destruct env_get_maybe_var as [c1|] eqn:Hc1.
      * subst. destruct t; simpl in *; try congruence.
        unfold read_env. rewrite nth_error_map, Hc1. reflexivity.
      * destruct Htc as (xs2 & Hxs2a & Hxs2b & ->). reflexivity.
  - constructor. constructor.
  - constructor; econstructor; [apply H7; assumption|apply H9; assumption].
  - rewrite read_valE_deep. constructor. econstructor.
    rewrite <- map_app with (f := read_nfvalx_or_lam fvs2) (l' := getvalEd_nf v :: nil).
    apply H5. assumption.
  - constructor. econstructor.
    + apply H6. assumption.
    + apply H7. assumption.
  - inversion He; subst.
    constructor; econstructor; [rewrite nth_error_map, H6, map_length; simpl; reflexivity|].
    rewrite subst_subst.
    erewrite subst_closed_at_ext; [apply H7; assumption|eapply H8, nth_error_In; eassumption|].
    intros n Hn. unfold comp, liftn_subst, read_env.
    destruct le_lt_dec.
    + rewrite !nth_error_map, nth_error_app2 by assumption.
      destruct (nth_error env _) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      rewrite subst_ren. erewrite subst_ext; [apply subst_id|]. intros n2. simpl.
      unfold comp; simpl. rewrite nth_error_map, plus_ren_correct, map_length.
      replace (nth_error l (length l + n2)) with (@None clo) by (symmetry; apply nth_error_None; lia).
      f_equal. lia.
    + simpl. rewrite !nth_error_map, nth_error_app1 by assumption.
      destruct (nth_error l _) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia]. reflexivity.
  - constructor. constructor. apply H6. assumption.
  - constructor. constructor.
  - inversion He; subst.
    constructor. econstructor.
    + erewrite subst_closed_at_ext; [apply H8; rewrite Hfvs2; reflexivity|apply H13; left; reflexivity|].
      intros n Hn. unfold liftn_subst, read_env.
      destruct le_lt_dec.
      * rewrite !nth_error_map, nth_error_app2 by (erewrite map_length, distinct_length; eassumption).
        erewrite !map_length, app_length, map_length, distinct_length by eassumption.
        destruct nth_error eqn:Hu.
        -- erewrite read_shiftn_clo; [reflexivity| |eapply H7, nth_error_In; eassumption].
           eapply distinct_incl; [|eassumption].
           rewrite <- Hfvs. eapply H7, nth_error_In; eassumption.
        -- apply nth_error_None in Hu. lia.
      * rewrite nth_error_map, nth_error_app1, nth_error_map by (erewrite map_length, distinct_length; eassumption).
        destruct nth_error as [y|] eqn:Hy.
        -- simpl. f_equal. rewrite index_app; [|eapply nth_error_In; eassumption].
           symmetry; eapply nth_error_index; eassumption.
        -- apply nth_error_None in Hy. erewrite distinct_length in Hy by eassumption. lia.
    + replace p with (length ys) by (eapply distinct_length; eassumption).
      apply H9. assumption.
  - rewrite read_valE_deep. constructor. econstructor.
    rewrite <- map_app with (f := fun pt2 => (length (fst pt2), read_nfvalx_or_lam (fst pt2 ++ fvs2) (snd pt2))) (l' := (ys, getvalEd_nf v2) :: nil).
    apply H6. assumption.
  - constructor. constructor.
    destruct e; simpl in *; try congruence; try (destruct o0; simpl in *; autoinjSome; simpl; congruence).
Qed.
