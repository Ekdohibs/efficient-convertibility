Require Import List.
Require Import Arith.
Require Import Freevar.
Require Import Misc.
Require Import Psatz.
Require Import Star.
Require Import Coq.Logic.Eqdep_dec.
Require Import FEnv.
Require Import STerm.
Require Import Pretty.
Require Import RedE.
Require Import RedM.
Require Import Inductive.

(** Compatibility proof between [redM] and [redE]. *)

Inductive read_eiM (res : freevar -> option clo) dom : eiM -> clo -> Prop :=
| read_eiM_lazy : forall t ys vs xs,
    map Some vs = map res ys ->
    read_eiM res dom (eiM_lazy t ys) (clo_term xs t vs)
| read_eiM_abs1 : forall t ys u ws vs xs fvs,
    map Some vs = map res ys ->
    redE shallow xs dom fvs (extE_term ws u) (out_ret (valEs_abs t vs)) ->
    read_eiM res dom (eiM_abs1 t ys) (clo_term xs u ws)
| read_eiM_abs2 : forall t ys u ws v vs xs fvs,
    map Some vs = map res ys ->
    redE deep xs dom fvs (extE_term ws u) (out_ret (valEd_abs t vs v)) ->
    read_eiM res dom (eiM_abs2 t ys v) (clo_term xs u ws)
| read_eiM_constr1 : forall tag ys u ws vs xs fvs,
    map Some vs = map res ys ->
    redE shallow xs dom fvs (extE_term ws u) (out_ret (valEs_constr tag vs)) ->
    read_eiM res dom (eiM_constr1 tag ys) (clo_term xs u ws)
| read_eiM_constr2 : forall tag ys u ws v vs xs fvs,
    map Some vs = map res ys ->
    redE deep xs dom fvs (extE_term ws u) (out_ret (valEd_constr tag vs v)) ->
    read_eiM res dom (eiM_constr2 tag ys v) (clo_term xs u ws)
| read_eiM_val : forall u ws v xs fvs,
    redE shallow xs dom fvs (extE_term ws u) (out_ret (valE_nf v)) ->
    read_eiM res dom (eiM_val v) (clo_term xs u ws)
| read_eiM_var : forall y,
    read_eiM res dom (eiM_val (nxvar y)) (clo_var y).

Lemma read_eiM_dom_mono :
  forall res dom u c, read_eiM res dom u c -> forall dom2, dom \subseteq dom2 -> read_eiM res dom2 u c.
Proof.
  intros res dom u c H; inversion H; subst; intros dom2 Hdom2; econstructor; try eassumption;
    eapply redE_dom_mono; eassumption.
Qed.

Definition read_memM (m : memxM) (res : freevar -> option clo) :=
  (forall x u, env_find (fst m) x = Some u -> exists v, res x = Some v /\ read_eiM res (snd m) u v) /\
  (forall x, env_find (fst m) x = None -> res x = None).

Lemma read_memM_Some :
  forall m res x u v, read_memM m res -> env_find (fst m) x = Some u -> res x = Some v -> read_eiM res (snd m) u v.
Proof.
  intros m res x u v Hread Hm Hres. apply Hread in Hm.
  destruct Hm as (v2 & Hx2 & Hv2). congruence.
Qed.


Inductive read_valM : forall {df}, (freevar -> option clo) -> valM df -> valE df -> Prop :=
| read_valM_nf : forall df res v, @read_valM df res (valM_nf v) (valE_nf v)
| read_valMs_abs : forall res t ys vs,
    map Some vs = map res ys ->
    @read_valM shallow res (valMs_abs t ys) (valEs_abs t vs)
| read_valMd_abs : forall res t ys v vs,
    map Some vs = map res ys ->
    @read_valM deep res (valMd_abs t ys v) (valEd_abs t vs v)
| read_valMs_constr : forall res tag ys vs,
    map Some vs = map res ys ->
    @read_valM shallow res (valMs_constr tag ys) (valEs_constr tag vs)
| read_valMd_constr : forall res tag ys v vs,
    map Some vs = map res ys ->
    @read_valM deep res (valMd_constr tag ys v) (valEd_constr tag vs v).


Definition read_memxM m res := read_memM m res /\ (forall x xs t env, res x = Some (clo_term xs t env) -> xs \subseteq (snd m)).

Inductive read_outM : forall df, (freevar -> option clo) -> outM (valM df) memxM -> out (valE df) -> Prop :=
| read_outM_div : forall df res, read_outM df res outM_div out_div
| read_outM_ret : forall df res m v1 v2,
    read_memxM m res -> read_valM res v1 v2 -> read_outM df res (outM_ret v1 m) (out_ret v2).

Inductive read_extM : forall df, (freevar -> option clo) -> extM df -> extE df -> Prop :=
| read_extM_term : forall df res env1 env2 m t,
    map Some env2 = map res env1 -> read_memxM m res -> read_extM df res (extM_term env1 m t) (extE_term env2 t)
| read_extM_clo : forall df res m x c,
    read_memxM m res -> res x = Some c -> read_extM df res (extM_clo m x) (extE_clo c)
| read_extM_app : forall df res env1 env2 o1 o2 t,
    map Some env2 = map res env1 -> read_outM shallow res o1 o2 -> read_extM df res (extM_app env1 o1 t) (extE_app env2 o2 t)
| read_extM_appnf : forall df res env1 env2 v o1 o2,
    map Some env2 = map res env1 -> read_outM deep res o1 o2 -> read_extM df res (extM_appnf env1 v o1) (extE_appnf env2 v o2)
| read_extM_switch : forall df res env1 env2 o1 o2 m,
    map Some env2 = map res env1 -> read_outM shallow res o1 o2 ->
    read_extM df res (extM_switch env1 o1 m) (extE_switch env2 o2 m)
| read_extM_switchnf1 : forall df res env1 env2 v m1 m m2,
    map Some env2 = map res env1 -> read_memxM m res ->
    read_extM df res (extM_switchnf1 env1 v m1 m m2) (extE_switchnf1 env2 v m1 m2)
| read_extM_switchnf2 : forall df res env1 env2 v m1 xs o1 o2 m2,
    map Some env2 = map res env1 -> read_outM deep res o1 o2 ->
    read_extM df res (extM_switchnf2 env1 v m1 xs o1 m2) (extE_switchnf2 env2 v m1 xs o2 m2)
| read_extMd_abs : forall res env1 env2 x t o1 o2,
    map Some env2 = map res env1 -> read_outM deep res o1 o2 -> read_extM deep res (extMd_abs env1 x t o1) (extEd_abs env2 x t o2)
| read_extMd_constr1 : forall res tag xs vs l ys ws m,
    read_memxM m res -> map Some vs = map res xs -> map Some ws = map res ys ->
    read_extM deep res (extMd_constr1 tag xs l m ys) (extEd_constr1 tag vs l ws)
| read_extMd_constr2 : forall res tag xs vs l o1 o2 ys ws,
    read_outM deep res o1 o2 -> map Some vs = map res xs -> map Some ws = map res ys ->
    read_extM deep res (extMd_constr2 tag xs l o1 ys) (extEd_constr2 tag vs l o2 ws).


Definition compat_res (res1 res2 : freevar -> option clo) := (forall x u, res1 x = Some u -> res2 x = Some u).

Lemma compat_res_refl :
  forall res, compat_res res res.
Proof.
  intros res x u H. exact H.
Qed.

Lemma compat_res_trans :
  forall res1 res2 res3, compat_res res1 res2 -> compat_res res2 res3 -> compat_res res1 res3.
Proof.
  intros res1 res2 res3 H1 H2 x u H. apply H2. apply H1. assumption.
Qed.

Lemma nenv_eqs : forall {A B : Type} {res : A -> option B} {env1 : list A} {env2 : list B} {n : nat} {x : A},
    nth_error env1 n = Some x -> map Some env2 = map res env1 -> exists u, nth_error env2 n = Some u /\ res x = Some u.
Proof.
  intros A B res env1 env2 n x H1 H2.
  assert (Heq : nth_error (map Some env2) n = nth_error (map res env1) n) by congruence.
  rewrite nth_error_map, nth_error_map, H1 in Heq.
  destruct (nth_error env2 n) as [u|]; [|congruence]. exists u; split; congruence.
Qed.

Lemma nenv_compat_list : forall {res1 res2 : freevar -> option clo} {env1 : list freevar} {env2 : list clo},
    compat_res res1 res2 -> map Some env2 = map res1 env1 -> map Some env2 = map res2 env1.
Proof.
  intros res1 res2 env1 env2 Hcompat. revert env2; induction env1 as [|x env1 Henv1]; intros env2 Heq.
  - simpl in *. assumption.
  - simpl in *. destruct env2 as [|u env2]; simpl in *; [congruence|].
    injection Heq; intros. f_equal; [|apply Henv1; assumption].
    symmetry. apply Hcompat. symmetry. assumption.
Qed.

Lemma compat_res_read_eiM :
  forall dom res1 res2 u c,
    compat_res res1 res2 -> read_eiM res1 dom u c -> read_eiM res2 dom u c.
Proof.
  intros dom res1 res2 u c H1 H2. inversion H2; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.

Lemma compat_res_read_valM :
  forall res1 res2 df v1 v2,
    compat_res res1 res2 -> @read_valM df res1 v1 v2 -> @read_valM df res2 v1 v2.
Proof.
  intros res1 res2 df v1 v2 H1 H2.
  inversion H2; subst; unexistT; subst; econstructor; try eassumption.
  all: eapply nenv_compat_list; eassumption.
Qed.

Lemma update_env_in_fst :
  forall {A : Type} (env : list (freevar * A)) x u v, env_find env x = Some u -> map fst (update_env env x v) = map fst env.
Proof.
  induction env as [|[y w] env]; intros x u v H.
  - simpl in H. congruence.
  - simpl in *. destruct freevar_eq_dec.
    + simpl. congruence.
    + simpl. f_equal. eapply IHenv; eassumption.
Qed.

Lemma read_memM_update :
  forall m res x c u, read_memM m res -> res x = Some c -> read_eiM res (snd m) u c -> read_memM (update_mem m x u) res.
Proof.
  intros [m dom] res x c u Hmem Hres Hread. unfold update_mem; simpl in *.
  split; simpl.
  - intros y v Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + injection Hy; intros; subst. exists c. split; assumption.
    + apply Hmem. assumption.
  - intros y Hy. rewrite env_find_update_env in Hy. destruct freevar_eq_dec.
    + congruence.
    + apply Hmem. assumption.
Qed.

Lemma read_memxM_update :
  forall m res x c u, read_memxM m res -> res x = Some c -> read_eiM res (snd m) u c -> read_memxM (update_mem m x u) res.
Proof.
  intros m res x c u H1 H2 H3. split; [|apply H1].
  eapply read_memM_update; [apply H1|eassumption|eassumption].
Qed.

Definition update_res (res : freevar -> option clo) x v := (fun a => if freevar_eq_dec a x then Some v else res a).

Definition redM_mklazy_nres t dom x res nenv :=
  match env_get_maybe_var nenv t with
  | Some _ => res
  | None => update_res res x (clo_term dom t nenv)
  end.

Lemma update_res_compat :
  forall res x v, res x = None -> compat_res res (update_res res x v).
Proof.
  intros res x v Hx y c Hy. unfold update_res. destruct freevar_eq_dec; [congruence|assumption].
Qed.

Lemma update_res_eq :
  forall res x v, update_res res x v x = Some v.
Proof.
  intros. unfold update_res. rewrite freevar_eq_dec_eq_ifte; reflexivity.
Qed.


Lemma update_res_read_memxM :
  forall m res x v1 v2 dom,
    env_find (fst m) x = None -> read_memxM m res -> read_eiM res dom v1 v2 ->
    match v2 with clo_term xs _ _ => xs \subseteq dom | _ => True end -> snd m \subseteq dom ->
    compat_res res (update_res res x v2) /\ read_memxM ((x, v1) :: fst m, dom) (update_res res x v2) /\ update_res res x v2 x = Some v2.
Proof.
  intros m res x v1 v2 dom H1 H2 H3 H4 H5.
  split; [apply update_res_compat, H2, H1|].
  split; [|apply update_res_eq].
  split; [split|].
  - intros y u Hu. simpl in Hu.
    destruct freevar_eq_dec.
    + subst; autoinjSome. simpl. exists v2.
      split; [apply update_res_eq|].
      eapply compat_res_read_eiM; [|eassumption]. apply update_res_compat, H2, H1.
    + apply H2 in Hu. destruct Hu as (v & Hv1 & Hv2); exists v.
      simpl. split; [unfold update_res; rewrite freevar_eq_dec_neq_ifte; assumption|].
      eapply compat_res_read_eiM, read_eiM_dom_mono; [|eassumption|eassumption]. apply update_res_compat, H2, H1.
  - intros y Hy; simpl in Hy. unfold update_res. destruct freevar_eq_dec; [congruence|].
    apply H2. assumption.
  - intros y xs t env Hy. simpl. unfold update_res in *.
    destruct freevar_eq_dec; [|rewrite <- H5; eapply H2; eassumption].
    subst; autoinjSome. assumption.
Qed.

Lemma redM_mklazy_nres_compat :
  forall t x env1 env2 m1 m2 res,
    map Some env2 = map res env1 ->
    redM_mklazy t env1 m1 x m2 ->
    read_memxM m1 res ->
    compat_res res (redM_mklazy_nres t (snd m1) x res env2) /\
    read_memxM m2 (redM_mklazy_nres t (snd m1) x res env2) /\
    redM_mklazy_nres t (snd m1) x res env2 x = Some match env_get_maybe_var env2 t with Some c => c | None => clo_term (snd m1) t env2 end.
Proof.
  intros t x env1 env2 m1 m2 res H1 H2 H3.
  unfold redM_mklazy, redM_mklazy_nres in *.
  destruct (env_get_maybe_var env1 t) as [y|] eqn:Hy.
  - destruct t; simpl in *; try congruence.
    destruct (nenv_eqs Hy H1) as (c & -> & Hc).
    destruct H2 as [-> ->].
    split; [apply compat_res_refl|].
    split; assumption.
  - destruct H2 as [Hx ->]. simpl.
    destruct (env_get_maybe_var env2 t) eqn:Henv2.
    + destruct t; simpl in *; try congruence.
      assert (length (map Some env2) = length (map res env1)) by congruence; rewrite !map_length in *.
      erewrite nth_error_None, <- H, <- nth_error_None in Hy. congruence.
    + apply update_res_read_memxM; [assumption|assumption| |reflexivity|reflexivity].
      constructor. assumption.
Qed.

Fixpoint redM_mknlazy_nres l dom xs res nenv :=
  match l, xs with
  | nil, _ | _, nil => res
  | t :: l, x :: xs => redM_mknlazy_nres l dom xs (redM_mklazy_nres t dom x res nenv) nenv
  end.

Lemma redM_mknlazy_nres_compat :
  forall l xs env1 env2 m1 m2 res,
    map Some env2 = map res env1 ->
    redM_mknlazy l env1 m1 xs m2 ->
    read_memxM m1 res ->
    compat_res res (redM_mknlazy_nres l (snd m1) xs res env2) /\
    read_memxM m2 (redM_mknlazy_nres l (snd m1) xs res env2) /\
    map (redM_mknlazy_nres l (snd m1) xs res env2) xs = map (fun t => Some match env_get_maybe_var env2 t with Some c => c | None => clo_term (snd m1) t env2 end) l.
Proof.
  intros l xs env1 env2 m1 m2 res H1 H2; revert res H1; induction H2; intros res H1 H3; simpl in *.
  - split; [apply compat_res_refl|]. split; [assumption|reflexivity].
  - destruct (redM_mklazy_nres_compat _ _ _ _ _ _ _ H1 H H3) as (H4 & H5 & H6).
    specialize (IHredM_mknlazy _ ltac:(eapply nenv_compat_list; eassumption) H5).
    erewrite <- redM_mklazy_usedvars_eq with (m2 := m2) in IHredM_mknlazy by eassumption.
    destruct IHredM_mknlazy as (H7 & H8 & H9).
    splits 3.
    + eapply compat_res_trans; eassumption.
    + eassumption.
    + f_equal; [|eassumption].
      apply H7. assumption.
Qed.


Definition redM_newvar_nres res a x := update_res res a (clo_var x).
Lemma redM_newvar_nres_compat :
  forall m1 m2 a x res,
    redM_newvar m1 m2 a x -> read_memxM m1 res ->
    compat_res res (redM_newvar_nres res a x) /\ read_memxM m2 (redM_newvar_nres res a x) /\ redM_newvar_nres res a x a = Some (clo_var x).
Proof.
  intros m1 m2 a x res (H1 & H2 & H3) H4.
  unfold redM_newvar_nres in *. rewrite -> H3.
  apply update_res_read_memxM; try eassumption.
  - constructor.
  - tauto.
  - prove_list_inc.
Qed.

Fixpoint redM_nnewvar_nres res la lx :=
  match la, lx with
  | nil, _ | _, nil => res
  | a :: la, x :: lx => redM_nnewvar_nres (redM_newvar_nres res a x) la lx
  end.

Lemma redM_nnewvar_nres_compat :
  forall m1 m2 la lx p res,
    redM_nnewvar m1 m2 la lx p -> read_memxM m1 res ->
    compat_res res (redM_nnewvar_nres res la lx) /\ read_memxM m2 (redM_nnewvar_nres res la lx) /\
    map (redM_nnewvar_nres res la lx) la = map (fun x => Some (clo_var x)) lx.
Proof.
  intros m1 m2 la lx p res H1; revert res; induction H1; intros res H2; simpl in *.
  - split; [apply compat_res_refl|]. split; [assumption|reflexivity].
  - eapply redM_newvar_nres_compat in H; [|eassumption].
    destruct H as (H3 & H4 & H5).
    destruct (IHredM_nnewvar _ H4) as (H6 & H7 & H8).
    splits 3.
    + eapply compat_res_trans; eassumption.
    + assumption.
    + f_equal; [|eassumption].
      apply H6. assumption.
Qed.


Lemma redM_redE :
  forall df e o,
    redM df e o ->
    forall m res e2,
      get_ext_memxM e = Some m -> read_extM df res e e2 ->
      exists m2 o2 res2, get_out_memxM o = Some m2 /\ redE df (snd m) (snd m2) nil e2 o2 /\ read_outM df res2 o o2 /\ compat_res res res2.
Proof.
  refine (preserved3_rec _ _ redM_is_ind3 _ _).
  intros df e o H m res e2 Hm He.
  Local Ltac use_recM_ H Hm Hrec Hread Hres a :=
    let Hred := fresh "Hred" in
    let tmp := fresh "_tmp" in
    let tmp2 := fresh "_tmp" in
    destruct H as [Hred tmp]; refine ((fun tmp2 => _) (tmp _ a _ _ _)); clear tmp;
    try (match type of tmp2 with
           exists (name1 : _) (name2 : _) (name3 : _), _ =>
           let name1 := fresh name1 in
           let name2 := fresh name2 in
           let name3 := fresh name3 in
           destruct tmp2 as (name1 & name2 & name3 & Hm & Hrec & Hread & Hres)
         end).
  Tactic Notation "use_recM" ident(H) ident(Hm) ident(Hrec) ident(Hread) ident(Hres) := use_recM_ H Hm Hrec Hread Hres uconstr:(_).
  Tactic Notation "use_recM" ident(H) ident(Hm) ident(Hrec) ident(Hread) ident(Hres) uconstr(a):= use_recM_ H Hm Hrec Hread Hres a.
  inversion H; unexistT; subst; unexistT; subst; simpl in *; subst; autoinjSome;
    lazymatch goal with [ _ : get_abortM _ = _ |- _ ] => idtac | _ => inversion He end; unexistT; subst; simpl in *.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H6) H3 H7). inversion Hx2; subst.
    + do 3 eexists. splits 4.
      * reflexivity.
      * constructor. econstructor; [eapply H6; eassumption|].
        eapply redE_fvs_any.
        destruct df; simpl; [eassumption|]. apply redE_shallow_deep_val in H1; assumption.
      * constructor; [eassumption|constructor].
      * apply compat_res_refl.
    + do 3 eexists. splits 4.
      * reflexivity.
      * constructor. econstructor.
      * constructor; [eassumption|constructor].
      * apply compat_res_refl.

  (* Abstractions *)
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eassumption.
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H10) H5 H11). inversion Hx2; subst.
    use_recM H6 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    destruct (update_result_memxM _ _ _ _ _ H7 Hm2) as (m3 & Ho2 & Hm3a & Hm3b).
    assert (HredE : redE deep xs (snd m2) nil (extE_term ws u) o2). {
      eapply redE_shallow_deep_abs in H9; [eapply redE_fvs_any; eassumption| | |eapply redE_fvs_any; eassumption].
        -- apply H10 in H11. assumption.
        -- eapply redM_usedvars_inc in Hred; [|reflexivity].
           rewrite Hm2 in Hred; assumption.
    }
    do 3 eexists. splits 4.
    + eassumption.
    + constructor. econstructor.
      * apply H10 in H11. etransitivity; [eassumption|]. rewrite <- Hm3b.
        eapply redM_usedvars_inc in Hred; [|reflexivity].
        rewrite Hm2 in Hred; assumption.
      * rewrite <- Hm3b. eassumption.
    + apply redM_abs_deep_result in Hred. destruct Hred as (v & m4 & ->).
      inversion H7; unexistT; subst. inversion Hread2; unexistT; subst. inversion H14; unexistT; subst.
      constructor; simpl in *; [|constructor; eassumption].
      eapply read_memxM_update; [eassumption|eapply Hres2; eassumption|].
      econstructor; [eassumption|]. autoinjSome. eassumption.
    + eassumption.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor.
      eapply redE_deep_shallow_abs in H10; [|reflexivity].
      econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eassumption.
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eassumption.
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.

  (* Constructors *)
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eassumption.
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H10) H5 H11). inversion Hx2; subst.
    use_recM H6 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    destruct (update_result_memxM _ _ _ _ _ H7 Hm2) as (m3 & Ho2 & Hm3a & Hm3b).
    assert (HredE : redE deep xs (snd m2) nil (extE_term ws u) o2). {
      eapply redE_shallow_deep_constr in H9; [eapply redE_fvs_any; eassumption| | |eapply redE_fvs_any; eassumption].
        -- apply H10 in H11. assumption.
        -- eapply redM_usedvars_inc in Hred; [|reflexivity].
           rewrite Hm2 in Hred; assumption.
    }
    do 3 eexists. splits 4.
    + eassumption.
    + constructor. econstructor.
      * apply H10 in H11. etransitivity; [eassumption|]. rewrite <- Hm3b.
        eapply redM_usedvars_inc in Hred; [|reflexivity].
        rewrite Hm2 in Hred; assumption.
      * rewrite <- Hm3b. eassumption.
    + apply redM_constr_deep_result in Hred. destruct Hred as (v & m4 & ->).
      inversion H7; unexistT; subst. inversion Hread2; unexistT; subst. inversion H14; unexistT; subst.
      constructor; simpl in *; [|constructor; eassumption].
      eapply read_memxM_update; [eassumption|eapply Hres2; eassumption|].
      econstructor; [eassumption|]. autoinjSome. eassumption.
    + eassumption.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eapply redE_deep_shallow_constr in H10; [eassumption|reflexivity].
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor; [eapply H8; eassumption|].
      eapply redE_fvs_any. eassumption.
    + constructor; [eassumption|constructor; assumption].
    + apply compat_res_refl.

  (* Lazy *)
  - assert (Hx2 := read_memM_Some _ _ _ _ _ (proj1 H8) H2 H9). inversion Hx2; subst.
    use_recM H4 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    destruct (update_result_memxM _ _ _ _ _ H5 Hm2) as (m3 & Ho2 & Hm3a & Hm3b).
    do 3 eexists. splits 4.
    + eassumption.
    + constructor. econstructor; [|eapply redE_fvs_any, redE_xs_mono; [rewrite <- Hm3b; eassumption|]].
      * apply H8 in H9. etransitivity; [eassumption|]. rewrite <- Hm3b.
        eapply redM_usedvars_inc in Hred; [|reflexivity].
        rewrite Hm2 in Hred; assumption.
      * apply H8 in H9. assumption.
    + inversion H5; unexistT; subst; inversion Hread2; unexistT; subst; try (simpl in *; congruence).
      * inversion H11; unexistT; subst. constructor; [|constructor].
        eapply read_memxM_update; [eassumption|eapply Hres2, H9|].
        simpl in *; autoinjSome. econstructor. eapply redE_xs_mono; [destruct df|].
        -- eassumption.
        -- eapply redE_deep_shallow_val; [eassumption|reflexivity].
        -- apply H8 in H9. assumption.
      * injection H0 as; subst. inversion H14; unexistT; subst.
        constructor; [|constructor; assumption].
        eapply read_memxM_update; [eassumption|eapply Hres2, H9|].
        simpl in *; autoinjSome. econstructor; [eassumption|].
        eapply redE_xs_mono; [eassumption|].
        apply H8 in H9. assumption.
      * injection H0 as; subst. inversion H14; unexistT; subst.
        constructor; [|constructor; assumption].
        eapply read_memxM_update; [eassumption|eapply Hres2, H9|].
        simpl in *; autoinjSome. econstructor; [eassumption|].
        eapply redE_xs_mono; [eassumption|].
        apply H8 in H9. assumption.
      * injection H0 as; subst. inversion H14; unexistT; subst.
        constructor; [|constructor; assumption].
        eapply read_memxM_update; [eassumption|eapply Hres2, H9|].
        simpl in *; autoinjSome. econstructor; [eassumption|].
        eapply redE_xs_mono; [eassumption|].
        apply H8 in H9. assumption.
      * injection H0 as; subst. inversion H14; unexistT; subst.
        constructor; [|constructor; assumption].
        eapply read_memxM_update; [eassumption|eapply Hres2, H9|].
        simpl in *; autoinjSome. econstructor; [eassumption|].
        eapply redE_xs_mono; [eassumption|].
        apply H8 in H9. assumption.
    + eassumption.


  - destruct (nenv_eqs H3 H6) as (c & Hc1 & Hc2).
    use_recM H4 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    do 3 eexists. splits 4.
    + eassumption.
    + constructor. econstructor; eassumption.
    + eassumption.
    + assumption.
  - do 3 eexists. splits 4.
    + reflexivity.
    + constructor. econstructor.
    + constructor; [eassumption|].
      constructor. assumption.
    + apply compat_res_refl.
  - destruct (redM_newvar_nres_compat m m2 a x res) as (Hcompat & Hread2 & Hres2); try assumption.
    destruct H5 as (Ha & Hx & Hm2). subst m2.
    use_recM H6 Hm3 Hrec3 Hread3 Hres3 (redM_newvar_nres res a x);
      [use_recM H7 Hm4 Hrec4 Hread4 Hres4; [|eassumption|]|reflexivity|constructor].
    + do 3 eexists. splits 4.
      * eassumption.
      * constructor. econstructor.
        -- eassumption.
        -- eapply redM_usedvars_inc in Hred0; [|eassumption].
           rewrite Hm4 in Hred0. rewrite <- Hred0.
           eapply redM_usedvars_inc in Hred; [|reflexivity].
           rewrite Hm3 in Hred. rewrite <- Hred. simpl. left; reflexivity.
        -- eapply redE_fvs_any. eapply redE_dom_mono; [eassumption|].
           eapply redM_usedvars_inc in Hred0; [|eassumption].
           rewrite Hm4 in Hred0. assumption.
        -- eapply redE_xs_mono; [eassumption|].
           eapply redM_usedvars_inc in Hred; [|reflexivity].
           rewrite Hm3 in Hred. rewrite <- Hred.
           simpl. prove_list_inc.
      * eassumption.
      * eapply compat_res_trans; [exact Hcompat|].
        eapply compat_res_trans; [exact Hres3|].
        eassumption.
    + constructor; [|eassumption].
      eapply nenv_compat_list; [|eassumption]. eapply compat_res_trans; eassumption.
    + simpl. f_equal; [symmetry; assumption|].
      eapply nenv_compat_list; eassumption.
    + assumption.
  - inversion H9; unexistT; subst.
    do 3 eexists; splits 4.
    + reflexivity.
    + constructor. econstructor.
    + constructor; [eassumption|]. inversion H10; unexistT; subst; constructor; assumption.
    + apply compat_res_refl.
  - use_recM H3 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    use_recM H4 Hm3 Hrec3 Hread3 Hres3; [|eassumption|constructor; [eapply nenv_compat_list; eassumption|eassumption]].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      * eapply redE_dom_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred0; [|eassumption].
        rewrite Hm3 in Hred0. assumption.
      * eapply redE_xs_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred; [|reflexivity].
        rewrite Hm2 in Hred. assumption.
    + eassumption.
    + eapply compat_res_trans; eassumption.
  - inversion H9; unexistT; subst. inversion H10; unexistT; subst.
    use_recM H3 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    use_recM H4 Hm3 Hrec3 Hread3 Hres3; [|eassumption|constructor; [eapply nenv_compat_list; eassumption|eassumption]].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      * eapply redE_dom_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred0; [|eassumption].
        rewrite Hm3 in Hred0. assumption.
      * eapply redE_xs_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred; [|reflexivity].
        rewrite Hm2 in Hred. assumption.
    + eassumption.
    + eapply compat_res_trans; eassumption.
  - inversion H9; unexistT; subst. inversion H10; unexistT; subst.
    destruct (redM_mklazy_nres_compat t2 x env env0 m m2 res) as (Hcompat & Hm2 & Hres2); try assumption.
    use_recM H4 Hm3 Hrec3 Hread3 Hres3; [do 3 eexists; splits 4|reflexivity|constructor].
    + eassumption.
    + constructor. econstructor; [reflexivity| |eapply redE_xs_mono; [eassumption|]].
      * eapply redM_usedvars_inc in Hred; [|reflexivity]. rewrite Hm3 in Hred.
        erewrite redM_mklazy_usedvars_eq; eassumption.
      * erewrite redM_mklazy_usedvars_eq; [reflexivity|eassumption].
    + eassumption.
    + eapply compat_res_trans; [exact Hcompat|exact Hres3].
    + simpl. f_equal; [|eapply nenv_compat_list; eassumption].
      symmetry; assumption.
    + assumption.
  - inversion H7; unexistT; subst.
    do 3 eexists; splits 4.
    + reflexivity.
    + constructor. econstructor.
    + constructor; [eassumption|].
      inversion H8; unexistT; subst; simpl in *; constructor.
    + apply compat_res_refl.

  - destruct (redM_mknlazy_nres_compat l lc env env2 m m2 res) as (Hcompat & Hm2 & Hres2); try assumption.
    do 3 eexists; splits 4.
    + reflexivity.
    + constructor.
      apply redE_constr_shallow with
          (lc := map (fun t => match env_get_maybe_var env2 t with Some c => c | None => clo_term (snd m) t env2 end) l).
      rewrite Forall2_map_right, Forall2_map_same.
      assert (snd m = snd m2) by (eapply redM_mknlazy_usedvars_eq; eassumption).
      apply Forall_True. intros t.
      destruct env_get_maybe_var; [reflexivity|].
      eexists; splits 3; [reflexivity|rewrite H1; reflexivity|reflexivity].
    + constructor; [eassumption|]. constructor. rewrite map_map, <- Hres2. reflexivity.
    + assumption.
  - destruct (redM_mknlazy_nres_compat l lc env env2 m m2 res) as (Hcompat & Hm2 & Hres2); try assumption.
    pose (nlc := map (fun t => match env_get_maybe_var env2 t with Some c => c | None => clo_term (snd m) t env2 end) l).
    assert (map Some nlc = map (redM_mknlazy_nres l (snd m) lc res env2) lc) by
        (unfold nlc; rewrite map_map, Hres2; reflexivity).
    use_recM H6 Hm3 Hrec3 Hread3 Hres3 (redM_mknlazy_nres l (snd m) lc res env2); [|reflexivity|constructor; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + assert (Hmeq : snd m = snd m2) by (eapply redM_mknlazy_usedvars_eq; eassumption).
      constructor. econstructor; [|rewrite Hmeq; eassumption].
      unfold nlc; rewrite Forall2_map_right, Forall2_map_same.
      apply Forall_True. intros t.
      destruct env_get_maybe_var; [reflexivity|].
      eexists; splits 3; [reflexivity| |reflexivity].
      rewrite Hmeq. eapply redM_usedvars_inc in Hred; [|reflexivity].
      rewrite Hm3 in Hred; assumption.
    + eassumption.
    + eapply compat_res_trans; eassumption.
  - destruct ws; simpl in *; [|congruence].
    do 3 eexists; splits 4.
    + reflexivity.
    + constructor. econstructor.
    + constructor; [eassumption|]. constructor. assumption.
    + apply compat_res_refl.
  - destruct ws as [|c ws]; simpl in *; [congruence|].
    injection H13 as H13 H14.
    use_recM H4 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; [eassumption|symmetry; eassumption]].
    use_recM H6 Hm3 Hrec3 Hread3 Hres3; [|eassumption|constructor; try eassumption; eapply nenv_compat_list; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      * eapply redE_dom_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred0; [|eassumption]; rewrite Hm3 in Hred0. assumption.
      * eapply redE_xs_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred; [|reflexivity]; rewrite Hm2 in Hred. assumption.
    + eassumption.
    + eapply compat_res_trans; eassumption.
  - inversion H8; unexistT; subst.
    use_recM H2 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      inversion H10; unexistT; subst; simpl in *; eassumption.
    + eassumption.
    + eassumption.

  - use_recM H3 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    use_recM H4 Hm3 Hrec3 Hread3 Hres3; [|eassumption|constructor; [|eassumption]; eapply nenv_compat_list; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      * eapply redE_dom_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred0; [|eassumption]; rewrite Hm3 in Hred0. assumption.
      * eapply redE_xs_mono; [eassumption|].
        eapply redM_usedvars_inc in Hred; [|reflexivity]; rewrite Hm2 in Hred. assumption.
    + eassumption.
    + eapply compat_res_trans; eassumption.
  - inversion H9; unexistT; subst. inversion H10; unexistT; subst.
    use_recM H4 Hm2 Hrec2 Hread2 Hres2; [do 3 eexists; splits 4|reflexivity|constructor].
    + eassumption.
    + constructor. econstructor; [|eassumption].
      rewrite H3. f_equal. f_equal.
      erewrite <- map_length, <- H7, map_length. reflexivity.
    + eassumption.
    + eassumption.
    + rewrite !map_app. f_equal; eassumption.
    + eassumption.
  - inversion H8; unexistT; subst. inversion H9; unexistT; subst.
    use_recM H3 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor. eassumption.
    + eassumption.
    + eassumption.
  - do 3 eexists; splits 4.
    + reflexivity.
    + constructor. econstructor.
    + constructor; [eassumption|]. constructor.
    + apply compat_res_refl.
  - destruct (redM_nnewvar_nres_compat m m2 la lx p res) as (Hcompat & Hm2 & Hres2); try assumption.
    use_recM H4 Hm3 Hrec3 Hread3 Hres3 (redM_nnewvar_nres res la lx); [|reflexivity|constructor].
    + use_recM H5 Hm4 Hrec4 Hread4 Hres4; [do 3 eexists; splits 4|eassumption|constructor].
      * eassumption.
      * constructor. econstructor.
        -- eapply redM_nnewvar_distinct; eassumption.
        -- erewrite redM_nnewvar_incl; [|eassumption].
           eapply redM_usedvars_inc in Hred; [|reflexivity]. rewrite Hm3 in Hred.
           eapply redM_usedvars_inc in Hred0; [|eassumption]. rewrite Hm4 in Hred0.
           etransitivity; eassumption.
        -- eapply redE_xsdom_mono; [eassumption| |eapply redM_usedvars_inc in Hred0; [rewrite Hm4 in Hred0|]; eassumption].
           rewrite list_inc_app_left. split; [|eapply redM_nnewvar_usedvars_inc; eassumption].
           eapply redM_nnewvar_incl; eassumption.
        -- eapply redE_xs_mono; [eassumption|].
           etransitivity; [eapply redM_nnewvar_usedvars_inc; eassumption|].
           eapply redM_usedvars_inc in Hred; [|reflexivity]. rewrite Hm3 in Hred. assumption.
      * eassumption.
      * eapply compat_res_trans; [|exact Hres4]. eapply compat_res_trans; [exact Hcompat|exact Hres3].
      * eapply nenv_compat_list; [|eassumption].
        eapply compat_res_trans; eassumption.
      * assumption.
    + rewrite !map_app. f_equal; [|eapply nenv_compat_list; eassumption].
      rewrite map_map, Hres2. reflexivity.
    + assumption.
  - inversion H11; unexistT; subst.
    use_recM H3 Hm2 Hrec2 Hread2 Hres2; [|reflexivity|constructor; eassumption].
    do 3 eexists; splits 4.
    + eassumption.
    + constructor. econstructor.
      inversion H8; unexistT; subst; simpl in *; eassumption.
    + eassumption.
    + eassumption.

  - destruct e; simpl in *; try congruence; destruct o0; simpl in *; congruence.
Qed.
